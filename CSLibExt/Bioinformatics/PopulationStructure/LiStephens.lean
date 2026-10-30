/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkov
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Li–Stephens haplotype copying model and its `O(K)` forward recursion

Li and Stephens (2003) model a target haplotype as an imperfect mosaic of `K` reference
haplotypes. The hidden state at each site is the index `k : Fin K` of the reference haplotype
being copied. Between consecutive sites the copying process switches, with probability `ρ`, to a
reference haplotype drawn uniformly at random (possibly the same one), and otherwise keeps
copying the same one, so the transition probability from `k` to `k'` is
`(1 - ρ) [k = k'] + ρ / K`. At each site the target allele equals the copied reference allele
with probability `1 - ε` and differs with mismatch probability `ε`. The copied haplotype at the
first site is uniform.

The model is an instance of the generic hidden Markov model `HMM` of
`CSLibExt.MachineLearning.Sequence.HiddenMarkov` (`hmm`). Its emissions depend on the site
through the reference panel, so the observation at a site is the panel column together with the
target allele (`obs`): `(fun k => H k t, x t)`. The panel is a fixed covariate, not a random
observation: the emissions are a distribution over the target allele for a given column, so
`hmm` is the model of the target haplotype conditional on the panel, and is not normalized over
its whole observation type `Obs K A` (for `K = 1` the emissions summed over all
`(Fin 1 → Bool) × Bool` give `2`).

## Main results

* `trans_row_sum`, `init_sum`, `emit_sum_bool`: the transition rows and the initial law sum to
  `1`, and with biallelic sites (`A = Bool`) the emissions sum to `1` over the target allele
  for each fixed panel column. For `R = ℝ`, `K ≥ 1` and `ρ, ε ∈ [0, 1]` all weights are also
  nonnegative, so `likelihood` is the conditional probability of the target haplotype given the
  panel (the normalization of that conditional law over target sequences is not proved here).
* `fastForward_eq_forward`: **the standard `O(K)` forward recursion**
  `α_{t+1}(k) = e_k(t+1) ((1 - ρ) α_t(k) + ρ (∑ j, α_t(j)) / K)` computes the generic forward
  variables of `hmm`; `likelihood_eq_sum_fastForward`: their sum is the likelihood.
* `fastForwardTab_get`, `likelihoodTab_eq`: the tabulated version on vectors, which computes
  the total `∑ j, α_t(j)` once per site.

## Cost model

The cost is the number of field operations. The generic forward step does `O(K²)` operations
(a sum over predecessors for each of the `K` states). Because every switch lands on a uniformly
random haplotype, the sum over predecessors collapses to `(1 - ρ) α_t(k) + ρ S / K` with the
single total `S = ∑ j, α_t(j)`. `fastStepTab` computes `S` once and then `O(1)` operations for
each state, so a site costs `O(K)`; `fastForwardTab` passes each site's table to the next, so
`t + 1` sites cost `O(t K)` in total. `fastStep` and `fastForward` are the pointwise
specification of the same recursion and make no cost claim: `fastStep` evaluates the sum
`∑ j, v j` anew for each output state (`O(K²)` for all `K` states), and the untabulated
`fastForward` re-evaluates earlier sites inside that sum.

## Parameter domain

The model's parameters are probabilities, `0 ≤ ρ ≤ 1` and `0 ≤ ε ≤ 1`, with `K ≥ 1`. The
recursion identities (`fastForward_eq_forward` and the tabulated versions) are algebraic and
hold for all `ρ ε` in any field, without these assumptions; outside the domain the weights may
cease to be probabilities. The rows always sum to `1`; the switching weight `ρ / K` is negative
exactly when `ρ < 0`, and the staying weight `1 - ρ + ρ / K` is negative exactly when
`ρ > K / (K - 1)` for `K ≥ 2` (for `K = 1` it is always `1`). For example, `K = 3` and `ρ = 2`
give staying weight `-1/3`, while `ρ = 11/10` still gives a stochastic row.

## Scope

The switch probability `ρ` is the same between every pair of consecutive sites; Li and Stephens
let it depend on the genetic distance between sites (`ρ_t = 1 - exp (-r_t / K)` with the scaled
recombination rate `r_t`). Their two-allele mismatch probability is the constant `ε` here.

## References

* N. Li and M. Stephens, *Modeling linkage disequilibrium and identifying recombination
  hotspots using single-nucleotide polymorphism data*, Genetics 165 (2003), 2213–2233.
* L. R. Rabiner, *A tutorial on hidden Markov models and selected applications in speech
  recognition*, Proc. IEEE 77 (1989), 257–286.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.PopulationStructure.LiStephens

open Cslib.MachineLearning.Sequence.HiddenMarkov

variable {A R : Type*} [DecidableEq A] [Field R] {K : ℕ}

/-- The observation at a site: the column of reference alleles and the target allele. -/
abbrev Obs (K : ℕ) (A : Type*) := (Fin K → A) × A

/-- The observation sequence for the reference panel `H` (haplotype `k` carries allele
`H k t` at site `t`) and the target haplotype `x`. -/
def obs (H : Fin K → ℕ → A) (x : ℕ → A) (t : ℕ) : Obs K A := (fun k => H k t, x t)

/-- The copying transition probability: switch with probability `ρ` to a uniformly random
reference haplotype (possibly the same one), otherwise keep copying `k`:
`(1 - ρ) [k = k'] + ρ / K`. -/
def trans (ρ : R) (k k' : Fin K) : R := (1 - ρ) * (if k = k' then 1 else 0) + ρ / K

/-- The emission probability: `1 - ε` if the target allele equals the allele of the copied
haplotype `k`, and the mismatch probability `ε` otherwise. -/
def emit (ε : R) (k : Fin K) (o : Obs K A) : R := if o.1 k = o.2 then 1 - ε else ε

/-- **The Li–Stephens copying model** with `K` reference haplotypes, switch probability `ρ` and
mismatch probability `ε`, as a hidden Markov model with a uniform initial copied haplotype. -/
def hmm (K : ℕ) (ρ ε : R) : HMM (Fin K) (Obs K A) R where
  init _ := 1 / K
  trans := trans ρ
  emit := emit ε

/-- Each transition row sums to `1` (when `K` is invertible in `R`, e.g. `K ≠ 0` over `ℝ`). -/
theorem trans_row_sum (hK : (K : R) ≠ 0) (ρ : R) (k : Fin K) : ∑ k', trans ρ k k' = 1 := by
  simp only [trans, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The initial law (uniform over the `K` haplotypes) sums to `1`. -/
theorem init_sum (hK : (K : R) ≠ 0) (ρ ε : R) :
    ∑ k, (hmm (A := A) K ρ ε).init k = 1 := by
  simp only [hmm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- With biallelic sites, the two emission probabilities at a site sum to `1` over the target
allele, for each fixed panel column `col` (the emissions are conditional on the panel). -/
theorem emit_sum_bool (ε : R) (k : Fin K) (col : Fin K → Bool) :
    ∑ a : Bool, emit ε k (col, a) = 1 := by
  cases h : col k <;> simp [emit, h]

/-- One step of the collapsed forward recursion on the previous site's forward variables `v`,
at output state `k`: `e_k ((1 - ρ) v k + ρ (∑ j, v j) / K)`. This is the pointwise
specification; each call evaluates the length-`K` sum, so use `fastStepTab` for the `O(K)`
per-site step. -/
def fastStep (ρ ε : R) (o : Obs K A) (v : Fin K → R) (k : Fin K) : R :=
  emit ε k o * ((1 - ρ) * v k + ρ * (∑ j, v j) / K)

/-- The forward variables of the collapsed recursion, as a function of site and state. This is
the untabulated specification (it re-evaluates earlier sites inside each sum); `fastForwardTab`
is the `O(t K)` implementation. -/
def fastForward (ρ ε : R) (y : ℕ → Obs K A) : ℕ → Fin K → R
  | 0, k => 1 / K * emit ε k (y 0)
  | t + 1, k => fastStep ρ ε (y (t + 1)) (fastForward ρ ε y t) k

/-- The sum over predecessors collapses: `∑ j, v j * trans ρ j k = (1 - ρ) v k + ρ (∑ v) / K`. -/
theorem sum_mul_trans (ρ : R) (v : Fin K → R) (k : Fin K) :
    ∑ j, v j * trans ρ j k = (1 - ρ) * v k + ρ * (∑ j, v j) / K := by
  simp only [trans, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul]
  ring

/-- **The collapsed forward recursion computes the forward variables** of the Li–Stephens HMM. -/
theorem fastForward_eq_forward (ρ ε : R) (y : ℕ → Obs K A) :
    ∀ (t : ℕ) (k : Fin K), fastForward ρ ε y t k = forward (hmm K ρ ε) y t k
  | 0, k => rfl
  | t + 1, k => by
      have ih : fastForward ρ ε y t = forward (hmm K ρ ε) y t :=
        funext (fastForward_eq_forward ρ ε y t)
      simp only [fastForward, fastStep, forward, ih]
      rw [show (hmm K ρ ε : HMM (Fin K) (Obs K A) R).trans = trans ρ from rfl, sum_mul_trans]
      simp only [hmm]
      ring

/-- **The likelihood of the target haplotype** (given the panel) is the sum of the collapsed
forward variables. -/
theorem likelihood_eq_sum_fastForward (ρ ε : R) (y : ℕ → Obs K A) (t : ℕ) :
    likelihood (hmm K ρ ε) y t = ∑ k, fastForward ρ ε y t k := by
  rw [likelihood_eq_sum_forward]
  exact Finset.sum_congr rfl fun k _ => (fastForward_eq_forward ρ ε y t k).symm

/-- One tabulated `O(K)` step: the total of the previous table is computed once. -/
def fastStepTab (ρ ε : R) (o : Obs K A) (v : Vector R K) : Vector R K :=
  let S := sumVec v
  Vector.ofFn fun k => emit ε k o * ((1 - ρ) * v[k] + ρ * S / K)

/-- The `O(K)` forward variables, tabulated site by site: `O(t K)` operations in total. -/
def fastForwardTab (ρ ε : R) (y : ℕ → Obs K A) : ℕ → Vector R K
  | 0 => Vector.ofFn fun k => 1 / K * emit ε k (y 0)
  | t + 1 => fastStepTab ρ ε (y (t + 1)) (fastForwardTab ρ ε y t)

/-- The tabulated `O(K)` recursion computes the forward variables of the Li–Stephens HMM. -/
theorem fastForwardTab_get (ρ ε : R) (y : ℕ → Obs K A) :
    ∀ (t : ℕ) (k : Fin K), (fastForwardTab ρ ε y t)[k] = forward (hmm K ρ ε) y t k
  | 0, k => by simp [fastForwardTab, ← fastForward_eq_forward, fastForward]
  | t + 1, k => by
      have ih := fastForwardTab_get ρ ε y t
      simp only [fastForwardTab, fastStepTab, sumVec]
      simp [ih, ← fastForward_eq_forward, fastForward, fastStep]

/-- **The tabulated Li–Stephens likelihood** in `O(t K)` operations. -/
def likelihoodTab (ρ ε : R) (y : ℕ → Obs K A) (t : ℕ) : R := sumVec (fastForwardTab ρ ε y t)

/-- The tabulated `O(K)` recursion computes the likelihood of the target haplotype. -/
theorem likelihoodTab_eq (ρ ε : R) (y : ℕ → Obs K A) (t : ℕ) :
    likelihoodTab ρ ε y t = likelihood (hmm K ρ ε) y t := by
  rw [likelihood_eq_sum_forward, likelihoodTab, sumVec]
  exact Finset.sum_congr rfl fun k _ => fastForwardTab_get ρ ε y t k

end Cslib.Bioinformatics.PopulationStructure.LiStephens

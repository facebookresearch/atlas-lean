/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Field

/-!
# Mutation–selection balance for heterozygous loss-of-function variants (`s_het`)

Loss-of-function (LoF) alleles of a gene arise at rate `U` per gene copy per generation and
lower the fitness of heterozygous carriers by `s = s_het`.

**Linear model.** When homozygotes are negligible the LoF frequency evolves by
`x ↦ (1 - s) x + U`, whose equilibrium `U / s` is the deterministic expectation used by Cassa
et al. (2017) and Weghorn et al. (2019). The fixed point is unique and attracts every orbit for
`0 < s < 2`; at it the fraction of LoF alleles that are new mutations is exactly `s` (the
"fraction of de novo mutations, a direct measure of `s_het`" of Weghorn et al.). In the
Wright–Fisher chain with this sampling probability and **arbitrary** population sizes
`N₀, N₁, …` (any demography), the expected frequency obeys the same linear recursion exactly,
so it tends to `U / s` whatever the demographic history. This exact statement is derived here
from the binomial mean; Weghorn et al. examine the deterministic approximation under realistic
demography by simulation, and drift does change the variance and the distribution.

**Diploid model.** Hardy–Weinberg genotypes with fitnesses `1, 1 - s, 1 - t` for wild-type
homozygotes, heterozygotes and LoF homozygotes, selection then mutation of wild-type alleles at
rate `U`. With multiplicative fitness `1 - t = (1 - s)²` the equilibrium is exactly `U / s`, and
mean fitness there is `(1 - U)²` whatever `s`: the load `1 - (1 - U)² = 2U - U²` depends on the
mutation rate alone (the Haldane–Muller principle; Haldane 1937, Muller 1950). If homozygotes
are at least that unfit (`t ≥ 2s - s²`, e.g. recessive lethal) every equilibrium in `[0, 1)`
lies at or below `U / s`. These exact finite statements (closed form and bound) are derived
here; the sources state the approximations `q ≈ U / s` and load `≈ 2U`.

## Main results

* `linStep_iterate`, `linStep_eq_self_iff`, `tendsto_linStep_iterate`: closed-form orbits, unique
  fixed point `U / s`, global attraction.
* `deNovoFraction_eq`: at equilibrium the de novo fraction `U / x*` is `s`.
* `meanFreq_pushStep`, `meanFreq_law`, `tendsto_meanFreq_law`: the **demography-free mean** of the
  linear Wright–Fisher chain with any sizes.
* `diploidStep_mult_fixed`: `U / s` is an equilibrium of the multiplicative diploid model.
* `meanFitness_mult_at_equilibrium`, `load_mult_at_equilibrium`: the Haldane–Muller load.
* `le_div_of_diploidStep_eq`: equilibria are at most `U / s` when `t ≥ 2s - s²`.

## Conventions

Time is in generations (not the diffusion units of `MathlibExt/Biology/README.md`) and
frequencies are per gene copy. `U` is the LoF mutation rate per copy per generation (the sum
over LoF sites) and `s` the per-generation fitness reduction of heterozygotes. The linear and
algebraic identities hold for all reals where stated; they are population-genetic statements
for `0 ≤ U ≤ s ≤ 1`, which keeps the sampling probability `(1 - s) x + U` in `[0, 1]` for
`x ∈ [0, 1]` (`kernel_nonneg`) and the equilibrium `U / s` in `[0, 1]`. The diploid bound needs
`0 < s ≤ 1`, `t ≤ 1` and `q < 1` so that mean fitness is positive (`meanFitness_pos`).

## References

* C. A. Cassa, D. Weghorn, D. J. Balick, D. M. Jordan, D. Nusinow, K. E. Samocha,
  A. O'Donnell-Luria, D. G. MacArthur, M. J. Daly, D. R. Beier, S. R. Sunyaev, *Estimating the
  selective effects of heterozygous protein-truncating variants from human exome data*,
  Nat. Genet. 49 (2017), 806–810.
* D. Weghorn, D. J. Balick, C. Cassa, J. A. Kosmicki, M. J. Daly, D. R. Beier, S. R. Sunyaev,
  *Applicability of the mutation–selection balance model to population genetics of
  heterozygous protein-truncating variants in humans*, Mol. Biol. Evol. 36 (2019), 1701–1710.
* J. B. S. Haldane, *The effect of variation on fitness*, Amer. Nat. 71 (1937), 337–349.
* H. J. Muller, *Our load of mutations*, Amer. J. Hum. Genet. 2 (1950), 111–176.
-/

@[expose] public section

open Finset Filter Topology

namespace MathlibExt.Biology.PopulationGenetics.MutationSelectionBalance

/-! ### The linear recursion -/

/-- One generation of the linear model: `x ↦ (1 - s) x + U`. -/
def linStep (s U x : ℝ) : ℝ := (1 - s) * x + U

/-- Closed-form orbit: `x_t = U / s + (1 - s)^t (x_0 - U / s)`. -/
theorem linStep_iterate {s : ℝ} (hs : s ≠ 0) (U x : ℝ) (t : ℕ) :
    (linStep s U)^[t] x = U / s + (1 - s) ^ t * (x - U / s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, linStep, pow_succ]
    field_simp
    ring

/-- `U / s` is the unique fixed point. -/
theorem linStep_eq_self_iff {s : ℝ} (hs : s ≠ 0) (U x : ℝ) :
    linStep s U x = x ↔ x = U / s := by
  unfold linStep
  constructor
  · intro h
    field_simp
    linarith
  · rintro rfl
    field_simp
    ring

/-- **Global attraction**: for `0 < s < 2` every orbit converges to `U / s`. -/
theorem tendsto_linStep_iterate {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (U x : ℝ) :
    Tendsto (fun t => (linStep s U)^[t] x) atTop (𝓝 (U / s)) := by
  simp_rw [linStep_iterate hs0.ne' U x]
  have h : Tendsto (fun t : ℕ => (1 - s) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith)
  simpa using (h.mul_const (x - U / s)).const_add (U / s)

/-- The fraction of LoF alleles in the next generation that are new mutations, from
frequency `x`: `U / ((1 - s) x + U)`. -/
noncomputable def deNovoFraction (s U x : ℝ) : ℝ := U / linStep s U x

/-- **At equilibrium the de novo fraction is `s_het`.** -/
theorem deNovoFraction_eq {s U : ℝ} (hs : s ≠ 0) (hU : U ≠ 0) :
    deNovoFraction s U (U / s) = s := by
  rw [deNovoFraction, (linStep_eq_self_iff hs U _).mpr rfl]
  field_simp

/-! ### The linear Wright–Fisher chain with arbitrary population sizes -/

/-- The transition probability from `i` LoF copies among `N` to `j` copies among `N'`: binomial
sampling of `N'` copies with success probability `(1 - s)(i / N) + U`. -/
noncomputable def kernel (s U : ℝ) (N N' : ℕ) (i : Fin (N + 1)) (j : Fin (N' + 1)) : ℝ :=
  (bernsteinPolynomial ℝ N' j).eval (linStep s U ((i : ℕ) / N))

/-- The mean LoF frequency `∑ μ_i (i / N)` of a distribution `μ` on `Fin (N + 1)`. -/
noncomputable def meanFreq (N : ℕ) (μ : Fin (N + 1) → ℝ) : ℝ := ∑ i, μ i * ((i : ℕ) / N)

/-- One generation of the chain acting on distributions. -/
noncomputable def pushStep (s U : ℝ) (N N' : ℕ) (μ : Fin (N + 1) → ℝ) : Fin (N' + 1) → ℝ :=
  fun j => ∑ i, μ i * kernel s U N N' i j

/-- The kernel rows have total mass one (for every real sampling probability). -/
theorem sum_kernel (s U : ℝ) (N N' : ℕ) (i : Fin (N + 1)) : ∑ j, kernel s U N N' i j = 1 := by
  have h := congrArg (Polynomial.eval (linStep s U ((i : ℕ) / N))) (bernsteinPolynomial.sum ℝ N')
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range (fun j => (bernsteinPolynomial ℝ N' j).eval _)]
  rfl

/-- The kernel entries are probabilities when the sampling probability is in `[0, 1]`. -/
theorem kernel_nonneg {s U : ℝ} {N N' : ℕ} {i : Fin (N + 1)}
    (h0 : 0 ≤ linStep s U ((i : ℕ) / N)) (h1 : linStep s U ((i : ℕ) / N) ≤ 1)
    (j : Fin (N' + 1)) : 0 ≤ kernel s U N N' i j := by
  unfold kernel
  rw [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_natCast, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X]
  have : 0 ≤ 1 - linStep s U ((i : ℕ) / N) := by linarith
  positivity

/-- The binomial mean: `∑_j kernel(i, j) (j / N') = (1 - s)(i / N) + U` for `N' > 0`. -/
theorem sum_kernel_mul (s U : ℝ) (N : ℕ) {N' : ℕ} (hN' : 0 < N') (i : Fin (N + 1)) :
    ∑ j, kernel s U N N' i j * ((j : ℕ) / N') = linStep s U ((i : ℕ) / N) := by
  set x := linStep s U ((i : ℕ) / N)
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum_smul ℝ N')
  simp only [Polynomial.eval_finsetSum, nsmul_eq_mul, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_X] at h
  have hN : (N' : ℝ) ≠ 0 := by exact_mod_cast hN'.ne'
  rw [← Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) * (bernsteinPolynomial ℝ N' j).eval x)] at h
  have : ∑ j : Fin (N' + 1), kernel s U N N' i j * ((j : ℕ) / N') =
      (∑ j : Fin (N' + 1), ((j : ℕ) : ℝ) * (bernsteinPolynomial ℝ N' j).eval x) / N' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold kernel
    ring
  rw [this, h]
  field_simp

/-- **Demography-free mean, one step**: for any sizes `N`, `N' > 0` and any distribution `μ`
of total mass one, the mean frequency after one generation is `(1 - s) m + U`. -/
theorem meanFreq_pushStep (s U : ℝ) (N : ℕ) {N' : ℕ} (hN' : 0 < N') {μ : Fin (N + 1) → ℝ}
    (hμ : ∑ i, μ i = 1) : meanFreq N' (pushStep s U N N' μ) = linStep s U (meanFreq N μ) := by
  unfold meanFreq pushStep
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, sum_kernel_mul s U N hN', linStep, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, hμ]
  rw [Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · ring

/-- Pushing a distribution forward preserves total mass. -/
theorem sum_pushStep (s U : ℝ) (N N' : ℕ) {μ : Fin (N + 1) → ℝ} (hμ : ∑ i, μ i = 1) :
    ∑ j, pushStep s U N N' μ j = 1 := by
  unfold pushStep
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_kernel, mul_one, hμ]

/-- The law of the LoF count in generation `t` for population sizes `N t` (any demography),
started from `μ₀`. -/
noncomputable def law (s U : ℝ) (N : ℕ → ℕ) (μ₀ : Fin (N 0 + 1) → ℝ) :
    (t : ℕ) → Fin (N t + 1) → ℝ
  | 0 => μ₀
  | t + 1 => pushStep s U (N t) (N (t + 1)) (law s U N μ₀ t)

/-- **Demography-free mean**: for every sequence of positive population sizes, `E[X_t]` follows
the deterministic linear recursion (derived from the binomial mean). The identity holds for all
real `s, U`; `law` is a probability law when `0 ≤ U ≤ s ≤ 1` and `μ₀` is one. -/
theorem meanFreq_law (s U : ℝ) {N : ℕ → ℕ} (hN : ∀ t, 0 < N t) {μ₀ : Fin (N 0 + 1) → ℝ}
    (hμ₀ : ∑ i, μ₀ i = 1) (t : ℕ) :
    meanFreq (N t) (law s U N μ₀ t) = (linStep s U)^[t] (meanFreq (N 0) μ₀) := by
  have hmass : ∀ t, ∑ i, law s U N μ₀ t i = 1 := by
    intro t
    induction t with
    | zero => exact hμ₀
    | succ t ih => exact sum_pushStep s U _ _ ih
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact meanFreq_pushStep s U _ (hN (t + 1)) (hmass t)

/-- The expected LoF frequency converges to `U / s` under any demography. -/
theorem tendsto_meanFreq_law {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (U : ℝ) {N : ℕ → ℕ}
    (hN : ∀ t, 0 < N t) {μ₀ : Fin (N 0 + 1) → ℝ} (hμ₀ : ∑ i, μ₀ i = 1) :
    Tendsto (fun t => meanFreq (N t) (law s U N μ₀ t)) atTop (𝓝 (U / s)) := by
  simp_rw [meanFreq_law s U hN hμ₀]
  exact tendsto_linStep_iterate hs0 hs2 U _

/-! ### The diploid model -/

/-- Mean fitness under Hardy–Weinberg with LoF frequency `q` and fitnesses `1, 1 - s, 1 - t`:
`1 - 2 q (1 - q) s - q² t`. -/
def meanFitness (s t q : ℝ) : ℝ := 1 - 2 * q * (1 - q) * s - q ^ 2 * t

/-- LoF frequency after selection: `q (1 - s (1 - q) - t q) / w̄`. -/
noncomputable def selected (s t q : ℝ) : ℝ := q * (1 - s * (1 - q) - t * q) / meanFitness s t q

/-- One generation: selection, then mutation of wild-type alleles at rate `U`. -/
noncomputable def diploidStep (s t U q : ℝ) : ℝ := (1 - U) * selected s t q + U

/-- With multiplicative fitness, `w̄ = (1 - s q)²` for every `q`. -/
theorem meanFitness_mult (s q : ℝ) : meanFitness s (2 * s - s ^ 2) q = (1 - s * q) ^ 2 := by
  unfold meanFitness; ring

/-- **`U / s` is an equilibrium** of the multiplicative diploid model (an algebraic identity for
`s ≠ 0`, `U ≠ 1`; a frequency in `[0, 1]` when `0 ≤ U ≤ s`). -/
theorem diploidStep_mult_fixed {s U : ℝ} (hs : s ≠ 0) (hU : U ≠ 1) :
    diploidStep s (2 * s - s ^ 2) U (U / s) = U / s := by
  unfold diploidStep selected
  rw [meanFitness_mult]
  have h1 : 1 - s * (U / s) = 1 - U := by field_simp
  have h2 : (1 - U) ≠ 0 := sub_ne_zero.mpr (Ne.symm hU)
  rw [h1]
  field_simp
  ring

/-- At the multiplicative equilibrium the mean fitness is `(1 - U)²`, independent of `s`.
Requires `U ≠ 1`, so that `U / s` is genuinely a fixed point (`diploidStep_mult_fixed`):
for `U = 1` the point `U / s` is not an equilibrium. -/
theorem meanFitness_mult_at_equilibrium {s : ℝ} (hs : s ≠ 0) (hU : U ≠ 1) (U : ℝ) :
    meanFitness s (2 * s - s ^ 2) (U / s) = (1 - U) ^ 2 := by
  rw [meanFitness_mult]; field_simp

/-- **Haldane–Muller load**: `1 - w̄ = 2U - U²` at the multiplicative equilibrium
(`U ≠ 1`, so `U / s` is a fixed point). -/
theorem load_mult_at_equilibrium {s : ℝ} (hs : s ≠ 0) (hU : U ≠ 1) (U : ℝ) :
    1 - meanFitness s (2 * s - s ^ 2) (U / s) = 2 * U - U ^ 2 := by
  rw [meanFitness_mult_at_equilibrium hs hU]; ring

/-- Mean fitness is positive for `0 ≤ q < 1` and `s, t ≤ 1` (nonnegative fitnesses). -/
theorem meanFitness_pos {s t q : ℝ} (hs : s ≤ 1) (ht : t ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < meanFitness s t q := by
  have : meanFitness s t q =
      (1 - q) ^ 2 + 2 * q * (1 - q) * (1 - s) + q ^ 2 * (1 - t) := by
    unfold meanFitness; ring
  rw [this]
  have h1 : 0 < (1 - q) ^ 2 := by have : 0 < 1 - q := by linarith
                                  positivity
  have h2 : 0 ≤ 2 * q * (1 - q) * (1 - s) := by
    have : 0 ≤ 1 - q := by linarith
    have : 0 ≤ 1 - s := by linarith
    positivity
  have h3 : 0 ≤ q ^ 2 * (1 - t) := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  linarith

/-- **Equilibria lie at or below `U / s`** when homozygotes are at least multiplicatively unfit
(`2s - s² ≤ t`, which includes recessive lethality `t = 1`): every fixed point `q ∈ [0, 1)` of
the diploid map satisfies `q ≤ U / s`. -/
theorem le_div_of_diploidStep_eq {s t U q : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (ht : t ≤ 1)
    (hst : 2 * s - s ^ 2 ≤ t) (hq0 : 0 ≤ q) (hq1 : q < 1) (hfix : diploidStep s t U q = q) :
    q ≤ U / s := by
  have hw := meanFitness_pos hs1 ht hq0 hq1
  -- `1 - selected = (1 - q)(1 - s q) / w̄`
  have hsel : 1 - selected s t q = (1 - q) * (1 - s * q) / meanFitness s t q := by
    unfold selected
    field_simp
    unfold meanFitness
    ring
  have hfix' : 1 - q = (1 - U) * (1 - selected s t q) := by
    unfold diploidStep at hfix; linarith
  rw [hsel] at hfix'
  have hq1' : 0 < 1 - q := by linarith
  -- hence `w̄ = (1 - U)(1 - s q)`
  have hw' : meanFitness s t q = (1 - U) * (1 - s * q) := by
    field_simp at hfix'
    linarith
  have hsq : 0 < 1 - s * q := by nlinarith
  -- `U (1 - s q) = q (s - (2 s - t) q) ≥ s q (1 - s q)`
  have key : U * (1 - s * q) = q * (s - (2 * s - t) * q) := by
    unfold meanFitness at hw'; nlinarith [hw']
  have hge : s * q * (1 - s * q) ≤ U * (1 - s * q) := by
    rw [key]
    have : q * (s * q) * (2 * s - t - s ^ 2) ≤ 0 := by
      have : 2 * s - t - s ^ 2 ≤ 0 := by linarith
      have : 0 ≤ q * (s * q) := by positivity
      nlinarith
    nlinarith
  have : s * q ≤ U := le_of_mul_le_mul_right hge hsq
  rw [le_div_iff₀ hs0]
  linarith

end MathlibExt.Biology.PopulationGenetics.MutationSelectionBalance

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import MathlibExt.InformationTheory.LogSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expectation-maximization never decreases the likelihood

The expectation-maximization algorithm (Dempster, Laird and Rubin, *Maximum likelihood from
incomplete data via the EM algorithm*, J. Roy. Statist. Soc. B 39, 1977; Bishop, *Pattern
Recognition and Machine Learning*, Section 9.4) for a model `p θ x z > 0` with a finite latent
space `Z` and data `xs : Fin N → X`. The log-likelihood is `logLik θ = ∑ n, log ∑ z, p θ (xs n) z`;
the E-step computes the posteriors `posterior θ x z = p θ x z / ∑ z', p θ x z'`; the M-step
increases `emQ θ' θ = ∑ n, ∑ z, posterior θ (xs n) z * log (p θ' (xs n) z)` in `θ'`.

Main results:

* `sum_mul_log_sub_le`: Gibbs' inequality `∑ q (log p - log q) ≤ log ∑ p` for a distribution `q`
  (from MathlibExt's log-sum inequality, `MathlibExt/InformationTheory/LogSum.lean`), tight at
  `q = p / ∑ p` (`sum_div_mul_log_sub`).
* `elbo_le_logLik`: **the evidence lower bound** `elbo θ q ≤ logLik θ` for all latent
  distributions; `elbo_posterior`: **equality at the posterior**.
* `emQ_sub_le_logLik_sub`: `ℓ(θ') - ℓ(θ) ≥ Q(θ' | θ) - Q(θ | θ)`; `logLik_le_of_emQ_le`: **the EM
  theorem**, a step that does not decrease `Q(· | θ)` does not decrease the likelihood.
* `logLik_iterate_monotone`: **the likelihood is monotone along the EM iterates** of any M-step
  with `Q(M θ | θ) ≥ Q(θ | θ)`.

## Relation to `FormalizedTextbooks`

`FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/Ch24.lean` states the
monotonicity of EM as a hypothesis (`EMMonotone L : ∀ t, L t ≤ L (t + 1)` on a bare sequence `L`);
`logLik_iterate_monotone` proves it for the log-likelihood along EM iterates. The two-component
symmetric Gaussian mixture of
`FormalizedTextbooks/HighDimensionalProbability/Chapter04/Section07/GaussianMixtureModel.lean` is a
distributional statement and does not involve EM.

## Cost model

No running-time model: the subject is the likelihood, over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.ExpectationMaximization

open Real

variable {Θ X Z : Type*} [Fintype Z]

/-! ## Gibbs' inequality -/

/-- A probability distribution on the finite latent space. -/
def IsDist (q : Z → ℝ) : Prop := (∀ z, 0 ≤ q z) ∧ ∑ z, q z = 1

/-- **Gibbs' inequality**, in the form behind the evidence lower bound: for positive weights `p`
and a distribution `q`, `∑ q (log p - log q) ≤ log ∑ p`. This is MathlibExt's log-sum inequality
`Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div` with `∑ q = 1`; terms with `q z = 0`
contribute `0` on both sides. -/
theorem sum_mul_log_sub_le {p q : Z → ℝ} (hp : ∀ z, 0 < p z) (hq : IsDist q) :
    ∑ z, q z * (log (p z) - log (q z)) ≤ log (∑ z, p z) := by
  obtain ⟨hq0, hq1⟩ := hq
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div Finset.univ q p
    (fun z _ => hq0 z) (fun z _ => hp z)
  rw [hq1, one_mul, one_div, log_inv] at h
  have hterm : ∀ z, q z * log (q z / p z) = -(q z * (log (p z) - log (q z))) := by
    intro z
    rcases (hq0 z).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [log_div hpos.ne' (hp z).ne']; ring
  simp only [hterm, Finset.sum_neg_distrib] at h
  linarith

/-- Equality in Gibbs' inequality at `q = p / ∑ p`. -/
theorem sum_div_mul_log_sub {p : Z → ℝ} (hp : ∀ z, 0 < p z) [Nonempty Z] :
    ∑ z, p z / (∑ z', p z') * (log (p z) - log (p z / ∑ z', p z')) = log (∑ z, p z) := by
  have hPpos : 0 < ∑ z', p z' := Finset.sum_pos (fun z _ => hp z) Finset.univ_nonempty
  have : ∀ z, p z / (∑ z', p z') * (log (p z) - log (p z / ∑ z', p z')) =
      p z / (∑ z', p z') * log (∑ z', p z') := by
    intro z
    rw [log_div (hp z).ne' hPpos.ne']
    ring
  rw [Finset.sum_congr rfl fun z _ => this z, ← Finset.sum_mul, ← Finset.sum_div,
    div_self hPpos.ne', one_mul]

/-! ## The model -/

variable {N : ℕ}

/-- The marginal `p_θ(x) = ∑ z, p_θ(x, z)` of a joint model `p` with finite latent space `Z`. -/
def marginal (p : Θ → X → Z → ℝ) (θ : Θ) (x : X) : ℝ := ∑ z, p θ x z

/-- The log-likelihood `ℓ(θ) = ∑ n, log p_θ(xₙ)` of the data `xs`. -/
noncomputable def logLik (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ) : ℝ :=
  ∑ n, log (marginal p θ (xs n))

/-- The posterior `p_θ(z | x) = p_θ(x, z) / p_θ(x)` (the E-step). -/
noncomputable def posterior (p : Θ → X → Z → ℝ) (θ : Θ) (x : X) (z : Z) : ℝ :=
  p θ x z / marginal p θ x

/-- The evidence lower bound of per-point latent distributions `q`:
`∑ n, ∑ z, q n z (log p_θ(xₙ, z) - log q n z)`. -/
noncomputable def elbo (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ) (q : Fin N → Z → ℝ) : ℝ :=
  ∑ n, ∑ z, q n z * (log (p θ (xs n) z) - log (q n z))

/-- The EM objective `Q(θ' | θ) = ∑ n, ∑ z, p_θ(z | xₙ) log p_θ'(xₙ, z)` (maximized in the
M-step). -/
noncomputable def emQ (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ' θ : Θ) : ℝ :=
  ∑ n, ∑ z, posterior p θ (xs n) z * log (p θ' (xs n) z)

/-- The entropy of the posteriors, `-∑ n, ∑ z, p_θ(z | xₙ) log p_θ(z | xₙ)`. -/
noncomputable def postEntropy (p : Θ → X → Z → ℝ) (xs : Fin N → X) (θ : Θ) : ℝ :=
  -∑ n, ∑ z, posterior p θ (xs n) z * log (posterior p θ (xs n) z)

variable {p : Θ → X → Z → ℝ}

/-- The posterior is a distribution. -/
theorem isDist_posterior [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (θ : Θ) (x : X) :
    IsDist (posterior p θ x) := by
  have hpos : 0 < marginal p θ x := Finset.sum_pos (fun z _ => hp θ x z) Finset.univ_nonempty
  refine ⟨fun z => (div_pos (hp θ x z) hpos).le, ?_⟩
  simp only [posterior]
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-- **The evidence lower bound**: for every choice of latent distributions, `elbo ≤ ℓ`. -/
theorem elbo_le_logLik (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X) (θ : Θ)
    {q : Fin N → Z → ℝ} (hq : ∀ n, IsDist (q n)) : elbo p xs θ q ≤ logLik p xs θ :=
  Finset.sum_le_sum fun n _ => sum_mul_log_sub_le (fun z => hp θ (xs n) z) (hq n)

/-- **The bound is tight at the posterior**: `elbo(θ, p_θ(· | x)) = ℓ(θ)`. -/
theorem elbo_posterior [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X) (θ : Θ) :
    elbo p xs θ (fun n => posterior p θ (xs n)) = logLik p xs θ :=
  Finset.sum_congr rfl fun n _ => sum_div_mul_log_sub fun z => hp θ (xs n) z

/-- The ELBO at the posterior of `θ` splits as `Q(θ' | θ)` plus the posterior entropy. -/
theorem elbo_posterior_eq (xs : Fin N → X) (θ' θ : Θ) :
    elbo p xs θ' (fun n => posterior p θ (xs n)) = emQ p xs θ' θ + postEntropy p xs θ := by
  simp only [elbo, emQ, postEntropy, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **The EM inequality**: the likelihood gains at least as much as `Q(· | θ)`:
`ℓ(θ') - ℓ(θ) ≥ Q(θ' | θ) - Q(θ | θ)`. -/
theorem emQ_sub_le_logLik_sub [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X)
    (θ' θ : Θ) : emQ p xs θ' θ - emQ p xs θ θ ≤ logLik p xs θ' - logLik p xs θ := by
  have h1 := elbo_le_logLik hp xs θ' (q := fun n => posterior p θ (xs n))
    fun n => isDist_posterior hp θ (xs n)
  have h2 := elbo_posterior hp xs θ
  rw [elbo_posterior_eq] at h1 h2
  linarith

/-- **The EM theorem**: a step that does not decrease `Q(· | θ)` does not decrease the
likelihood. -/
theorem logLik_le_of_emQ_le [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X)
    {θ' θ : Θ} (h : emQ p xs θ θ ≤ emQ p xs θ' θ) : logLik p xs θ ≤ logLik p xs θ' := by
  have := emQ_sub_le_logLik_sub hp xs θ' θ
  linarith

/-- **EM iterates have monotone likelihood**: for any M-step `M` with
`Q(M θ | θ) ≥ Q(θ | θ)` (in particular a maximizer of `Q(· | θ)`, or a generalized-EM step), the
log-likelihood is monotone along `θ₀, M θ₀, M (M θ₀), …`. -/
theorem logLik_iterate_monotone [Nonempty Z] (hp : ∀ θ x z, 0 < p θ x z) (xs : Fin N → X)
    {M : Θ → Θ} (hM : ∀ θ, emQ p xs θ θ ≤ emQ p xs (M θ) θ) (θ₀ : Θ) :
    Monotone fun k => logLik p xs (M^[k] θ₀) := by
  refine monotone_nat_of_le_succ fun k => ?_
  simp only [Function.iterate_succ_apply']
  exact logLik_le_of_emQ_le hp xs (hM _)

end Cslib.MachineLearning.LatentVariable.ExpectationMaximization

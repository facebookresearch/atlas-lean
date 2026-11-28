/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The Kong–Cox linear allele-sharing model

For a finite set of inheritance vectors, a null mass function of total mass one, and a score
with positive null variance, `likelihood_eq` gives the exact single-pedigree likelihood in the
linear model. The conditional observation likelihoods are fixed as the parameter varies, and
the likelihood at zero must be nonzero. The algebra allows nonuniform null masses, unlike the
uniform null in Appendix A, and all real weights and parameters, including those outside the
probability model's admissible range.

For a finite set of pedigrees and arbitrary real weights and null posterior mean scores,
`hasDerivAt_sum_log_zero` gives the derivative at zero of the sum of the log-affine terms.

## References

* Augustine Kong and Nancy J. Cox, *Allele-Sharing Models: LOD Scores and Accurate Linkage Tests*,
  American Journal of Human Genetics **61** (1997), 1179–1188, model (1) and Appendix A.
-/

namespace WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted

section

variable {V : Type*} [Fintype V]

@[expose] public section

/-- The null mean `μ = ∑_v P₀(v) S(v)` of the allele-sharing score. -/
def nullMean (P₀ S : V → ℝ) : ℝ :=
  ∑ v, P₀ v * S v

/-- The null variance `σ² = ∑_v P₀(v) (S(v) - μ)²` of the allele-sharing score. -/
def nullVariance (P₀ S : V → ℝ) : ℝ :=
  ∑ v, P₀ v * (S v - nullMean P₀ S) ^ 2

/-- The normalized score `Z(v) = (S(v) - μ) / σ`. It is meaningful when the null variance `σ²` is
positive; if `σ² = 0`, Lean's convention `x / 0 = 0` makes `Z(v) = 0`. -/
noncomputable def normalizedScore (P₀ S : V → ℝ) (v : V) : ℝ :=
  (S v - nullMean P₀ S) / Real.sqrt (nullVariance P₀ S)

/-- Kong and Cox's linear allele-sharing model `P_δ(v) = P₀(v) (1 + δ γ Z(v))`. -/
noncomputable def linearModel (P₀ S : V → ℝ) (γ δ : ℝ) (v : V) : ℝ :=
  P₀ v * (1 + δ * γ * normalizedScore P₀ S v)

/-- The likelihood `L(δ) = ∑_v ℓ(v) P_δ(v)` of observed marker data, where `ℓ(v)` is the
probability of the data given the inheritance vector `v`. -/
noncomputable def likelihood (P₀ S ℓ : V → ℝ) (γ δ : ℝ) : ℝ :=
  ∑ v, ℓ v * linearModel P₀ S γ δ v

/-- The null posterior mean `Z̄ = ∑_v ℓ(v) P₀(v) Z(v) / ∑_v ℓ(v) P₀(v)` of the normalized score
given the observed data. It is meaningful when `∑_v ℓ(v) P₀(v) ≠ 0`; otherwise Lean's convention
`x / 0 = 0` makes the value `0`. -/
noncomputable def posteriorMeanScore (P₀ S ℓ : V → ℝ) : ℝ :=
  (∑ v, ℓ v * P₀ v * normalizedScore P₀ S v) / ∑ v, ℓ v * P₀ v

end

/-- **Likelihood under the null.** At `δ = 0`, integrating the conditional observation
likelihood against the linear model is the same as integrating it against the null masses. -/
public theorem likelihood_zero (P₀ S ℓ : V → ℝ) (γ : ℝ) :
    likelihood P₀ S ℓ γ 0 = ∑ v, ℓ v * P₀ v := by
  simp only [likelihood, linearModel, zero_mul, add_zero, mul_one]

/-- **Exact likelihood under missing data** (Kong and Cox 1997, Appendix A). Let `V` be a finite
set, `P₀ : V → ℝ` with `∑_v P₀(v) = 1`, `S : V → ℝ` a score with positive null variance
`σ² > 0`, and `ℓ : V → ℝ` the probability of
the observed marker data given each inheritance vector (it does not depend on `δ`), with
`L(0) = ∑_v ℓ(v) P₀(v) ≠ 0`. Then for every weight `γ` and every `δ`,
`L(δ) = L(0) (1 + δ γ Z̄)`, where `Z̄` is the null posterior mean of `Z` given the data.

Source: Kong and Cox (1997), Appendix A. -/
public theorem likelihood_eq (P₀ S ℓ : V → ℝ) (hsum : ∑ v, P₀ v = 1)
    (hvar : 0 < nullVariance P₀ S) (hL : ∑ v, ℓ v * P₀ v ≠ 0) (γ δ : ℝ) :
    likelihood P₀ S ℓ γ δ =
      likelihood P₀ S ℓ γ 0 * (1 + δ * γ * posteriorMeanScore P₀ S ℓ) := by
  -- Retain the model hypotheses even though the algebra only needs the nonzero baseline.
  have _ := hsum
  have _ := hvar
  rw [likelihood_zero, posteriorMeanScore, mul_add, mul_one, mul_left_comm _ (δ * γ),
    mul_div_cancel₀ _ hL, Finset.mul_sum, ← Finset.sum_add_distrib, likelihood]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold linearModel
  ring

end

-- Evaluate the model itself here, without unfolding its definitions in a client module.
example :
    let P₀ : Fin 2 → ℝ := fun _ => 1 / 2
    let S : Fin 2 → ℝ := ![-1, 1]
    let ℓ : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    likelihood P₀ S ℓ 1 0 = 1 / 2 ∧
      posteriorMeanScore P₀ S ℓ = 1 / 2 ∧
      likelihood P₀ S ℓ 1 (1 / 2) = 5 / 8 := by
  norm_num [likelihood, linearModel, posteriorMeanScore, normalizedScore, nullVariance, nullMean,
    Fin.sum_univ_two]

/-- **The score at `δ = 0`** (Kong and Cox 1997). Let `ι` be a finite set of independent
pedigrees with weights `γᵢ` and null posterior mean scores `Z̄ᵢ` (real numbers). The function
`δ ↦ ∑ᵢ log (1 + δ γᵢ Z̄ᵢ)` has derivative `∑ᵢ γᵢ Z̄ᵢ` at `δ = 0`.

Source: Kong and Cox (1997). -/
public theorem hasDerivAt_sum_log_zero {ι : Type*} [Fintype ι] (γ Zbar : ι → ℝ) :
    HasDerivAt (fun δ => ∑ i, Real.log (1 + δ * (γ i * Zbar i))) (∑ i, γ i * Zbar i) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have ha : HasDerivAt (fun δ : ℝ => 1 + δ * (γ i * Zbar i)) (γ i * Zbar i) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (γ i * Zbar i)).const_add 1)
  have hne : (1 : ℝ) + 0 * (γ i * Zbar i) ≠ 0 := by simp
  simpa only [zero_mul, add_zero, div_one] using ha.log hne

end WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted

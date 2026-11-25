/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.MMatrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-!
# Final demand and gross output in a productive input–output economy

For a nonnegative input–output matrix `A` in the productive regime, gross output is monotone
in final demand: if `x = A x + d`, `x' = A x' + d'` and `d ≤ d'` entrywise, then `x ≤ x'`.
The spectral form (`grossOutput_mono`) assumes spectral radius `< 1` and uses the nonnegative
Leontief inverse `Matrix.inv_one_sub_nonneg`; the row-sum form
(`grossOutput_mono_of_rowSum_lt_one`) assumes every row sum is below `1`, the explicit
`ℓ∞` operator-norm contraction bound, which bounds the spectral radius.

Invertibility of `1 - A` alone does not suffice: without nonnegativity the Leontief inverse
can have negative entries.

## Main results

* `MathlibExt.Economics.InputOutput.grossOutput_mono`
* `MathlibExt.Economics.InputOutput.grossOutput_mono_of_rowSum_lt_one`

## References

* R. E. Miller, P. D. Blair, *Input-Output Analysis: Foundations and Extensions*, 2nd ed.,
  Cambridge University Press (2009), Chapter 2 (`x = (I - A)⁻¹ f` with a nonnegative Leontief
  inverse).
* D. Hawkins, H. A. Simon, "Note: Some Conditions of Macroeconomic Stability",
  Econometrica 17 (1949), 245–248.

Atlas roadmap target AP06.T03.
-/

namespace MathlibExt.Economics.InputOutput

open Matrix

/-- **Final-demand monotonicity of gross output (spectral regime).** Let the input matrix `A`
be entrywise nonnegative with spectral radius `< 1`. If `x` and `x'` are gross outputs for
final demands `d ≤ d'` (`x = A x + d`, `x' = A x' + d'`), then `x ≤ x'` entrywise. -/
theorem grossOutput_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA0 : ∀ i j, 0 ≤ A i j) (hA : spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < 1)
    {d d' x x' : ι → ℝ} (hx : x = A *ᵥ x + d) (hx' : x' = A *ᵥ x' + d') (hd : d ≤ d') :
    x ≤ x' := by
  have hdet : IsUnit (1 - A).det :=
    (Matrix.isUnit_iff_isUnit_det _).1
      (Matrix.isUnit_one_sub_of_spectralRadius_lt_one hA)
  have hmul : (1 - A) *ᵥ (x' - x) = d' - d := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    linear_combination hx' - hx
  have hinv : (1 - A)⁻¹ *ᵥ ((1 - A) *ᵥ (x' - x)) = x' - x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hdiff : x' - x = (1 - A)⁻¹ *ᵥ (d' - d) := by
    rw [← hinv, hmul]
  intro i
  have hnn : 0 ≤ x' i - x i := by
    have h : 0 ≤ (x' - x) i := by
      rw [hdiff, Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Matrix.inv_one_sub_nonneg hA0 hA i j) (sub_nonneg.mpr (hd j))
    exact h
  exact sub_nonneg.mp hnn

/-- **Final-demand monotonicity of gross output (row-sum contraction regime).** If the
nonnegative input matrix `A` has every row sum below `1` (its `ℓ∞` operator norm is `< 1`),
then increasing final demand weakly increases required gross output. -/
theorem grossOutput_mono_of_rowSum_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j < 1)
    {d d' x x' : ι → ℝ} (hx : x = A *ᵥ x + d) (hx' : x' = A *ᵥ x' + d') (hd : d ≤ d') :
    x ≤ x' := by
  let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have hnorm : ‖A.map (algebraMap ℝ ℂ)‖₊ < 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    apply (Finset.sup_lt_iff (show (⊥ : NNReal) < 1 from zero_lt_one)).mpr
    intro i _
    show (∑ j, ‖(A.map (algebraMap ℝ ℂ)) i j‖₊) < 1
    have hentry : ∀ j, ((‖(A.map (algebraMap ℝ ℂ)) i j‖₊ : NNReal) : ℝ) = A i j := by
      intro j
      have h1 : ‖algebraMap ℝ ℂ (A i j)‖ = |A i j| := by simp
      rw [coe_nnnorm, Matrix.map_apply, h1, abs_of_nonneg (hA0 i j)]
    rw [← NNReal.coe_lt_coe, NNReal.coe_sum, NNReal.coe_one]
    calc (∑ j, ((‖(A.map (algebraMap ℝ ℂ)) i j‖₊ : NNReal) : ℝ)) = ∑ j, A i j :=
            Finset.sum_congr rfl fun j _ => hentry j
      _ < 1 := hrow i
  have hρ : spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < 1 :=
    lt_of_le_of_lt (spectrum.spectralRadius_le_nnnorm _) (by exact_mod_cast hnorm)
  exact grossOutput_mono hA0 hρ hx hx' hd

end MathlibExt.Economics.InputOutput

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormCoefficientActions
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Actual finite Hilbert Gram coefficient bounds

The finite sums are the original source values under an actual representation
of the same-p completion. The original coefficient and its computed positive
unitization complement give a norm-square decomposition for those sums.
Consequently a zero original Gram sum has a zero transformed coefficient sum.
This proves the kernel inclusion required for descent to the actual Gram
span; it assumes no descended operator, bound, norm model or nondegeneracy.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra InnerProductSpace BigOperators

namespace HaarTwistedCore

noncomputable section

universe uG uA uH uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable {ι : Type uI}

/-- The literal weighted finite sum of original-source Hilbert operator values. -/
def finiteHilbertGram (s : Finset ι) (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) : H :=
  ∑ i ∈ s, z i • σ (p.toNonUnitalCompletion (f i)) (ξ i)

/-- The literal finite coefficient transform using the actual unitized source action. -/
def finiteHilbertGramCoefficient (a : Unitization ℂ A) (s : Finset ι)
    (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) : H :=
  finiteHilbertGram μ α p σ s z (fun i => coefficientLeftUnitization μ α a (f i)) ξ

omit [μ.Regular] in
/-- The non-scalar coefficient transform retains exactly the original coefficient values. -/
@[simp]
theorem finiteHilbertGramCoefficient_inr (a : A) (s : Finset ι)
    (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) :
    finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ =
      ∑ i ∈ s, z i • σ (p.toNonUnitalCompletion (coefficientLeft μ α a (f i))) (ξ i) := by
  simp only [finiteHilbertGramCoefficient, finiteHilbertGram, coefficientLeftUnitization_inr]

omit [μ.Regular] in
/-- The original coefficient and computed complement give the exact finite Gram square identity. -/
theorem finiteHilbertGramCoefficient_inner_square (a : A) (s : Finset ι)
    (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) :
    ⟪finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ,
      finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ⟫_ℂ +
    ⟪finiteHilbertGramCoefficient μ α p σ (coefficientSquareComplement a) s z f ξ,
      finiteHilbertGramCoefficient μ α p σ (coefficientSquareComplement a) s z f ξ⟫_ℂ =
      ((‖a‖ ^ 2 : ℝ) : ℂ) *
        ⟪finiteHilbertGram μ α p σ s z f ξ, finiteHilbertGram μ α p σ s z f ξ⟫_ℂ := by
  let π : Carrier μ α →⋆ₙₐ[ℂ] (H →L[ℂ] H) := σ.comp p.toNonUnitalCompletion
  let c := coefficientSquareComplement a
  let r : ℂ := ((‖a‖ ^ 2 : ℝ) : ℂ)
  have hInner (u v : Carrier μ α) (x y : H) :
      ⟪π u x, π v y⟫_ℂ = ⟪x, π (star u * v) y⟫_ℂ := by
    have hProduct : π (star u * v) = star (π u) * π v := by
      rw [map_mul, map_star]
    rw [hProduct]
    change ⟪π u x, π v y⟫_ℂ = ⟪x, star (π u) (π v y)⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  have hCross (u v : Carrier μ α) (x y : H) :
      ⟪π (coefficientLeft μ α a u) x, π (coefficientLeft μ α a v) y⟫_ℂ +
      ⟪π (coefficientLeftUnitization μ α c u) x,
        π (coefficientLeftUnitization μ α c v) y⟫_ℂ = r * ⟪π u x, π v y⟫_ℂ := by
    rw [hInner, hInner, hInner]
    have hOperators :
        π (star (coefficientLeft μ α a u) * coefficientLeft μ α a v) +
          π (star (coefficientLeftUnitization μ α c u) * coefficientLeftUnitization μ α c v) =
            r • π (star u * v) := by
      have h := congrArg π (coefficientLeft_cross_gram_square μ α a u v)
      simpa only [map_add, map_smul, c, r] using h
    calc
      _ = ⟪x, (π (star (coefficientLeft μ α a u) * coefficientLeft μ α a v) +
          π (star (coefficientLeftUnitization μ α c u) *
            coefficientLeftUnitization μ α c v)) y⟫_ℂ := by
        change ⟪x, _⟫_ℂ + ⟪x, _⟫_ℂ = ⟪x, _ + _⟫_ℂ
        rw [inner_add_right]
        simp only [ContinuousLinearMap.coe_coe]
      _ = ⟪x, (r • π (star u * v)) y⟫_ℂ := by rw [hOperators]
      _ = r * ⟪x, π (star u * v) y⟫_ℂ := by
        change ⟪x, r • π (star u * v) y⟫_ℂ = _
        exact inner_smul_right _ _ _
  have hSmul (u : Carrier μ α) (w : ℂ) (x : H) : w • π u x = π u (w • x) :=
    (map_smul (π u) w x).symm
  have hPair (i j : ι) :
      ⟪z i • π (coefficientLeft μ α a (f i)) (ξ i),
        z j • π (coefficientLeft μ α a (f j)) (ξ j)⟫_ℂ +
      ⟪z i • π (coefficientLeftUnitization μ α c (f i)) (ξ i),
        z j • π (coefficientLeftUnitization μ α c (f j)) (ξ j)⟫_ℂ =
      r * ⟪z i • π (f i) (ξ i), z j • π (f j) (ξ j)⟫_ℂ := by
    simp_rw [hSmul]
    exact hCross (f i) (f j) (z i • ξ i) (z j • ξ j)
  simp only [finiteHilbertGramCoefficient, finiteHilbertGram, coefficientLeftUnitization_inr]
  change ⟪∑ i ∈ s, z i • π (coefficientLeft μ α a (f i)) (ξ i),
      ∑ j ∈ s, z j • π (coefficientLeft μ α a (f j)) (ξ j)⟫_ℂ +
    ⟪∑ i ∈ s, z i • π (coefficientLeftUnitization μ α c (f i)) (ξ i),
      ∑ j ∈ s, z j • π (coefficientLeftUnitization μ α c (f j)) (ξ j)⟫_ℂ =
    r * ⟪∑ i ∈ s, z i • π (f i) (ξ i), ∑ j ∈ s, z j • π (f j) (ξ j)⟫_ℂ
  simp_rw [sum_inner, inner_sum]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (⟪z i • π (coefficientLeft μ α a (f i)) (ξ i),
          z j • π (coefficientLeft μ α a (f j)) (ξ j)⟫_ℂ +
        ⟪z i • π (coefficientLeftUnitization μ α c (f i)) (ξ i),
          z j • π (coefficientLeftUnitization μ α c (f j)) (ξ j)⟫_ℂ) := by
      simp only [Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s, r * ⟪z i • π (f i) (ξ i), z j • π (f j) (ξ j)⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hPair i j
    _ = _ := by simp only [Finset.mul_sum]

omit [μ.Regular] in
/-- The computed coefficient and complement sums have the exact original norm-square decomposition. -/
theorem finiteHilbertGramCoefficient_norm_sq (a : A) (s : Finset ι)
    (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) :
    ‖finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ‖ ^ 2 +
      ‖finiteHilbertGramCoefficient μ α p σ (coefficientSquareComplement a) s z f ξ‖ ^ 2 =
        ‖a‖ ^ 2 * ‖finiteHilbertGram μ α p σ s z f ξ‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ)
    (finiteHilbertGramCoefficient_inner_square μ α p σ a s z f ξ)
  have hr : RCLike.re ((‖a‖ ^ 2 : ℝ) : ℂ) = ‖a‖ ^ 2 := by
    rw [RCLike.re_eq_complex_re, Complex.ofReal_re]
  have hi : RCLike.im ((‖a‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [RCLike.im_eq_complex_im, Complex.ofReal_im]
  simpa only [map_add, RCLike.mul_re, hr, hi, zero_mul, sub_zero, inner_self_eq_norm_sq] using h

omit [μ.Regular] in
/-- The original finite Gram coefficient transform has the actual coefficient norm bound. -/
theorem norm_finiteHilbertGramCoefficient_inr_le (a : A) (s : Finset ι)
    (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H) :
    ‖finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ‖ ≤
      ‖a‖ * ‖finiteHilbertGram μ α p σ s z f ξ‖ := by
  have hSquare := finiteHilbertGramCoefficient_norm_sq μ α p σ a s z f ξ
  have hLe : ‖finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ‖ ^ 2 ≤
      (‖a‖ * ‖finiteHilbertGram μ α p σ s z f ξ‖) ^ 2 := by
    calc
      _ ≤ ‖finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ‖ ^ 2 +
          ‖finiteHilbertGramCoefficient μ α p σ (coefficientSquareComplement a) s z f ξ‖ ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = ‖a‖ ^ 2 * ‖finiteHilbertGram μ α p σ s z f ξ‖ ^ 2 := hSquare
      _ = _ := (mul_pow _ _ 2).symm
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg a) (norm_nonneg _))).mp hLe

omit [μ.Regular] in
/-- A zero original finite Gram sum has a zero transformed coefficient sum. -/
theorem finiteHilbertGramCoefficient_inr_eq_zero_of_eq_zero (a : A) (s : Finset ι)
    (z : ι → ℂ) (f : ι → Carrier μ α) (ξ : ι → H)
    (hGram : finiteHilbertGram μ α p σ s z f ξ = 0) :
    finiteHilbertGramCoefficient μ α p σ (a : Unitization ℂ A) s z f ξ = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  simpa only [hGram, norm_zero, mul_zero] using
    norm_finiteHilbertGramCoefficient_inr_le μ α p σ a s z f ξ

end

end HaarTwistedCore

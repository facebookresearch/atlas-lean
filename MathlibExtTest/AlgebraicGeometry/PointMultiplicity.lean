/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PointMultiplicity
import MathlibExt.AlgebraicGeometry.SeshadriConstant
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

/-! ### Points and lines of the projective plane -/

private theorem e₂_ne_zero : (![0, 0, 1] : Fin 3 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 2

private theorem e₀_ne_zero : (![1, 0, 0] : Fin 3 → ℚ) ≠ 0 := by
  intro h
  simpa using congrFun h 0

/-- The point `[0 : 0 : 1]` lies on the line `x₀ = 0`, whose coordinate vector is `[1 : 0 : 0]`. -/
example : (mk ℚ ![0, 0, 1] e₂_ne_zero).orthogonal (mk ℚ ![1, 0, 0] e₀_ne_zero) := by
  rw [orthogonal_mk]
  simp [dotProduct, Fin.sum_univ_three]

/-- The point `[1 : 0 : 0]` does not lie on the line `x₀ = 0`. -/
example : ¬(mk ℚ ![1, 0, 0] e₀_ne_zero).orthogonal (mk ℚ ![1, 0, 0] e₀_ne_zero) := by
  rw [orthogonal_mk]
  simp [dotProduct, Fin.sum_univ_three]

/-- Incidence is symmetric. -/
example (p ℓ : ℙ ℚ (Fin 3 → ℚ)) (h : p.orthogonal ℓ) : ℓ.orthogonal p :=
  orthogonal_comm.1 h

/-- Incidence does not depend on the representatives. -/
example (p ℓ : ℙ ℚ (Fin 3 → ℚ)) : p.orthogonal ℓ ↔ p.rep ⬝ᵥ ℓ.rep = 0 :=
  orthogonal_iff_rep_dotProduct_rep

/-- Rescaling a representative gives the same point, so incidence is invariant under it. -/
example (ℓ : ℙ ℚ (Fin 3 → ℚ)) :
    (mk ℚ ((2 : ℚ) • ![0, 0, 1]) (smul_ne_zero two_ne_zero e₂_ne_zero)).orthogonal ℓ ↔
      (mk ℚ ![0, 0, 1] e₂_ne_zero).orthogonal ℓ := by
  rw [mk_smul_eq two_ne_zero]

/-! ### Order of vanishing and multiplicity -/

/-- Nonzero constants vanish nowhere; the zero polynomial vanishes to infinite order. -/
example (v : Fin 3 → ℚ) : (C 3 : MvPolynomial (Fin 3) ℚ).orderAt v = 0 :=
  orderAt_C_of_ne_zero (by norm_num) v

example (v : Fin 3 → ℚ) : (0 : MvPolynomial (Fin 3) ℚ).orderAt v = ⊤ := by
  simp

/-- Constants, including zero (the junk value), have multiplicity zero, by `simp`. -/
example (a : ℚ) (p : ℙ ℚ (Fin 3 → ℚ)) : (C a : MvPolynomial (Fin 3) ℚ).multiplicityAt p = 0 := by
  simp

/-- The line `x₀ = 0` has multiplicity one at `[0 : 0 : 1]` and zero at `[1 : 0 : 0]`. -/
example : (∑ i, C (![1, 0, 0] i) * X i : MvPolynomial (Fin 3) ℚ).multiplicityAt
    (mk ℚ ![0, 0, 1] e₂_ne_zero) = 1 :=
  multiplicityAt_sum_C_mul_X_of_orthogonal e₀_ne_zero
    (by rw [orthogonal_mk]; simp [dotProduct, Fin.sum_univ_three])

example : (∑ i, C (![1, 0, 0] i) * X i : MvPolynomial (Fin 3) ℚ).multiplicityAt
    (mk ℚ ![1, 0, 0] e₀_ne_zero) = 0 :=
  multiplicityAt_sum_C_mul_X_of_not_orthogonal e₀_ne_zero
    (by rw [orthogonal_mk]; simp [dotProduct, Fin.sum_univ_three])

private theorem x₀x₁_isHomogeneous : (X 0 * X 1 : MvPolynomial (Fin 3) ℚ).IsHomogeneous 2 :=
  (isHomogeneous_X ℚ 0).mul (isHomogeneous_X ℚ 1)

/-- A nonzero polynomial has positive multiplicity exactly at the points where it vanishes. -/
example (p : ℙ ℚ (Fin 3 → ℚ)) :
    0 < (X 0 : MvPolynomial (Fin 3) ℚ).multiplicityAt p ↔ p.rep 0 = 0 := by
  rw [multiplicityAt_pos_iff (X_ne_zero 0), eval_X]

/-- The point `(0, 0, 1)` is a singular point of the conic `x₀ x₁ = 0` (two lines meet there),
and the conic vanishes there to order exactly two: the mixed second derivative is `1`. -/
private theorem x₀x₁_orderAt : (X 0 * X 1 : MvPolynomial (Fin 3) ℚ).orderAt ![0, 0, 1] = 2 := by
  refine le_antisymm ?_ ?_
  · by_contra! h
    have h3 : ((2 : ℕ) : ℕ∞) + 1 ≤ (X 0 * X 1 : MvPolynomial (Fin 3) ℚ).orderAt ![0, 0, 1] :=
      Order.add_one_le_of_lt (by simpa using h)
    have h2 := (natCast_add_one_le_orderAt_iff.1 h3).2 0
    rw [show ((2 : ℕ) : ℕ∞) = (1 : ℕ) + 1 by norm_num, natCast_add_one_le_orderAt_iff] at h2
    have h1 := h2.2 1
    rw [Nat.cast_one, one_le_orderAt_iff] at h1
    simp [pderiv_X] at h1
  · rw [two_le_orderAt_iff]
    refine ⟨by simp, fun i => ?_⟩
    fin_cases i <;> simp [pderiv_X]

/-- Hence the conic has multiplicity two at the point `[0 : 0 : 1]`, computed at a representative. -/
example : (X 0 * X 1 : MvPolynomial (Fin 3) ℚ).multiplicityAt (mk ℚ ![0, 0, 1] e₂_ne_zero) = 2 := by
  rw [multiplicityAt_mk x₀x₁_isHomogeneous, x₀x₁_orderAt]
  rfl

/-- The multiplicity of a homogeneous polynomial does not depend on the representative. -/
example (F : MvPolynomial (Fin 3) ℚ) (hF : F.IsHomogeneous 2) :
    F.multiplicityAt (mk ℚ ((2 : ℚ) • ![0, 0, 1]) (smul_ne_zero two_ne_zero e₂_ne_zero)) =
      F.multiplicityAt (mk ℚ ![0, 0, 1] e₂_ne_zero) := by
  rw [multiplicityAt_mk hF, multiplicityAt_mk hF, orderAt_smul hF two_ne_zero]

/-- The affine-chart multiplicity of `MathlibExt.AlgebraicGeometry.SeshadriConstant` (least degree
of a monomial of the shifted polynomial, `0` for the zero polynomial) is `orderAt`. -/
example (f : MathlibExt.AlgebraicGeometry.SeshadriConstant.PlanePolynomial)
    (a : MathlibExt.AlgebraicGeometry.SeshadriConstant.AffinePoint) :
    MathlibExt.AlgebraicGeometry.SeshadriConstant.multiplicity f a = (f.orderAt a).toNat := by
  open MathlibExt.AlgebraicGeometry in
  classical
  by_cases hf : f = 0
  · subst hf
    simp [SeshadriConstant.multiplicity, SeshadriConstant.shifted]
  have hne : (SeshadriConstant.shifted f a).support.Nonempty := by
    rw [MvPolynomial.support_nonempty, ne_eq, SeshadriConstant.shifted_eq_zero_iff]
    exact hf
  rw [SeshadriConstant.multiplicity, dite_eq_left hne]
  obtain ⟨m, hm, hmN⟩ := Finset.mem_image.1 (Finset.min'_mem
    ((SeshadriConstant.shifted f a).support.image SeshadriConstant.monomialDegree)
    (Finset.image_nonempty.mpr hne))
  have hord : f.orderAt a = (SeshadriConstant.monomialDegree m : ℕ∞) := by
    change ((SeshadriConstant.shifted f a : MvPolynomial (Fin 2) ℂ) :
      MvPowerSeries (Fin 2) ℂ).order = _
    rw [MvPowerSeries.order_eq_nat]
    refine ⟨⟨m, by rw [coeff_coe]; exact mem_support_iff.1 hm, ?_⟩, fun d hd => ?_⟩
    · rw [Finsupp.degree_eq_sum]
      rfl
    · rw [coeff_coe]
      by_contra hc
      have hle := Finset.min'_le
        ((SeshadriConstant.shifted f a).support.image SeshadriConstant.monomialDegree) _
        (Finset.mem_image.2 ⟨d, mem_support_iff.2 hc, rfl⟩)
      rw [← hmN] at hle
      rw [Finsupp.degree_eq_sum] at hd
      exact absurd hle (not_le.2 hd)
  rw [hord, ENat.toNat_natCast, hmN]

/-! ### Characteristic zero is needed for the derivative criterion -/

/-- Over `ZMod 2`, `X₀²` vanishes at the origin and its partial derivative is identically zero,
yet it does not vanish to infinite order: the recursion of `natCast_add_one_le_orderAt_iff`
fails without characteristic zero, which is why `orderAt` is defined by the Taylor expansion. -/
example : ¬∀ n : ℕ, ((n : ℕ∞) + 1 ≤ (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)).orderAt 0 ↔
    eval 0 (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) = 0 ∧
      ∀ i, (n : ℕ∞) ≤ (pderiv i (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2))).orderAt 0) := by
  intro h
  have hd : ∀ i : Fin 1, pderiv i (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) = 0 := by
    intro i
    fin_cases i
    simp [CharTwo.two_eq_zero]
  have htop : (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)).orderAt 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun n => ?_
    exact le_trans le_self_add ((h n).2 ⟨by simp, fun i => by simp [hd i]⟩)
  have hne : (X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)) ≠ 0 := by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]
    exact one_ne_zero
  exact orderAt_ne_top hne 0 htop

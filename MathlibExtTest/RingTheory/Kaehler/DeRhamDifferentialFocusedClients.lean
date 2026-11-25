/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Kaehler.DeRhamDifferential
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Focused clients for the algebraic de Rham differential

On the polynomial algebra `A = ℚ[x, y, z]`, coefficients of forms are read off
by contracting with the coordinate functionals of the basis `dx, dy, dz` of
`Ω[A⁄ℚ]`, using the degree-restricted contraction API.

* `d(xy)` has `dy`-coefficient `x`, so the degree-zero differential is nonzero.
* `ω = x dy` is nonzero, `dω = dx ∧ dy` is nonzero, and `d(dω) = 0`.
* For `α = x dy` and `β = z`, `d(α ∧ β) = dα ∧ β - α ∧ dβ` has `dy ∧ dz`-coefficient
  `-x`; the sign-flipped Leibniz formula gives a different form.
* In characteristic two, `d(x²) = 0` although `x² ≠ 0`.
* Deletion, contraction and Cartan's identity are evaluated on `dx ∧ dy`.
-/

open KaehlerDifferential KaehlerDifferential.DeRham MvPolynomial

namespace MathlibExtTest.RingTheory.Kaehler

/-- The polynomial algebra in three variables over `ℚ`. -/
abbrev A := MvPolynomial (Fin 3) ℚ

/-- The Kähler module of `A` over `ℚ`. -/
abbrev Ω₁ := Ω[A⁄ℚ]

/-- The universal differential of a variable. -/
noncomputable abbrev dX (i : Fin 3) : Ω₁ := D ℚ A (X i)

/-- The coordinate functional dual to `dX i`. -/
noncomputable abbrev coord (i : Fin 3) : Module.Dual A Ω₁ :=
  (mvPolynomialBasis ℚ (Fin 3)).coord i

lemma coord_D (i : Fin 3) (p : A) : coord i (D ℚ A p) = pderiv i p :=
  mvPolynomialBasis_repr_apply ℚ (Fin 3) p i

/-- The `dX i`-coefficient of a one-form, read through contraction. -/
noncomputable def ev₁ (i : Fin 3) : ⋀[A]^1 Ω₁ →ₗ[A] A :=
  (exteriorPower.zeroEquiv A Ω₁).toLinearMap ∘ₗ exteriorPower.contractLeft A Ω₁ (coord i) 0

/-- The `dX i ∧ dX j`-coefficient of a two-form, read through two contractions. -/
noncomputable def ev₂ (i j : Fin 3) : ⋀[A]^2 Ω₁ →ₗ[A] A :=
  ev₁ j ∘ₗ exteriorPower.contractLeft A Ω₁ (coord i) 1

lemma ev₁_ιMulti (i : Fin 3) (a : Ω₁) :
    ev₁ i (exteriorPower.ιMulti A 1 ![a]) = coord i a := by
  have h := LinearMap.congr_fun (exteriorPower.zeroEquiv_comp_contractLeft A Ω₁ (coord i))
    (exteriorPower.ιMulti A 1 ![a])
  change (exteriorPower.zeroEquiv A Ω₁)
    (exteriorPower.contractLeft A Ω₁ (coord i) 0 (exteriorPower.ιMulti A 1 ![a])) = _
  simpa [exteriorPower.oneEquiv_ιMulti] using h

lemma ev₂_ιMulti (i j : Fin 3) (a b : Ω₁) :
    ev₂ i j (exteriorPower.ιMulti A 2 ![a, b]) =
      coord i a * coord j b - coord i b * coord j a := by
  have hb : (![a, b] ∘ (0 : Fin 2).succAbove) = ![b] := by
    funext k; fin_cases k; rfl
  have ha : (![a, b] ∘ (1 : Fin 2).succAbove) = ![a] := by
    funext k; fin_cases k; rfl
  rw [ev₂, LinearMap.comp_apply, exteriorPower.contractLeft_apply_ιMulti, Fin.sum_univ_two, hb,
    ha]
  simp only [map_add, map_smul, ev₁_ιMulti]
  simp [smul_eq_mul, sub_eq_add_neg, mul_comm]

/-- The degree-zero differential of `xy` has `dy`-coefficient `x`. -/
lemma ev₁_differential_xy :
    ev₁ 1 (differential ℚ A 0 ((X 0 * X 1 : A) • differentialForm ℚ A 0 Fin.elim0)) = X 0 := by
  rw [differential_smul_differentials]
  have hv : (Fin.cons (D ℚ A (X 0 * X 1)) (fun i : Fin 0 => D ℚ A (Fin.elim0 i)) :
      Fin 1 → Ω₁) = ![D ℚ A (X 0 * X 1)] := by
    funext k; fin_cases k; rfl
  rw [hv, ev₁_ιMulti, coord_D]
  simp [pderiv_X]

/-- The degree-zero differential is nonzero on `xy`. -/
example : differential ℚ A 0 ((X 0 * X 1 : A) • differentialForm ℚ A 0 Fin.elim0) ≠ 0 := by
  intro h
  have := ev₁_differential_xy
  rw [h, map_zero] at this
  exact X_ne_zero 0 this.symm

/-- The one-form `ω = x dy`. -/
noncomputable def ω : Forms ℚ A 1 := (X 0 : A) • differentialForm ℚ A 1 ![X 1]

lemma ω_ne_zero : ω ≠ 0 := by
  intro h
  have h1 : ev₁ 1 ω = X 0 := by
    rw [ω, map_smul, smul_eq_mul]
    change X 0 * ev₁ 1 (exteriorPower.ιMulti A 1 ![dX 1]) = X 0
    rw [ev₁_ιMulti, coord_D]
    simp [pderiv_X]
  rw [h, map_zero] at h1
  exact X_ne_zero 0 h1.symm

lemma differential_ω : differential ℚ A 1 ω = exteriorPower.ιMulti A 2 ![dX 0, dX 1] := by
  rw [ω, differential_smul_differentials]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- `dω = dx ∧ dy` has `dx ∧ dy`-coefficient one, hence is nonzero. -/
lemma ev₂_differential_ω : ev₂ 0 1 (differential ℚ A 1 ω) = 1 := by
  rw [differential_ω, ev₂_ιMulti]
  simp

/-- Both steps of `d ∘ d` act on nonzero inputs, and the composite still vanishes. -/
example : ω ≠ 0 ∧ differential ℚ A 1 ω ≠ 0 ∧
    differential ℚ A 2 (differential ℚ A 1 ω) = 0 := by
  refine ⟨ω_ne_zero, fun h => ?_, differential_squared ℚ A 1 ω⟩
  have := ev₂_differential_ω
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The explicit scalar-wedge formula agrees: `d(1 • dx ∧ dy) = d1 ∧ dx ∧ dy = 0`. -/
example : differential ℚ A 2 ((1 : A) • differentialForm ℚ A 2 ![X 0, X 1]) = 0 := by
  rw [differential_smul_differentials]
  apply AlternatingMap.map_coord_zero _ 0
  simp

/-- The one-form `α = x dy` and the function `β = z`. -/
noncomputable def α : Forms ℚ A 1 := (X 0 : A) • differentialForm ℚ A 1 ![X 1]

/-- The function `z` as a zero-form. -/
noncomputable def β : Forms ℚ A 0 := (X 2 : A) • differentialForm ℚ A 0 Fin.elim0

lemma differential_β :
    differential ℚ A 0 β = (1 : A) • exteriorPower.ιMulti A 1 ![dX 2] := by
  rw [β, differential_smul_differentials, one_smul]
  congr 1
  funext k
  fin_cases k
  rfl

/-- The wedge `α ∧ dβ = x dy ∧ dz` has `dy ∧ dz`-coefficient `x`. -/
lemma ev₂_α_wedge_dβ : ev₂ 1 2 (wedge ℚ A 1 1 α (differential ℚ A 0 β)) = X 0 := by
  rw [differential_β, α, wedge_smul_ιMulti]
  have hv : (Fin.append (fun i : Fin 1 => D ℚ A (![X 1] i)) ![dX 2] : Fin (1 + 1) → Ω₁) =
      ![dX 1, dX 2] := by
    funext k; fin_cases k <;> rfl
  rw [hv]
  change ev₂ 1 2 ((X 0 * 1 : A) • exteriorPower.ιMulti A 2 ![dX 1, dX 2]) = _
  rw [map_smul, smul_eq_mul, ev₂_ιMulti]
  simp

/-- The direct computation `d(xz dy) = d(xz) ∧ dy` has `dy ∧ dz`-coefficient `-x`. -/
example : ev₂ 1 2 (differential ℚ A (1 + 0) (wedge ℚ A 1 0 α β)) = -X 0 := by
  rw [α, β, wedge_smul_ιMulti]
  have hv : (Fin.append (fun i : Fin 1 => D ℚ A (![X 1] i))
      (fun i : Fin 0 => D ℚ A (Fin.elim0 i)) : Fin (1 + 0) → Ω₁) =
        fun i : Fin (1 + 0) => D ℚ A (![X 1] i) := by
    funext k; fin_cases k; rfl
  rw [hv, differential_smul_differentials]
  have hw : (Fin.cons (D ℚ A (X 0 * X 2)) (fun i : Fin 1 => D ℚ A (![X 1] i)) : Fin 2 → Ω₁) =
      ![D ℚ A (X 0 * X 2), dX 1] := by
    funext k; fin_cases k <;> rfl
  change ev₂ 1 2 (exteriorPower.ιMulti A 2
    (Fin.cons (D ℚ A (X 0 * X 2)) (fun i : Fin 1 => D ℚ A (![X 1] i)))) = _
  rw [hw, ev₂_ιMulti]
  simp

/-- The graded Leibniz rule at `m = 1` subtracts `α ∧ dβ`. -/
lemma leibniz_α_β :
    (differential ℚ A (1 + 0) (wedge ℚ A 1 0 α β) : E ℚ A) =
      (differential ℚ A 1 α : E ℚ A) * (β : E ℚ A) -
        (α : E ℚ A) * (differential ℚ A 0 β : E ℚ A) := by
  rw [differential_leibniz, pow_one, Units.neg_smul, one_smul, sub_eq_add_neg]

/-- The sign-flipped Leibniz formula is false on `α` and `β`. -/
example :
    (differential ℚ A (1 + 0) (wedge ℚ A 1 0 α β) : E ℚ A) ≠
      (differential ℚ A 1 α : E ℚ A) * (β : E ℚ A) +
        (α : E ℚ A) * (differential ℚ A 0 β : E ℚ A) := by
  intro h
  rw [leibniz_α_β, sub_eq_add_neg, add_right_inj, neg_eq_iff_add_eq_zero] at h
  have h2 : (2 : A) • ((α : E ℚ A) * (differential ℚ A 0 β : E ℚ A)) = 0 := by
    rw [two_smul]; exact h
  have hc : (C (1 / 2 : ℚ) : A) * 2 = 1 := by
    rw [show (2 : A) = C 2 from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  have h0 : (α : E ℚ A) * (differential ℚ A 0 β : E ℚ A) = 0 := by
    calc (α : E ℚ A) * (differential ℚ A 0 β : E ℚ A)
        = ((C (1 / 2 : ℚ) : A) * 2) • ((α : E ℚ A) * (differential ℚ A 0 β : E ℚ A)) := by
          rw [hc, one_smul]
      _ = 0 := by rw [mul_smul, h2, smul_zero]
  have hw : wedge ℚ A 1 1 α (differential ℚ A 0 β) = 0 := by
    apply Subtype.ext
    simp [h0]
  have := ev₂_α_wedge_dβ
  rw [hw, map_zero] at this
  exact X_ne_zero 0 this.symm

/-- Deletion splits off each factor of `dx ∧ dy` with alternating signs. -/
example : exteriorPower.deletion A Ω₁ 1 (exteriorPower.ιMulti A 2 ![dX 0, dX 1]) =
    exteriorPower.ιMulti A 1 ![dX 1] ⊗ₜ[A] dX 0 -
      exteriorPower.ιMulti A 1 ![dX 0] ⊗ₜ[A] dX 1 := by
  have hb : (![dX 0, dX 1] ∘ (0 : Fin 2).succAbove) = ![dX 1] := by
    funext k; fin_cases k; rfl
  have ha : (![dX 0, dX 1] ∘ (1 : Fin 2).succAbove) = ![dX 0] := by
    funext k; fin_cases k; rfl
  rw [exteriorPower.deletion_apply_ιMulti, Fin.sum_univ_two, hb, ha]
  simp [sub_eq_add_neg]
  rw [TensorProduct.smul_tmul', neg_one_smul, TensorProduct.neg_tmul]

/-- Contracting `dx ∧ dy` by the `dx`-coordinate leaves `dy`. -/
example : exteriorPower.contractLeft A Ω₁ (coord 0) 1
    (exteriorPower.ιMulti A 2 ![dX 0, dX 1]) = exteriorPower.ιMulti A 1 ![dX 1] := by
  have hb : (![dX 0, dX 1] ∘ (0 : Fin 2).succAbove) = ![dX 1] := by
    funext k; fin_cases k; rfl
  rw [exteriorPower.contractLeft_apply_ιMulti, Fin.sum_univ_two, hb]
  simp

/-- Two contractions by the same functional vanish even on `dx ∧ dy ∧ dz`. -/
example : exteriorPower.contractLeft A Ω₁ (coord 0) 1
    (exteriorPower.contractLeft A Ω₁ (coord 0) 2
      (exteriorPower.ιMulti A 3 ![dX 0, dX 1, dX 2])) = 0 :=
  LinearMap.congr_fun (exteriorPower.contractLeft_comp_contractLeft A Ω₁ (coord 0) 1) _

/-- Cartan's identity: contracting `dx ∧ dy` by the `dx`-coordinate after
wedging with `dx` returns `dy`, since the `dx`-coordinate of `dy` vanishes. -/
example : exteriorPower.contractLeft A Ω₁ (coord 0) 1
    (exteriorPower.wedgeLeft A Ω₁ (dX 0) 1 (exteriorPower.ιMulti A 1 ![dX 1])) =
      exteriorPower.ιMulti A 1 ![dX 1] := by
  have h := LinearMap.congr_fun
    (exteriorPower.contractLeft_comp_wedgeLeft_add_wedgeLeft_comp_contractLeft A Ω₁
      (coord 0) (dX 0) 0) (exteriorPower.ιMulti A 1 ![dX 1])
  have h0 : exteriorPower.contractLeft A Ω₁ (coord 0) 0 (exteriorPower.ιMulti A 1 ![dX 1]) = 0 := by
    rw [exteriorPower.contractLeft_apply_ιMulti]
    simp
  simp only [LinearMap.add_apply, LinearMap.comp_apply, h0, map_zero, add_zero,
    LinearMap.smul_apply, LinearMap.id_apply, coord_D, pderiv_X] at h
  simpa using h

section CharTwo

/-- In any `ZMod 2`-algebra, `d(a²) = 2a da = 0`. -/
lemma oneFormProjection_absolute_sq {B : Type*} [CommRing B] [Algebra (ZMod 2) B] (a : B) :
    oneFormProjection B
      (absoluteDifferential B 2 0 ((a ^ 2) • differentialForm ℤ B 0 Fin.elim0)) = 0 := by
  rw [oneFormProjection_absolute_zero, Derivation.leibniz_pow]
  have h2 : ((2 : ℕ) : B) = 0 := by
    rw [← map_natCast (algebraMap (ZMod 2) B) 2, show ((2 : ℕ) : ZMod 2) = 0 from rfl, map_zero]
  rw [← Nat.cast_smul_eq_nsmul B, h2, zero_smul]

/-- A polynomial algebra of characteristic two. -/
abbrev A₂ := MvPolynomial (Fin 1) (ZMod 2)

/-- In `(ZMod 2)[x]`, `d(x²)` vanishes although `x² ≠ 0`. The integer-algebra
structure is the one the absolute differential is stated with. -/
example : (X 0 ^ 2 : A₂) ≠ 0 ∧
    oneFormProjection A₂ (absoluteDifferential A₂ 2 0
      ((X 0 ^ 2 : A₂) • @differentialForm ℤ A₂ _ _ (Ring.toIntAlgebra A₂) 0 Fin.elim0)) = 0 := by
  refine ⟨?_, oneFormProjection_absolute_sq (X 0)⟩
  rw [X_pow_eq_monomial, Ne, monomial_eq_zero]
  exact one_ne_zero

/-- The `ZMod 2`-linear absolute differential is the integer-base differential. -/
example {B : Type*} [CommRing B] [Algebra (ZMod 2) B] (x : Forms ℤ B 1) :
    absoluteDifferential B 2 1 x = differential ℤ B 1 x :=
  absoluteDifferential_eq_differential 2 B 1 x

end CharTwo

end MathlibExtTest.RingTheory.Kaehler

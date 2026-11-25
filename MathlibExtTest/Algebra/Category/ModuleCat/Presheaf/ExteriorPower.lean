/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
import Mathlib.Algebra.Module.Rat
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Tests for the exterior-power functor on presheaves of modules

A concrete presheaf `F` over `ℕ` with the constant ring `ℚ`: every section space is `ℚ²` and each
restriction map `n + 1 ⟶ n` is `diag(2, 3)`; the endomorphism `φ` acts as `diag(5, 7)` at every
level. The determinant reads values on `⋀² ℚ²`, so the tests pin the actual numbers: restriction
multiplies `e₀ ∧ e₁` by `6` (by `36` over two steps), `exteriorPowerMap 2 φ` by `35`, both
composites in the naturality square by `210`, and the functor's laws hold on these values. Degrees
`1` and `0` are the boundary cases.
-/

open CategoryTheory Opposite PresheafOfModules

namespace MathlibExtTest.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-- The constant presheaf of rings `ℚ` on `ℕ`. -/
abbrev Q : ℕᵒᵖ ⥤ CommRingCat.{0} := (Functor.const ℕᵒᵖ).obj (CommRingCat.of ℚ)

local instance (X : ℕᵒᵖ) : CommRing ((Q ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing ℚ)

/-- `diag(a, b)` on `ℚ²`. -/
def diag (a b : ℚ) : (Fin 2 → ℚ) →+ (Fin 2 → ℚ) where
  toFun v := ![a * v 0, b * v 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp [mul_add]

lemma diag_apply (a b : ℚ) (v : Fin 2 → ℚ) : diag a b v = ![a * v 0, b * v 1] := rfl

/-- `ℚ²` at every level, with every restriction map `n + 1 ⟶ n` equal to `diag(2, 3)`. -/
abbrev P : ℕᵒᵖ ⥤ Ab.{0} :=
  Functor.ofOpSequence (X := fun _ => AddCommGrpCat.of (Fin 2 → ℚ))
    (fun _ => AddCommGrpCat.ofHom (diag 2 3))

instance (X : ℕᵒᵖ) : Module ℚ (P.obj X) := inferInstanceAs (Module ℚ (Fin 2 → ℚ))

instance (X : ℕᵒᵖ) : Module ((Q ⋙ forget₂ CommRingCat RingCat).obj X) (P.obj X) :=
  inferInstanceAs (Module ℚ (Fin 2 → ℚ))

/-- The presheaf of `ℚ`-modules `ℚ²` with restriction maps `diag(2, 3)`. -/
noncomputable def F : PresheafOfModules.{0} (Q ⋙ forget₂ CommRingCat RingCat) :=
  ofPresheaf P fun _ _ f r m => map_rat_smul (P.map f).hom r m

/-- The endomorphism of `F` acting as `diag(5, 7)` at every level. -/
noncomputable def φ : F ⟶ F :=
  homMk
    (NatTrans.ofOpSequence (F := P) (G := P) (fun _ => AddCommGrpCat.ofHom (diag 5 7))
      (fun n => by
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (v : Fin 2 → ℚ) => ?_)
        change diag 5 7 (diag 2 3 v) = diag 2 3 (diag 5 7 v)
        ext i
        fin_cases i <;> simp [diag_apply] <;> ring))
    (fun _ r m => map_rat_smul (diag 5 7) r m)

/-- Restriction from level `1` to level `0`: `diag(2, 3)`. -/
abbrev r₁₀ : op 1 ⟶ op 0 := (homOfLE (Nat.zero_le 1)).op

/-- Restriction from level `3` to level `1`, two steps: `diag(4, 9)`. -/
abbrev r₃₁ : op 3 ⟶ op 1 := (homOfLE (by norm_num : (1 : ℕ) ≤ 3)).op

example (v : Fin 2 → ℚ) : F.map r₁₀ v = diag 2 3 v := rfl

example (v : Fin 2 → ℚ) : F.map r₃₁ v = diag 2 3 (diag 2 3 v) := rfl

example (X : ℕᵒᵖ) (v : Fin 2 → ℚ) : φ.app X v = diag 5 7 v := rfl

/-- A vector of `ℚ²` as a section of `F` over `X`. -/
abbrev sec (X : ℕᵒᵖ) (v : Fin 2 → ℚ) : F.obj X := v

/-- The determinant, read on `⋀² ℚ²`. -/
noncomputable def det₂ : ⋀[ℚ]^2 (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
  exteriorPower.alternatingMapLinearEquiv Matrix.detRowAlternating

lemma det₂_ιMulti (v : Fin 2 → Fin 2 → ℚ) :
    det₂ (exteriorPower.ιMulti ℚ 2 v) = v 0 0 * v 1 1 - v 0 1 * v 1 0 := by
  rw [det₂, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact Matrix.det_fin_two (Matrix.of v)

/-- The standard basis vectors of `ℚ²`. -/
abbrev e₀ : Fin 2 → ℚ := Pi.single 0 1
abbrev e₁ : Fin 2 → ℚ := Pi.single 1 1

/-- `e₀ ∧ e₁` in the sections of `extPow 2 F` over `X`. -/
noncomputable abbrev w (X : ℕᵒᵖ) : (extPow 2 F).obj X := exteriorPower.ιMulti _ 2 ![e₀, e₁]

-- `e₀ ∧ e₁ ≠ 0`: its determinant is `1`.
example (X : ℕᵒᵖ) : det₂ (w X) = 1 := by
  change det₂ (exteriorPower.ιMulti ℚ 2 ![e₀, e₁]) = 1
  rw [det₂_ιMulti]; simp

/-! ### The object part: restriction maps of `extPow` -/

-- Restriction on `⋀²` from level `1` to level `0` multiplies by `det diag(2, 3) = 6`.
example : det₂ ((extPow 2 F).map r₁₀ (w (op 1))) = 6 := by
  rw [extPow_map_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 2 3 (![e₀, e₁] i)) = 6
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

-- The two-step restriction from level `3` to level `1` multiplies by `det diag(4, 9) = 36`.
example : det₂ ((extPow 2 F).map r₃₁ (w (op 3))) = 36 := by
  rw [extPow_map_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 2 3 (diag 2 3 (![e₀, e₁] i))) = 36
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

/-! ### The map part: `exteriorPowerMap` -/

-- `⋀² φ` multiplies by `det diag(5, 7) = 35` at every level.
example (X : ℕᵒᵖ) : det₂ ((exteriorPowerMap 2 φ).app X (w X)) = 35 := by
  rw [exteriorPowerMap_app_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 5 7 (![e₀, e₁] i)) = 35
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

-- Naturality against the restriction from level `1` to level `0`: `⋀² φ` then restriction, and
-- restriction then `⋀² φ`, both multiply by `35 * 6`.
example : det₂ ((extPow 2 F).map r₁₀ ((exteriorPowerMap 2 φ).app (op 1) (w (op 1)))) = 210 := by
  rw [exteriorPowerMap_app_ιMulti, extPow_map_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 2 3 (diag 5 7 (![e₀, e₁] i))) = 210
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

example : det₂ ((exteriorPowerMap 2 φ).app (op 0) ((extPow 2 F).map r₁₀ (w (op 1)))) = 210 := by
  rw [extPow_map_ιMulti]
  change det₂ ((exteriorPowerMap 2 φ).app (op 0)
    (exteriorPower.ιMulti _ 2 fun i => sec (op 0) (diag 2 3 (![e₀, e₁] i)))) = 210
  rw [exteriorPowerMap_app_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 5 7 (diag 2 3 (![e₀, e₁] i))) = 210
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

/-! ### The functor and its laws -/

example : (exteriorPowerFunctor Q 2).obj F = extPow 2 F := rfl

example : (exteriorPowerFunctor Q 2).map φ = exteriorPowerMap 2 φ := rfl

-- Identity law, computed on `e₀ ∧ e₁`.
example (X : ℕᵒᵖ) : ((exteriorPowerFunctor Q 2).map (𝟙 F)).app X (w X) = w X := by
  change (exteriorPowerMap 2 (𝟙 F)).app X (w X) = w X
  rw [exteriorPowerMap_app_ιMulti]
  rfl

-- Composition law, computed on `e₀ ∧ e₁`: `⋀² (φ ≫ φ)` and the composite of two `⋀² φ` both
-- multiply by `35 * 35`.
example (X : ℕᵒᵖ) : det₂ (((exteriorPowerFunctor Q 2).map (φ ≫ φ)).app X (w X)) = 1225 := by
  change det₂ ((exteriorPowerMap 2 (φ ≫ φ)).app X (w X)) = 1225
  rw [exteriorPowerMap_app_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 5 7 (diag 5 7 (![e₀, e₁] i))) = 1225
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

example (X : ℕᵒᵖ) :
    det₂ (((exteriorPowerFunctor Q 2).map φ).app X
      (((exteriorPowerFunctor Q 2).map φ).app X (w X))) = 1225 := by
  change det₂ ((exteriorPowerMap 2 φ).app X ((exteriorPowerMap 2 φ).app X (w X))) = 1225
  rw [exteriorPowerMap_app_ιMulti, exteriorPowerMap_app_ιMulti]
  change det₂ (exteriorPower.ιMulti ℚ 2 fun i => diag 5 7 (diag 5 7 (![e₀, e₁] i))) = 1225
  rw [det₂_ιMulti]; simp [diag_apply]; norm_num

/-! ### Boundary degrees `0` and `1` -/

-- Degree `1`: `⋀¹` is the module itself, and both parts act as on `F`.
example (X : ℕᵒᵖ) (v : Fin 2 → ℚ) :
    exteriorPower.oneEquiv _ _ ((exteriorPowerMap 1 φ).app X (exteriorPower.ιMulti _ 1 ![v])) =
      ![5 * v 0, 7 * v 1] := by
  rw [exteriorPowerMap_app_ιMulti, exteriorPower.oneEquiv_ιMulti]
  rfl

example (v : Fin 2 → ℚ) :
    exteriorPower.oneEquiv _ _ ((extPow 1 F).map r₁₀ (exteriorPower.ιMulti _ 1 ![v])) =
      ![2 * v 0, 3 * v 1] := by
  rw [extPow_map_ιMulti]
  change exteriorPower.oneEquiv _ _
    (exteriorPower.ιMulti _ 1 fun i => sec (op 0) (diag 2 3 (![v] i))) = _
  rw [exteriorPower.oneEquiv_ιMulti]
  rfl

-- Degree `0`: `⋀⁰` is the ring; `⋀⁰ φ` and the restriction (the identity of the constant
-- ring `ℚ`) send `1` to `1`, although `φ` and `F.map r₁₀` are not the identity.
example (X : ℕᵒᵖ) :
    exteriorPower.zeroEquiv _ _
      ((exteriorPowerMap 0 φ).app X (exteriorPower.ιMulti _ 0 ![])) = 1 := by
  rw [exteriorPowerMap_app_ιMulti, exteriorPower.zeroEquiv_ιMulti]

example :
    exteriorPower.zeroEquiv _ _ ((extPow 0 F).map r₁₀ (exteriorPower.ιMulti _ 0 ![])) = 1 := by
  rw [extPow_map_ιMulti]
  change exteriorPower.zeroEquiv _ _
    (exteriorPower.ιMulti _ 0 fun i => sec (op 0) (diag 2 3 (![] i))) = _
  rw [exteriorPower.zeroEquiv_ιMulti]

end MathlibExtTest.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

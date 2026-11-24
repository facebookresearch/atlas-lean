/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NatIso

open CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

theorem map_eq_iff (α : F ≅ G) {X Y : C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ G.map f = G.map g := by
  constructor
  · intro h
    calc G.map f = α.inv.app X ≫ F.map f ≫ α.hom.app Y := by
          rw [← naturality_1 α f]
      _ = α.inv.app X ≫ F.map g ≫ α.hom.app Y := by rw [h]
      _ = G.map g := naturality_1 α g
  · intro h
    calc F.map f = α.hom.app X ≫ G.map f ≫ α.inv.app Y := by
          rw [← naturality_2 α f]
      _ = α.hom.app X ≫ G.map g ≫ α.inv.app Y := by rw [h]
      _ = F.map g := naturality_2 α g

/-- A map is an isomorphism in every integer degree when it is so in every
natural degree, the integer and natural functors agree in nonnegative degrees,
and both endpoints vanish in negative degrees. -/
theorem isIso_map_int_of_nat
    (FNat : ℕ → C ⥤ D) (FInt : ℤ → C ⥤ D)
    (e : ∀ n : ℕ, FInt (n : ℤ) ≅ FNat n)
    {X Y : C} (f : X ⟶ Y)
    (hNat : ∀ n, IsIso ((FNat n).map f))
    (hnegX : ∀ z, z < 0 → IsZero ((FInt z).obj X))
    (hnegY : ∀ z, z < 0 → IsZero ((FInt z).obj Y))
    (z : ℤ) : IsIso ((FInt z).map f) := by
  by_cases hz : z < 0
  · exact IsZero.isIso (hnegX z hz) (hnegY z hz) _
  · have hzNonneg : 0 ≤ z := le_of_not_gt hz
    have hzEq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzNonneg
    have hInt : IsIso ((FInt (z.toNat : ℤ)).map f) :=
      (NatIso.isIso_map_iff (e z.toNat) f).mpr (hNat z.toNat)
    rw [hzEq] at hInt
    exact hInt

/-- Apply `Functor.leftOp` to a natural isomorphism, reversing its direction. -/
protected def leftOp {F G : C ⥤ Dᵒᵖ} (e : F ≅ G) : G.leftOp ≅ F.leftOp where
  hom := e.hom.leftOp
  inv := e.inv.leftOp
  hom_inv_id := by
    ext X
    dsimp
    rw [← unop_comp, e.inv_hom_id_app, unop_id]
  inv_hom_id := by
    ext X
    dsimp
    rw [← unop_comp, e.hom_inv_id_app, unop_id]

end CategoryTheory.NatIso

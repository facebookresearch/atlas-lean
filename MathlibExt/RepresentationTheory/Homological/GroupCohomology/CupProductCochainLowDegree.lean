/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProduct
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupCocycleOneOne
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupCocycleOneTwo

/-!
# General cup formulas in low cochain degrees

The existing arbitrary-degree inhomogeneous formula specializes to the explicit
(1,1) and (1,2) cocycle formulas. Foundational cocycle modules are independent
of this comparison and the general Alexander–Whitney construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u
namespace groupCohomology
variable (G : Type u) [Group G] (k : Type u) [CommRing k]
variable (A B : Rep k G)

private lemma cochainsIso₁_inv_apply (M : Rep k G)
    (x : G → M) (g : Fin 1 → G) :
    (cochainsIso₁ M).inv.hom x g = x (g 0) := rfl

private lemma cochainsIso₂_inv_apply (M : Rep k G)
    (x : G × G → M) (g : Fin 2 → G) :
    (cochainsIso₂ M).inv.hom x g = x (g 0, g 1) := rfl

private lemma cochainsIso₂_hom_apply (M : Rep k G)
    (x : (inhomogeneousCochains M).X 2) (g h : G) :
    (cochainsIso₂ M).hom.hom x (g, h) = x ![g, h] := rfl

private lemma cochainsIso₃_hom_apply (M : Rep k G)
    (x : (inhomogeneousCochains M).X 3) (g h j : G) :
    (cochainsIso₃ M).hom.hom x (g, h, j) = x ![g, h, j] := rfl

/-- In degree `(1,1)`, the general cochain pairing has the explicit
two-variable cup formula. -/
theorem inhomogeneousCupPairing_one_one
    (x : G → A) (y : G → B) :
    (cochainsIso₂ (A ⊗ B)).hom.hom
        (((inhomogeneousCupPairing G k A B).pair 1 1).hom
          ((cochainsIso₁ A).inv.hom x ⊗ₜ[k] (cochainsIso₁ B).inv.hom y)) =
      cupCochainOneOne A B x y := by
  funext gh
  rcases gh with ⟨g, h⟩
  rw [cochainsIso₂_hom_apply, cupCochainOneOne_apply]
  have hcup := inhomogeneousCupPairing_apply G k A B 1 1
    ((cochainsIso₁ A).inv.hom x) ((cochainsIso₁ B).inv.hom y) ![g, h]
  erw [cochainsIso₁_inv_apply G k A, cochainsIso₁_inv_apply G k B] at hcup
  simpa [Fin.partialProd] using hcup

/-- In degree `(1,2)`, the general cochain pairing has the explicit
three-variable cup formula. -/
theorem inhomogeneousCupPairing_one_two
    (x : G → A) (y : G × G → B) :
    (cochainsIso₃ (A ⊗ B)).hom.hom
        (((inhomogeneousCupPairing G k A B).pair 1 2).hom
          ((cochainsIso₁ A).inv.hom x ⊗ₜ[k] (cochainsIso₂ B).inv.hom y)) =
      cupCochainOneTwo A B x y := by
  funext ghj
  rcases ghj with ⟨g, h, j⟩
  rw [cochainsIso₃_hom_apply, cupCochainOneTwo_apply]
  have hcup := inhomogeneousCupPairing_apply G k A B 1 2
    ((cochainsIso₁ A).inv.hom x) ((cochainsIso₂ B).inv.hom y) ![g, h, j]
  erw [cochainsIso₁_inv_apply G k A, cochainsIso₂_inv_apply G k B] at hcup
  simpa [Fin.partialProd] using hcup


/-- Pointwise form of the degree-(1,1) cochain comparison. -/
theorem inhomogeneousCupPairing_one_one_apply
    {k G : Type u} [CommRing k] [Group G] (A B : Rep k G)
    (x : G → A) (y : G → B) (g h : G) :
    (cochainsIso₂ (A ⊗ B)).hom.hom
        (((inhomogeneousCupPairing G k A B).pair 1 1).hom
          ((cochainsIso₁ A).inv.hom x ⊗ₜ[k] (cochainsIso₁ B).inv.hom y)) (g, h) =
      cupCochainOneOne A B x y (g, h) :=
  congrFun (inhomogeneousCupPairing_one_one G k A B x y) (g, h)

/-- Pointwise form of the degree-(1,2) cochain comparison. -/
theorem inhomogeneousCupPairing_one_two_apply
    {k G : Type u} [CommRing k] [Group G] (A B : Rep k G)
    (x : G → A) (y : G × G → B) (g h j : G) :
    (cochainsIso₃ (A ⊗ B)).hom.hom
        (((inhomogeneousCupPairing G k A B).pair 1 2).hom
          ((cochainsIso₁ A).inv.hom x ⊗ₜ[k] (cochainsIso₂ B).inv.hom y)) (g, h, j) =
      cupCochainOneTwo A B x y (g, h, j) :=
  congrFun (inhomogeneousCupPairing_one_two G k A B x y) (g, h, j)

end groupCohomology

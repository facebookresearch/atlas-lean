/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCylinder
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# Inner horns and finite-interval endpoint corners

The auxiliary family is the literal union of the native inner horn family
and the actual endpoint corner maps of the finite-interval product cylinder
against every boundary inclusion. It includes both zero-dimensional corners.
Their specified pushout arrows are canonically isomorphic to the two interval
endpoint inclusions; this does not assert literal membership of an isomorphic
representative in an `ofHoms` family.

These are the maps in Cisinski, Higher Categories and Homotopical Algebra,
Remark 3.3.4, July 30, 2026 version, printed page 94. Closure and generation
properties are separate results.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- The literal family of inner horns and both actual endpoint corners
against every standard boundary, including dimension zero. -/
def auxiliaryGenerators : MorphismProperty SSet.{u} :=
  innerHornInclusions ⊔ .ofHoms (fun i : ℕ × Fin 2 ↦
    productPrecylinder.{u}.endpointCorner (boundary.{u} i.1).ι i.2)

/-- Membership retains equality of arrows, including their domains,
codomains and maps, for the endpoint-corner part of the family. -/
lemma auxiliaryGenerators.mem_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    auxiliaryGenerators f ↔ innerHornInclusions f ∨
      ∃ (n : ℕ) (ε : Fin 2),
        Arrow.mk f = Arrow.mk (productPrecylinder.{u}.endpointCorner (boundary.{u} n).ι ε) := by
  change (innerHornInclusions f ∨ MorphismProperty.ofHoms _ f) ↔ _
  rw [MorphismProperty.ofHoms_iff]
  simp only [Prod.exists]

/-- Every native inner horn inclusion belongs to the auxiliary family. -/
lemma auxiliaryGenerators.horn_ι_mem {n : ℕ} {k : Fin (n + 1)}
    (h0 : 0 < k) (hn : k < Fin.last n) :
    auxiliaryGenerators (horn.{u} n k).ι := by
  change innerHornInclusions _ ∨ _
  exact Or.inl (horn_ι_mem_innerHornInclusions h0 hn)

/-- Both endpoint corners in every dimension are actual family members. -/
lemma auxiliaryGenerators.endpointCorner_mem (n : ℕ) (ε : Fin 2) :
    auxiliaryGenerators (productPrecylinder.{u}.endpointCorner (boundary.{u} n).ι ε) := by
  change innerHornInclusions _ ∨ _
  exact Or.inr (MorphismProperty.ofHoms.mk (n, ε))

/-- Identify the specified dimension-zero corner arrow with the original
interval endpoint. The pushout source and product target are both transported
by their canonical isomorphisms. -/
def endpointCornerZeroIso (ε : Fin 2) :
    Arrow.mk (productPrecylinder.{u}.endpointCorner (boundary.{u} 0).ι ε) ≅
      Arrow.mk (endpoint.{u} ε) := by
  have h0 : IsInitial (boundary.{u} 0 : SSet) := by
    simpa only [boundary_zero] using (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u})))
  have hI0 : IsInitial (productPrecylinder.{u}.I.obj (boundary.{u} 0 : SSet)) :=
    IsInitial.isInitialObj (G := productPrecylinder.{u}.I) (X := _) h0
  have : IsIso ((productPrecylinder.{u}.app (boundary.{u} 0 : SSet)).endpoint ε) :=
    isIso_of_isInitial h0 hI0 _
  let a := asIso (pushout.inl (boundary.{u} 0).ι
    ((productPrecylinder.{u}.app (boundary.{u} 0 : SSet)).endpoint ε))
  let e : (𝟙_ SSet.{u}) ≅ (Δ[0] : SSet) :=
    isTerminalTensorUnit.uniqueUpToIso stdSimplex.isTerminalObj₀
  let b : joyalInterval.{u} ⊗ (Δ[0] : SSet.{u}) ≅ joyalInterval.{u} :=
    (tensorLeft joyalInterval.{u}).mapIso e.symm ≪≫ ρ_ joyalInterval.{u}
  have hb : b.hom = fst joyalInterval.{u} (Δ[0] : SSet.{u}) := by
    change joyalInterval.{u} ◁ e.inv ≫ (ρ_ joyalInterval.{u}).hom = _
    have he : e.inv = toUnit (Δ[0] : SSet.{u}) := isTerminalTensorUnit.hom_ext _ _
    rw [he]
    exact whiskerLeft_toUnit_comp_rightUnitor_hom _ _
  have hpoint : (productPrecylinder.{u}.app (Δ[0] : SSet.{u})).endpoint ε ≫ b.hom =
      endpoint.{u} ε := by
    have he := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ joyalInterval.{u} ⊗ Δ[0] ↦ f ≫ b.hom)
      (productPrecylinder_endpoint (Δ[0] : SSet.{u}) ε)
    refine he.trans ?_
    rw [hb, lift_fst, unitPoint, ← Category.assoc]
    have ht : toUnit (Δ[0] : SSet.{u}) ≫ e.hom = 𝟙 (Δ[0] : SSet) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht, Category.id_comp]
  refine Arrow.isoMk a.symm b ?_
  apply (Iso.inv_comp_eq a).mpr
  exact ((Precylinder.inl_endpointCorner_assoc productPrecylinder.{u}
    (boundary.{u} 0).ι ε b.hom).trans hpoint).symm

/-- The inverse source comparison is the actual pushout coprojection. -/
@[simp]
lemma endpointCornerZeroIso_inv_left (ε : Fin 2) :
    (endpointCornerZeroIso.{u} ε).inv.left = pushout.inl (boundary.{u} 0).ι
      ((productPrecylinder.{u}.app (boundary 0 : SSet)).endpoint ε) := rfl

/-- The target comparison is the first projection of the actual product. -/
@[simp]
lemma endpointCornerZeroIso_hom_right (ε : Fin 2) :
    (endpointCornerZeroIso.{u} ε).hom.right = fst joyalInterval.{u} (Δ[0] : SSet) := by
  change joyalInterval.{u} ◁ toUnit (Δ[0] : SSet.{u}) ≫ (ρ_ joyalInterval).hom = _
  exact whiskerLeft_toUnit_comp_rightUnitor_hom _ _

end SSet.joyalInterval

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem

/-!
# Public anodyne-system clients

The corner axioms give actual relative cylinder extensions. Each extension
retains its whole prescribed base map and both maps from the pushout diagram.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.AnodyneSystem

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}] (An : MorphismProperty C)
  [P.IsAnodyneSystem.{w} An]

/-- The endpoint axiom extends a relative cylinder over the entire base cylinder. -/
theorem exists_endpoint_extension {X Y Z B : C} (i : X ⟶ Y) [Mono i]
    (ε : Fin 2) (p : Z ⟶ B) (hp : An.rlp p) (a : Y ⟶ Z)
    (h : P.I.obj X ⟶ Z) (b : P.I.obj Y ⟶ B)
    (hi : i ≫ a = (P.app X).endpoint ε ≫ h)
    (ha : a ≫ p = (P.app Y).endpoint ε ≫ b)
    (hh : h ≫ p = P.I.map i ≫ b) :
    ∃ l : P.I.obj Y ⟶ Z,
      (P.app Y).endpoint ε ≫ l = a ∧ P.I.map i ≫ l = h ∧ l ≫ p = b := by
  have : HasLiftingProperty (P.endpointCorner i ε) p :=
    hp _ (Precylinder.IsAnodyneSystem.endpoint_corner (P := P) (An := An) i ε)
  let sq : CommSq (pushout.desc a h hi) (P.endpointCorner i ε) p b := ⟨by
    apply pushout.hom_ext
    · simpa only [pushout.inl_desc_assoc, Precylinder.inl_endpointCorner_assoc] using ha
    · simpa only [pushout.inr_desc_assoc, Precylinder.inr_endpointCorner_assoc] using hh⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have hl := congrArg (fun k ↦ pushout.inl i ((P.app X).endpoint ε) ≫ k) sq.fac_left
    simpa only [Precylinder.inl_endpointCorner_assoc, pushout.inl_desc] using hl
  · have hl := congrArg (fun k ↦ pushout.inr i ((P.app X).endpoint ε) ≫ k) sq.fac_left
    simpa only [Precylinder.inr_endpointCorner_assoc, pushout.inr_desc] using hl

/-- The boundary axiom extends a relative cylinder with its full boundary data. -/
theorem exists_boundary_extension {X Y Z B : C} (i : X ⟶ Y) (hi : An i)
    (p : Z ⟶ B) (hp : An.rlp p) (a : Y ⨿ Y ⟶ Z) (h : P.I.obj X ⟶ Z)
    (b : P.I.obj Y ⟶ B) (hc : coprod.map i i ≫ a = (P.app X).i ≫ h)
    (ha : a ≫ p = (P.app Y).i ≫ b) (hh : h ≫ p = P.I.map i ≫ b) :
    ∃ l : P.I.obj Y ⟶ Z,
      (P.app Y).i ≫ l = a ∧ P.I.map i ≫ l = h ∧ l ≫ p = b := by
  have : HasLiftingProperty (P.boundaryCorner i) p :=
    hp _ (Precylinder.IsAnodyneSystem.boundary_corner (P := P) (An := An) i hi)
  let sq : CommSq (pushout.desc a h hc) (P.boundaryCorner i) p b := ⟨by
    apply pushout.hom_ext
    · simpa only [pushout.inl_desc_assoc, Precylinder.inl_boundaryCorner_assoc] using ha
    · simpa only [pushout.inr_desc_assoc, Precylinder.inr_boundaryCorner_assoc] using hh⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have hl := congrArg (fun k ↦ pushout.inl (coprod.map i i) (P.app X).i ≫ k) sq.fac_left
    simpa only [Precylinder.inl_boundaryCorner_assoc, pushout.inl_desc] using hl
  · have hl := congrArg (fun k ↦ pushout.inr (coprod.map i i) (P.app X).i ≫ k) sq.fac_left
    simpa only [Precylinder.inr_boundaryCorner_assoc, pushout.inr_desc] using hl

end MathlibExtTest.AlgebraicTopology.ModelCategory.AnodyneSystem

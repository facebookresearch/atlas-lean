/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PresheafCylinderCorners

/-!
# Public clients for presheaf cylinder unions

The clients use the canonical pushout domains, the actual union isomorphisms
and a right lifting property to extend compatible source and boundary data.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u v'

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.PresheafCylinderCorners

variable {A : Type v} [Category.{v'} A]
  (P : Precylinder (𝟭 (Aᵒᵖ ⥤ Type u))) [P.IsExact.{w}]
  {X Y : Aᵒᵖ ⥤ Type u} (i : X ⟶ Y) [Mono i]

/-- Both coprojections of the specified endpoint pushout retain their
original cylinder maps under the union identification. -/
theorem endpointUnionRestrictions (ε : Fin 2) :
    Mono (P.endpointCorner i ε) ∧
    pushout.inl i ((P.app X).endpoint ε) ≫ (P.endpointCornerUnionIso i ε).hom ≫
        (Subobject.mk (P.I.map i) ⊔ Subobject.mk ((P.app Y).endpoint ε)).arrow =
      (P.app Y).endpoint ε ∧
    pushout.inr i ((P.app X).endpoint ε) ≫ (P.endpointCornerUnionIso i ε).hom ≫
        (Subobject.mk (P.I.map i) ⊔ Subobject.mk ((P.app Y).endpoint ε)).arrow =
      P.I.map i :=
  ⟨inferInstance, by simp, by simp⟩

/-- The boundary comparison has the exact source and target supplied by
the natural cylinder boundary. -/
theorem boundaryPullback :
    IsPullback (coprod.map i i) (P.app X).i (P.app Y).i (P.I.map i) :=
  P.boundary_isPullback i

/-- The boundary union identifies the given pushout over its actual
ambient cylinder, including both coprojections. -/
theorem boundaryUnionRestrictions :
    Mono (P.boundaryCorner i) ∧
    pushout.inl (coprod.map i i) (P.app X).i ≫ (P.boundaryCornerUnionIso i).hom ≫
        (Subobject.mk (P.I.map i) ⊔ Subobject.mk (P.app Y).i).arrow = (P.app Y).i ∧
    pushout.inr (coprod.map i i) (P.app X).i ≫ (P.boundaryCornerUnionIso i).hom ≫
        (Subobject.mk (P.I.map i) ⊔ Subobject.mk (P.app Y).i).arrow = P.I.map i :=
  ⟨inferInstance, by simp, by simp⟩

/-- A map with the right lifting property against monomorphisms extends
compatible data on the entire target boundary and the source cylinder. -/
theorem exists_extend_source_boundary {E B : Aᵒᵖ ⥤ Type u} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp p)
    (a : Y ⨿ Y ⟶ E) (b : P.I.obj X ⟶ E)
    (h : coprod.map i i ≫ a = (P.app X).i ≫ b) (q : P.I.obj Y ⟶ B)
    (ha : a ≫ p = (P.app Y).i ≫ q) (hb : b ≫ p = P.I.map i ≫ q) :
    ∃ H : P.I.obj Y ⟶ E, (P.app Y).i ≫ H = a ∧ P.I.map i ≫ H = b ∧ H ≫ p = q := by
  have : HasLiftingProperty (P.boundaryCorner i) p :=
    hp _ (MorphismProperty.monomorphisms.infer_property _)
  let sq : CommSq (pushout.desc a b h) (P.boundaryCorner i) p q := ⟨by
    apply pushout.hom_ext
    · simpa only [pushout.inl_desc_assoc, Precylinder.inl_boundaryCorner_assoc] using ha
    · simpa only [pushout.inr_desc_assoc, Precylinder.inr_boundaryCorner_assoc] using hb⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have he := congrArg (fun k ↦ pushout.inl (coprod.map i i) (P.app X).i ≫ k) sq.fac_left
    simpa only [Precylinder.inl_boundaryCorner_assoc, pushout.inl_desc] using he
  · have he := congrArg (fun k ↦ pushout.inr (coprod.map i i) (P.app X).i ≫ k) sq.fac_left
    simpa only [Precylinder.inr_boundaryCorner_assoc, pushout.inr_desc] using he

end MathlibExtTest.AlgebraicTopology.ModelCategory.PresheafCylinderCorners

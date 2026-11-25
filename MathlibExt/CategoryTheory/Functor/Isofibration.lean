/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Isofibrations of ordinary categories

A functor `F : C ⥤ D` is an *isofibration* when every isomorphism in `D`
whose domain is in the strict image of `F` on objects lifts strictly to an
isomorphism in `C`: given `X : C` and `g : F.obj X ≅ Y`, there exist
`Y' : C`, `f : X ≅ Y'` and `h : F.obj Y' = Y` with
`F.mapIso f ≪≫ eqToIso h = g`.

This is the strict, "evil" notion used for categorical fibrations of
simplicial sets via the homotopy-category functor: equality of the
lifted codomain on the nose is part of the data. In particular a general
equivalence of categories (full, faithful, essentially surjective) need
not be an isofibration; see
`Functor.isIsofibration_of_isEquivalence_of_surjective` for the
surjective-on-objects form. For example, the inclusion of one object into
the walking isomorphism is an equivalence, but it cannot lift an isomorphism
strictly to the other object.

## Main definitions

* `CategoryTheory.Functor.IsIsofibration`: the `Prop` class above.
* `CategoryTheory.isofibrations`: the corresponding
  `MorphismProperty Cat.{u, u}`.

## Main results

* Identity functors and composites of isofibrations are isofibrations;
  hence `isofibrations.IsMultiplicative`.
* Fully faithful functors that are surjective on objects are
  isofibrations; hence isomorphisms of categories (`Functor.IsIso`,
  `IsoCat`, and `IsIso` morphisms in `Cat`) and surjective equivalences
  are isofibrations.
* `isofibrations.RespectsIso` and stability under retracts.

Pullback stability in `Cat` (`isofibrations.IsStableUnderBaseChange`)
is not proved here. The pinned Mathlib provides `HasLimits Cat` with a
concrete description of limits (`CategoryTheory/Category/Cat/Limit.lean`:
objects of a limit are limits in `Type` of the object diagram, and
morphisms are limits of the hom diagram), and it also provides the
walking-isomorphism category `CategoryTheory.WalkingIso`
(`AlgebraicTopology/SimplicialSet/CoherentIso.lean`). What is missing is
packaged elementwise API for pullbacks in `Cat` (a characterization of
the objects, morphisms and isomorphisms of a pullback category in terms
of its projections), so constructing the lifted isomorphism in a
pullback category would require new API disproportionate to this file;
this is left as follow-up work rather than assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ u

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- A functor `F : C ⥤ D` is an isofibration when every isomorphism
`g : F.obj X ≅ Y` in `D` lifts strictly to an isomorphism in `C`:
there are `Y' : C`, `f : X ≅ Y'` and `h : F.obj Y' = Y` with
`F.mapIso f ≪≫ eqToIso h = g`. -/
class IsIsofibration (F : C ⥤ D) : Prop where
  /-- Every isomorphism out of `F.obj X` lifts to an isomorphism out of `X`. -/
  exists_lift : ∀ {X : C} {Y : D} (g : F.obj X ≅ Y),
    ∃ (Y' : C) (f : X ≅ Y') (h : F.obj Y' = Y), F.mapIso f ≪≫ eqToIso h = g

/-- The lifting property defining an isofibration, as an existence
statement for isomorphisms. -/
theorem exists_iso_lift (F : C ⥤ D) [F.IsIsofibration] {X : C} {Y : D}
    (g : F.obj X ≅ Y) :
    ∃ (Y' : C) (f : X ≅ Y') (h : F.obj Y' = Y), F.mapIso f ≪≫ eqToIso h = g :=
  IsIsofibration.exists_lift g

/-- The lifting property defining an isofibration, phrased for a morphism
that is known to be an isomorphism. -/
theorem exists_lift_hom (F : C ⥤ D) [F.IsIsofibration] {X : C} {Y : D}
    (g : F.obj X ⟶ Y) [IsIso g] :
    ∃ (Y' : C) (f : X ⟶ Y') (h : F.obj Y' = Y),
      IsIso f ∧ F.map f ≫ eqToHom h = g := by
  obtain ⟨Y', f, h, hf⟩ := F.exists_iso_lift (asIso g)
  refine ⟨Y', f.hom, h, f.isIso_hom, ?_⟩
  have := congrArg Iso.hom hf
  simpa using this

/-- Constructor for `IsIsofibration` from the morphism-level lifting
property. -/
theorem isIsofibration_of_exists_lift_hom (F : C ⥤ D)
    (h : ∀ {X : C} {Y : D} (g : F.obj X ⟶ Y) [IsIso g],
      ∃ (Y' : C) (f : X ⟶ Y') (hY : F.obj Y' = Y),
        IsIso f ∧ F.map f ≫ eqToHom hY = g) :
    F.IsIsofibration where
  exists_lift g := by
    obtain ⟨Y', f, hY, hfiso, hf⟩ := h g.hom
    refine ⟨Y', asIso f, hY, ?_⟩
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, eqToIso.hom]
    exact hf

/-- The identity functor is an isofibration. -/
instance isIsofibration_id : (𝟭 C).IsIsofibration where
  exists_lift g := ⟨_, g, rfl, by apply Iso.ext; simp⟩

/-- The composite of isofibrations is an isofibration. -/
instance isIsofibration_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.IsIsofibration] [G.IsIsofibration] : (F ⋙ G).IsIsofibration where
  exists_lift := by
    intro X Z g
    obtain ⟨Y', h, hY, hh⟩ := G.exists_iso_lift g
    obtain ⟨X', f, hX, hf⟩ := F.exists_iso_lift h
    refine ⟨X', f, (congrArg G.obj hX).trans hY, ?_⟩
    change G.mapIso (F.mapIso f) ≪≫ eqToIso ((congrArg G.obj hX).trans hY) = g
    rw [← eqToIso_trans (congrArg G.obj hX) hY, ← Iso.trans_assoc]
    have hGeq : G.mapIso (eqToIso hX) = eqToIso (congrArg G.obj hX) :=
      eqToIso_map G hX
    rw [← hGeq, ← Functor.mapIso_trans, hf, hh]

/-- A fully faithful functor that is surjective on objects is an
isofibration. -/
theorem isIsofibration_of_full_faithful_of_surjective (F : C ⥤ D)
    [F.Full] [F.Faithful] (hF : Function.Surjective F.obj) :
    F.IsIsofibration where
  exists_lift := by
    intro X Y g
    obtain ⟨Y', hY⟩ := hF Y
    refine ⟨Y', F.preimageIso (g ≪≫ (eqToIso hY).symm), hY, ?_⟩
    have hmap : F.mapIso (F.preimageIso (g ≪≫ (eqToIso hY).symm)) =
        g ≪≫ (eqToIso hY).symm := by
      apply Iso.ext
      simp
    rw [hmap]
    simp

/-- An equivalence of categories that is surjective on objects is an
isofibration. Surjectivity cannot be dropped: a skeleton inclusion is
an equivalence but not an isofibration in general. -/
theorem isIsofibration_of_isEquivalence_of_surjective (F : C ⥤ D)
    [F.IsEquivalence] (hF : Function.Surjective F.obj) :
    F.IsIsofibration :=
  F.isIsofibration_of_full_faithful_of_surjective hF

/-- A functor that is an isomorphism of categories (full, faithful and
bijective on objects) is an isofibration. -/
instance isIsofibration_of_isIso (F : C ⥤ D) [F.IsIso] : F.IsIsofibration :=
  F.isIsofibration_of_full_faithful_of_surjective (F.bijective_obj.surjective)

/-- A retract of an isofibration (in the arrow category of functors,
with strict equalities of functors) is an isofibration. -/
theorem isIsofibration_of_retract (F : C ⥤ D)
    {C' : Type u₄} [Category.{v₄} C'] {D' : Type u₅} [Category.{v₅} D']
    (G : C' ⥤ D') [G.IsIsofibration]
    (iL : C ⥤ C') (rL : C' ⥤ C) (iR : D ⥤ D') (rR : D' ⥤ D)
    (hiL : iL ⋙ rL = 𝟭 C) (hiR : iR ⋙ rR = 𝟭 D)
    (hi : iL ⋙ G = F ⋙ iR) (hr : rL ⋙ F = G ⋙ rR) :
    F.IsIsofibration := by
  apply isIsofibration_of_exists_lift_hom
  intro X Y g hg
  have hiX : G.obj (iL.obj X) = iR.obj (F.obj X) := Functor.congr_obj hi X
  obtain ⟨Z', β, hZ, hβiso, hβ⟩ :=
    G.exists_lift_hom (eqToHom hiX ≫ iR.map g)
  have := hβiso
  have hrLX : rL.obj (iL.obj X) = X := Functor.congr_obj hiL X
  refine ⟨rL.obj Z', eqToHom hrLX.symm ≫ rL.map β,
    (Functor.congr_obj hr Z').trans ((congrArg rR.obj hZ).trans
      (Functor.congr_obj hiR Y)), by infer_instance, ?_⟩
  have e1 := Functor.congr_hom hr β
  have e2 := Functor.congr_hom hiR g
  simp only [Functor.comp_map, Functor.id_map] at e1 e2
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [e1]
  simp only [Functor.comp_obj, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  change eqToHom ((congrArg F.obj hrLX.symm).trans (Functor.congr_obj hr (iL.obj X))) ≫
      rR.map (G.map β) ≫
        eqToHom ((congrArg rR.obj hZ).trans (Functor.congr_obj hiR Y)) = g
  rw [← eqToHom_trans (congrArg rR.obj hZ) (Functor.congr_obj hiR Y),
    ← Category.assoc (rR.map (G.map β)), ← eqToHom_map rR hZ, ← Functor.map_comp, hβ,
    Functor.map_comp, eqToHom_map, Category.assoc, e2]
  simp

end Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The functor underlying an equivalence of categories that is
surjective on objects is an isofibration. -/
theorem Equivalence.isIsofibration_functor_of_surjective (e : C ≌ D)
    (hF : Function.Surjective e.functor.obj) : e.functor.IsIsofibration :=
  e.functor.isIsofibration_of_isEquivalence_of_surjective hF

/-- The inverse functor of an equivalence of categories that is
surjective on objects is an isofibration. -/
theorem Equivalence.isIsofibration_inverse_of_surjective (e : C ≌ D)
    (hF : Function.Surjective e.inverse.obj) : e.inverse.IsIsofibration :=
  e.inverse.isIsofibration_of_isEquivalence_of_surjective hF

/-- The functor underlying a strict isomorphism of categories is an
isofibration. -/
instance IsoCat.isIsofibration_functor (e : IsoCat C D) : e.functor.IsIsofibration :=
  e.functor.isIsofibration_of_isIso

/-- The inverse functor of a strict isomorphism of categories is an
isofibration. -/
instance IsoCat.isIsofibration_inverse (e : IsoCat C D) : e.inverse.IsIsofibration :=
  e.inverse.isIsofibration_of_isIso

/-- The morphism property in `Cat.{u, u}` consisting of isofibrations:
a morphism `F : X ⟶ Y` in `Cat` lies in `isofibrations` when its
underlying functor `F.toFunctor` is an isofibration. -/
def isofibrations : MorphismProperty Cat.{u, u} :=
  fun _ _ F => F.toFunctor.IsIsofibration

namespace isofibrations

variable {X Y Z : Cat.{u, u}}

/-- Membership in `isofibrations` unfolds to the `IsIsofibration` class
on the underlying functor. -/
theorem mem_iff (F : X ⟶ Y) : isofibrations F ↔ F.toFunctor.IsIsofibration :=
  Iff.rfl

/-- Identity morphisms in `Cat` are isofibrations. -/
theorem id_mem (X : Cat.{u, u}) : isofibrations (𝟙 X) := by
  change (𝟭 X).IsIsofibration
  infer_instance

/-- The composite of isofibrations in `Cat` is an isofibration. -/
theorem comp_mem {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : isofibrations F) (hG : isofibrations G) : isofibrations (F ≫ G) := by
  have hF' : F.toFunctor.IsIsofibration := hF
  have hG' : G.toFunctor.IsIsofibration := hG
  change (F.toFunctor ⋙ G.toFunctor).IsIsofibration
  infer_instance

end isofibrations

/-- Isofibrations in `Cat` contain identities and are stable under
composition. -/
instance : MorphismProperty.IsMultiplicative (isofibrations.{u}) where
  id_mem X := isofibrations.id_mem X
  comp_mem _ _ hF hG := isofibrations.comp_mem hF hG

/-- A morphism in `Cat` is an isofibration when its underlying functor
is an isofibration. This is the `toCatHom` form of `isofibrations.mem_iff`. -/
theorem isofibrations_toCatHom {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.IsIsofibration] : isofibrations F.toCatHom :=
  inferInstanceAs F.IsIsofibration

/-- Isomorphisms in `Cat` are isofibrations: an isomorphism in `Cat`
has a strict inverse functor, so its underlying functor is an
isomorphism of categories. -/
theorem isofibrations_of_isIso {X Y : Cat.{u, u}} (F : X ⟶ Y) [IsIso F] :
    isofibrations F := by
  rw [isofibrations.mem_iff]
  exact @Functor.isIsofibration_of_isIso _ _ _ _ F.toFunctor
    (IsoCat.isIso_functor
      { functor := F.toFunctor
        inverse := (inv F).toFunctor
        unit_eq := (congrArg Cat.Hom.toFunctor (IsIso.hom_inv_id F)).symm
        counit_eq := congrArg Cat.Hom.toFunctor (IsIso.inv_hom_id F) })

/-- Isofibrations in `Cat` are stable under pre- and postcomposition
with isomorphisms in `Cat`. -/
instance : MorphismProperty.RespectsIso (isofibrations.{u}) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _f hf => isofibrations.comp_mem (isofibrations_of_isIso e.hom) hf)
    (fun e _f hf => isofibrations.comp_mem hf (isofibrations_of_isIso e.hom))

/-- Isofibrations in `Cat` are stable under retracts. -/
instance : MorphismProperty.IsStableUnderRetracts (isofibrations.{u}) where
  of_retract {X Y Z W f g} h hg := by
    have hg' : (g : Z ⟶ W).toFunctor.IsIsofibration := hg
    have := hg'
    change (f : X ⟶ Y).toFunctor.IsIsofibration
    exact Functor.isIsofibration_of_retract (f : X ⟶ Y).toFunctor
      (g : Z ⟶ W).toFunctor h.i.left.toFunctor h.r.left.toFunctor
      h.i.right.toFunctor h.r.right.toFunctor
      (congrArg Cat.Hom.toFunctor h.retract_left)
      (congrArg Cat.Hom.toFunctor h.retract_right)
      (congrArg Cat.Hom.toFunctor h.i_w)
      (congrArg Cat.Hom.toFunctor h.r_w)

end CategoryTheory

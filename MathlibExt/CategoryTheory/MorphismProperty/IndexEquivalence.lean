/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
public import Mathlib.CategoryTheory.Equivalence

/-!
# Original diagram classes under an index equivalence

An actual index equivalence compares the classes on both functor categories.
Its original unit covers every source object, and its original counit covers
every target object. Left and right lifting classes are transported using the
existing adjunction lifting correspondence.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uD vD uS vS uM vM
open CategoryTheory

namespace CategoryTheory.MorphismProperty

section Orthogonals

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]

/-- An equivalence transports the complete left lifting class of an iso-stable property. -/
theorem inverseImage_llp_of_equivalence (e : D ≌ S) (P : MorphismProperty S)
    [P.RespectsIso] :
    P.llp.inverseImage e.functor = (P.inverseImage e.functor).llp := by
  ext X Y i
  constructor
  · intro hi A B p hp
    exact (Functor.hasLiftingProperty_iff_of_isEquivalence e.functor i p).mp
      (hi (e.functor.map p) hp)
  · intro hi A B p hp
    have hp' : P (e.functor.map (e.inverse.map p)) :=
      (P.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor S S).mapIso e.counitIso).app (Arrow.mk p))).mpr hp
    exact (e.toAdjunction.hasLiftingProperty_iff i p).mpr
      (hi (e.inverse.map p) hp')

/-- An equivalence transports the complete right lifting class of an iso-stable property. -/
theorem inverseImage_rlp_of_equivalence (e : D ≌ S) (P : MorphismProperty S)
    [P.RespectsIso] :
    P.rlp.inverseImage e.functor = (P.inverseImage e.functor).rlp := by
  ext X Y p
  constructor
  · intro hp A B i hi
    exact (Functor.hasLiftingProperty_iff_of_isEquivalence e.functor i p).mp
      (hp (e.functor.map i) hi)
  · intro hp A B i hi
    have hi' : P (e.functor.map (e.inverse.map i)) :=
      (P.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor S S).mapIso e.counitIso).app (Arrow.mk i))).mpr hi
    exact (e.symm.toAdjunction.hasLiftingProperty_iff i p).mp
      (hp (e.inverse.map i) hi')

end Orthogonals

section OriginalComponents

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M]

/-- The actual unit compares an original component with its representative component. -/
def unitComponentArrowIso (e : D ≌ S) {F G : D ⥤ M} (f : F ⟶ G) (d : D) :
    Arrow.mk (f.app d) ≅ Arrow.mk (f.app (e.inverse.obj (e.functor.obj d))) :=
  Arrow.isoMk (F.mapIso (e.unitIso.app d)) (G.mapIso (e.unitIso.app d))
    (f.naturality (e.unit.app d))

/-- All four component maps retain the original unit and its actual inverse. -/
theorem unitComponentArrowIso_fields (e : D ≌ S) {F G : D ⥤ M} (f : F ⟶ G) (d : D) :
    (unitComponentArrowIso e f d).hom.left = F.map (e.unit.app d) ∧
      (unitComponentArrowIso e f d).hom.right = G.map (e.unit.app d) ∧
      (unitComponentArrowIso e f d).inv.left = F.map (e.unitInv.app d) ∧
      (unitComponentArrowIso e f d).inv.right = G.map (e.unitInv.app d) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The actual counit compares the transported representative component with its original. -/
def counitComponentArrowIso (e : D ≌ S) {F G : S ⥤ M} (f : F ⟶ G) (s : S) :
    Arrow.mk (f.app (e.functor.obj (e.inverse.obj s))) ≅ Arrow.mk (f.app s) :=
  Arrow.isoMk (F.mapIso (e.counitIso.app s)) (G.mapIso (e.counitIso.app s))
    (f.naturality (e.counit.app s))

/-- All four target component maps retain the original counit and its actual inverse. -/
theorem counitComponentArrowIso_fields (e : D ≌ S) {F G : S ⥤ M} (f : F ⟶ G) (s : S) :
    (counitComponentArrowIso e f s).hom.left = F.map (e.counit.app s) ∧
      (counitComponentArrowIso e f s).hom.right = G.map (e.counit.app s) ∧
      (counitComponentArrowIso e f s).inv.left = F.map (e.counitInv.app s) ∧
      (counitComponentArrowIso e f s).inv.right = G.map (e.counitInv.app s) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every original object is detected by precomposition with the actual inverse functor. -/
theorem functorCategory_inverseImage_congrLeft (e : D ≌ S) (P : MorphismProperty M)
    [P.RespectsIso] :
    (P.functorCategory S).inverseImage (e.congrLeft (E := M)).functor =
      P.functorCategory D := by
  ext F G f
  constructor
  · intro hf d
    exact (P.arrow_mk_iso_iff (unitComponentArrowIso e f d)).mpr
      (hf (e.functor.obj d))
  · intro hf s
    exact hf (e.inverse.obj s)

/-- The reverse precomposition detects every original target object through the counit. -/
theorem functorCategory_inverseImage_congrLeft_inverse (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory D).inverseImage (e.congrLeft (E := M)).inverse =
      P.functorCategory S := by
  ext F G f
  constructor
  · intro hf s
    exact (P.arrow_mk_iso_iff (counitComponentArrowIso e f s)).mp
      (hf (e.inverse.obj s))
  · intro hf d
    exact hf (e.functor.obj d)

/-- The complete all-original left class is the inverse image of the representative left class. -/
theorem functorCategory_llp_inverseImage_congrLeft (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory S).llp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).llp := by
  rw [inverseImage_llp_of_equivalence, functorCategory_inverseImage_congrLeft]

/-- The complete all-original right class is the inverse image of the representative right class. -/
theorem functorCategory_rlp_inverseImage_congrLeft (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory S).rlp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).rlp := by
  rw [inverseImage_rlp_of_equivalence, functorCategory_inverseImage_congrLeft]

/-- Reverse precomposition retains the entire representative left lifting class. -/
theorem functorCategory_llp_inverseImage_congrLeft_inverse (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory D).llp.inverseImage (e.congrLeft (E := M)).inverse =
      (P.functorCategory S).llp := by
  change (P.functorCategory D).llp.inverseImage (e.symm.congrLeft (E := M)).functor = _
  exact functorCategory_llp_inverseImage_congrLeft e.symm P

/-- Reverse precomposition retains the entire representative right lifting class. -/
theorem functorCategory_rlp_inverseImage_congrLeft_inverse (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory D).rlp.inverseImage (e.congrLeft (E := M)).inverse =
      (P.functorCategory S).rlp := by
  change (P.functorCategory D).rlp.inverseImage (e.symm.congrLeft (E := M)).functor = _
  exact functorCategory_rlp_inverseImage_congrLeft e.symm P

/-- Both inverse images retain the complete double left orthogonal generated by a base class. -/
theorem functorCategory_rlp_llp_inverseImage_congrLeft (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory S).rlp.llp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).rlp.llp := by
  rw [inverseImage_llp_of_equivalence, functorCategory_rlp_inverseImage_congrLeft]

/-- Both inverse images retain the complete double right orthogonal generated by a base class. -/
theorem functorCategory_llp_rlp_inverseImage_congrLeft (e : D ≌ S)
    (P : MorphismProperty M) [P.RespectsIso] :
    (P.functorCategory S).llp.rlp.inverseImage (e.congrLeft (E := M)).functor =
      (P.functorCategory D).llp.rlp := by
  rw [inverseImage_rlp_of_equivalence, functorCategory_llp_inverseImage_congrLeft]

end OriginalComponents

end CategoryTheory.MorphismProperty

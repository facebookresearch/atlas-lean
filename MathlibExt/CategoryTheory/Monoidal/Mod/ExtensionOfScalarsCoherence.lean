/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalars
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Coherence of actual extension and restriction of scalars

Restriction precomposes the original module action with the actual scalar
map. Its identity and composition comparisons have identity carrier maps.
Their adjoint mates give the comparisons for the balanced induction functors.
In particular the induction compositor retains the two original generators.

This is the categorical scalar-change construction used in the proof of
Schwede--Shipley's module comparison theorem and in EKMM, Chapter III, §4.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory Functor
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod.ExtensionOfScalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D : C} [MonObj A] [MonObj B] [MonObj D]

/-- Restriction by the actual identity scalar map has the unchanged module carrier. -/
def restrictionIdIso : restriction (𝟙 A) ≅ 𝟭 (Mod C A) :=
  NatIso.ofComponents (F := restriction (𝟙 A)) (G := 𝟭 (Mod C A)) (fun M =>
    { hom := Mod.Hom.mk' (M := (restriction (𝟙 A)).obj M) (N := M) (𝟙 M.X) (by
        change (((𝟙 A) ▷ M.X) ≫ M.mod.smul) ≫ 𝟙 M.X =
          (A ◁ 𝟙 M.X) ≫ M.mod.smul
        simp)
      inv := Mod.Hom.mk' (M := M) (N := (restriction (𝟙 A)).obj M) (𝟙 M.X) (by
        change M.mod.smul ≫ 𝟙 M.X =
          (A ◁ 𝟙 M.X) ≫ ((𝟙 A) ▷ M.X) ≫ M.mod.smul
        simp)
      hom_inv_id := by
        apply Mod.hom_ext
        change (𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
        simp
      inv_hom_id := by
        apply Mod.hom_ext
        change (𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
        simp })
    (by
      intro M N f
      apply Mod.hom_ext
      change f.hom ≫ 𝟙 N.X = 𝟙 M.X ≫ f.hom
      simp)

/-- Both original restriction stages agree with restriction by the composite scalar map. -/
def restrictionCompIso (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q] :
    restriction q ⋙ restriction p ≅ restriction (p ≫ q) :=
  NatIso.ofComponents (F := restriction q ⋙ restriction p) (G := restriction (p ≫ q)) (fun M =>
    { hom := Mod.Hom.mk' (M := (restriction q ⋙ restriction p).obj M)
        (N := (restriction (p ≫ q)).obj M) (𝟙 M.X) (by
        change ((p ▷ M.X) ≫ (q ▷ M.X) ≫ M.mod.smul) ≫ 𝟙 M.X =
          (A ◁ 𝟙 M.X) ≫ ((p ≫ q) ▷ M.X) ≫ M.mod.smul
        simp [comp_whiskerRight, Category.assoc])
      inv := Mod.Hom.mk' (M := (restriction (p ≫ q)).obj M)
        (N := (restriction q ⋙ restriction p).obj M) (𝟙 M.X) (by
        change (((p ≫ q) ▷ M.X) ≫ M.mod.smul) ≫ 𝟙 M.X =
          (A ◁ 𝟙 M.X) ≫ (p ▷ M.X) ≫ (q ▷ M.X) ≫ M.mod.smul
        simp [comp_whiskerRight, Category.assoc])
      hom_inv_id := by
        apply Mod.hom_ext
        change (𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
        simp
      inv_hom_id := by
        apply Mod.hom_ext
        change (𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
        simp })
    (by
      intro M N f
      apply Mod.hom_ext
      change f.hom ≫ 𝟙 N.X = 𝟙 M.X ≫ f.hom
      simp)

/-- The whole identity-restriction comparison is the original identity on the carrier. -/
@[simp]
theorem restrictionIdIso_hom_hom (M : Mod C A) :
    ((restrictionIdIso (A := A)).hom.app M).hom = 𝟙 M.X := rfl

/-- The inverse identity-restriction comparison also retains the whole original carrier. -/
@[simp]
theorem restrictionIdIso_inv_hom (M : Mod C A) :
    ((restrictionIdIso (A := A)).inv.app M).hom = 𝟙 M.X := rfl

/-- The actual composite-restriction comparison has the unchanged original carrier map. -/
@[simp]
theorem restrictionCompIso_hom_hom (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] (M : Mod C D) :
    ((restrictionCompIso p q).hom.app M).hom = 𝟙 M.X := rfl

/-- The inverse composite-restriction comparison has the same original identity carrier map. -/
@[simp]
theorem restrictionCompIso_inv_hom (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q] (M : Mod C D) :
    ((restrictionCompIso p q).inv.app M).hom = 𝟙 M.X := rfl

/-- Actual balanced induction by the identity scalar map is naturally the identity functor. -/
def inductionIdIso [HasCoequalizers (Mod C A)] : induction (𝟙 A) ≅ 𝟭 (Mod C A) :=
  (conjugateIsoEquiv (Adjunction.id (C := Mod C A)) (adjunction (𝟙 A))).symm
    (restrictionIdIso (A := A)).symm

/-- Actual balanced induction is compatible with the whole original composite scalar map. -/
def inductionCompIso (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q]
    [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)] :
    induction p ⋙ induction q ≅ induction (p ≫ q) :=
  (conjugateIsoEquiv (adjunction (p ≫ q)) ((adjunction p).comp (adjunction q))).symm
    (restrictionCompIso p q).symm

/-- The identity induction comparison is the mate of the actual identity restriction map. -/
theorem inductionIdIso_conjugate [HasCoequalizers (Mod C A)] :
    conjugateEquiv (Adjunction.id (C := Mod C A)) (adjunction (𝟙 A))
      (inductionIdIso (A := A)).hom = (restrictionIdIso (A := A)).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The induction compositor is the actual adjoint mate of the full restriction compositor. -/
theorem inductionCompIso_conjugate (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q]
    [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)] :
    conjugateEquiv (adjunction (p ≫ q)) ((adjunction p).comp (adjunction q))
      (inductionCompIso p q).hom = (restrictionCompIso p q).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The identity induction comparison contracts the original balanced unit generator. -/
theorem inductionIdIso_generator [HasCoequalizers (Mod C A)] (M : Mod C A) :
    generator (𝟙 A) M ≫ ((inductionIdIso (A := A)).hom.app M).hom = 𝟙 M.X := by
  have h := congrArg Mod.Hom.hom
    (unit_conjugateEquiv (Adjunction.id (C := Mod C A)) (adjunction (𝟙 A))
      (inductionIdIso (A := A)).hom M)
  rw [inductionIdIso_conjugate] at h
  change (𝟙 M.X) ≫ 𝟙 M.X =
    ((adjunction (𝟙 A)).unit.app M).hom ≫ ((inductionIdIso (A := A)).hom.app M).hom at h
  rw [unit_hom, Category.id_comp] at h
  exact h.symm

/-- The whole induction compositor takes the two original generators to the composite generator. -/
theorem inductionCompIso_generator (p : A ⟶ B) [IsMonHom p]
    (q : B ⟶ D) [IsMonHom q]
    [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)] (M : Mod C A) :
    generator p M ≫ generator q (object p M) ≫ ((inductionCompIso p q).hom.app M).hom =
      generator (p ≫ q) M := by
  have h := congrArg Mod.Hom.hom
    (unit_conjugateEquiv (adjunction (p ≫ q)) ((adjunction p).comp (adjunction q))
      (inductionCompIso p q).hom M)
  rw [inductionCompIso_conjugate] at h
  change ((adjunction (p ≫ q)).unit.app M).hom ≫ 𝟙 _ =
    (((adjunction p).comp (adjunction q)).unit.app M).hom ≫
      ((inductionCompIso p q).hom.app M).hom at h
  have hu : (((adjunction p).comp (adjunction q)).unit.app M).hom =
      generator p M ≫ generator q (object p M) := by
    rw [Adjunction.comp_unit_app, Mod.comp_hom']
    change ((adjunction p).unit.app M).hom ≫ ((adjunction q).unit.app (object p M)).hom = _
    rw [unit_hom, unit_hom]
    rfl
  rw [unit_hom, hu] at h
  change generator (p ≫ q) M ≫ 𝟙 (object (p ≫ q) M).X =
    (generator p M ≫ generator q (object p M)) ≫ ((inductionCompIso p q).hom.app M).hom at h
  exact (Category.assoc (generator p M) (generator q (object p M))
    ((inductionCompIso p q).hom.app M).hom).symm.trans (h.symm.trans (Category.comp_id _))

/-- An equality of actual scalar maps gives the original identity comparison on restricted carriers. -/
def restrictionCongrIso {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p'] (h : p = p') :
    restriction p ≅ restriction p' := by
  cases h
  exact Iso.refl _

/-- Scalar-equality transport has the original identity carrier map. -/
@[simp]
theorem restrictionCongrIso_hom_hom {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    (h : p = p') (M : Mod C B) :
    ((restrictionCongrIso h).hom.app M).hom = 𝟙 M.X := by
  cases h
  rfl

/-- The inverse scalar-equality transport has the same original identity carrier map. -/
@[simp]
theorem restrictionCongrIso_inv_hom {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    (h : p = p') (M : Mod C B) :
    ((restrictionCongrIso h).inv.app M).hom = 𝟙 M.X := by
  cases h
  rfl

/-- Equality transport for the actual balanced induction functor. -/
def inductionCongrIso {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    [HasCoequalizers (Mod C B)] (h : p = p') : induction p ≅ induction p' := by
  cases h
  exact Iso.refl _

/-- Scalar-equality transport on balanced induction is the mate of its actual restriction transport. -/
theorem inductionCongrIso_conjugate {p p' : A ⟶ B} [IsMonHom p] [IsMonHom p']
    [HasCoequalizers (Mod C B)] (h : p = p') :
    conjugateEquiv (adjunction p') (adjunction p) (inductionCongrIso h).hom =
      (restrictionCongrIso h).inv := by
  cases h
  simp [inductionCongrIso, restrictionCongrIso]

/-- Restriction composition retains both complete routes and the actual scalar associativity transport. -/
theorem restriction_associativity {E : C} [MonObj E]
    (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q] (r : D ⟶ E) [IsMonHom r] :
    whiskerRight (restrictionCompIso q r).hom (restriction p) ≫
        (restrictionCompIso p (q ≫ r)).hom =
      (Functor.associator (restriction r) (restriction q) (restriction p)).hom ≫
        whiskerLeft (restriction r) (restrictionCompIso p q).hom ≫
          (restrictionCompIso (p ≫ q) r).hom ≫
            (restrictionCongrIso (Category.assoc p q r)).hom := by
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change (𝟙 M.X) ≫ 𝟙 M.X =
    (𝟙 M.X) ≫ 𝟙 M.X ≫ 𝟙 M.X ≫
      ((restrictionCongrIso (Category.assoc p q r)).hom.app M).hom
  simp only [restrictionCongrIso_hom_hom]
  change (𝟙 M.X) ≫ 𝟙 M.X = (𝟙 M.X) ≫ 𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X
  simp only [Category.id_comp]

/-- The source scalar identity is the actual target unitor for restriction. -/
theorem restriction_unit_source (p : A ⟶ B) [IsMonHom p] :
    (restrictionCompIso (𝟙 A) p).hom ≫ (restrictionCongrIso (Category.id_comp p)).hom =
      whiskerLeft (restriction p) (restrictionIdIso (A := A)).hom ≫
        (Functor.rightUnitor (restriction p)).hom := by
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change (𝟙 M.X) ≫ ((restrictionCongrIso (Category.id_comp p)).hom.app M).hom =
    (𝟙 M.X) ≫ 𝟙 M.X
  simp only [restrictionCongrIso_hom_hom]
  rfl

/-- The target scalar identity is the actual source unitor for restriction. -/
theorem restriction_unit_target (p : A ⟶ B) [IsMonHom p] :
    (restrictionCompIso p (𝟙 B)).hom ≫ (restrictionCongrIso (Category.comp_id p)).hom =
      whiskerRight (restrictionIdIso (A := B)).hom (restriction p) ≫
        (Functor.leftUnitor (restriction p)).hom := by
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change (𝟙 M.X) ≫ ((restrictionCongrIso (Category.comp_id p)).hom.app M).hom =
    (𝟙 M.X) ≫ 𝟙 M.X
  simp only [restrictionCongrIso_hom_hom]
  rfl

/-- The actual balanced induction source unit is coherent with the original scalar identity map. -/
theorem induction_unit_source (p : A ⟶ B) [IsMonHom p]
    [HasCoequalizers (Mod C A)] [HasCoequalizers (Mod C B)] :
    (inductionCompIso (𝟙 A) p).hom ≫ (inductionCongrIso (Category.id_comp p)).hom =
      whiskerRight (inductionIdIso (A := A)).hom (induction p) ≫
        (Functor.leftUnitor (induction p)).hom := by
  apply (conjugateEquiv (adjunction p) ((adjunction (𝟙 A)).comp (adjunction p))).injective
  rw [← conjugateEquiv_comp (adjunction p) (adjunction (𝟙 A ≫ p))
    ((adjunction (𝟙 A)).comp (adjunction p))]
  rw [← conjugateEquiv_comp (adjunction p) ((Adjunction.id (C := Mod C A)).comp (adjunction p))
    ((adjunction (𝟙 A)).comp (adjunction p))]
  rw [inductionCongrIso_conjugate, inductionCompIso_conjugate,
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight, inductionIdIso_conjugate]
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change ((restrictionCongrIso (Category.id_comp p)).inv.app M).hom ≫ 𝟙 M.X =
    (𝟙 M.X) ≫ 𝟙 M.X
  simp only [restrictionCongrIso_inv_hom]
  rfl

/-- The actual balanced induction target unit is coherent with the original scalar identity map. -/
theorem induction_unit_target (p : A ⟶ B) [IsMonHom p] [HasCoequalizers (Mod C B)] :
    (inductionCompIso p (𝟙 B)).hom ≫ (inductionCongrIso (Category.comp_id p)).hom =
      whiskerLeft (induction p) (inductionIdIso (A := B)).hom ≫
        (Functor.rightUnitor (induction p)).hom := by
  apply (conjugateEquiv (adjunction p) ((adjunction p).comp (adjunction (𝟙 B)))).injective
  rw [← conjugateEquiv_comp (adjunction p) (adjunction (p ≫ 𝟙 B))
    ((adjunction p).comp (adjunction (𝟙 B)))]
  rw [← conjugateEquiv_comp (adjunction p) ((adjunction p).comp (Adjunction.id (C := Mod C B)))
    ((adjunction p).comp (adjunction (𝟙 B)))]
  rw [inductionCongrIso_conjugate, inductionCompIso_conjugate,
    conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft, inductionIdIso_conjugate]
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change ((restrictionCongrIso (Category.comp_id p)).inv.app M).hom ≫ 𝟙 M.X =
    (𝟙 M.X) ≫ 𝟙 M.X
  simp only [restrictionCongrIso_inv_hom]
  rfl

/-- The two full balanced-induction composition routes agree with actual scalar associativity. -/
theorem induction_associativity {E : C} [MonObj E]
    (p : A ⟶ B) [IsMonHom p] (q : B ⟶ D) [IsMonHom q] (r : D ⟶ E) [IsMonHom r]
    [HasCoequalizers (Mod C B)] [HasCoequalizers (Mod C D)] [HasCoequalizers (Mod C E)] :
    whiskerRight (inductionCompIso p q).hom (induction r) ≫
        (inductionCompIso (p ≫ q) r).hom ≫
          (inductionCongrIso (Category.assoc p q r)).hom =
      (Functor.associator (induction p) (induction q) (induction r)).hom ≫
        whiskerLeft (induction p) (inductionCompIso q r).hom ≫
          (inductionCompIso p (q ≫ r)).hom := by
  apply (conjugateEquiv (adjunction (p ≫ q ≫ r))
    (((adjunction p).comp (adjunction q)).comp (adjunction r))).injective
  rw [← conjugateEquiv_comp (adjunction (p ≫ q ≫ r))
    ((adjunction (p ≫ q)).comp (adjunction r))
    (((adjunction p).comp (adjunction q)).comp (adjunction r))]
  rw [← conjugateEquiv_comp (adjunction (p ≫ q ≫ r)) (adjunction ((p ≫ q) ≫ r))
    ((adjunction (p ≫ q)).comp (adjunction r))]
  rw [← conjugateEquiv_comp (adjunction (p ≫ q ≫ r))
    ((adjunction p).comp ((adjunction q).comp (adjunction r)))
    (((adjunction p).comp (adjunction q)).comp (adjunction r))]
  rw [← conjugateEquiv_comp (adjunction (p ≫ q ≫ r)) ((adjunction p).comp (adjunction (q ≫ r)))
    ((adjunction p).comp ((adjunction q).comp (adjunction r)))]
  rw [inductionCongrIso_conjugate, inductionCompIso_conjugate,
    conjugateEquiv_whiskerRight, inductionCompIso_conjugate,
    inductionCompIso_conjugate, conjugateEquiv_whiskerLeft, inductionCompIso_conjugate,
    conjugateEquiv_associator_hom]
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  change (((restrictionCongrIso (Category.assoc p q r)).inv.app M).hom ≫ 𝟙 M.X) ≫ 𝟙 M.X =
    ((𝟙 M.X) ≫ 𝟙 M.X) ≫ 𝟙 M.X
  simp only [restrictionCongrIso_inv_hom]
  rfl

end CategoryTheory.Mod.ExtensionOfScalars

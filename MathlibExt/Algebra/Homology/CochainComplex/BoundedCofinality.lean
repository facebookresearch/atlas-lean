/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded

/-!
# Bounded cofinality through the original component lifts

The original full faithful functor lifts a complex from chosen source
objects and component isomorphisms. Its differential is the preimage of
the conjugated original differential; faithfulness proves its shape and
square-zero equations.

Ordinary cofinality uses target complements. Strict cofinality uses
source complements and their original functor images. The finite-window
constructions retain the original zeros, differentials and biproducts.
These are the object complements used in Weibel, *The K-book*, IV.8.13
and V.Remark 2.2.1. Approximation and K-space comparisons require their
separate proofs and ambient conventions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uA vA uB vB uI

namespace CategoryTheory.Functor

section ComplexLift

variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
variable {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
variable (F : A ⥤ B) [F.PreservesZeroMorphisms] [F.Full] [F.Faithful]
variable {I : Type uI} {c : ComplexShape I}

/-- The source complex uses the actual preimages of the conjugated original differentials. -/
@[implicit_reducible]
def preimageHomologicalComplex (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) : HomologicalComplex A c where
  X := X
  d i j := F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)
  shape i j hij := by
    apply F.map_injective
    rw [Functor.map_preimage, K.shape i j hij]
    simp only [zero_comp, comp_zero, Functor.map_zero]
  d_comp_d' i j k _ _ := by
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, Functor.map_zero]
    calc
      ((e i).hom ≫ K.d i j ≫ (e j).inv) ≫ ((e j).hom ≫ K.d j k ≫ (e k).inv) =
          (e i).hom ≫ K.d i j ≫ ((e j).inv ≫ (e j).hom) ≫ K.d j k ≫ (e k).inv := by
            simp only [Category.assoc]
      _ = (e i).hom ≫ (K.d i j ≫ K.d j k) ≫ (e k).inv := by
        rw [Iso.inv_hom_id]
        simp only [Category.id_comp, Category.assoc]
      _ = 0 := by rw [K.d_comp_d]; simp

/-- Every lifted term is its original selected source object. -/
theorem preimageHomologicalComplex_X (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i : I) :
    (F.preimageHomologicalComplex K X e).X i = X i := rfl

/-- Every lifted differential is the preimage of the whole original conjugated differential. -/
theorem preimageHomologicalComplex_d (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i j : I) :
    (F.preimageHomologicalComplex K X e).d i j =
      F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv) := rfl

/-- Mapping the lifted differential returns the same original conjugated differential. -/
theorem map_preimageHomologicalComplex_d (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i j : I) :
    F.map ((F.preimageHomologicalComplex K X e).d i j) =
      (e i).hom ≫ K.d i j ≫ (e j).inv :=
  F.map_preimage _

/-- The component lifts and proved differential squares give the whole original complex iso. -/
def preimageHomologicalComplexIso (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) :
    (F.mapHomologicalComplex c).obj (F.preimageHomologicalComplex K X e) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents e (by
    intro i j _
    dsimp only [Functor.mapHomologicalComplex, preimageHomologicalComplex]
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The entire forward comparison retains the original component chart. -/
theorem preimageHomologicalComplexIso_hom_f (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i : I) :
    (F.preimageHomologicalComplexIso K X e).hom.f i = (e i).hom := rfl

/-- The entire inverse comparison retains the inverse original component chart. -/
theorem preimageHomologicalComplexIso_inv_f (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i : I) :
    (F.preimageHomologicalComplexIso K X e).inv.f i = (e i).inv := rfl

/-- The component lift retains the original finite support supplied for its source objects. -/
@[implicit_reducible]
def boundedPreimageOfComponents (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) : CochainComplex.Bounded A :=
  CochainComplex.Bounded.of A (F.preimageHomologicalComplex K X e) a b hX

/-- The bounded lift keeps each original selected source object. -/
theorem boundedPreimageOfComponents_X (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (i : ℤ) :
    (F.boundedPreimageOfComponents K X e a b hX).obj.X i = X i := rfl

/-- The bounded lift keeps the whole original preimage differential. -/
theorem boundedPreimageOfComponents_d (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (i j : ℤ) :
    (F.boundedPreimageOfComponents K X e a b hX).obj.d i j =
      F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv) := rfl

/-- The mapped bounded differential is the same actual conjugated target differential. -/
theorem boundedPreimageOfComponents_map_d (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj
      (F.boundedPreimageOfComponents K X e a b hX)).obj.d i j =
        (e i).hom ≫ K.d i j ≫ (e j).inv :=
  F.map_preimageHomologicalComplex_d K X e i j

/-- The original finite window remains a support witness for the whole source lift. -/
theorem boundedPreimageOfComponents_outside (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (j : ℤ)
    (hj : j < a ∨ b < j) :
    IsZero ((F.boundedPreimageOfComponents K X e a b hX).obj.X j) := hX j hj

/-- The internally lifted bounded source has the whole original raw complex comparison. -/
def boundedPreimageOfComponentsRawIso (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) :
    ((F.mapCochainComplexBounded).obj
      (F.boundedPreimageOfComponents K X e a b hX)).obj ≅ K :=
  F.preimageHomologicalComplexIso K X e

end ComplexLift

end CategoryTheory.Functor

namespace CochainComplex.BoundedCofinality

section Components

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B] [HasBinaryBiproducts B]
variable (F : A ⥤ B)

/-- Ordinary cofinality supplies a target complement and an actual source image object. -/
structure TargetComponent (X : B) where
  /-- The complement is an original target object. -/
  complement : B
  /-- The stabilized total is an original source object. -/
  total : A
  /-- Its original image is the target object plus the target complement. -/
  comparison : F.obj total ≅ X ⊞ complement

/-- Strict cofinality supplies a source complement and an actual source image object. -/
structure SourceComponent (X : B) where
  /-- The complement is an original source object. -/
  complement : A
  /-- The stabilized total is an original source object. -/
  total : A
  /-- Its original image uses the same functor image of the source complement. -/
  comparison : F.obj total ≅ X ⊞ F.obj complement

/-- The ordinary component data is chosen from the actual target complement condition. -/
def chosenTargetComponent
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y)) (X : B) : TargetComponent F X :=
  Classical.choice (show Nonempty (TargetComponent F X) from by
    obtain ⟨Y, Z, ⟨e⟩⟩ := hcofinal X
    exact ⟨⟨Y, Z, e⟩⟩)

/-- The strict component data is chosen from the actual source complement condition. -/
def chosenSourceComponent
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y)) (X : B) : SourceComponent F X :=
  Classical.choice (show Nonempty (SourceComponent F X) from by
    obtain ⟨Y, Z, ⟨e⟩⟩ := hcofinal X
    exact ⟨⟨Y, Z, e⟩⟩)

end Components

section ZeroDifferential

variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- The original cochain object with a prescribed family and the zero differential in every pair. -/
def zeroDifferentialComplex (X : ℤ → A) : CochainComplex A ℤ where
  X := X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- The zero-differential complex retains each prescribed original object. -/
theorem zeroDifferentialComplex_X (X : ℤ → A) (i : ℤ) :
    (zeroDifferentialComplex X).X i = X i := rfl

/-- The whole original differential of the complement is zero. -/
theorem zeroDifferentialComplex_d (X : ℤ → A) (i j : ℤ) :
    (zeroDifferentialComplex X).d i j = 0 := rfl

end ZeroDifferential

section Windows

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasBinaryBiproducts B]
variable (F : A ⥤ B)

/-- Original component lifts produce the whole original bounded biproduct comparison. -/
def boundedBiprodComparison [F.Additive] [F.Full] [F.Faithful]
    (K L : CochainComplex.Bounded B) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ (K.obj ⊞ L.obj).X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) :
    (F.mapCochainComplexBounded).obj
      (F.boundedPreimageOfComponents (K.obj ⊞ L.obj) X e a b hX) ≅ K ⊞ L := by
  letI : PreservesBinaryBiproduct K L (CochainComplex.Bounded.ι B) :=
    preservesBinaryBiproduct_of_preservesBiproduct (CochainComplex.Bounded.ι B) K L
  exact (CochainComplex.Bounded.fullyFaithfulι B).preimageIso
    ((F.boundedPreimageOfComponentsRawIso (K.obj ⊞ L.obj) X e a b hX).trans
      ((CochainComplex.Bounded.ι B).mapBiprod K L).symm)

omit [Preadditive A] [HasZeroObject A] in
/-- The ordinary complement uses the chosen original target object only inside the same window. -/
@[implicit_reducible]
def ordinaryComplementX
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : B :=
  if a ≤ j ∧ j ≤ b then
    (chosenTargetComponent F hcofinal (K.obj.X j)).complement else 0

omit [Preadditive A] [HasZeroObject B] in
/-- The ordinary source total uses an original source object, and the original zero outside. -/
@[implicit_reducible]
def ordinarySourceX
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : A :=
  if a ≤ j ∧ j ≤ b then
    (chosenTargetComponent F hcofinal (K.obj.X j)).total else 0

omit [Preadditive A] [HasZeroObject A] in
/-- The target complement is bounded in the original window and has zero differential. -/
@[implicit_reducible]
def ordinaryComplement
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ) : CochainComplex.Bounded B :=
  CochainComplex.Bounded.of B
    (zeroDifferentialComplex (ordinaryComplementX F hcofinal K a b)) a b (by
      intro j hj
      have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
      simp only [zeroDifferentialComplex_X, ordinaryComplementX,
        ite_eq_right hn]
      exact isZero_zero B)

omit [Preadditive A] [HasZeroObject A] in
/-- The whole original target-complement differential is zero in every pair of degrees. -/
theorem ordinaryComplement_d
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b i j : ℤ) :
    (ordinaryComplement F hcofinal K a b).obj.d i j = 0 := rfl

omit [Preadditive A] [HasZeroObject B] in
/-- The ordinary source objects have the same original support, with actual zero objects outside. -/
theorem ordinarySourceX_outside
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) (hj : j < a ∨ b < j) :
    IsZero (ordinarySourceX F hcofinal K a b j) := by
  have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
  simp only [ordinarySourceX, ite_eq_right hn]
  exact isZero_zero A

/-- Actual ordinary complements and original zero charts give every raw target component iso. -/
def ordinaryComponentIso [F.Additive]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ) :
    F.obj (ordinarySourceX F hcofinal K a b j) ≅
      (K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj).X j := by
  by_cases hj : a ≤ j ∧ j ≤ b
  · simp only [ordinarySourceX, ite_eq_left hj]
    exact (chosenTargetComponent F hcofinal (K.obj.X j)).comparison.trans
      (by
        simpa only [ordinaryComplement, CochainComplex.Bounded.of_obj,
          zeroDifferentialComplex_X, ordinaryComplementX, ite_eq_left hj] using
          (HomologicalComplex.biprodXIso K.obj
            (ordinaryComplement F hcofinal K a b).obj j).symm)
  · simp only [ordinarySourceX, ite_eq_right hj]
    have hOutside : j < a ∨ b < j := by simpa only [not_and_or, not_le] using hj
    have hC : IsZero ((ordinaryComplement F hcofinal K a b).obj.X j) := by
      simp only [ordinaryComplement, CochainComplex.Bounded.of_obj,
        zeroDifferentialComplex_X, ordinaryComplementX, ite_eq_right hj]
      exact isZero_zero B
    have hT : IsZero ((K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj).X j) :=
      ((biprod_isZero_iff _ _).mpr ⟨hK j hOutside, hC⟩).of_iso
        (HomologicalComplex.biprodXIso K.obj
          (ordinaryComplement F hcofinal K a b).obj j)
    exact F.mapZeroObject.trans hT.isoZero.symm

/-- The whole ordinary stabilized complex is lifted through the original functor and support. -/
@[implicit_reducible]
def ordinarySourceLift [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) : CochainComplex.Bounded A :=
  F.boundedPreimageOfComponents (K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj)
    (ordinarySourceX F hcofinal K a b) (ordinaryComponentIso F hcofinal K a b hK) a b
    (ordinarySourceX_outside F hcofinal K a b)

/-- The actual mapped source lift is the original bounded target plus its target complement. -/
def ordinaryComparison [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) :
    (F.mapCochainComplexBounded).obj (ordinarySourceLift F hcofinal K a b hK) ≅
      K ⊞ ordinaryComplement F hcofinal K a b :=
  boundedBiprodComparison F K (ordinaryComplement F hcofinal K a b)
    (ordinarySourceX F hcofinal K a b) (ordinaryComponentIso F hcofinal K a b hK) a b
    (ordinarySourceX_outside F hcofinal K a b)

/-- The actual mapped ordinary source differential retains the full original biproduct chart. -/
theorem ordinarySourceLift_map_d [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj (ordinarySourceLift F hcofinal K a b hK)).obj.d i j =
      (ordinaryComponentIso F hcofinal K a b hK i).hom ≫
        (K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj).d i j ≫
          (ordinaryComponentIso F hcofinal K a b hK j).inv :=
  F.boundedPreimageOfComponents_map_d _ _ _ a b _ i j

/-- The whole ordinary source lift remains zero outside the original target window. -/
theorem ordinarySourceLift_outside [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ)
    (hj : j < a ∨ b < j) : IsZero ((ordinarySourceLift F hcofinal K a b hK).obj.X j) :=
  ordinarySourceX_outside F hcofinal K a b j hj

/-- Ordinary object cofinality induces ordinary cofinality of the original bounded functor. -/
theorem ordinaryCofinal [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y)) :
    ∀ K : CochainComplex.Bounded B, ∃ L : CochainComplex.Bounded B,
      (F.mapCochainComplexBounded).essImage (K ⊞ L) := by
  intro K
  obtain ⟨a, b, hK⟩ := K.property
  exact ⟨ordinaryComplement F hcofinal K a b, ordinarySourceLift F hcofinal K a b hK,
    ⟨ordinaryComparison F hcofinal K a b hK⟩⟩

omit [Preadditive A] [HasZeroObject B] in
/-- The strict complement is an actual source object inside the original finite window. -/
@[implicit_reducible]
def strictComplementX
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : A :=
  if a ≤ j ∧ j ≤ b then
    (chosenSourceComponent F hcofinal (K.obj.X j)).complement else 0

omit [Preadditive A] [HasZeroObject B] in
/-- The strict total is an actual source object, with the original source zero outside. -/
@[implicit_reducible]
def strictSourceX
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : A :=
  if a ≤ j ∧ j ≤ b then
    (chosenSourceComponent F hcofinal (K.obj.X j)).total else 0

omit [HasZeroObject B] in
/-- The strict complement is the original source zero-differential complex in the same window. -/
@[implicit_reducible]
def strictComplement
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ) : CochainComplex.Bounded A :=
  CochainComplex.Bounded.of A
    (zeroDifferentialComplex (strictComplementX F hcofinal K a b)) a b (by
      intro j hj
      have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
      simp only [zeroDifferentialComplex_X, strictComplementX, ite_eq_right hn]
      exact isZero_zero A)

omit [HasZeroObject B] in
/-- The strict source complement has the original zero differential in every pair of degrees. -/
theorem strictComplement_d
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b i j : ℤ) :
    (strictComplement F hcofinal K a b).obj.d i j = 0 := rfl

omit [HasZeroObject B] in
/-- The actual source complement remains zero outside the original target window. -/
theorem strictComplement_outside
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) (hj : j < a ∨ b < j) :
    IsZero ((strictComplement F hcofinal K a b).obj.X j) := by
  have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
  simp only [strictComplement, CochainComplex.Bounded.of_obj,
    zeroDifferentialComplex_X, strictComplementX, ite_eq_right hn]
  exact isZero_zero A

omit [Preadditive A] [HasZeroObject B] in
/-- The strict source total remains the actual source zero outside the same finite window. -/
theorem strictSourceX_outside
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) (hj : j < a ∨ b < j) :
    IsZero (strictSourceX F hcofinal K a b j) := by
  have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
  simp only [strictSourceX, ite_eq_right hn]
  exact isZero_zero A

/-- Original strict component complements retain their source images and actual zero charts. -/
def strictComponentIso [F.Additive]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ) :
    F.obj (strictSourceX F hcofinal K a b j) ≅
      (K.obj ⊞ ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj).X j := by
  by_cases hj : a ≤ j ∧ j ≤ b
  · simp only [strictSourceX, ite_eq_left hj]
    exact (chosenSourceComponent F hcofinal (K.obj.X j)).comparison.trans
      (by
        simpa only [Functor.mapCochainComplexBounded_obj_X, strictComplement,
          CochainComplex.Bounded.of_obj, zeroDifferentialComplex_X,
          strictComplementX, ite_eq_left hj] using
          (HomologicalComplex.biprodXIso K.obj
            ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj j).symm)
  · simp only [strictSourceX, ite_eq_right hj]
    have hOutside : j < a ∨ b < j := by simpa only [not_and_or, not_le] using hj
    have hC : IsZero
        (((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj.X j) :=
      F.map_isZero (strictComplement_outside F hcofinal K a b j hOutside)
    have hT : IsZero
        ((K.obj ⊞ ((F.mapCochainComplexBounded).obj
          (strictComplement F hcofinal K a b)).obj).X j) :=
      ((biprod_isZero_iff _ _).mpr ⟨hK j hOutside, hC⟩).of_iso
        (HomologicalComplex.biprodXIso K.obj
          ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj j)
    exact F.mapZeroObject.trans hT.isoZero.symm

/-- The whole strict stabilized complex is lifted through the original functor and same support. -/
@[implicit_reducible]
def strictSourceLift [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) : CochainComplex.Bounded A :=
  F.boundedPreimageOfComponents
    (K.obj ⊞ ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj)
    (strictSourceX F hcofinal K a b) (strictComponentIso F hcofinal K a b hK) a b
    (strictSourceX_outside F hcofinal K a b)

/-- The original bounded comparison has the actual source-complement image as its second summand. -/
def strictComparison [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) :
    (F.mapCochainComplexBounded).obj (strictSourceLift F hcofinal K a b hK) ≅
      K ⊞ (F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b) :=
  boundedBiprodComparison F K ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b))
    (strictSourceX F hcofinal K a b) (strictComponentIso F hcofinal K a b hK) a b
    (strictSourceX_outside F hcofinal K a b)

/-- The mapped strict source differential retains the whole original raw biproduct differential. -/
theorem strictSourceLift_map_d [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj (strictSourceLift F hcofinal K a b hK)).obj.d i j =
      (strictComponentIso F hcofinal K a b hK i).hom ≫
        (K.obj ⊞ ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj).d i j ≫
          (strictComponentIso F hcofinal K a b hK j).inv :=
  F.boundedPreimageOfComponents_map_d _ _ _ a b _ i j

/-- The whole strict source lift remains zero outside the same original finite window. -/
theorem strictSourceLift_outside [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ)
    (hj : j < a ∨ b < j) : IsZero ((strictSourceLift F hcofinal K a b hK).obj.X j) :=
  strictSourceX_outside F hcofinal K a b j hj

/-- Strict object cofinality induces source-complement cofinality of the original bounded map. -/
theorem strictCofinal [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y)) :
    ∀ K : CochainComplex.Bounded B, ∃ L : CochainComplex.Bounded A,
      (F.mapCochainComplexBounded).essImage (K ⊞ (F.mapCochainComplexBounded).obj L) := by
  intro K
  obtain ⟨a, b, hK⟩ := K.property
  exact ⟨strictComplement F hcofinal K a b, strictSourceLift F hcofinal K a b hK,
    ⟨strictComparison F hcofinal K a b hK⟩⟩

end Windows

end CochainComplex.BoundedCofinality

end

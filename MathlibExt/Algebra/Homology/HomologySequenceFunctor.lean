/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ExactSequence
public import MathlibExt.CategoryTheory.ComposableArrows.Edge
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import MathlibExt.Algebra.Homology.ShortComplex.ShortExactSequences

/-!
# Functorial exact six-term homology sequences

This file provides functoriality of short exact sequences and of the six-term homology
exact sequences associated to short exact sequences of homological complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'


namespace HomologicalComplex.HomologySequence

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- The connecting morphisms of short exact complexes form a natural
transformation from third-term homology in degree `i` to first-term homology
in the adjacent degree `j`. -/
noncomputable def δNatTrans (i j : ι) (hij : c.Rel i j) :
    (CategoryTheory.ShortComplex.isShortExact (HomologicalComplex C c)).ι ⋙
          CategoryTheory.ShortComplex.π₃ ⋙
        HomologicalComplex.homologyFunctor C c i ⟶
      (CategoryTheory.ShortComplex.isShortExact (HomologicalComplex C c)).ι ⋙
          CategoryTheory.ShortComplex.π₁ ⋙
        HomologicalComplex.homologyFunctor C c j where
  app S := S.property.δ i j hij
  naturality S T f :=
    (HomologicalComplex.HomologySequence.δ_naturality
      f.hom S.property T.property i j hij).symm

@[simp]
lemma δNatTrans_app (i j : ι) (hij : c.Rel i j)
    (S : CategoryTheory.ShortComplex.ShortExactSequences
      (HomologicalComplex C c)) :
    (δNatTrans (C := C) (c := c) i j hij).app S =
      S.property.δ i j hij :=
  rfl

/-- The exact six-term homology sequence functor attached to a short exact sequence of
    complexes. -/
noncomputable def exactSequenceFunctor (i j : ι) (hij : c.Rel i j) :
    CategoryTheory.ShortComplex.ShortExactSequences (HomologicalComplex C c) ⥤
      ComposableArrows.ExactSequences C 5 where
  obj S := ⟨composableArrows₅ S.property i j hij, composableArrows₅_exact S.property i j hij⟩
  map {S T} f :=
    ⟨mapComposableArrows₅ f.hom S.property T.property i j hij⟩
  map_id S := by
    ext1
    apply ComposableArrows.hom_ext₅
    · simp [HomologicalComplex.homologyMap_id]
    · simp [HomologicalComplex.homologyMap_id]
    · simp [HomologicalComplex.homologyMap_id]
    · simp [HomologicalComplex.homologyMap_id]
    · simp [HomologicalComplex.homologyMap_id]
    · simp [HomologicalComplex.homologyMap_id]
  map_comp {S T U} f g := by
    ext1
    apply ComposableArrows.hom_ext₅
    · simp [HomologicalComplex.homologyMap_comp]; rfl
    · simp [HomologicalComplex.homologyMap_comp]; rfl
    · simp [HomologicalComplex.homologyMap_comp]; rfl
    · simp [HomologicalComplex.homologyMap_comp]; rfl
    · simp [HomologicalComplex.homologyMap_comp]; rfl
    · simp [HomologicalComplex.homologyMap_comp]; rfl

@[simp]
lemma exactSequenceFunctor_obj_obj (i j : ι) (hij : c.Rel i j)
    (S : CategoryTheory.ShortComplex.ShortExactSequences (HomologicalComplex C c)) :
    ((exactSequenceFunctor (C := C) (c := c) i j hij).obj S).obj =
      composableArrows₅ S.property i j hij :=
  rfl

@[simp]
lemma exactSequenceFunctor_map_hom (i j : ι) (hij : c.Rel i j)
    {S T : CategoryTheory.ShortComplex.ShortExactSequences (HomologicalComplex C c)}
    (f : S ⟶ T) :
    ((exactSequenceFunctor (C := C) (c := c) i j hij).map f).hom =
      mapComposableArrows₅ f.hom S.property T.property i j hij :=
  rfl

/-- The exact six-term homology sequence of a pointwise short exact family. -/
noncomputable def exactSequenceFunctorOfFamily
    {X : Type*} [Category X]
    (F : X ⥤ ShortComplex (HomologicalComplex C c))
    (hF : ∀ x : X, (F.obj x).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    X ⥤ ComposableArrows.ExactSequences C 5 :=
  CategoryTheory.ShortComplex.familyFunctor F hF ⋙
    exactSequenceFunctor i j hij

@[simp]
lemma exactSequenceFunctorOfFamily_obj_obj
    {X : Type*} [Category X]
    (F : X ⥤ ShortComplex (HomologicalComplex C c))
    (hF : ∀ x : X, (F.obj x).ShortExact)
    (i j : ι) (hij : c.Rel i j) (x : X) :
    ((exactSequenceFunctorOfFamily F hF i j hij).obj x).obj =
      composableArrows₅ (hF x) i j hij :=
  rfl

/-- The connecting natural transformation of a pointwise short exact family. -/
noncomputable def δNatTransOfFamily
    {X : Type*} [Category X]
    (F : X ⥤ ShortComplex (HomologicalComplex C c))
    (hF : ∀ x : X, (F.obj x).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    F ⋙ CategoryTheory.ShortComplex.π₃ ⋙
          HomologicalComplex.homologyFunctor C c i ⟶
      F ⋙ CategoryTheory.ShortComplex.π₁ ⋙
          HomologicalComplex.homologyFunctor C c j where
  app x := (hF x).δ i j hij
  naturality x y f :=
    (HomologicalComplex.HomologySequence.δ_naturality
      (F.map f) (hF x) (hF y) i j hij).symm

@[simp]
lemma δNatTransOfFamily_app
    {X : Type*} [Category X]
    (F : X ⥤ ShortComplex (HomologicalComplex C c))
    (hF : ∀ x : X, (F.obj x).ShortExact)
    (i j : ι) (hij : c.Rel i j) (x : X) :
    (δNatTransOfFamily F hF i j hij).app x = (hF x).δ i j hij :=
  rfl

@[simp]
lemma δNatTransOfFamily_app_eq_exactSequence_edge
    {X : Type*} [Category X]
    (F : X ⥤ ShortComplex (HomologicalComplex C c))
    (hF : ∀ x : X, (F.obj x).ShortExact)
    (i j : ι) (hij : c.Rel i j) (x : X) :
    (δNatTransOfFamily F hF i j hij).app x =
      ((exactSequenceFunctorOfFamily F hF i j hij).obj x).obj.map' 2 3 :=
  rfl

/-- Apply a complex-valued bifunctor to a short exact sequence, naturally in both variables. -/
noncomputable def mapShortExactSequenceBifunctor
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact → (S.map (F.flip.obj x)).ShortExact) :
    ShortComplex.ShortExactSequences C ⥤
      (X ⥤ ShortComplex.ShortExactSequences (HomologicalComplex D c)) where
  obj S :=
    { obj := fun x => ⟨S.obj.map (F.flip.obj x), hF x S.obj S.property⟩
      map := fun f => ⟨S.obj.mapNatTrans (F.flip.map f)⟩
      map_id := fun x => by
        apply ObjectProperty.hom_ext
        have h : F.flip.map (𝟙 x) = 𝟙 (F.flip.obj x) := F.flip.map_id x
        rw [h]
        rfl
      map_comp := fun f g => by
        apply ObjectProperty.hom_ext
        have h : F.flip.map (f ≫ g) = F.flip.map f ≫ F.flip.map g := F.flip.map_comp f g
        rw [h]
        rfl }
  map φ :=
    { app := fun x => ⟨(F.flip.obj x).mapShortComplex.map φ.hom⟩
      naturality := fun x y f => by
        apply ObjectProperty.hom_ext
        apply ShortComplex.hom_ext
        · exact (F.map φ.hom.τ₁).naturality f
        · exact (F.map φ.hom.τ₂).naturality f
        · exact (F.map φ.hom.τ₃).naturality f }
  map_id S := by
    ext x : 2
    apply ObjectProperty.hom_ext
    apply ShortComplex.hom_ext
    · simp [ShortComplex.map, Functor.mapShortComplex]
    · simp [ShortComplex.map, Functor.mapShortComplex]
    · simp [ShortComplex.map, Functor.mapShortComplex]
  map_comp φ ψ := by
    ext x : 2
    apply ObjectProperty.hom_ext
    apply ShortComplex.hom_ext
    · simp [ShortComplex.map, Functor.mapShortComplex]
    · simp [ShortComplex.map, Functor.mapShortComplex]
    · simp [ShortComplex.map, Functor.mapShortComplex]

/-- The functorial exact six-term homology sequence of a complex-valued bifunctor. -/
noncomputable def exactSequenceBifunctor
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact → (S.map (F.flip.obj x)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    ShortComplex.ShortExactSequences C ⥤ (X ⥤ ComposableArrows.ExactSequences D 5) :=
  mapShortExactSequenceBifunctor F hF ⋙
    (CategoryTheory.Functor.whiskeringRight X
      (ShortComplex.ShortExactSequences (HomologicalComplex D c))
      (ComposableArrows.ExactSequences D 5)).obj (exactSequenceFunctor i j hij)

/-- The connecting morphism extracted from a bifunctorial family of short
exact homological complexes. It is jointly natural in the short exact input
and in the second parameter. -/
noncomputable def δBifunctor
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact →
      (S.map (F.flip.obj x)).ShortExact)
    (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.isShortExact C).ι ⋙ ShortComplex.π₃ ⋙ F ⋙
          (CategoryTheory.Functor.whiskeringRight X
            (HomologicalComplex D c) D).obj
              (HomologicalComplex.homologyFunctor D c i) ⟶
      (ShortComplex.isShortExact C).ι ⋙ ShortComplex.π₁ ⋙ F ⋙
          (CategoryTheory.Functor.whiskeringRight X
            (HomologicalComplex D c) D).obj
              (HomologicalComplex.homologyFunctor D c j) where
  app S :=
    { app := fun x => (hF x S.obj S.property).δ i j hij
      naturality := fun x y f =>
        (HomologicalComplex.HomologySequence.δ_naturality
          (S.obj.mapNatTrans (F.flip.map f))
          (hF x S.obj S.property) (hF y S.obj S.property) i j hij).symm }
  naturality S T f := by
    ext x
    exact (HomologicalComplex.HomologySequence.δ_naturality
      ((F.flip.obj x).mapShortComplex.map f.hom)
      (hF x S.obj S.property) (hF x T.obj T.property) i j hij).symm

@[simp]
lemma δBifunctor_app_app
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact →
      (S.map (F.flip.obj x)).ShortExact)
    (i j : ι) (hij : c.Rel i j)
    (S : ShortComplex.ShortExactSequences C) (x : X) :
    ((δBifunctor F hF i j hij).app S).app x =
      (hF x S.obj S.property).δ i j hij :=
  rfl

lemma δBifunctor_app_app_eq_exactSequence_edge
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact →
      (S.map (F.flip.obj x)).ShortExact)
    (i j : ι) (hij : c.Rel i j)
    (S : ShortComplex.ShortExactSequences C) (x : X) :
    ((δBifunctor F hF i j hij).app S).app x =
      (((exactSequenceBifunctor F hF i j hij).obj S).obj x).obj.map' 2 3 :=
  rfl

/-- Naturality of the bifunctorial connecting morphism in the short exact
input, stated directly in terms of homology maps. -/
@[reassoc]
lemma δBifunctor_naturality_first
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact →
      (S.map (F.flip.obj x)).ShortExact)
    (i j : ι) (hij : c.Rel i j)
    {S T : ShortComplex.ShortExactSequences C} (f : S ⟶ T) (x : X) :
    HomologicalComplex.homologyMap
          ((F.flip.obj x).mapShortComplex.map f.hom).τ₃ i ≫
        (hF x T.obj T.property).δ i j hij =
      (hF x S.obj S.property).δ i j hij ≫
        HomologicalComplex.homologyMap
          ((F.flip.obj x).mapShortComplex.map f.hom).τ₁ j := by
  exact congr_app ((δBifunctor F hF i j hij).naturality f) x

/-- Naturality of the bifunctorial connecting morphism in the second
parameter, stated directly in terms of homology maps. -/
@[reassoc]
lemma δBifunctor_naturality_second
    {X : Type*} [Category X] {C : Type*} [Category C] [HasZeroMorphisms C]
    {D : Type*} [Category D] [Abelian D] {ι : Type*} {c : ComplexShape ι}
    (F : C ⥤ X ⥤ HomologicalComplex D c)
    [∀ (x : X), (F.flip.obj x).PreservesZeroMorphisms]
    (hF : ∀ (x : X) (S : ShortComplex C), S.ShortExact →
      (S.map (F.flip.obj x)).ShortExact)
    (i j : ι) (hij : c.Rel i j)
    (S : ShortComplex.ShortExactSequences C) {x y : X} (f : x ⟶ y) :
    HomologicalComplex.homologyMap
          (S.obj.mapNatTrans (F.flip.map f)).τ₃ i ≫
        (hF y S.obj S.property).δ i j hij =
      (hF x S.obj S.property).δ i j hij ≫
        HomologicalComplex.homologyMap
          (S.obj.mapNatTrans (F.flip.map f)).τ₁ j :=
  ((δBifunctor F hF i j hij).app S).naturality f

end HomologicalComplex.HomologySequence

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.WeightedClosedFormSpaces

/-!
# Natural weighted negative-cyclic diagrams and their fixed projections

Morphisms of graded mixed complexes form their actual category.
A negative-cyclic diagram has the actual product terms, differential
d+u epsilon and componentwise maps in every degree. Its cochain
projection is the actual first product coefficient and is natural.
Native shift and Dold--Kan then give the full underlying-form map
of diagrams, rather than an independently chosen map of form spaces.

Reference: PTVV arXiv:1111.3209v4 §1.1, Definitions 1.7--1.8.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedClosedFormSpaces
open MathlibExt.DGSource

universe u v w

variable {k : Type u} [CommRing k]

/-- The actual identity map of the graded mixed complex. -/
def mixedId (G : GradedMixed k) : MixedMap G G where
  map _ := 𝟙 _
  epsilon _ _ _ _ := by simp

/-- Composition retains every cochain map and its actual epsilon compatibility. -/
def mixedComp {G H K : GradedMixed k} (f : MixedMap G H) (g : MixedMap H K) :
    MixedMap G K where
  map p := f.map p ≫ g.map p
  epsilon p a b h := by
    simp only [HomologicalComplex.comp_f]
    rw [← Category.assoc, f.epsilon p a b h, Category.assoc, g.epsilon p a b h]
    simp only [Category.assoc]

/-- Extensionality of actual mixed maps. -/
theorem mixedMap_ext {G H : GradedMixed k} {f g : MixedMap G H}
    (h : ∀ p : ℤ, f.map p = g.map p) : f = g := by
  cases f with
  | mk f fe =>
    cases g with
    | mk g ge =>
      have hfg : f = g := funext h
      cases hfg
      rfl

/-- The native category of actual graded mixed cochain complexes. -/
instance : Category (GradedMixed k) where
  Hom G H := MixedMap G H
  id G := mixedId G
  comp f g := mixedComp f g
  id_comp _f := mixedMap_ext (fun _ => Category.id_comp _)
  comp_id _f := mixedMap_ext (fun _ => Category.comp_id _)
  assoc _f _g _h := mixedMap_ext (fun _ => Category.assoc _ _ _)

/-- The actual weight cochain functor. -/
def weightFunctor (p : ℤ) : GradedMixed k ⥤ CochainComplex (ModuleCat.{u} k) ℤ where
  obj G := G.weight p
  map f := f.map p

/-- A map of product terms commutes with the actual first-coefficient projection. -/
theorem termMap_first {G H : GradedMixed k} (f : MixedMap G H) (p n : ℤ) :
    termMap f p n ≫ firstProjection H p n =
      firstProjection G p n ≫ (f.map p).f n := by
  have raw : termMap f p n ≫ ModuleCat.ofHom (LinearMap.proj (R := k) (0 : ℕ)) =
      ModuleCat.ofHom (LinearMap.proj (R := k) (0 : ℕ)) ≫
        (f.map (p + (0 : ℤ))).f (n - 2 * (0 : ℤ)) := by
    ext x
    rfl
  have natural := eqToHom_naturality
    (fun z : ℤ × ℤ => (f.map z.1).f z.2)
    (show (p + (0 : ℤ), n - 2 * (0 : ℤ)) = (p, n) by simp)
  dsimp only [firstProjection]
  rw [← Category.assoc, raw, Category.assoc, natural, ← Category.assoc]

/-- Every component-normalized NC cochain map commutes with its actual projection. -/
theorem weightProjection_natural {G H : GradedMixed k} (f : MixedMap G H) (p : ℤ)
    (M : NegativeCyclicModel G p) (N : NegativeCyclicModel H p)
    (g : M.complex ⟶ N.complex) (h : IsNegativeCyclicMap f p M N g) :
    g ≫ weightProjection N = weightProjection M ≫ f.map p := by
  ext1 n
  change g.f n ≫ (N.termIso n).hom ≫ firstProjection H p n =
    (M.termIso n).hom ≫ firstProjection G p n ≫ (f.map p).f n
  rw [← Category.assoc, h n, Category.assoc, termMap_first]

/-- A genuine diagram of weighted NC complexes, fixed in all terms and maps. -/
structure NegativeCyclicDiagram {J : Type v} [Category.{w} J]
    (F : J ⥤ GradedMixed k) (p : ℤ) where
  complex : J ⥤ CochainComplex (ModuleCat.{u} k) ℤ
  termIso : ∀ (j : J) (n : ℤ), (complex.obj j).X n ≅ term (F.obj j) p n
  differential_eq : ∀ (j : J) (n : ℤ),
    (complex.obj j).d n (n + 1) ≫ (termIso j (n + 1)).hom =
      (termIso j n).hom ≫ differential (F.obj j) p n
  map_eq : ∀ (i j : J) (f : i ⟶ j) (n : ℤ),
    (complex.map f).f n ≫ (termIso j n).hom =
      (termIso i n).hom ≫ termMap (F.map f) p n

/-- Each object of the actual diagram supplies its fixed single-weight NC model. -/
def NegativeCyclicDiagram.toModel {J : Type v} [Category.{w} J]
    {F : J ⥤ GradedMixed k} {p : ℤ} (D : NegativeCyclicDiagram F p) (j : J) :
    NegativeCyclicModel (F.obj j) p where
  complex := D.complex.obj j
  termIso := D.termIso j
  differential_eq := D.differential_eq j

/-- The completed natural cochain projection of actual NC diagrams. -/
def NegativeCyclicDiagram.projection {J : Type v} [Category.{w} J]
    {F : J ⥤ GradedMixed k} {p : ℤ} (D : NegativeCyclicDiagram F p) :
    D.complex ⟶ F ⋙ weightFunctor p where
  app j := weightProjection (D.toModel j)
  naturality i j f := weightProjection_natural (F.map f) p
    (D.toModel i) (D.toModel j) (D.complex.map f) (D.map_eq i j f)

/-- The actual closed-form diagram with its source degree shift. -/
def NegativeCyclicDiagram.closedSpaces {J : Type v} [Category.{w} J]
    {F : J ⥤ GradedMixed k} (p : ℕ) (n : ℤ) (D : NegativeCyclicDiagram F (p : ℤ)) :
    J ⥤ SSet.{u} :=
  D.complex ⋙ CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} k) ℤ)
    (n - (p : ℤ)) ⋙ cochainToSSet k

/-- The corresponding ordinary p-form diagram of the same actual mixed object. -/
def formSpaces {J : Type v} [Category.{w} J] (F : J ⥤ GradedMixed k) (p : ℕ) (n : ℤ) :
    J ⥤ SSet.{u} :=
  F ⋙ weightFunctor (p : ℤ) ⋙
    CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} k) ℤ) (n - (p : ℤ)) ⋙
      cochainToSSet k

/-- Every form simplex has the actual underlying-form natural transformation. -/
def NegativeCyclicDiagram.underlying {J : Type v} [Category.{w} J]
    {F : J ⥤ GradedMixed k} (p : ℕ) (n : ℤ) (D : NegativeCyclicDiagram F (p : ℤ)) :
    D.closedSpaces p n ⟶ formSpaces F p n :=
  Functor.whiskerRight D.projection
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} k) ℤ) (n - (p : ℤ)) ⋙
      cochainToSSet k)

end MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModelContracts
public import MathlibExt.CategoryTheory.DGAlgebraCategoryModels
public import MathlibExt.CategoryTheory.PerfectDGModuleModels
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Actual cosimplicial resolutions and DG mapping spaces

The latching diagram contains all proper injective simplex maps. Its
colimit arrow is the native universal map to the actual degree term.
Reedy cofibrancy tests that arrow against actual trivial DG fibrations;
degreewise cofibrancy alone would permit a constant resolution and lose
the derived mapping space.

DG-algebra finite presentation uses actual cosimplicial mapping spaces
and their canonical filtered-colimit comparison. Finite type of a DG
category uses an actual quasi-equivalence of enhanced module categories
with a homotopically finitely presented DG algebra, as in the source.
Neither local geometricity nor a tangent identification is an input.

References: Toën--Vaquié, arXiv:math/0503269v5, §2.1,
Definition2.4(7) and §3.1, pp36--37; Hovey, Model Categories, §5.
Native DG Hom, opposite and module primitives retain their public
source attribution in DGSource and DGSourceMore.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.CosimplicialDGMappingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.Algebra.Homology.DGCyclicBarModels

universe u v w

/-- The proper injective maps into the specified simplex form its actual boundary index. -/
def latchingProperty (n : SimplexCategory) : ObjectProperty (Over n) :=
  fun a => a.left.len < n.len ∧ Function.Injective a.hom.toOrderHom

/-- The literal proper-face index, with all commuting triangles retained. -/
abbrev LatchingIndex (n : SimplexCategory) := (latchingProperty n).FullSubcategory

/-- The actual degree terms on all proper faces. -/
def latchingDiagram {C : Type v} [Category.{w} C]
    (D : SimplexCategory ⥤ C) (n : SimplexCategory) : LatchingIndex n ⥤ C :=
  (latchingProperty n).ι ⋙ Over.forget n ⋙ D

/-- The cocone is induced by the literal face maps into degree n. -/
def latchingCocone {C : Type v} [Category.{w} C]
    (D : SimplexCategory ⥤ C) (n : SimplexCategory) : Cocone (latchingDiagram D n) where
  pt := D.obj n
  ι.app a := D.map a.obj.hom
  ι.naturality a b f := by
    dsimp [latchingDiagram]
    rw [Category.comp_id, ← D.map_comp, Over.w]

/-- A source resolution is augmented, homotopically constant and Reedy cofibrant.
Latching colimits are actual universal cocones, not freely named boundary objects. -/
structure CosimplicialResolution {C : Type v} [Category.{w} C]
    (X : C) (weak cofibration : MorphismProperty C) where
  diagram : SimplexCategory ⥤ C
  augmentation : diagram ⟶ (Functor.const SimplexCategory).obj X
  augmentation_weak : ∀ n : SimplexCategory, weak (augmentation.app n)
  latching : ∀ n : SimplexCategory, ColimitCocone (latchingDiagram diagram n)
  reedy_cofibrant : ∀ n : SimplexCategory,
    cofibration ((latching n).isColimit.desc (latchingCocone diagram n))

variable (k : Type u) [CommRing k]

/-- The actual DG cofibration square-lifting test. -/
def dgCofibrations : MorphismProperty (DGCat k) :=
  fun C D f => ∀ (E F : DGCat k) (p : E ⟶ F), IsTrivialFibration p →
    ∀ (a : C ⟶ E) (b : D ⟶ F), a ≫ p = f ≫ b →
      ∃ l : D ⟶ E, f ≫ l = a ∧ l ≫ p = b

/-- The actual augmented DG frame used by the source mapping-space construction. -/
abbrev DGFrame (T : DGCat k) :=
  CosimplicialResolution T (quasiEquivalences k) (dgCofibrations k)

/-- A functorial DG frame keeps every actual augmented resolution and all simplex maps. -/
structure DGFrameSystem (k : Type u) [CommRing k] where
  frame : ∀ C : DGCat k, DGFrame k C
  map : ∀ {C D : DGCat k} (_f : C ⟶ D), (frame C).diagram ⟶ (frame D).diagram
  augmentation : ∀ {C D : DGCat k} (f : C ⟶ D),
    map f ≫ (frame D).augmentation =
      (frame C).augmentation ≫ (CategoryTheory.Functor.const SimplexCategory).map f
  map_id : ∀ C : DGCat k, map (𝟙 C) = 𝟙 (frame C).diagram
  map_comp : ∀ {C D E : DGCat k} (f : C ⟶ D) (g : D ⟶ E), map (f ≫ g) = map f ≫ map g

/-- DG-algebra weak equivalence is quasi-isomorphism of the actual cochain map. -/
def algebraWeakEquivalences : MorphismProperty (DGAlgebra k) :=
  fun _ _ f => QuasiIso f.hom

/-- Projective DG-algebra trivial fibrations retain every degreewise surjectivity test. -/
def IsDGAlgebraTrivialFibration {A B : DGAlgebra k} (f : A ⟶ B) : Prop :=
  QuasiIso f.hom ∧ ∀ n : ℤ, Function.Surjective (f.hom.f n)

/-- The actual DG-algebra cofibration lifting test. -/
def algebraCofibrations : MorphismProperty (DGAlgebra k) :=
  fun A B f => ∀ (C D : DGAlgebra k) (p : C ⟶ D), IsDGAlgebraTrivialFibration k p →
    ∀ (a : A ⟶ C) (b : B ⟶ D), a ≫ p = f ≫ b →
      ∃ l : B ⟶ C, f ≫ l = a ∧ l ≫ p = b

/-- The native augmented DG-algebra frame uses the same actual latching construction. -/
abbrev AlgebraFrame (A : DGAlgebra k) :=
  CosimplicialResolution A (algebraWeakEquivalences k) (algebraCofibrations k)

variable {k}

/-- Hom from every actual resolution term, with native precomposition simplicial maps. -/
def algebraMapping {A : DGAlgebra k} (R : AlgebraFrame k A) (B : DGAlgebra k) : SSet.{u} where
  obj n := R.diagram.obj n.unop ⟶ B
  map f := ↾fun g => R.diagram.map f.unop ≫ g
  map_id n := by ext g; simp
  map_comp f g := by ext h; simp [Category.assoc]

/-- Postcomposition is the actual algebra-induced map on every mapping simplex. -/
def algebraMappingMap {A B C : DGAlgebra k} (R : AlgebraFrame k A) (f : B ⟶ C) :
    algebraMapping R B ⟶ algebraMapping R C where
  app n := ↾fun g => g ≫ f
  naturality n m g := by ext a; simp [algebraMapping, Category.assoc]

/-- The actual target-algebra functor, retaining every scalar map. -/
def algebraMappingFunctor {A : DGAlgebra k} (R : AlgebraFrame k A) :
    DGAlgebra k ⥤ SSet.{u} where
  obj := algebraMapping R
  map := algebraMappingMap R
  map_id B := by ext n g; simp [algebraMappingMap]
  map_comp f g := by ext n h; simp [algebraMappingMap, Category.assoc]

/-- The canonical comparison to the mapping space of the actual filtered colimit. -/
def algebraFilteredComparison {A : DGAlgebra k} (R : AlgebraFrame k A)
    {J : Type u} [Category.{u} J] (D : J ⥤ DGAlgebra k) (c : ColimitCocone D) :
    colimit (D ⋙ algebraMappingFunctor R) ⟶ algebraMapping R c.cocone.pt :=
  colimit.desc _ ((algebraMappingFunctor R).mapCocone c.cocone)

/-- Homotopical finite presentation is the actual filtered derived-mapping test.
Filtered colimits of DG algebras preserve the underlying quasi-isomorphisms;
the source frame, rather than an ordinary set of maps, computes the derived Hom. -/
def IsHomotopicallyFinitelyPresented {A : DGAlgebra k} (R : AlgebraFrame k A) : Prop :=
  ∀ (J : Type u) [Category.{u} J] [IsFiltered J]
    (D : J ⥤ DGAlgebra k) (c : ColimitCocone D),
    MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.WeakEquivalence
      (algebraFilteredComparison R D c)

/-- The module-category comparison retains the actual enriched Hom complexes. -/
structure ModuleMoritaModel (C D : DGCat k) where
  functor : EnrichedFunctor (Cochains k) (DGDerivedModules k C) (DGDerivedModules k D)
  quasiEquivalence : functor.IsQuasiEquivalence

/-- Finite type has the source DG-algebra and module-category meaning.
The opposite coefficient category renders the source's left B-module convention. -/
def IsFiniteType (T : DGCat k) : Prop :=
  ∃ (B : DGAlgebra k) (R : AlgebraFrame k B),
    IsHomotopicallyFinitelyPresented R ∧
      Nonempty (ModuleMoritaModel T (oppositeCategory (algebraCategory B)))

end MathlibExt.CategoryTheory.CosimplicialDGMappingModels

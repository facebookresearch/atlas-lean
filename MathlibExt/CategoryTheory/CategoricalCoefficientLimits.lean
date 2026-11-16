/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

/-!
# Actual categorical cores and coefficient-diagram limits

The core consists of simplices all of whose edges extend to the native
walking-isomorphism nerve. Mapping objects are native internal Homs.
Categorical equivalence is tested by weak homotopy equivalence on their
cores against every inner-Kan target, so it retains categorical mapping
data rather than just the homotopy type of the whole nerve.

A categorical diagram model uses this equivalence, actual monomorphism
augmentations and the injective lifting property. Its limit is the
native limit of that specified diagram. Geometric coefficient diagrams
and their v-hyperdescent comparisons remain separate construction work.

References: Lurie, Higher Topos Theory, Section 2.2.5; Anschuetz--Mann,
arXiv:2403.01951v2, Theorem 1.1. These are original adapters to native
simplicial/coherent-isomorphism and internal-Hom constructions.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.CategoricalCoefficientLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalClosed
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

universe u v w

/-- Inner horn filling, with every universe and simplex index explicit. -/
def IsInnerKan (X : SSet.{u}) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 3)), 0 < i.val → i.val < n + 2 →
    ∀ a : (SSet.horn.{u} (n + 2) i).toSSet ⟶ X,
      ∃ b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 2)) ⟶ X,
        (SSet.horn.{u} (n + 2) i).ι ≫ b = a

/-- Every edge of a core simplex is the image of an actual coherent isomorphism. -/
def core (X : SSet.{u}) : X.Subcomplex where
  obj n := {s | ∀ e : SimplexCategory.mk 1 ⟶ n.unop,
    ∃ f : SSet.coherentIso.{u} ⟶ X,
      f.app (op (SimplexCategory.mk 1)) SSet.coherentIso.hom.edge = X.map e.op s}
  map {n m} g s hs e := by
    obtain ⟨f, hf⟩ := hs (e ≫ g.unop)
    refine ⟨f, ?_⟩
    simpa only [op_comp, X.map_comp, types_comp_apply, Quiver.Hom.op_unop] using hf

/-- Actual simplicial maps preserve the prescribed equivalence edges. -/
def coreMap {X Y : SSet.{u}} (f : X ⟶ Y) : (core X).toSSet ⟶ (core Y).toSSet where
  app n := ↾fun s ↦ ⟨f.app n s.val, by
    intro e
    obtain ⟨g, hg⟩ := s.property e
    refine ⟨g ≫ f, ?_⟩
    change f.app (op (SimplexCategory.mk 1))
      (g.app (op (SimplexCategory.mk 1)) SSet.coherentIso.hom.edge) =
        Y.map e.op (f.app n s.val)
    rw [hg]
    exact congrArg (fun q ↦ q s.val) (f.naturality e.op)⟩
  naturality n m g := by
    ext s
    apply Subtype.ext
    exact congrArg (fun q ↦ q s.val) (f.naturality g)

/-- The actual categorical mapping simplicial set. -/
abbrev mapping (X Z : SSet.{u}) : SSet.{u} := (ihom X).obj Z

/-- Native precomposition on every mapping simplex. -/
def mappingRestriction {X Y : SSet.{u}} (f : X ⟶ Y) (Z : SSet.{u}) :
    mapping Y Z ⟶ mapping X Z := (MonoidalClosed.pre f).app Z

/-- Categorical equivalence, tested on actual core mapping spaces into every inner-Kan target. -/
def IsCategoricalEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ Z : SSet.{u}, IsInnerKan Z → WeakEquivalence (coreMap (mappingRestriction f Z))

/-- The actual two endpoint inclusions into the coherent-isomorphism cylinder. -/
def equivalenceEndpoint (X : SSet.{u}) (right : Bool) : X ⟶ SSet.coherentIso.{u} ⊗ X :=
  (λ_ X).inv ≫ ((SSet.const (if right then SSet.coherentIso.x₁ else SSet.coherentIso.x₀)) ⊗ₘ 𝟙 X)

/-- A natural equivalence retains every simplex of the actual coherent-isomorphism cylinder. -/
def EquivalenceHomotopy {X Y : SSet.{u}} (f g : X ⟶ Y) : Prop :=
  ∃ H : SSet.coherentIso.{u} ⊗ X ⟶ Y,
    equivalenceEndpoint X false ≫ H = f ∧ equivalenceEndpoint X true ≫ H = g

/-- Actual injective categorical fibrancy of a specified diagram. -/
def IsInjectivelyFibrant {J : Type v} [Category.{w} J] (D : J ⥤ SSet.{max u v w}) : Prop :=
  (∀ j, IsInnerKan (D.obj j)) ∧
    ∀ (A B : J ⥤ SSet.{max u v w}) (i : A ⟶ B),
      (∀ j, Mono (i.app j) ∧ IsCategoricalEquivalence (i.app j)) →
      ∀ f : A ⟶ D, ∃ g : B ⟶ D, i ≫ g = f

/-- A native categorical diagram replacement, with its actual augmentation. -/
structure DiagramModel {J : Type v} [Category.{w} J] (D : J ⥤ SSet.{max u v w}) where
  diagram : J ⥤ SSet.{max u v w}
  augmentation : D ⟶ diagram
  mono : ∀ j, Mono (augmentation.app j)
  equivalence : ∀ j, IsCategoricalEquivalence (augmentation.app j)
  fibrant : IsInjectivelyFibrant.{u, v, w} diagram

/-- The actual categorical limit of the displayed replacement diagram. -/
abbrev categoricalLimit {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{max u v w}}
    (M : DiagramModel.{u, v, w} D) : SSet.{max u v w} := limit M.diagram

/-- The canonical comparison from the original native limit. -/
def limitComparison {J : Type v} [Category.{w} J] {D : J ⥤ SSet.{max u v w}}
    (M : DiagramModel.{u, v, w} D) : limit D ⟶ categoricalLimit.{u, v, w} M :=
  lim.map M.augmentation

/-- A coefficient comparison lifts through the actual categorical augmentations. -/
def comparisonLift {J : Type v} [Category.{w} J]
    {D E : J ⥤ SSet.{max u v w}} (f : D ⟶ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) :
    M.diagram ⟶ N.diagram :=
  Classical.choose (N.fibrant.2 D M.diagram M.augmentation
    (fun j ↦ ⟨M.mono j, M.equivalence j⟩) (f ≫ N.augmentation))

/-- Its entire augmentation square is the original coefficient comparison. -/
theorem comparisonLift_square {J : Type v} [Category.{w} J]
    {D E : J ⥤ SSet.{max u v w}} (f : D ⟶ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) :
    M.augmentation ≫ comparisonLift.{u, v, w} f M N = f ≫ N.augmentation :=
  Classical.choose_spec (N.fibrant.2 D M.diagram M.augmentation
    (fun j ↦ ⟨M.mono j, M.equivalence j⟩) (f ≫ N.augmentation))

/-- The actual global coefficient comparison is the native limit map of this lift. -/
def categoricalMap {J : Type v} [Category.{w} J]
    {D E : J ⥤ SSet.{max u v w}} (f : D ⟶ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) :
    categoricalLimit.{u, v, w} M ⟶ categoricalLimit.{u, v, w} N :=
  lim.map (comparisonLift.{u, v, w} f M N)

/-- Reindexing lifts through the actual categorical augmentations by injective fibrancy. -/
def restrictionLift {J K : Type v} [Category.{w} J] [Category.{w} K]
    {D : J ⥤ SSet.{max u v w}} {E : K ⥤ SSet.{max u v w}}
    (r : K ⥤ J) (e : r ⋙ D ≅ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) :
    r ⋙ M.diagram ⟶ N.diagram :=
  Classical.choose (N.fibrant.2 (r ⋙ D) (r ⋙ M.diagram)
    (Functor.whiskerLeft r M.augmentation)
    (fun k ↦ ⟨M.mono (r.obj k), M.equivalence (r.obj k)⟩)
    (e.hom ≫ N.augmentation))

/-- The chosen lift is normalized by the displayed native augmentation square. -/
theorem restrictionLift_square {J K : Type v} [Category.{w} J] [Category.{w} K]
    {D : J ⥤ SSet.{max u v w}} {E : K ⥤ SSet.{max u v w}}
    (r : K ⥤ J) (e : r ⋙ D ≅ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) :
    Functor.whiskerLeft r M.augmentation ≫ restrictionLift.{u, v, w} r e M N =
      e.hom ≫ N.augmentation :=
  Classical.choose_spec (N.fibrant.2 (r ⋙ D) (r ⋙ M.diagram)
    (Functor.whiskerLeft r M.augmentation)
    (fun k ↦ ⟨M.mono (r.obj k), M.equivalence (r.obj k)⟩)
    (e.hom ≫ N.augmentation))

/-- The actual source-limit cone after reindexing its native projections. -/
def restrictionCone {J K : Type v} [Category.{w} J] [Category.{w} K]
    {D : J ⥤ SSet.{max u v w}} {E : K ⥤ SSet.{max u v w}}
    (r : K ⥤ J) (e : r ⋙ D ≅ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) : Cone N.diagram :=
  (Cone.postcompose (restrictionLift.{u, v, w} r e M N)).obj
    ((limit.cone M.diagram).whisker r)

/-- The fixed native restriction map between the actual categorical limits. -/
def categoricalRestriction {J K : Type v} [Category.{w} J] [Category.{w} K]
    {D : J ⥤ SSet.{max u v w}} {E : K ⥤ SSet.{max u v w}}
    (r : K ⥤ J) (e : r ⋙ D ≅ E)
    (M : DiagramModel.{u, v, w} D) (N : DiagramModel.{u, v, w} E) :
    categoricalLimit.{u, v, w} M ⟶ categoricalLimit.{u, v, w} N :=
  limit.lift N.diagram (restrictionCone.{u, v, w} r e M N)

end MathlibExt.CategoryTheory.CategoricalCoefficientLimits

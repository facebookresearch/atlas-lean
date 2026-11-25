/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
public import MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
public import MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Global graded mixed de Rham and actual weighted closed-form limits

The affine system is fixed by actual simplicial Kähler forms on QA,
their native Moore normalization and every generator-normalized map.
Its pullback to all affine-family simplices is the graded mixed de Rham
diagram of the prestack. Weighted negative-cyclic diagrams retain the
actual product complexes and their natural cochain projections.

Global form spaces are the native limits of injectively fibrant space
diagrams over this actual family category. These are form spaces, so a
space homotopy limit is appropriate here. The value universe contains
both the family objects and their morphisms. The underlying-form map
is induced by the fixed NC projection and an actual lifting square.
It is not independently chosen.

References: PTVV arXiv:1111.3209v4 §1.1, Definitions 1.7--1.8;
Bousfield--Kan, Homotopy limits, Chapters X--XI.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

universe u v w

variable {k : Type u} [CommRing k]

/-- The coherent affine DR functor is fixed by the actual source models and all maps. -/
structure AffineDRSystem (Q : AlgebraReplacementFunctor k) where
  functor : SAlg k ⥤ GradedMixed k
  forms : ∀ A : SAlg k, SimplicialDRModel (Q.functor.obj A)
  model : ∀ A : SAlg k, AffineDRModel Q A (forms A)
  object_eq : ∀ A : SAlg k, (model A).graded = functor.obj A
  simplicial_map : ∀ (A B : SAlg k) (f : A ⟶ B),
    SimplicialDRMap (forms A) (forms B) (Q.functor.map f)
  map_model : ∀ (A B : SAlg k) (f : A ⟶ B),
    AffineDRMap (model A) (model B) f (simplicial_map A B f)
  map_eq : ∀ (A B : SAlg k) (f : A ⟶ B),
    HEq (functor.map f) ((map_model A B f).map)
  homotopy_invariant : ∀ (A B : SAlg k) (f : A ⟶ B),
    AlgebraWeakEquivalence f → ∀ p : ℤ, QuasiIso ((functor.map f).map p)

/-- The actual graded mixed DR diagram on every affine-family simplex of X. -/
def globalDR {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q) (X : Prestack k) :
    Families X ⥤ GradedMixed k := algebraProjection X ⋙ D.functor

/-- Sized injective fibrancy, with all index/value universes explicit. -/
def IsSpaceInjectivelyFibrant {J : Type v} [Category.{w} J]
    (D : J ⥤ SSet.{max u v w}) : Prop :=
  ∀ (A B : J ⥤ SSet.{max u v w}) (i : A ⟶ B),
    (∀ j, Mono (i.app j) ∧ WeakEquivalence (i.app j)) →
      ∀ f : A ⟶ D, ∃ g : B ⟶ D, i ≫ g = f

/-- A native sized diagram replacement is an actual trivial-monomorphism augmentation. -/
structure SpaceDiagramReplacement {J : Type v} [Category.{w} J]
    (D : J ⥤ SSet.{max u v w}) where
  diagram : J ⥤ SSet.{max u v w}
  map : D ⟶ diagram
  mono : ∀ j, Mono (map.app j)
  weak : ∀ j, WeakEquivalence (map.app j)
  fibrant : IsSpaceInjectivelyFibrant.{u, v, w} diagram
  kan : ∀ j, SSet.KanComplex (diagram.obj j)

/-- The actual closed-form diagram over every affine family, with native value lifting. -/
def closedDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
    Families X ⥤ SSet.{u + 1} :=
  algebraProjection X ⋙ NC.closedSpaces p n ⋙ liftSimplicial

/-- The actual underlying p-form diagram of the same graded mixed DR functor. -/
def ordinaryDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (X : Prestack k) : Families X ⥤ SSet.{u + 1} :=
  algebraProjection X ⋙ formSpaces D.functor p n ⋙ liftSimplicial

/-- The actual natural NC-to-form projection on every affine family simplex. -/
def underlyingDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
    closedDiagram D p n NC X ⟶ ordinaryDiagram D p n X :=
  Functor.whiskerRight (Functor.whiskerLeft (algebraProjection X) (NC.underlying p n))
    liftSimplicial

/-- Global form realization chooses actual replacements of these two fixed diagrams. -/
structure GlobalFormModel {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) where
  closed : SpaceDiagramReplacement.{u, u + 1, u} (closedDiagram D p n NC X)
  ordinary : SpaceDiagramReplacement.{u, u + 1, u} (ordinaryDiagram D p n X)

/-- The true global closed-form space retains the NC closing data in the full limit. -/
def globalClosedForms {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (M : GlobalFormModel D p n NC X) : SSet.{u + 1} := limit M.closed.diagram

/-- The actual ordinary global form space. -/
def globalForms {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (M : GlobalFormModel D p n NC X) : SSet.{u + 1} := limit M.ordinary.diagram

/-- The NC projection lifts through the actual trivial-cofibration augmentation. -/
def underlyingLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (M : GlobalFormModel D p n NC X) : M.closed.diagram ⟶ M.ordinary.diagram :=
  Classical.choose (M.ordinary.fibrant _ _ M.closed.map
    (fun j => ⟨M.closed.mono j, M.closed.weak j⟩)
    (underlyingDiagram D p n NC X ≫ M.ordinary.map))

/-- Its augmentation square is the fixed underlying-form natural transformation. -/
theorem underlyingLift_square {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (M : GlobalFormModel D p n NC X) :
    M.closed.map ≫ underlyingLift M = underlyingDiagram D p n NC X ≫ M.ordinary.map :=
  Classical.choose_spec (M.ordinary.fibrant _ _ M.closed.map
    (fun j => ⟨M.closed.mono j, M.closed.weak j⟩)
    (underlyingDiagram D p n NC X ≫ M.ordinary.map))

/-- The true global underlying-form map is the native map between those limits. -/
def globalUnderlyingForm {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (M : GlobalFormModel D p n NC X) : globalClosedForms M ⟶ globalForms M :=
  lim.map (underlyingLift M)

/-- A global closed form is an actual vertex in the closing-data space. -/
abbrev GlobalClosedForm {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (M : GlobalFormModel D p n NC X) :=
  (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶ globalClosedForms M

/-- Reindexing a global closed-form diagram retains every actual algebra/simplex map. -/
theorem closedDiagram_reindex {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicDiagram D.functor (p : ℤ))
    {X Y : Prestack k} (f : X ⟶ Y) :
    reindex f ⋙ closedDiagram D p n NC Y = closedDiagram D p n NC X := rfl

/-- The actual closed-form pullback lift is computed by the injective lifting property. -/
def closedPullbackLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X) :
    reindex f ⋙ MY.closed.diagram ⟶ MX.closed.diagram :=
  Classical.choose (MX.closed.fibrant _ _
    (Functor.whiskerLeft (reindex f) MY.closed.map)
    (fun j => ⟨MY.closed.mono ((reindex f).obj j), MY.closed.weak ((reindex f).obj j)⟩)
    MX.closed.map)

/-- `ℓ` extends the augmentation of `MX` along the reindexed augmentation of `MY`. Such lifts exist
by injective fibrancy (`closedPullbackLift` chooses one) but are not unique. -/
def IsClosedPullbackLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X)
    (ℓ : reindex f ⋙ MY.closed.diagram ⟶ MX.closed.diagram) : Prop :=
  Functor.whiskerLeft (reindex f) MY.closed.map ≫ ℓ = MX.closed.map

theorem closedPullbackLift_spec {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X) :
    IsClosedPullbackLift f MY MX (closedPullbackLift f MY MX) := by
  unfold IsClosedPullbackLift closedPullbackLift
  exact Classical.choose_spec (MX.closed.fibrant _ _
    (Functor.whiskerLeft (reindex f) MY.closed.map)
    (fun j => ⟨MY.closed.mono ((reindex f).obj j), MY.closed.weak ((reindex f).obj j)⟩)
    MX.closed.map)

/-- The full native cone for restriction to all X-families. -/
def restrictedClosedCone {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y) (MY : GlobalFormModel D p n NC Y) :
    Cone (reindex f ⋙ MY.closed.diagram) where
  pt := globalClosedForms MY
  π := Functor.whiskerLeft (reindex f) (limit.cone MY.closed.diagram).π

/-- Actual global pullback is the native limit map of the reindexed cone and the chosen lift
`closedPullbackLift` (`globalClosedPullbackOf` with that lift); it is canonical only after
inverting weak equivalences. -/
def globalClosedPullback {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X) :
    globalClosedForms MY ⟶ globalClosedForms MX :=
  limit.lift MX.closed.diagram
    ⟨globalClosedForms MY, (restrictedClosedCone f MY).π ≫ closedPullbackLift f MY MX⟩

/-- The global closed-form pullback defined by the lift `ℓ`. Different lifts agree after inverting
weak equivalences, and pullback is functorial there; these are requested in
`WantedExt.AlgebraicGeometry.DerivedPullbackFunctorialityWanted`. -/
def globalClosedPullbackOf {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X)
    (ℓ : reindex f ⋙ MY.closed.diagram ⟶ MX.closed.diagram) :
    globalClosedForms MY ⟶ globalClosedForms MX :=
  limit.lift MX.closed.diagram ⟨globalClosedForms MY, (restrictedClosedCone f MY).π ≫ ℓ⟩

theorem globalClosedPullback_eq_globalClosedPullbackOf {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {p : ℕ} {n : ℤ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X) :
    globalClosedPullback f MY MX =
      globalClosedPullbackOf f MY MX (closedPullbackLift f MY MX) := rfl

/-- The literal space weak-equivalence localization for affine normalization. -/
def spaceWeakEquivalences : MorphismProperty SSet.{u + 1} :=
  fun _ _ f => WeakEquivalence f

/-- The actual localization functor on these sized form spaces. -/
abbrev spaceQ : SSet.{u + 1} ⥤ (spaceWeakEquivalences.{u}).Localization :=
  (spaceWeakEquivalences.{u}).Q

/-- A closed-form affine comparison is the actual restriction at its canonical
affine family, normalized after inverting only space weak equivalences. -/
structure AffineClosedFormNormalization {Q : AlgebraReplacementFunctor k}
    (D : AffineDRSystem Q) (p : ℕ) (n : ℤ)
    (NC : NegativeCyclicDiagram D.functor (p : ℤ))
    (A : SAlg k) (X : Prestack k) (x : (X.obj A).obj (op (SimplexCategory.mk 0)))
    (M : GlobalFormModel D p n NC X) where
  map : globalClosedForms M ⟶ ((NC.closedSpaces p n) ⋙ liftSimplicial).obj A
  normalized : (spaceQ.{u}).map map ≫
      (spaceQ.{u}).map (M.closed.map.app (family X A (op (SimplexCategory.mk 0)) x)) =
    (spaceQ.{u}).map (limit.π M.closed.diagram (family X A (op (SimplexCategory.mk 0)) x))
  weak : WeakEquivalence map

end MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms

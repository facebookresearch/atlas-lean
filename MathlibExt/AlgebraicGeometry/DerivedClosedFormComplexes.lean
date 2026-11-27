/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of the larger-universe realization adapt:
`TauCeti/AlgebraicTopology/DoldKan/Cochain.lean` at
62bbc0596dc3539d488232e4e924a338548ea0a9.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/DoldKan/Cochain.lean
Modification: retain the native functors at the affine-family coefficient universe.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Actual global weighted negative-cyclic complexes and closing-data paths

Global complexes are native limits of injectively fibrant replacements
of the entire affine-family diagram. Module carriers are lifted to the
universe of that index; a large diagram is not silently forced into
small coefficient modules. The underlying form is the literal weighted
NC projection, lifted through its actual augmentation square.

The space realization uses native good truncation and Dold--Kan in that
same module universe. Isotropic homotopies are paths in the realization
of this actual closed-form space, retaining every NC closing coefficient.

References: PTVV arXiv:1111.3209v4, §1.1 and §2.2; Bousfield--Kan,
Chapters X--XI. The larger-universe realization adapts the completed
Tau Ceti CochainToSSet construction at revision
62bbc0596dc3539d488232e4e924a338548ea0a9 (Apache 2.0), credited in
DGSourceMore/CochainToSSet.lean; its native functors are retained.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicTopology
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- Actual coefficient modules in the universe containing all affine families. -/
abbrev GlobalComplex (k : Type u) [CommRing k] :=
  CochainComplex (ModuleCat.{u + 1} k) ℤ

/-- Native universe lifting retains coefficients and every linear map. -/
def liftModules (k : Type u) [CommRing k] : ModuleCat.{u} k ⥤ ModuleCat.{u + 1} k where
  obj V := ModuleCat.of k (ULift.{u + 1} V)
  map f := ModuleCat.ofHom
    { toFun := fun x => ULift.up (f x.down)
      map_add' x y := by apply ULift.ext; exact f.hom.map_add x.down y.down
      map_smul' a x := by apply ULift.ext; exact f.hom.map_smul a x.down }
  map_id V := rfl
  map_comp f g := rfl

instance liftModules_preservesZeroMorphisms (k : Type u) [CommRing k] :
    (liftModules k).PreservesZeroMorphisms where
  map_zero X Y := by ext x; rfl

/-- Lift all cochain terms and differentials using the native complex functor. -/
def liftComplex (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat.{u} k) ℤ ⥤ GlobalComplex k :=
  (liftModules k).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Good truncation/Dold--Kan with the actual larger coefficient universe. -/
def realize (k : Type u) [CommRing k] : GlobalComplex k ⥤ SSet.{u + 1} :=
  ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u + 1} k) ⋙
    Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u + 1} k))

/-- Native simplicial-module realization is Kan in the actual coefficient universe. -/
theorem realize_kan (K : GlobalComplex k) : SSet.KanComplex ((realize k).obj K) := by
  change SSet.KanComplex
    (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
      forget (ModuleCat.{u + 1} k))
  infer_instance

/-- The actual injective replacement of a complete affine-family cochain diagram. -/
structure ComplexDiagramReplacement {J : Type (u + 1)} [Category.{u} J]
    (D : J ⥤ GlobalComplex k) where
  diagram : J ⥤ GlobalComplex k
  map : D ⟶ diagram
  mono : ∀ j, Mono (map.app j)
  weak : ∀ j, QuasiIso (map.app j)
  fibrant : ∀ (A B : J ⥤ GlobalComplex k) (i : A ⟶ B),
    (∀ j, Mono (i.app j) ∧ QuasiIso (i.app j)) →
      ∀ f : A ⟶ diagram, ∃ g : B ⟶ diagram, i ≫ g = f

/-- The actual global NC diagram, with every component and scalar map lifted. -/
def ncDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
    Families X ⥤ GlobalComplex k :=
  algebraProjection X ⋙ NC.complex ⋙ liftComplex k

/-- The actual ordinary weight-p diagram of the same derived de Rham system. -/
def weightDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (X : Prestack k) : Families X ⥤ GlobalComplex k :=
  algebraProjection X ⋙ D.functor ⋙ weightFunctor (p : ℤ) ⋙ liftComplex k

/-- The native first-coefficient projection in the complete lifted diagram. -/
def projectionDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
    ncDiagram D p NC X ⟶ weightDiagram D p X :=
  Functor.whiskerRight (Functor.whiskerLeft (algebraProjection X) NC.projection) (liftComplex k)

/-- Global realization choices for the actual two fixed cochain diagrams. -/
structure GlobalNCModel {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (p : ℕ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) where
  closed : ComplexDiagramReplacement (ncDiagram D p NC X)
  ordinary : ComplexDiagramReplacement (weightDiagram D p X)

/-- The actual global negative-cyclic complex is the native replacement limit. -/
def ncComplex {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) : GlobalComplex k := limit G.closed.diagram

/-- The corresponding actual ordinary weight-p de Rham complex. -/
def weightComplex {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) : GlobalComplex k := limit G.ordinary.diagram

/-- The projection lift is chosen through its genuine injective lifting square. -/
def projectionLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) : G.closed.diagram ⟶ G.ordinary.diagram :=
  Classical.choose (G.ordinary.fibrant _ _ G.closed.map
    (fun j => ⟨G.closed.mono j, G.closed.weak j⟩)
    (projectionDiagram D p NC X ≫ G.ordinary.map))

/-- Its actual augmentation square is fixed by the NC first-coefficient map. -/
theorem projectionLift_square {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) :
    G.closed.map ≫ projectionLift G = projectionDiagram D p NC X ≫ G.ordinary.map :=
  Classical.choose_spec (G.ordinary.fibrant _ _ G.closed.map
    (fun j => ⟨G.closed.mono j, G.closed.weak j⟩)
    (projectionDiagram D p NC X ≫ G.ordinary.map))

/-- Native limit functoriality gives the actual underlying-form cochain map. -/
def projection {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) : ncComplex G ⟶ weightComplex G := limMap (projectionLift G)

/-- Source-normalized global p-form realization with degree n-p. -/
def closedSpace {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) (n : ℤ) : SSet.{u + 1} :=
  (realize k).obj ((ncComplex G)⟦n - (p : ℤ)⟧)

/-- A closed form is an actual closing-data vertex. -/
abbrev ClosedForm {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) (n : ℤ) := (closedSpace G n) _⦋0⦌

/-- The genuine zero closed form uses the zero of the native simplicial coefficient module. -/
def zeroForm {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)} {X : Prestack k}
    (G : GlobalNCModel D p NC X) (n : ℤ) : ClosedForm G n := by
  change ((Idempotents.DoldKan.Γ.obj
    (((ncComplex G)⟦n - (p : ℤ)⟧).truncLE' ComplexShape.embeddingDownNat)).obj (op ⦋0⦌))
  exact 0

/-- Actual NC pullback lift over the complete reindexed affine-family diagram. -/
def ncPullbackLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X) :
    reindex f ⋙ GY.closed.diagram ⟶ GX.closed.diagram :=
  Classical.choose (GX.closed.fibrant _ _
    (Functor.whiskerLeft (reindex f) GY.closed.map)
    (fun j => ⟨GY.closed.mono ((reindex f).obj j), GY.closed.weak ((reindex f).obj j)⟩)
    GX.closed.map)

/-- `ℓ` extends the augmentation of `GX` along the reindexed augmentation of `GY`. Such lifts exist
by injective fibrancy (`ncPullbackLift` chooses one) but are not unique. -/
def IsNCPullbackLift {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X)
    (ℓ : reindex f ⋙ GY.closed.diagram ⟶ GX.closed.diagram) : Prop :=
  Functor.whiskerLeft (reindex f) GY.closed.map ≫ ℓ = GX.closed.map

theorem ncPullbackLift_spec {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X) :
    IsNCPullbackLift f GY GX (ncPullbackLift f GY GX) := by
  unfold IsNCPullbackLift ncPullbackLift
  exact Classical.choose_spec (GX.closed.fibrant _ _
    (Functor.whiskerLeft (reindex f) GY.closed.map)
    (fun j => ⟨GY.closed.mono ((reindex f).obj j), GY.closed.weak ((reindex f).obj j)⟩)
    GX.closed.map)

/-- The global negative-cyclic (NC) pullback along `f` defined by a map `ℓ` from the replaced NC
diagram of `GY`, reindexed along `f`, to that of `GX`: the map of limits
`ncComplex GY ⟶ ncComplex GX` whose components are the limit projections of `GY` at the reindexed
families followed by `ℓ`. -/
def ncPullbackOf {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X)
    (ℓ : reindex f ⋙ GY.closed.diagram ⟶ GX.closed.diagram) : ncComplex GY ⟶ ncComplex GX :=
  limit.lift GX.closed.diagram
    ⟨ncComplex GY, Functor.whiskerLeft (reindex f) (limit.cone GY.closed.diagram).π ≫ ℓ⟩

/-- Native limit restriction and the chosen lift `ncPullbackLift` define global NC pullback
(`ncPullbackOf` with that lift). The lift is a choice; lifts need not be unique (see
`IsNCPullbackLift`). -/
def ncPullback {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X) :
    ncComplex GY ⟶ ncComplex GX :=
  limit.lift GX.closed.diagram
    ⟨ncComplex GY,
      Functor.whiskerLeft (reindex f) (limit.cone GY.closed.diagram).π ≫
        ncPullbackLift f GY GX⟩

theorem ncPullback_eq_ncPullbackOf {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X) :
    ncPullback f GY GX = ncPullbackOf f GY GX (ncPullbackLift f GY GX) := rfl

/-- Source-normalized pullback acts on all closing-data simplices by the actual cochain map. -/
def closedPullback {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X) (n : ℤ) :
    closedSpace GY n ⟶ closedSpace GX n :=
  (realize k).map ((shiftFunctor (GlobalComplex k) (n - (p : ℤ))).map (ncPullback f GY GX))

/-- Actual cochain realization maps preserve the distinguished module zero. -/
theorem realize_map_zero {F P : GlobalComplex k} (f : F ⟶ P) :
    ((realize k).map f).app (op ⦋0⦌)
      (0 : (Idempotents.DoldKan.Γ.obj (F.truncLE' ComplexShape.embeddingDownNat)) _⦋0⦌) =
      (0 : (Idempotents.DoldKan.Γ.obj (P.truncLE' ComplexShape.embeddingDownNat)) _⦋0⦌) := by
  change ((Idempotents.DoldKan.Γ.map
    (HomologicalComplex.truncLE'Map f ComplexShape.embeddingDownNat)).app (op ⦋0⦌)).hom 0 = 0
  exact map_zero _

/-- Global pullback fixes the genuine zero closing-data vertex. -/
theorem closedPullback_zero {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {p : ℕ} {NC : NegativeCyclicDiagram D.functor (p : ℤ)}
    {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X) (n : ℤ) :
    (closedPullback f GY GX n).app (op ⦋0⦌) (zeroForm GY n) = zeroForm GX n :=
  realize_map_zero _

end MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCotangentModels

/-!
# The literal algebra-splitting action on first-order geometric lifts

An algebra splitting is an actual map A to the actual square-zero
extension algebra with projection equal to the identity. The action
applies the original prestack functor to that map, at every parameter
simplex and every original point of F(A). Composition with coefficient
extension maps is the native functor composition.

This is the raw splitting action used before the source derived
resolution/coherent cotangent transpose. It does not identify the
pullback of L_F with L_A. The eventual chart differential is the
transpose of this action via the two representing comparisons; all
derived splitting/gauge/coefficient coherence stays in that source
construction.

Source: PTVV1111.3209v4, Section1.2; HAGII math/0404373v7,
Sections1.3.7/1.4.1. Native square-zero kernels and based deformation
fibres are reused from the imported source models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineSplittingCotangentActions

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k] {A : SAlg k}

/-- Every source splitting is a literal actual algebra map with its exact projection equation. -/
structure AlgebraSplitting (E : SquareZeroExtension A) where
  map : A ⟶ E.algebra
  projection : map ≫ E.projection = 𝟙 A

/-- The raw strict splittings form the original constant simplicial set. Derived replacement is separate. -/
def strictSplittings (E : SquareZeroExtension A) : SSet.{u + 1} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u + 1} (AlgebraSplitting E))

/-- The whole actual action applies F to each splitting, retaining all point/parameter simplices. -/
def splittingAction (F : Prestack k) (E : SquareZeroExtension A) :
    strictSplittings E ⊗ F.obj A ⟶ F.obj E.algebra where
  app n := ↾fun p => (F.map p.1.down.map).app n p.2
  naturality n m a := by
    ext p
    exact congrArg (fun q => q p.2) ((F.map p.1.down.map).naturality a)

/-- The actual second parameter projection of the same native simplicial pair. -/
def splittingParameter (F : Prestack k) (E : SquareZeroExtension A) :
    strictSplittings E ⊗ F.obj A ⟶ F.obj A where
  app _ := ↾fun p => p.2
  naturality _ _ _ := rfl

/-- The literal action projects back to the same original point in F(A), in every simplicial degree. -/
theorem splittingAction_projection (F : Prestack k) (E : SquareZeroExtension A) :
    splittingAction F E ≫ F.map E.projection = splittingParameter F E := by
  ext n p
  change ((F.map p.1.down.map ≫ F.map E.projection).app n) p.2 = p.2
  rw [← _root_.CategoryTheory.Functor.map_comp, p.1.down.projection, F.map_id]
  rfl

/-- The original coefficient extension map transports actual splittings by ordinary algebra composition. -/
def splittingMap {E E' : SquareZeroExtension A} (f : E.algebra ⟶ E'.algebra)
    (h : f ≫ E'.projection = E.projection) : strictSplittings E ⟶ strictSplittings E' where
  app _ := ↾fun s => ULift.up
    { map := s.down.map ≫ f
      projection := by rw [Category.assoc, h, s.down.projection] }
  naturality _ _ _ := rfl

/-- Coefficient transport commutes with the same all-parameter splitting action. -/
theorem splittingAction_naturality (F : Prestack k) {E E' : SquareZeroExtension A}
    (f : E.algebra ⟶ E'.algebra) (h : f ≫ E'.projection = E.projection) :
    ((splittingMap f h) ⊗ₘ 𝟙 (F.obj A)) ≫ splittingAction F E' =
      splittingAction F E ≫ F.map f := by
  ext n p
  change (F.map (p.1.down.map ≫ f)).app n p.2 =
    ((F.map p.1.down.map ≫ F.map f).app n) p.2
  rw [F.map_comp]

/-- A strict splitting gives the actual based geometric deformation through the native diagonal/path comparison. -/
def splittingDerivation (F : DerivedPrestack.{u, u + 1} k) (E : SquareZeroExtension A)
    (s : AlgebraSplitting E) (x : (Δ[0] : SSet.{u + 1}) ⟶ F.functor.obj A)
    (P : KanPathModel (F.functor.obj A)) :
    (Δ[0] : SSet.{u + 1}) ⟶ deformationFibre F E x P :=
  splitOrigin F
    { toSquareZeroExtension := E
      splitting := s.map
      splitting_projection := s.projection } x P

end MathlibExt.AlgebraicGeometry.AffineSplittingCotangentActions

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingCorner
public import MathlibExt.CategoryTheory.Functor.PullbackObjObj.SourceArrowIso
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero

/-!
# Mapping objects with zero target

Proves terminality of enriched mapping objects into the zero diagram and invertibility of
source-change maps. These give an explicit Arrow isomorphism for the mapping pullback corner
against a zero-target arrow.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.NativeMappingZeroSource

open PointedCGWH.EnrichedFunctorMapping
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The same original mapping object into the actual native zero diagram is terminal. -/
def terminal (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsTerminal (mappingObject X (zeroDiagram (A := I))) := by
  let _ : PreservesLimits (WeightedEndVariance.rightFunctor X) :=
    (tensorMappingAdjunction X).rightAdjoint_preservesLimits
  exact (zeroDiagramIsTerminal (A := I)).isTerminalObj
    (WeightedEndVariance.rightFunctor X) zeroDiagram

/-- Actual source maps between these same original terminal mapping objects are isomorphisms. -/
theorem source_isIso {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (p : X ⟶ Y) :
    IsIso (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor zeroDiagram.toEnrichedFunctor
      X.toEnrichedFunctor p) := by
  let e : mappingObject Y (zeroDiagram (A := I)) ≅ mappingObject X zeroDiagram :=
    (terminal Y).conePointUniqueUpToIso (terminal X)
  have h : Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor zeroDiagram.toEnrichedFunctor
      X.toEnrichedFunctor p = e.hom := (terminal X).hom_ext _ _
  rw [h]
  infer_instance

/-- The actual corner at the original zero target has an isomorphic first projection. -/
theorem corner_first_isIso {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (p : X ⟶ Y) (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsIso (NativeMappingCorner.square p (toZero Z)).fst := by
  let _ : IsIso ((WeightedEndVariance.bifunctor.map p.op).app zeroDiagram) := source_isIso p
  exact (NativeMappingCorner.square p (toZero Z)).isPullback.isIso_fst_of_isIso

/-- The entire original zero-target corner Arrow is the actual original source-mapping Arrow. -/
def cornerArrowIso {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (p : X ⟶ Y) (Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    Arrow.mk (NativeMappingCorner.square p (toZero Z)).π ≅
      Arrow.mk (Enriched.weightedEnd.mapWeight Y.toEnrichedFunctor Z.toEnrichedFunctor
        X.toEnrichedFunctor p) :=
  Functor.PullbackObjObj.sourceArrowIso (NativeMappingCorner.square p (toZero Z))
    (corner_first_isIso p Z)

end PointedCGWH.NativeMappingZeroSource

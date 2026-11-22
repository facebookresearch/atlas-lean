/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedFreeSmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientGenerators
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Genuine projective left lifting for original marked free arrows

The whole native free/evaluation adjunction transports the actual
coefficient cofibration lifting property. The full original free-mono
right class is exactly coefficient trivial fibrations at evaluation.
Consequently every original marked mono gives a projective free
cofibration without a diagram-model or cofibrancy outcome hypothesis.
-/

noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The actual original free coefficient cofibration has full left lifting against every native projective
  free-mono right map. -/
theorem enrichedFree_markedCofibration_left (C : Type v) [EnrichedCategory SSet.{u} C]
    (c : C) {A D : Marked.{u}} (f : A ⟶ D) (hf : cofibrations Marked.{u} f) :
    (enrichedFreeGenerators C coefficientGeneratingMonos).rlp.llp
      ((enrichedFreeDiagramFunctor C c).map f) := by
  have hleft : coefficientGeneratingMonos.rlp.llp f := by
    rw [coefficientGeneratingMonos_rlp, trivialFibrations_llp]
    exact hf
  intro F G p hp
  exact (Adjunction.hasLiftingProperty_iff (enrichedFreeEvaluationAdjunction C c) f p).mpr
    (hleft (p.app c) ((enrichedFreeGenerators_rlp_iff C coefficientGeneratingMonos p).mp hp c))

/-- Every original marked mono, with its unchanged source and target markings, is a genuine projective free left map. -/
theorem enrichedFree_markedMono_left (C : Type v) [EnrichedCategory SSet.{u} C]
    (c : C) {A D : Marked.{u}} (f : A ⟶ D) [Mono f] :
    (enrichedFreeGenerators C coefficientGeneratingMonos).rlp.llp
      ((enrichedFreeDiagramFunctor C c).map f) := by
  apply enrichedFree_markedCofibration_left C c f
  rw [coefficientMarkedCofibrations_eq]
  infer_instance

end SSet.Marked

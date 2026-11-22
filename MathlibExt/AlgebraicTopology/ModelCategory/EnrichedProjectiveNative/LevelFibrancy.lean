/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero
public import MathlibExt.Topology.Category.PointedCGWH.Closed

/-!
# Fibrancy of native enriched diagrams

In the native projective model on PointedCGWH-valued enriched diagrams, every object is
fibrant. The proof identifies fibrations with the evaluationwise class and uses fibrancy of
pointed compactly generated weak Hausdorff spaces, with the specified bottom element of the
realized generating ordinal.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] modelCategory MonoidalClosed.enrichedCategorySelf

/-- Every actual native level diagram is fibrant, from the original evaluated base fibrancy. -/
theorem allObjectsFibrant (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : IsFibrant X := by
  have hX : fibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (toZero X) := by
    rw [fibrations_eq]
    apply (EvaluationTransfer.evaluationProperty_iff
      (fun a : I => evaluation (V := PointedCGWH.{u, v}) a) (fibrations PointedCGWH.{u, v}) _).mpr
    intro a
    let _ : IsFibrant (X.toEnrichedFunctor.obj a) :=
      PointedCGWH.modelCategory.allObjectsFibrant _
    let _ : Fibration ((evaluation (V := PointedCGWH.{u, v}) a).map (toZero X)) :=
      (isFibrant_iff_of_isTerminal (component (toZero X) a)
        (initialDiagram_component_isZero a).isTerminal).mp inferInstance
    exact HomotopicalAlgebra.mem_fibrations _
  exact (isFibrant_iff_of_isTerminal (toZero X) zeroDiagramIsTerminal).mpr
    ((HomotopicalAlgebra.fibration_iff _).mpr hX)

end HomotopicalAlgebra.EnrichedProjective.Native

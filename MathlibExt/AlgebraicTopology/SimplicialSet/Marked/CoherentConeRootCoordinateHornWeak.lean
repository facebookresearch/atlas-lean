/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHornSuccessor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHornSourceIso

/-!
# Genuine coefficient weakness of the SAME original entire root-horn inclusion

Every actual original marked skeletal successor is a coefficient trivial
cofibration, and the SAME complete marked horn prism is their genuine
natural-number transfinite composition. The original restricted whole
marked source isomorphism transports that actual coefficient conclusion
to the SAME original full root-horn attaching map. No weak-class or
filler outcome is supplied as a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- The entire SAME original marked horn-prism inclusion is a genuine coefficient trivial cofibration through its
original full marked skeletal transfinite composition. -/
theorem coneRootCoordinateHornPrism_trivialCofibration {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) :
    trivialCofibrations Marked.{u} (coneRootCoordinateHornPrismMap j hj) := by
  rw [← llp_eq_of_wfs (trivialCofibrations Marked.{u}) (fibrations Marked.{u})]
  let W : MorphismProperty Marked.{u} := (fibrations Marked.{u}).llp
  let h := coneRootCoordinateHornFiltrationTransfiniteComposition j hj hj'
  let hw : W.TransfiniteCompositionOfShape ℕ (coneRootCoordinateHornPrismMap j hj) :=
    { toTransfiniteCompositionOfShape := h
      map_mem d _ := by
        have hs := coneRootCoordinateHornFiltration_step_trivialCofibration j hj hj' d
        rw [← llp_eq_of_wfs (trivialCofibrations Marked.{u}) (fibrations Marked.{u})] at hs
        exact hs }
  exact (transfiniteCompositionsOfShape_le W ℕ) _ ⟨hw⟩

/-- The SAME entire original marked root-horn attaching map is a genuine trivial cofibration in the actual original
coefficient model. -/
theorem coneRootCoordinateHorn_trivialCofibration {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) :
    trivialCofibrations Marked.{u} (coneRootCoordinateHornMap j) :=
  ((trivialCofibrations Marked.{u}).arrow_mk_iso_iff (coneRootCoordinateHornPrismArrowIso j hj)).mp
    (coneRootCoordinateHornPrism_trivialCofibration j hj hj')

/-- The complete original nonterminal root-horn inclusion is actually weak in the genuine coefficient model,
retaining its SAME entire original source, target, inherited marking and attaching map. -/
theorem coneRootCoordinateHorn_weakEquivalence {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) :
    weakEquivalences Marked.{u} (coneRootCoordinateHornMap j) :=
  (coneRootCoordinateHorn_trivialCofibration j hj hj').2

end SSet.Marked.CoherentWeight

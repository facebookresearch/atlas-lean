/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.GrahamWeightedAuxiliaryAlgebra
import Code.Ising.CorrelationRatio

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem grahamExpectation_preEq22
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    let Z := currentSum G beta J ∅
    expectationJ G beta J {i, j, k, l} -
        expectationJ G beta J {i, j} * expectationJ G beta J {k, l} -
        expectationJ G beta J {i, k} * expectationJ G beta J {j, l} -
        expectationJ G beta J {i, l} * expectationJ G beta J {j, k} +
        2 * expectationJ G beta J {i, m} * expectationJ G beta J {j, m} *
          expectationJ G beta J {k, m} * expectationJ G beta J {l, m} =
      (2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k -
        2 * sourcePairDisconnSum G beta J {i, j} ∅ i m *
          currentSum G beta J {k, l} * Z -
        2 * StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m *
          sourcePairDisconnSum G beta J {k, l} ∅ k m) / Z ^ 4 := by
  dsimp
  have hpre := grahamCurrentSum_preEq22 G beta J
    hij hik hil hjk hjl hkl him hjm hkm hlm
  dsimp at hpre
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta J)
  rw [current_representation, current_representation, current_representation,
    current_representation, current_representation, current_representation,
    current_representation, current_representation, current_representation,
    current_representation, current_representation]
  field_simp [hZ]
  ring_nf at hpre ⊢
  exact hpre

end StatMech.FrontierA

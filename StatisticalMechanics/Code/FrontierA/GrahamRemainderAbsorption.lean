/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamComponentAssociationReduction
import Code.FrontierA.GrahamLemmaOneSwitchingRestriction










open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem grahamRemainderAbsorption_of_cutPositiveAssociation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    {j k l m : V}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m)
    (hassoc : GrahamCutPositiveAssociation G beta J m) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
          sourcePairDisconnSum G beta J {k, l} ∅ k m +
        gatedSourcePairSum G beta J {j, l} ∅
            (fun n => ¬ CurrentConnected G n k m ∧
              ¬ CurrentConnected G n k l) *
          currentSum G beta J ∅ ^ 2 <=
      sourcePairDisconnSum G beta J {j, l} ∅ k m *
        currentSum G beta J ∅ ^ 2 := by
  rw [← grahamWeightedLemmaOne_iff_remainder_absorbed
    G beta J hjk hjl hkl]
  exact grahamWeightedLemmaOne_of_cutPositiveAssociation
    G beta J hbeta hJ hjk hkl hjm hkm hlm hassoc

end StatMech.FrontierA

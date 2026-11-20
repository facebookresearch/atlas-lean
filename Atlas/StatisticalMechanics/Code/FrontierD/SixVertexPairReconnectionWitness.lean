/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample












open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexReconnectionIceRuleDecidable
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))



def sixVertexFourByTwoMiddleArrows :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide
    ((v.2.val = 0 /\ v.1.val = 3) \/
      (v.2.val = 1 /\ v.1.val ≠ 3))
  vertical v := decide
    ((v.2.val = 0 /\ v.1.val = 0) \/
      (v.2.val = 1 /\ v.1.val = 3))

theorem sixVertexFourByTwoMiddleArrows_ice :
    sixVertexFourByTwoMiddleArrows.IceRule := by
  decide +revert

theorem sixVertexFourByTwoMiddleArrows_seamCount :
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        sixVertexFourByTwoMiddleArrows
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  decide +revert

theorem sixVertexFourByTwoLowArrows_cTypeCount :
    sixVertexTorusCTypeCount sixVertexFourByTwoLowArrows = 0 := by
  norm_num [sixVertexTorusCTypeCount, SixVertexArrows.IsCType,
    sixVertexFourByTwoLowArrows, sixVertexFourByTwoTorus,
    SixVertexArrows.cyclicPred]

theorem sixVertexFourByTwoHighArrows_cTypeCount :
    sixVertexTorusCTypeCount sixVertexFourByTwoHighArrows = 8 := by
  norm_num [sixVertexTorusCTypeCount, SixVertexArrows.IsCType,
    sixVertexFourByTwoHighArrows, sixVertexFourByTwoTorus,
    SixVertexArrows.cyclicPred]
  decide +revert

theorem sixVertexFourByTwoMiddleArrows_cTypeCount :
    sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows = 4 := by
  norm_num [sixVertexTorusCTypeCount, SixVertexArrows.IsCType,
    sixVertexFourByTwoMiddleArrows, sixVertexFourByTwoTorus,
    SixVertexArrows.cyclicPred]
  decide +revert


theorem sixVertexFourByTwo_reconnection_markedWeight :
    sixVertexTorusMarkedWeight sixVertexFourByTwoLowArrows *
        sixVertexTorusMarkedWeight sixVertexFourByTwoHighArrows =
      sixVertexTorusMarkedWeight sixVertexFourByTwoMiddleArrows *
        sixVertexTorusMarkedWeight sixVertexFourByTwoMiddleArrows := by
  rw [sixVertexTorusMarkedWeight_eq_pow _ sixVertexFourByTwoLowArrows_ice,
    sixVertexTorusMarkedWeight_eq_pow _ sixVertexFourByTwoHighArrows_ice,
    sixVertexTorusMarkedWeight_eq_pow _ sixVertexFourByTwoMiddleArrows_ice,
    sixVertexFourByTwoLowArrows_cTypeCount,
    sixVertexFourByTwoHighArrows_cTypeCount,
    sixVertexFourByTwoMiddleArrows_cTypeCount]
  simp only [pow_zero, one_mul, ← pow_add]


theorem sixVertexFourByTwo_reconnection_multiplicity (k : Nat) :
    sixVertexMarkedPairMultiplicity
        sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows k =
      sixVertexMarkedPairMultiplicity
        sixVertexFourByTwoMiddleArrows sixVertexFourByTwoMiddleArrows k := by
  unfold sixVertexMarkedPairMultiplicity
  exact congrArg (fun p : Real[X] => p.coeff k)
    sixVertexFourByTwo_reconnection_markedWeight



theorem sixVertexFourByTwo_exists_weightPreserving_reconnection :
    exists alpha beta : SixVertexArrows sixVertexFourByTwoTorus,
      alpha.IceRule /\ beta.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus alpha
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus beta
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexTorusMarkedWeight sixVertexFourByTwoLowArrows *
          sixVertexTorusMarkedWeight sixVertexFourByTwoHighArrows =
        sixVertexTorusMarkedWeight alpha * sixVertexTorusMarkedWeight beta := by
  exact ⟨sixVertexFourByTwoMiddleArrows, sixVertexFourByTwoMiddleArrows,
    sixVertexFourByTwoMiddleArrows_ice,
    sixVertexFourByTwoMiddleArrows_ice,
    sixVertexFourByTwoMiddleArrows_seamCount,
    sixVertexFourByTwoMiddleArrows_seamCount,
    sixVertexFourByTwo_reconnection_markedWeight⟩

end

end StatMech.FrontierD

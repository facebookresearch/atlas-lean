/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectConnectedInsertionCharge
import Code.FrontierD.FKRectTorusConcreteRibbon
import Code.FrontierD.FKRectTorusDisconnectedInsertion

open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectEulerHomologyDefect_eq_two_mul_netIndicator
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) =
      2 * (fkRectNetIndicator R
        (fkRectConfigurationOfEdges R F) : Int) := by
  induction F using Finset.induction_on with
  | empty =>
      rw [fkRectEulerHomologyDefect_empty, fkRectNetIndicator_empty]
      norm_num
  | @insert e F heF ih =>
      let old := fkRectConfigurationOfEdges R F
      let new := fkRectConfigurationOfEdges R (insert e F)
      by_cases holdNet : FKRectHasNet R old
      · have hnewNet : FKRectHasNet R new :=
          FKRectHasNet.insert R F e holdNet
        have holdIndicator : fkRectNetIndicator R old = 1 :=
          (fkRectNetIndicator_eq_one_iff R old).2 holdNet
        have hnewIndicator : fkRectNetIndicator R new = 1 :=
          (fkRectNetIndicator_eq_one_iff R new).2 hnewNet
        have holdDefect : fkRectEulerHomologyDefect R old = 2 := by
          rw [ih, holdIndicator]
          norm_num
        rcases fkRectEulerHomologyDefect_classified_of_concreteRibbon
            R (insert e F) with hzero | htwo
        · have hmono := fkRectEulerHomologyDefect_insert_mono R F e heF
          dsimp only [old, new] at holdDefect hmono
          omega
        · rw [htwo, hnewIndicator]
          norm_num
      · have holdIndicator : fkRectNetIndicator R old = 0 :=
          (fkRectNetIndicator_eq_zero_iff R old).2 holdNet
        have holdDefect : fkRectEulerHomologyDefect R old = 0 := by
          rw [ih, holdIndicator]
          norm_num
        by_cases hreach : (fkRectOpenGraph R old).Reachable
            (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)
        · let r := hreach.some
          have hsurface :=
            fkRectConnectedInsertionSurfaceBridge_unconditional
              R F e r heF holdNet
          have hcriterion :=
            fkRectEulerHomologyDefect_insert_eq_two_iff_hasNet
              R F e heF r holdDefect holdNet hsurface
          by_cases hnewNet : FKRectHasNet R new
          · have hnewIndicator : fkRectNetIndicator R new = 1 :=
              (fkRectNetIndicator_eq_one_iff R new).2 hnewNet
            have hnewDefect : fkRectEulerHomologyDefect R new = 2 :=
              hcriterion.2 hnewNet
            rw [hnewDefect, hnewIndicator]
            norm_num
          · have hnewIndicator : fkRectNetIndicator R new = 0 :=
              (fkRectNetIndicator_eq_zero_iff R new).2 hnewNet
            rcases fkRectEulerHomologyDefect_classified_of_concreteRibbon
                R (insert e F) with hzero | htwo
            · rw [hzero, hnewIndicator]
              norm_num
            · exact False.elim (hnewNet (hcriterion.1 htwo))
        · have hnewNoNet : ¬ FKRectHasNet R new :=
            not_fkRectHasNet_insert_of_not_reachable
              R F e holdNet hreach
          have hnewIndicator : fkRectNetIndicator R new = 0 :=
            (fkRectNetIndicator_eq_zero_iff R new).2 hnewNoNet
          have hnewDefect : fkRectEulerHomologyDefect R new = 0 := by
            rw [fkRectEulerHomologyDefect_insert_of_not_reachable
              R F e heF (fkRectTorusIndexedEdge_eq_medialPrimals R e) hreach,
              holdDefect]
          rw [hnewDefect, hnewIndicator]
          norm_num


theorem fkRectEulerHomologyDefect_eq_two_iff_hasNet
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectEulerHomologyDefect R omega = 2 ↔ FKRectHasNet R omega := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega := by
    exact fkRectConfigurationOfEdges_openEdges R omega
  rw [← homega,
    fkRectEulerHomologyDefect_eq_two_mul_netIndicator]
  constructor
  · intro h
    have hindicator : fkRectNetIndicator R
        (fkRectConfigurationOfEdges R F) = 1 := by
      have hle := fkRectNetIndicator_le_one R
        (fkRectConfigurationOfEdges R F)
      omega
    exact (fkRectNetIndicator_eq_one_iff R _).1 hindicator
  · intro hnet
    rw [(fkRectNetIndicator_eq_one_iff R _).2 hnet]
    norm_num



theorem fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectEulerHomologyDefect R omega =
      2 * (fkRectNetIndicator R omega : Int) := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  rw [← homega]
  exact fkRectEulerHomologyDefect_eq_two_mul_netIndicator R F

end

end StatMech.FrontierD

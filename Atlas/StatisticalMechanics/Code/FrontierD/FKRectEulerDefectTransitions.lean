/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectEulerDefectInsertion
import Code.FrontierD.FKMedialBoundaryToggleParity

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedialLoopCount_insert_dichotomy
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) + 1 =
        fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) ∨
      fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) + 1 =
        fkRectMedialLoopCount R
          (fkRectConfigurationOfEdges R (insert e F)) := by
  have hpair := fkRectConfigurationToMedialPairing_insert R F e heF
  have h := fkMedialLoopCount_toggle_dichotomy R.medialTorus
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e)
  unfold fkRectMedialLoopCount
  rwa [hpair]



theorem fkRectEulerHomologyDefect_insert_dichotomy
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) =
        fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) ∨
      fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) =
        fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) + 2 := by
  obtain ⟨p, q, hedge⟩ : ∃ p q : R.Vertex,
      fkRectTorusIndexedEdge R e = s(p, q) := by
    induction fkRectTorusIndexedEdge R e using Sym2.inductionOn with
    | _ p q => exact ⟨p, q, rfl⟩
  by_cases hpq : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable p q
  · have hk := fkRectFinsetClusterCount_insert_of_reachable
      R F e hedge hpq
    rcases fkRectMedialLoopCount_insert_dichotomy R F e heF with hl | hl
    · right
      rw [fkRectEulerHomologyDefect_configurationOfEdges,
        fkRectEulerHomologyDefect_configurationOfEdges,
        Finset.card_insert_of_notMem heF, hk]
      push_cast
      omega
    · left
      rw [fkRectEulerHomologyDefect_configurationOfEdges,
        fkRectEulerHomologyDefect_configurationOfEdges,
        Finset.card_insert_of_notMem heF, hk]
      push_cast
      omega
  · left
    exact fkRectEulerHomologyDefect_insert_of_not_reachable
      R F e heF hedge hpq

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialReachability

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedialLoopCount_insert_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) {p q : R.Vertex}
    (hedge : fkRectTorusIndexedEdge R e = s(p, q))
    (hpq : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable p q) :
    fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) + 1 =
      fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
  let omega := fkRectConfigurationOfEdges R F
  let pairing := fkRectConfigurationToMedialPairing R omega
  have hpair := fkRectConfigurationToMedialPairing_insert R F e heF
  have hdisc := fkRectMedial_west_east_not_reachable_of_endpoints
    R omega e hedge hpq
  have hcount := fkMedialLoopCount_toggle_of_not_reachable
    R.medialTorus pairing (fkRectMedialVertexOfEdge R e) hdisc
  unfold fkRectMedialLoopCount
  rw [hpair]
  exact hcount


theorem fkRectMedialLoopCount_insert_le_add_one
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectMedialLoopCount R (fkRectConfigurationOfEdges R (insert e F)) ≤
      fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) + 1 := by
  have hpair := fkRectConfigurationToMedialPairing_insert R F e heF
  have hcount := fkMedialLoopCount_toggle_le_add_one R.medialTorus
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e)
  unfold fkRectMedialLoopCount
  rw [hpair]
  exact hcount



theorem fkRectEulerHomologyDefect_insert_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) {p q : R.Vertex}
    (hedge : fkRectTorusIndexedEdge R e = s(p, q))
    (hpq : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable p q) :
    fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) =
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) := by
  have hk := fkRectFinsetClusterCount_insert_of_not_reachable
    R F e hedge hpq
  have hl := fkRectMedialLoopCount_insert_of_not_reachable
    R F e heF hedge hpq
  rw [fkRectEulerHomologyDefect_configurationOfEdges,
    fkRectEulerHomologyDefect_configurationOfEdges,
    Finset.card_insert_of_notMem heF]
  push_cast
  omega



theorem fkRectEulerHomologyDefect_insert_mono
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) ≤
      fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) := by
  have hex : ∃ p q : R.Vertex, fkRectTorusIndexedEdge R e = s(p, q) := by
    induction fkRectTorusIndexedEdge R e using Sym2.inductionOn with
    | _ p q => exact ⟨p, q, rfl⟩
  obtain ⟨p, q, hedge⟩ := hex
  by_cases hpq : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable p q
  · have hk := fkRectFinsetClusterCount_insert_of_reachable
      R F e hedge hpq
    have hl := fkRectMedialLoopCount_insert_le_add_one R F e heF
    rw [fkRectEulerHomologyDefect_configurationOfEdges,
      fkRectEulerHomologyDefect_configurationOfEdges,
      Finset.card_insert_of_notMem heF]
    push_cast
    omega
  · rw [fkRectEulerHomologyDefect_insert_of_not_reachable
      R F e heF hedge hpq]

end

end StatMech.FrontierD

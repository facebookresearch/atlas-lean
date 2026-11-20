/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalSquarefree
import Code.Onsager.DecorationFormalAssembly
import Code.Onsager.FinalAssembly










namespace StatMech.Onsager

def ons_DecFormalRepeatedEdgeVanishes : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ)
      (edge : ons_DecEdge L), 2 ≤ m edge →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0

theorem ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes) :
    ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L := by
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  exact ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes
    L (hvanish L hL)

theorem ons_spinKacWardIdentities_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_decoratedFormal
  exact ons_decoratedFormalKacWardIdentity_of_repeatedEdgeVanishes hvanish

theorem ons_free_energy_of_repeatedEdgeVanishes
    (hvanish : ons_DecFormalRepeatedEdgeVanishes)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) := by
  apply ons_free_energy_of_spinKacWard_all
    (fun gamma ↦ ons_spinKacWardIdentities_of_repeatedEdgeVanishes
      hvanish gamma)
  exact hbeta

end StatMech.Onsager

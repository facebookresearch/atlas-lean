/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalCoefficient










namespace StatMech.Onsager

open Finset StatMech.Ising

theorem ons_not_isSquarefreeExponent_iff
    {E : Type*} (m : E →₀ ℕ) :
    ¬ ons_IsSquarefreeExponent m ↔ ∃ edge, 2 ≤ m edge := by
  constructor
  · intro hm
    by_contra hnone
    apply hm
    intro edge
    by_contra hle
    apply hnone
    exact ⟨edge, by omega⟩
  · rintro ⟨edge, hedge⟩ hm
    have := hm edge
    omega



theorem ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes
    (L : ℕ) [Fact (2 < L)]
    (hvanish : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ),
      ¬ ons_IsSquarefreeExponent m →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
    ons_decoratedFormalKacWardIdentity L :=
  ons_decoratedFormalKacWardIdentity_of_nonsquarefree_zero L hvanish

theorem ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes
    (L : ℕ) [Fact (2 < L)]
    (hvanish : ∀ (a b : Fin 2) (m : ons_DecEdge L →₀ ℕ)
      (edge : ons_DecEdge L), 2 ≤ m edge →
      MvPowerSeries.coeff m
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0) :
    ons_decoratedFormalKacWardIdentity L := by
  apply ons_decoratedFormalKacWardIdentity_of_nonsquarefree_vanishes L
  intro a b m hm
  obtain ⟨edge, hedge⟩ := (ons_not_isSquarefreeExponent_iff m).mp hm
  exact hvanish a b m edge hedge

end StatMech.Onsager

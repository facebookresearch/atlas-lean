/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderCrossings









namespace StatMech.FrontierD

noncomputable section



theorem fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul_pow_pred
    (R : FKRectTorus)
    (mu : ConfigSpace (Sym2 R.Vertex) → Real)
    (hmu : ∀ rho, 0 ≤ mu rho) (n : Nat) (hn : 0 < n) (a : Real)
    (hmass : ∀ (S : Finset (Fin R.width)), S.card = n →
      ∀ (pair : Fin R.width → Fin R.width) (first : Fin R.width), first ∈ S →
        StatMech.Probability.finiteEventMass mu
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} ≤ a ^ (S.erase first).card) :
    StatMech.Probability.finiteEventMass mu
        {rho | n ≤ fkRectHorizontalCylinderCrossingClusterCount R rho} ≤
      Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
  apply fkRectHorizontalCylinderCrossingTail_le_choose_mul_pairCount_mul
    R mu hmu n (a ^ (n - 1))
  intro S hcard pair
  have hS : S.Nonempty := Finset.card_pos.mp (hcard ▸ hn)
  obtain ⟨first, hfirst⟩ := hS
  calc
    StatMech.Probability.finiteEventMass mu
        {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} ≤
      a ^ (S.erase first).card := hmass S hcard pair first hfirst
    _ = a ^ (n - 1) := by
      rw [Finset.card_erase_of_mem hfirst, hcard]

end

end StatMech.FrontierD

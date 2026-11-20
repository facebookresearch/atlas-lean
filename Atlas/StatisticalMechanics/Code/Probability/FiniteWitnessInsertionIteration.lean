/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Probability.FiniteWitnessUnionBound









namespace StatMech.Probability

noncomputable section

variable {Omega I : Type*} [Fintype Omega] [Fintype I]
  [DecidableEq Omega] [DecidableEq I]



theorem finiteEventMass_le_pow_erase_of_insert_step
    (mu : Omega → Real) (hmu : ∀ omega, 0 ≤ mu omega)
    (hsum : ∑ omega, mu omega = 1)
    (Witness : Finset I → Omega → Prop)
    {a : Real} (ha : 0 ≤ a)
    (step : ∀ (T : Finset I) (first : I), first ∈ T →
      ∀ (x : I), x ∉ T →
      finiteEventMass mu {omega | Witness (insert x T) omega} ≤
        a * finiteEventMass mu {omega | Witness T omega})
    (S : Finset I) (first : I) (hfirst : first ∈ S) :
    finiteEventMass mu {omega | Witness S omega} ≤
      a ^ (S.erase first).card := by
  classical
  let mass (T : Finset I) :=
    finiteEventMass mu {omega | Witness T omega}
  have iter : ∀ U : Finset I, first ∉ U →
      mass (insert first U) ≤ a ^ U.card := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        intro _
        calc
          mass {first} ≤ ∑ omega, mu omega := by
            unfold mass finiteEventMass
            apply Finset.sum_le_sum
            intro omega _
            by_cases hW : Witness {first} omega
            · simp [hW]
            · simp [hW, hmu omega]
          _ = 1 := hsum
          _ = a ^ (∅ : Finset I).card := by simp
    | @insert x U hx ih =>
        intro hfirstInsert
        have hfirstU : first ∉ U := by
          intro hmem
          exact hfirstInsert (Finset.mem_insert_of_mem hmem)
        have hxf : x ≠ first := by
          intro h
          exact hfirstInsert (h ▸ Finset.mem_insert_self x U)
        have hxBase : x ∉ insert first U := by
          simp [hx, hxf]
        calc
          mass (insert first (insert x U)) =
              mass (insert x (insert first U)) := by
            rw [Finset.insert_comm]
          _ ≤ a * mass (insert first U) :=
            step (insert first U) first (Finset.mem_insert_self first U)
              x hxBase
          _ ≤ a * a ^ U.card :=
            mul_le_mul_of_nonneg_left (ih hfirstU) ha
          _ = a ^ (insert x U).card := by
            rw [Finset.card_insert_of_notMem hx, pow_succ]
            ring
  calc
    finiteEventMass mu {omega | Witness S omega} =
        mass (insert first (S.erase first)) := by
      rw [Finset.insert_erase hfirst]
    _ ≤ a ^ (S.erase first).card :=
      iter (S.erase first) (Finset.notMem_erase first S)

end

end StatMech.Probability

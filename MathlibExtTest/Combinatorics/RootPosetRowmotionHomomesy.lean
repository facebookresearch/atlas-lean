/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.RootPosetRowmotionHomomesy
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Fin.Basic

open MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted
open scoped BigOperators

namespace MathlibExtTest.RootPosetRowmotionHomomesy

private def emptyAntichain (P : Type*) [PartialOrder P] : PosetAntichain P :=
  ⟨∅, by simpa only [Finset.coe_empty] using IsAntichain.empty⟩

private theorem rankZero : IsTypeARootPoset (Fin 0) 0 := by
  let _ : IsEmpty {p : Fin 0 × Fin 0 // p.1 ≤ p.2} := ⟨fun p => Fin.elim0 p.val.1⟩
  exact ⟨Equiv.equivOfIsEmpty _ _, fun x => Fin.elim0 x⟩

private theorem rankZeroRowmotion :
    IsAntichainRowmotion (Fin 0) (id : PosetAntichain (Fin 0) → _) :=
  ⟨Function.bijective_id, fun _ x => Fin.elim0 x⟩

-- The empty poset has one antichain, whose size is zero throughout its orbit.
example :
    (∑ i ∈ Finset.range 1, ((Nat.iterate id i (emptyAntichain (Fin 0))).val.card : ℚ)) /
      (1 : ℚ) = 0 := by
  have h := (conjecture_holds 0 (Fin 0) id (fun A => A.val.card)
    rankZero rankZeroRowmotion (fun _ => rfl)).2.2 (emptyAntichain (Fin 0)) 1 (by decide) rfl
  simpa using h

private theorem rankOne : IsTypeARootPoset PUnit 1 := by
  let _ : Unique {p : Fin 1 × Fin 1 // p.1 ≤ p.2} :=
    uniqueOfSubsingleton ⟨(0, 0), le_rfl⟩
  refine ⟨Equiv.ofUnique _ _, fun a b => ?_⟩
  rw [Subsingleton.elim b a]
  simp

private def toggle (A : PosetAntichain PUnit) : PosetAntichain PUnit :=
  ⟨if PUnit.unit ∈ A.val then ∅ else {PUnit.unit}, by
    intro a _ b _ hab _
    exact hab (Subsingleton.elim a b)⟩

private theorem mem_toggle (A : PosetAntichain PUnit) (x : PUnit) :
    x ∈ (toggle A).val ↔ x ∉ A.val := by
  cases x
  by_cases h : PUnit.unit ∈ A.val <;> simp [toggle, h]

private theorem toggle_involutive : Function.Involutive toggle := by
  intro A
  apply Subtype.ext
  ext x
  simp only [mem_toggle, not_not]

private theorem rankOneRowmotion : IsAntichainRowmotion PUnit toggle := by
  refine ⟨toggle_involutive.bijective, fun A x => ?_⟩
  rw [mem_toggle]
  constructor
  · intro hx
    refine ⟨?_, fun y _ _ => Subsingleton.elim y x⟩
    rintro ⟨a, ha, _⟩
    exact hx (Subsingleton.elim a x ▸ ha)
  · rintro ⟨h, _⟩ hx
    exact h ⟨x, hx, le_rfl⟩

-- The rank-one cycle has length two. Averaging over two traversals gives the same mean.
example :
    (∑ i ∈ Finset.range 4, ((Nat.iterate toggle i (emptyAntichain PUnit)).val.card : ℚ)) /
      (4 : ℚ) = 1 / 2 := by
  let A := emptyAntichain PUnit
  have hreturn : Nat.iterate toggle 4 A = A := by
    change toggle (toggle (toggle (toggle A))) = A
    rw [toggle_involutive (toggle (toggle A)), toggle_involutive]
  exact (conjecture_holds 1 PUnit toggle (fun B => B.val.card)
    rankOne rankOneRowmotion (fun _ => rfl)).2.2 A 4 (by decide) hreturn

end MathlibExtTest.RootPosetRowmotionHomomesy

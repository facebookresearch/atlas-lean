/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
Canonical finite p-group and Sylow APIs. Counting is checked in index form; no order-ten
classification is asserted.
-/

set_option autoImplicit false
noncomputable section

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

example [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n := IsPGroup.iff_card

example [Finite G] [Nontrivial G] (hG : IsPGroup p G) :
    Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hG

example (hG : Nat.card G = p ^ 2) (a b : G) : a * b = b * a :=
  (IsPGroup.isMulCommutative_of_card_eq_prime_sq hG).is_comm.comm a b

example [Finite G] (P : Sylow p G) :
    Nat.card P = p ^ (Nat.card G).factorization p := Sylow.card_eq_multiplicity P

example (S : Subgroup G) (hS : IsPGroup p S) : ∃ P : Sylow p G, S ≤ P :=
  IsPGroup.exists_le_sylow hS

example [Finite G] : MulAction.IsPretransitive G (Sylow p G) := inferInstance
example [Finite G] (P : Sylow p G) : Nat.card (Sylow p G) ∣ P.index := Sylow.card_dvd_index P
example [Finite G] : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G

example [Fintype G] (h : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  exists_prime_orderOf_dvd_card p h

-- The legacy pole set `{x | ∃ h ≠ 1, h • x = x}` (points with nontrivial
-- stabilizer) is closed under the action: if `p` has a nontrivial
-- stabilizer element, so does `g • p`, by conjugation.  This is the content
-- of the legacy `SylowTheorems.smul_mem_poles`, from `MulAction.stabilizer`
-- conjugation.
example {X : Type*} [MulAction G X] (g : G) (p : X)
    (hp : ∃ h ∈ MulAction.stabilizer G p, h ≠ 1) :
    ∃ h ∈ MulAction.stabilizer G (g • p), h ≠ 1 := by
  obtain ⟨h, hstab, hne⟩ := hp
  refine ⟨MulAut.conj g h, ?_, ?_⟩
  · rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact Subgroup.mem_map.mpr ⟨h, hstab, rfl⟩
  · intro heq
    exact hne ((MulAut.conj g).injective (by simpa using heq))

#print axioms IsPGroup.iff_card
#print axioms IsPGroup.center_nontrivial
#print axioms IsPGroup.isMulCommutative_of_card_eq_prime_sq
#print axioms Sylow.card_eq_multiplicity
#print axioms IsPGroup.exists_le_sylow
#print axioms Sylow.isPretransitive_of_finite
#print axioms Sylow.card_dvd_index
#print axioms card_sylow_modEq_one
#print axioms exists_prime_orderOf_dvd_card

end

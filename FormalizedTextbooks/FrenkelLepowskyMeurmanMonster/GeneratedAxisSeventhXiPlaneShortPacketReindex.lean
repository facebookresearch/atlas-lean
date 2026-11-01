/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation

/-! Complete finite reindexing of the signed pair, octad and odd packets. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem product_sum {β : Type*} [AddCommMonoid β] (n m : ℕ)
    (f : Fin (n * m) → β) :
    (∑ k : Fin (n * m), f k) =
      ∑ i : Fin n, ∑ j : Fin m, f (finProdFinEquiv (i, j)) := by
  have h := (Equiv.sum_comp finProdFinEquiv f).symm
  rw [Fintype.sum_prod_type] at h
  exact h

/-- Every packet position occurs exactly once in the three complete source blocks. -/
theorem generatedSeventhXiShortPacket_sum_split {β : Type*} [AddCommMonoid β]
    (f : Fin 27624 → β) :
    (∑ k : Fin 27624, f k) =
      (∑ s : Fin 2, ∑ p : Fin 276,
        f ⟨276 * s.val + p.val, by omega⟩) +
      (∑ g : Fin 231, ∑ e : Fin 64,
        f ⟨552 + 64 * g.val + e.val, by omega⟩) +
      (∑ g : Fin 512, ∑ j : Fin 24,
        f ⟨15336 + 24 * g.val + j.val, by omega⟩) := by
  rw [Fin.sum_univ_add (a := 552) (b := 27072)]
  rw [Fin.sum_univ_add (a := 14784) (b := 12288)]
  rw [product_sum 2 276, product_sum 231 64, product_sum 512 24]
  dsimp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.castAdd, Fin.natAdd, Fin.castLE]
  simp only [Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm, add_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

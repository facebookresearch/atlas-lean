/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.Rev
import MathlibExt.Combinatorics.SimpleGraph.OrderRobustOrderedRamsey

namespace MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted

private def reverseOrder (n : ℕ) : MathlibExt.Order.StrictTotalOrder (Fin n) where
  lt a b := b < a
  irrefl := lt_irrefl
  trans hab hbc := hbc.trans hab
  total h := (lt_or_gt_of_ne h).symm

/-- Reversing labels embeds the reverse order, including at size zero. -/
private theorem reverseEmbedding (n : ℕ) : IsOrderedEmbedding (reverseOrder n) Fin.rev :=
  ⟨Fin.rev_injective, fun _ _ h => Fin.rev_lt_rev.mpr h⟩

/-- An edgeless red copy can use an entirely red host, and an edgeless blue copy can use
an entirely blue one. Neither copy imposes any condition on the colors of nonedges. -/
example : HasRedOrderedCopy (⊥ : SimpleGraph (Fin 3)) (reverseOrder 3) (⊤ : SimpleGraph (Fin 3)) ∧
    HasBlueOrderedCopy (⊥ : SimpleGraph (Fin 3)) (reverseOrder 3) (⊥ : SimpleGraph (Fin 3)) :=
  ⟨⟨Fin.rev, reverseEmbedding 3, fun _ _ h => h.elim⟩,
   ⟨Fin.rev, reverseEmbedding 3, fun _ _ h => h.elim⟩⟩

/-- A two-vertex edge has no red copy in the all-blue host of the same size. -/
example : ¬ HasRedOrderedCopy (⊤ : SimpleGraph (Fin 2)) (reverseOrder 2)
    (⊥ : SimpleGraph (Fin 2)) :=
  fun ⟨_, _, h⟩ => h 0 1 (by decide)

/-- A blue copy of an edge requires a missing red edge between distinct images. -/
example : HasBlueOrderedCopy (⊤ : SimpleGraph (Fin 2)) (reverseOrder 2) (⊥ : SimpleGraph (Fin 2)) ∧
    ¬ HasBlueOrderedCopy (⊤ : SimpleGraph (Fin 2)) (reverseOrder 2) (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨⟨Fin.rev, reverseEmbedding 2, fun _ _ _ => id⟩, ?_⟩
  rintro ⟨f, hf, hc⟩
  exact hc 0 1 (by decide) (hf.1.ne (by decide))

/-- The least host size for an edgeless target is its vertex count, for all `n` including zero. -/
example (n : ℕ) : orderedRamseyNumber (⊥ : SimpleGraph (Fin n)) (reverseOrder n) = n := by
  have hn : OrderedRamseyProp (⊥ : SimpleGraph (Fin n)) (reverseOrder n) n :=
    fun _ => Or.inl ⟨Fin.rev, reverseEmbedding n, fun _ _ h => h.elim⟩
  apply le_antisymm (Nat.sInf_le (s := {k | OrderedRamseyProp ⊥ (reverseOrder n) k}) hn)
  change n ≤ orderedRamseyNumber ⊥ (reverseOrder n)
  have hk := Nat.sInf_mem (s := {k | OrderedRamseyProp ⊥ (reverseOrder n) k}) ⟨n, hn⟩
  change OrderedRamseyProp ⊥ (reverseOrder n) (orderedRamseyNumber ⊥ (reverseOrder n)) at hk
  rcases hk ⊥ with ⟨f, hf, _⟩ | ⟨f, hf, _⟩ <;>
    simpa using Fintype.card_le_of_injective f hf.1

example : conjecture := conjecture_holds

end MathlibExt.Combinatorics.OrderRobustOrderedRamseyWanted

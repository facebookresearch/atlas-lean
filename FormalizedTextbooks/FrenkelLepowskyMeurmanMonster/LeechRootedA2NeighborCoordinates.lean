/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2NeighborCount

/-! Actual catalogue coordinate criteria for the standard rooted A2 neighbor count. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact two-coordinate root condition on an original short-vector address. -/
abbrev leechRootedA2NeighborPredicate (r : GriessShortIndex) : Prop :=
  griessShortIntegral r 0 + griessShortIntegral r 1 = 4 ∨
    griessShortIntegral r 0 + griessShortIntegral r 1 = -4

/-- The original odd family meets the root precisely at an exceptional root coordinate. -/
theorem leechRootedA2Odd_neighbor_iff (d : Fin 2048) (j : Fin 24) :
    leechRootedA2NeighborPredicate (Sum.inr (Sum.inr (d, j))) ↔
      (golayEncodedMask d.val).testBit 0 ≠ (golayEncodedMask d.val).testBit 1 ∧
        (j = 0 ∨ j = 1) := by
  have h : ∀ (a b : Bool) (j : Fin 24),
      ((if a then (-1 : ℤ) else 1) * (if (0 : Fin 24) = j then -3 else 1) +
        (if b then (-1 : ℤ) else 1) * (if (1 : Fin 24) = j then -3 else 1) = 4 ∨
       (if a then (-1 : ℤ) else 1) * (if (0 : Fin 24) = j then -3 else 1) +
        (if b then (-1 : ℤ) else 1) * (if (1 : Fin 24) = j then -3 else 1) = -4) ↔
        a ≠ b ∧ (j = 0 ∨ j = 1) := by
    decide +kernel
  exact h _ _ j

/-- The actual original odd-coordinate neighbors. -/
abbrev leechRootedA2OddNeighbor :=
  {p : Fin 2048 × Fin 24 // leechRootedA2NeighborPredicate (Sum.inr (Sum.inr p))}

/-- The exceptional position is one of the two original root coordinates. -/
abbrev leechRootedA2RootPosition := {j : Fin 24 // j = 0 ∨ j = 1}

/-- The original coordinate criterion gives the full actual odd-family identification. -/
def leechRootedA2OddNeighborEquiv :
    leechRootedA2OddNeighbor ≃ leechRootedA2OddCode × leechRootedA2RootPosition :=
  (Equiv.subtypeEquivRight (fun p : Fin 2048 × Fin 24 =>
    leechRootedA2Odd_neighbor_iff p.1 p.2)).trans
      (@Equiv.subtypeProdEquivProd (Fin 2048) (Fin 24)
        (fun d => (golayEncodedMask d.val).testBit 0 ≠ (golayEncodedMask d.val).testBit 1)
        (fun j => j = 0 ∨ j = 1))

/-- There are exactly two genuine exceptional root positions. -/
theorem leechRootedA2RootPosition_card : Fintype.card leechRootedA2RootPosition = 2 := by
  decide +kernel

/-- Exactly2048 original odd short classes have the required root pairing. -/
theorem leechRootedA2OddNeighbor_card : Fintype.card leechRootedA2OddNeighbor = 2048 := by
  rw [Fintype.card_congr leechRootedA2OddNeighborEquiv, Fintype.card_prod,
    leechRootedA2OddCode_card, leechRootedA2RootPosition_card]

/-- A genuine pair short class meets the root exactly when one coordinate is outside its pair. -/
theorem leechRootedA2Pair_neighbor_iff (s : Fin 2) (p : Fin 276) :
    leechRootedA2NeighborPredicate (Sum.inl (s, p)) ↔
      (griessCoordinatePair p).1.val < 2 ∧ 2 ≤ (griessCoordinatePair p).2.val := by
  have h : ∀ (s : Fin 2) (a b : Fin 24), a < b → (
      ((4 * (if (0 : Fin 24) = a then (1 : ℤ) else 0) +
         (if s = 0 then (-4 : ℤ) else 4) * (if (0 : Fin 24) = b then 1 else 0)) +
       (4 * (if (1 : Fin 24) = a then (1 : ℤ) else 0) +
         (if s = 0 then (-4 : ℤ) else 4) * (if (1 : Fin 24) = b then 1 else 0)) = 4 ∨
       (4 * (if (0 : Fin 24) = a then (1 : ℤ) else 0) +
         (if s = 0 then (-4 : ℤ) else 4) * (if (0 : Fin 24) = b then 1 else 0)) +
       (4 * (if (1 : Fin 24) = a then (1 : ℤ) else 0) +
         (if s = 0 then (-4 : ℤ) else 4) * (if (1 : Fin 24) = b then 1 else 0)) = -4) ↔
        a.val < 2 ∧ 2 ≤ b.val) := by
    decide +kernel
  exact h s (griessCoordinatePair p).1 (griessCoordinatePair p).2
    (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2

/-- The actual coordinate pairs with one root coordinate and one outside coordinate. -/
abbrev leechRootedA2CoordinatePair :=
  {q : griessCoordinatePairs // q.val.1.val < 2 ∧ 2 ≤ q.val.2.val}

/-- The original signed-pair catalogue neighbors. -/
abbrev leechRootedA2PairNeighbor :=
  {p : Fin 2 × Fin 276 // leechRootedA2NeighborPredicate (Sum.inl p)}

/-- Actual ordered-pair indexing gives the full signed-pair family identification. -/
def leechRootedA2PairNeighborEquiv :
    leechRootedA2PairNeighbor ≃ Fin 2 × leechRootedA2CoordinatePair where
  toFun p := (p.val.1, ⟨griessCoordinatePairEquiv p.val.2,
    (leechRootedA2Pair_neighbor_iff p.val.1 p.val.2).mp p.property⟩)
  invFun p := ⟨(p.1, griessCoordinatePairEquiv.symm p.2.val), by
    apply (leechRootedA2Pair_neighbor_iff p.1 _).mpr
    have he : griessCoordinatePair (griessCoordinatePairEquiv.symm p.2.val) = p.2.val.val :=
      congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply p.2.val)
    simpa only [he] using p.2.property⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · exact griessCoordinatePairEquiv.symm_apply_apply p.val.2
  right_inv p := by
    refine Prod.ext ?_ ?_
    · rfl
    · apply Subtype.ext
      exact griessCoordinatePairEquiv.apply_symm_apply p.2.val

/-- Exactly44 actual unordered coordinate pairs meet the root once. -/
theorem leechRootedA2CoordinatePair_card : Fintype.card leechRootedA2CoordinatePair = 44 := by
  decide +kernel

/-- Exactly88 original signed-pair short classes have the required root pairing. -/
theorem leechRootedA2PairNeighbor_card : Fintype.card leechRootedA2PairNeighbor = 88 := by
  rw [Fintype.card_congr leechRootedA2PairNeighborEquiv, Fintype.card_prod,
    Fintype.card_fin, leechRootedA2CoordinatePair_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

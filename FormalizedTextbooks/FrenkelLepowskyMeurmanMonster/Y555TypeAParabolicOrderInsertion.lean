/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Descending insertion words and elementary type A relations. -/
module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The descending string of simple generators from k+m-1 down to k. -/
def typeAInsertion {G : Type*} [Group G] (s : ℕ → G) : ℕ → ℕ → G
  | _, 0 => 1
  | k, m + 1 => typeAInsertion s (k + 1) m * s k

/-- The three local relations for the first n simple generators of a type A chain. -/
structure TypeAChainRelations {G : Type*} [Group G] (s : ℕ → G) (n : ℕ) : Prop where
  /-- Every generator is an involution. -/
  square : ∀ i, i < n → s i * s i = 1
  /-- Nonadjacent simple generators commute. -/
  commute : ∀ i j, i < n → j < n → i + 1 < j → s i * s j = s j * s i
  /-- Adjacent simple generators obey the braid relation. -/
  braid : ∀ i, i + 1 < n → s i * s (i + 1) * s i = s (i + 1) * s i * s (i + 1)

variable {G : Type*} [Group G] {s : ℕ → G} {n : ℕ}

/-- Restricting a chain preserves all its relations. -/
theorem TypeAChainRelations.restrict (h : TypeAChainRelations s n) {m : ℕ} (hm : m ≤ n) :
    TypeAChainRelations s m where
  square i hi := h.square i (lt_of_lt_of_le hi hm)
  commute i j hi hj hij := h.commute i j (lt_of_lt_of_le hi hm)
    (lt_of_lt_of_le hj hm) hij
  braid i hi := h.braid i (lt_of_lt_of_le hi hm)

/-- A generator at distance at least two commutes with an entire descending string. -/
theorem typeAInsertion_commute_below (h : TypeAChainRelations s n)
    (k m j : ℕ) (hkm : k + m ≤ n) (hj : j + 1 < k) :
    typeAInsertion s k m * s j = s j * typeAInsertion s k m := by
  induction m generalizing k with
  | zero => simp [typeAInsertion]
  | succ m ih =>
    have hk : k < n := by omega
    have hjn : j < n := by omega
    simp only [typeAInsertion, mul_assoc]
    rw [← h.commute j k hjn hk hj, ← mul_assoc,
      ih (k + 1) (by omega) (by omega), mul_assoc]

/-- Multiplying a descending string by its last generator deletes that generator. -/
theorem typeAInsertion_cancel_last (h : TypeAChainRelations s n)
    (k m : ℕ) (hkm : k + (m + 1) ≤ n) :
    typeAInsertion s k (m + 1) * s k = typeAInsertion s (k + 1) m := by
  rw [typeAInsertion, mul_assoc, h.square k (by omega), mul_one]

/-- Right multiplication by an interior generator exits on the left one index lower. -/
theorem typeAInsertion_interior (h : TypeAChainRelations s n)
    (k m j : ℕ) (hkm : k + m ≤ n) (hkj : k < j) (hjm : j < k + m) :
    typeAInsertion s k m * s j = s (j - 1) * typeAInsertion s k m := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    by_cases hj : j = k + 1
    · subst j
      obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 :=
        ⟨m - 1, by omega⟩
      simp only [typeAInsertion]
      have hb := h.braid k (by omega)
      have hc := typeAInsertion_commute_below h (k + 1 + 1) r k (by omega) (by omega)
      simp only [Nat.add_sub_cancel]
      calc
        (typeAInsertion s (k + 1 + 1) r * s (k + 1) * s k) * s (k + 1) =
            typeAInsertion s (k + 1 + 1) r *
              (s (k + 1) * s k * s (k + 1)) := by group
        _ = typeAInsertion s (k + 1 + 1) r *
              (s k * s (k + 1) * s k) := by rw [hb]
        _ = s k * (typeAInsertion s (k + 1 + 1) r * s (k + 1) * s k) := by
          simp only [← mul_assoc]
          rw [hc]
    · have hdist : k + 1 < j := by omega
      rw [typeAInsertion, mul_assoc, h.commute k j (by omega) (by omega) hdist,
        ← mul_assoc, ih (k + 1) (by omega) (by omega) (by omega), mul_assoc]

/-- Right multiplication of an insertion representative produces a lower-rank generator
and another insertion representative, or only another representative. -/
theorem typeAInsertion_move (h : TypeAChainRelations s (n + 1))
    (k j : ℕ) (hk : k ≤ n + 1) (hj : j < n + 1) :
    ∃ l ≤ n + 1, ∃ a : G,
      (a = 1 ∨ ∃ i < n, a = s i) ∧
      typeAInsertion s k (n + 1 - k) * s j =
        a * typeAInsertion s l (n + 1 - l) := by
  by_cases hkn : k = n + 1
  · subst k
    by_cases hjn : j = n
    · subst j
      refine ⟨n, by omega, 1, Or.inl rfl, ?_⟩
      simp [typeAInsertion]
    · refine ⟨n + 1, le_rfl, s j, Or.inr ⟨j, by omega, rfl⟩, ?_⟩
      simp [typeAInsertion]
  · have hkn : k < n + 1 := by omega
    by_cases hbelow : j + 1 < k
    · refine ⟨k, hk, s j, Or.inr ⟨j, by omega, rfl⟩, ?_⟩
      exact typeAInsertion_commute_below h k _ j (by omega) hbelow
    · by_cases hextend : j + 1 = k
      · subst k
        refine ⟨j, by omega, 1, Or.inl rfl, ?_⟩
        have he : n + 1 - j = (n + 1 - (j + 1)) + 1 := by omega
        rw [he, typeAInsertion, one_mul]
      · by_cases hcancel : j = k
        · subst j
          refine ⟨k + 1, by omega, 1, Or.inl rfl, ?_⟩
          have he : n + 1 - k = (n + 1 - (k + 1)) + 1 := by omega
          rw [he, typeAInsertion_cancel_last h k _ (by omega), one_mul]
        · have hinside : k < j := by omega
          refine ⟨k, hk, s (j - 1), Or.inr ⟨j - 1, by omega, rfl⟩, ?_⟩
          exact typeAInsertion_interior h k _ j (by omega) hinside (by omega)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

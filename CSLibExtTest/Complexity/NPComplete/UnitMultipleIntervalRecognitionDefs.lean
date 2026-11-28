/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module


import CSLibExt.Complexity.NPComplete.UnitMultipleIntervalRecognitionDefs
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.UnitMultipleIntervalRecognition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (d : ℕ) (i : UnitMultipleIntervalRecognitionInstance) :
    unitMultipleIntervalRecognitionDec d (bitEncode i) = true ↔
      WellFormed i ∧ UnitMultipleIntervalRecognitionFeasible d i := by
  simp [unitMultipleIntervalRecognitionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every `d`. -/
example (d : ℕ) : unitMultipleIntervalRecognitionDec d [true] = false := by
  have h : bitDecode (α := UnitMultipleIntervalRecognitionInstance) [true] = none := rfl
  simp [unitMultipleIntervalRecognitionDec, h]

/-- Two unit intervals that share a point start at most one apart. -/
private theorem close_of_mem {a b x : ℝ} (ha : x ∈ Set.Icc a (a + 1))
    (hb : x ∈ Set.Icc b (b + 1)) : a ≤ b + 1 ∧ b ≤ a + 1 := by
  obtain ⟨h₁, h₂⟩ := ha
  obtain ⟨h₃, h₄⟩ := hb
  constructor <;> linarith

/-- Disjoint unit intervals start more than one apart. -/
private theorem far_of_disjoint {a b : ℝ}
    (h : Disjoint (Set.Icc a (a + 1)) (Set.Icc b (b + 1))) : a + 1 < b ∨ b + 1 < a := by
  by_contra hn
  rw [not_or, not_lt, not_lt] at hn
  rcases le_total a b with hab | hab
  · exact Set.disjoint_left.1 h ⟨hab, hn.1⟩ ⟨le_rfl, by linarith⟩
  · exact Set.disjoint_left.1 h ⟨le_rfl, by linarith⟩ ⟨hab, hn.2⟩

/-- Three pairwise disjoint unit intervals cannot all meet one unit interval. -/
private theorem no_three_meet {c a₁ a₂ a₃ : ℝ} (h₁ : a₁ ≤ c + 1 ∧ c ≤ a₁ + 1)
    (h₂ : a₂ ≤ c + 1 ∧ c ≤ a₂ + 1) (h₃ : a₃ ≤ c + 1 ∧ c ≤ a₃ + 1)
    (h₁₂ : a₁ + 1 < a₂ ∨ a₂ + 1 < a₁) (h₁₃ : a₁ + 1 < a₃ ∨ a₃ + 1 < a₁)
    (h₂₃ : a₂ + 1 < a₃ ∨ a₃ + 1 < a₂) : False := by
  rcases h₁₂ with h₁₂ | h₁₂ <;> rcases h₁₃ with h₁₃ | h₁₃ <;> rcases h₂₃ with h₂₃ | h₂₃ <;>
    linarith [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]

section Representation

variable {d n : ℕ} {H : SimpleGraph (Fin n)} {l : Fin n → Fin d → ℝ}
  (hiff : ∀ u v, u ≠ v →
    (H.Adj u v ↔ ((⋃ j, Set.Icc (l u j) (l u j + 1)) ∩ (⋃ j, Set.Icc (l v j) (l v j + 1))).Nonempty))
include hiff

/-- In a representation, adjacent vertices have a pair of meeting intervals. -/
private theorem meet_of_adj {u v : Fin n} (huv : u ≠ v) (h : H.Adj u v) :
    ∃ j k, l u j ≤ l v k + 1 ∧ l v k ≤ l u j + 1 := by
  obtain ⟨x, hx, hy⟩ := (hiff u v huv).1 h
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
  exact ⟨j, k, close_of_mem hj hk⟩

/-- In a representation, every interval of a vertex is disjoint from every interval of a
non-adjacent vertex. -/
private theorem far_of_not_adj {u v : Fin n} (huv : u ≠ v) (h : ¬ H.Adj u v) (j k : Fin d) :
    l u j + 1 < l v k ∨ l v k + 1 < l u j :=
  far_of_disjoint (Set.disjoint_left.2 fun x hx hy =>
    h ((hiff u v huv).2 ⟨x, Set.mem_iUnion.2 ⟨j, hx⟩, Set.mem_iUnion.2 ⟨k, hy⟩⟩))

end Representation

/-- A single edge is a unit interval graph: `[0, 1]` and `[1, 2]` meet at `1`. -/
example :
    unitMultipleIntervalRecognitionDec 1
      (bitEncode ((2, [(0, 1)]) : UnitMultipleIntervalRecognitionInstance)) = true := by
  apply (accepts_encoding 1 _).2
  refine ⟨by unfold WellFormed; decide, fun v _ => (v : ℝ), ?_, ?_⟩
  · intro v j j' hjj
    exact absurd (Subsingleton.elim j j') hjj
  · intro u v huv
    have key : ∀ u v : Fin 2, u ≠ v → (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by decide
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj, Set.Nonempty,
      Set.mem_inter_iff, Set.mem_iUnion, Set.mem_Icc]
    rcases key u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨fun _ => ⟨1, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩, fun _ => ⟨by decide, by decide⟩⟩

/-- The claw `K₁,₃`. -/
private abbrev claw : UnitMultipleIntervalRecognitionInstance := (4, [(0, 1), (0, 2), (0, 3)])

/-- The claw is not a unit interval graph: its three pairwise non-adjacent leaves would need
three pairwise disjoint unit intervals meeting the centre's interval. -/
example : unitMultipleIntervalRecognitionDec 1 (bitEncode claw) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, l, -, hiff⟩
  have hadj : ∀ t : Fin 3, (Graph claw).Adj 0 t.succ := by
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
    decide
  have hnadj : ∀ t t' : Fin 3, t ≠ t' → ¬ (Graph claw).Adj t.succ t'.succ := by
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
    decide
  have hmeet : ∀ t : Fin 3, l t.succ 0 ≤ l 0 0 + 1 ∧ l 0 0 ≤ l t.succ 0 + 1 := by
    intro t
    obtain ⟨j, k, h⟩ := meet_of_adj hiff (Fin.succ_ne_zero t).symm (hadj t)
    rw [Subsingleton.elim j 0, Subsingleton.elim k 0] at h
    exact ⟨h.2, h.1⟩
  have hfar : ∀ t t' : Fin 3, t ≠ t' →
      l t.succ 0 + 1 < l t'.succ 0 ∨ l t'.succ 0 + 1 < l t.succ 0 := fun t t' h =>
    far_of_not_adj hiff (fun e => h (Fin.succ_inj.1 e)) (hnadj t t' h) 0 0
  exact no_three_meet (hmeet 0) (hmeet 1) (hmeet 2) (hfar 0 1 (by decide)) (hfar 0 2 (by decide))
    (hfar 1 2 (by decide))

/-- Interval starts for the claw with two intervals per vertex: the centre uses `0` and `10`,
the leaves `1, 20`, `11, 30` and `-1, 40`. -/
private def starts : List (List ℤ) := [[0, 10], [1, 20], [11, 30], [-1, 40]]

/-- The interval starts as a representation. -/
private noncomputable def clawStarts (v : Fin 4) (j : Fin 2) : ℝ :=
  ((starts.getD v []).getD j 0 : ℤ)

/-- With two intervals per vertex the claw is representable: the centre meets the first and
third leaves with its first interval and the second leaf with its second interval. -/
example : unitMultipleIntervalRecognitionDec 2 (bitEncode claw) = true := by
  apply (accepts_encoding 2 _).2
  refine ⟨by unfold WellFormed; decide, clawStarts, ?_, ?_⟩
  · intro v j j' hjj
    have key : ∀ j j' : Fin 2, j ≠ j' → (j = 0 ∧ j' = 1) ∨ (j = 1 ∧ j' = 0) := by decide
    have hv : ∀ v : Fin 4, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by decide
    rw [Set.disjoint_left]
    rintro x ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    rcases key j j' hjj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hv v with rfl | rfl | rfl | rfl <;>
      simp [clawStarts, starts] at h₁ h₂ h₃ h₄ <;> linarith
  · intro u v huv
    have key : ∀ u v : Fin 4, u ≠ v →
        (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 3) ∨
        (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 1 ∧ v = 3) ∨
        (u = 2 ∧ v = 0) ∨ (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨
        (u = 3 ∧ v = 0) ∨ (u = 3 ∧ v = 1) ∨ (u = 3 ∧ v = 2) := by decide
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj, Set.Nonempty,
      Set.mem_inter_iff, Set.mem_iUnion, Fin.exists_fin_two, Set.mem_Icc]
    rcases key u v huv with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [clawStarts, starts]
      exact ⟨1, by norm_num⟩
    · simp [clawStarts, starts]
      exact ⟨11, by norm_num⟩
    · simp [clawStarts, starts]
      exact ⟨0, by norm_num⟩
    · simp [clawStarts, starts]
      exact ⟨1, by norm_num⟩
    · simp [clawStarts, starts]
      intro x h₁
      constructor <;> intro h₂ <;> rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> linarith
    · simp [clawStarts, starts]
      intro x h₁
      constructor <;> intro h₂ <;> rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> linarith
    · simp [clawStarts, starts]
      exact ⟨11, by norm_num⟩
    · simp [clawStarts, starts]
      intro x h₁
      constructor <;> intro h₂ <;> rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> linarith
    · simp [clawStarts, starts]
      intro x h₁
      constructor <;> intro h₂ <;> rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> linarith
    · simp [clawStarts, starts]
      exact ⟨0, by norm_num⟩
    · simp [clawStarts, starts]
      intro x h₁
      constructor <;> intro h₂ <;> rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> linarith
    · simp [clawStarts, starts]
      intro x h₁
      constructor <;> intro h₂ <;> rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> linarith

/-- The star `K₁,₅`. -/
private abbrev star5 : UnitMultipleIntervalRecognitionInstance :=
  (6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)])

/-- `K₁,₅` is not a unit `2`-interval graph: some three leaves meet the same interval of the
centre, and their meeting intervals are pairwise disjoint. -/
example : unitMultipleIntervalRecognitionDec 2 (bitEncode star5) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, l, -, hiff⟩
  have hadj : ∀ t : Fin 5, (Graph star5).Adj 0 t.succ := by
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
    decide
  have hnadj : ∀ t t' : Fin 5, t ≠ t' → ¬ (Graph star5).Adj t.succ t'.succ := by
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
    decide
  have hmeet : ∀ t : Fin 5, ∃ j k, l t.succ k ≤ l 0 j + 1 ∧ l 0 j ≤ l t.succ k + 1 := by
    intro t
    obtain ⟨j, k, h⟩ := meet_of_adj hiff (Fin.succ_ne_zero t).symm (hadj t)
    exact ⟨j, k, h.2, h.1⟩
  choose j k hjk using hmeet
  have hpigeon : ∀ f : Fin 5 → Fin 2,
      ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a = f b ∧ f a = f c := by decide
  obtain ⟨a, b, c, hab, hac, hbc, hjb, hjc⟩ := hpigeon j
  have hfar : ∀ t t' : Fin 5, t ≠ t' →
      l t.succ (k t) + 1 < l t'.succ (k t') ∨ l t'.succ (k t') + 1 < l t.succ (k t) :=
    fun t t' h => far_of_not_adj hiff (fun e => h (Fin.succ_inj.1 e)) (hnadj t t' h) _ _
  have hb := hjk b
  have hc := hjk c
  rw [← hjb] at hb
  rw [← hjc] at hc
  exact no_three_meet (hjk a) hb hc (hfar a b hab) (hfar a c hac) (hfar b c hbc)

/-- The rejected instances are well formed, so the rejections come from representability. -/
example : WellFormed claw ∧ WellFormed star5 := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.UnitMultipleIntervalRecognition

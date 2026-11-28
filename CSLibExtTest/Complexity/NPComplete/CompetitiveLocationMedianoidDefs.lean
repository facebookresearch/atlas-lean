/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CompetitiveLocationMedianoidDefs

namespace MetaMathlibExt.Complexity.NPComplete.CompetitiveLocationMedianoid

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Two vertices joined by an edge of length `1`, weights `5` and `3`, an existing facility at
vertex `1`, one new facility, and target `W`. -/
private abbrev med (W : ℕ) : CompetitiveLocationMedianoidInstance := (2, [(0, 1, 1)], [5, 3], [1], 1, W)

private theorem le_sum_of_mem {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.sum
  | b :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem h
      simp only [List.sum_cons]
      omega

/-- The customer at the existing facility `1` is never captured: the empty walk to `1` has
length `0`. -/
private theorem not_captured_one (W : ℕ) (Y : Finset (Fin (med W).1)) :
    ¬ Captured (med W) Y ⟨1, Nat.one_lt_two⟩ := by
  rintro ⟨y, -, p, hp⟩
  exact absurd (hp ⟨1, Nat.one_lt_two⟩ (by simp) SimpleGraph.Walk.nil) (by simp [walkLength])

/-- Every edge of the graph of `med 5` has length at least `1`. -/
private theorem edge_pos : ∀ e ∈ (Graph (med 5)).edgeSet, 1 ≤ edgeLength (med 5) e := by
  have key : ∀ a b : Fin 2, a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ endpoints (med 5) ∨
      ((b : ℕ), (a : ℕ)) ∈ endpoints (med 5)) → 1 ≤ edgeLength (med 5) s(a, b) := by
    decide
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact key a b ((SimpleGraph.fromRel_adj _ _ _).1 he)

/-- The new facility at vertex `0` captures the customer at `0`: every walk from `0` to the
existing facility `1` uses the edge of length `1`. -/
private theorem captured_zero : Captured (med 5) {⟨0, by decide⟩} ⟨0, by decide⟩ := by
  refine ⟨⟨0, by decide⟩, by simp, SimpleGraph.Walk.nil, fun x hx q => ?_⟩
  obtain rfl : x = ⟨1, by decide⟩ := Fin.ext (by simpa using hx)
  have hlen : 0 < q.edges.length := by
    rw [SimpleGraph.Walk.length_edges]
    exact Nat.pos_of_ne_zero fun h => absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) (by decide)
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hlen
  have h1 := edge_pos e (q.edges_subset_edgeSet he)
  have h2 := le_sum_of_mem (List.mem_map.2 ⟨e, he, rfl⟩ : edgeLength (med 5) e ∈
    q.edges.map (edgeLength (med 5)))
  simp only [walkLength, SimpleGraph.Walk.edges_nil, List.map_nil, List.sum_nil]
  omega

open Classical in
/-- With `Y = {0}` exactly the customer at `0` is captured. -/
private theorem captured_set :
    Finset.univ.filter (Captured (med 5) {⟨0, by decide⟩}) = {⟨0, by decide⟩} := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  have hv2 : (v : ℕ) < 2 := v.2
  rcases (by omega : (v : ℕ) = 0 ∨ (v : ℕ) = 1) with h | h
  · obtain rfl : v = ⟨0, by decide⟩ := Fin.ext h
    exact ⟨fun _ => rfl, fun _ => captured_zero⟩
  · obtain rfl : v = ⟨1, by decide⟩ := Fin.ext h
    exact ⟨fun hc => absurd hc (not_captured_one 5 _), fun hv => absurd hv (by decide)⟩

/-- The decision problem accepts target `5`: the facility at `0` captures weight `5`. -/
example : competitiveLocationMedianoidDec (bitEncode (med 5)) = true := by
  have hw : WellFormed (med 5) := by unfold WellFormed endpoints; decide
  have hf : CompetitiveLocationMedianoidFeasible (med 5) := by
    refine ⟨{⟨0, by decide⟩}, rfl, ?_⟩
    rw [captured_set]
    simp [weight]
  simp [competitiveLocationMedianoidDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed target `6`: only the customer at `0`, of weight
`5`, can ever be captured. -/
example : WellFormed (med 6) ∧ competitiveLocationMedianoidDec (bitEncode (med 6)) = false := by
  have hf : ¬ CompetitiveLocationMedianoidFeasible (med 6) := by
    rintro ⟨Y, -, hW⟩
    classical
    have hsub : Finset.univ.filter (Captured (med 6) Y) ⊆ {⟨0, by decide⟩} := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hv2 : (v : ℕ) < 2 := v.2
      rcases (by omega : (v : ℕ) = 0 ∨ (v : ℕ) = 1) with h | h
      · exact Finset.mem_singleton.2 (Fin.ext h)
      · obtain rfl : v = ⟨1, by decide⟩ := Fin.ext h
        exact absurd hv (not_captured_one 6 Y)
    rcases Finset.subset_singleton_iff.1 hsub with h | h <;> rw [h] at hW <;> simp [weight] at hW
  exact ⟨by unfold WellFormed endpoints; decide,
    by simp [competitiveLocationMedianoidDec, bitDecode_bitEncode, hf]⟩

/-- A zero edge length is malformed, although one new facility trivially meets the target `0`. -/
example :
    CompetitiveLocationMedianoidFeasible
        ((2, [(0, 1, 0)], [5, 3], [1], 1, 0) : CompetitiveLocationMedianoidInstance) ∧
      competitiveLocationMedianoidDec
        (bitEncode ((2, [(0, 1, 0)], [5, 3], [1], 1, 0) : CompetitiveLocationMedianoidInstance)) =
          false := by
  have hw : ¬ WellFormed ((2, [(0, 1, 0)], [5, 3], [1], 1, 0) :
      CompetitiveLocationMedianoidInstance) := by
    unfold WellFormed endpoints; decide
  exact ⟨⟨{⟨0, by decide⟩}, rfl, Nat.zero_le _⟩,
    by simp [competitiveLocationMedianoidDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : competitiveLocationMedianoidDec [true] = false := by
  have h : bitDecode (α := CompetitiveLocationMedianoidInstance) [true] = none := rfl
  simp [competitiveLocationMedianoidDec, h]

end MetaMathlibExt.Complexity.NPComplete.CompetitiveLocationMedianoid

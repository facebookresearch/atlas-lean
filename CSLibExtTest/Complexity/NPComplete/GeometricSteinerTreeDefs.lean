/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeometricSteinerTreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeometricSteinerTree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GeometricTravelingSalesman (point toInt discreteDist)

private theorem dec_bitEncode (i : GeometricSteinerTreeInstance) :
    geometricSteinerTreeDec (bitEncode i) = true ↔
      WellFormed i ∧ GeometricSteinerTreeFeasible i := by
  simp [geometricSteinerTreeDec, bitDecode_bitEncode]

/-- A graph whose vertices are all among `x` and `y` has no cycle: a cycle needs three distinct
vertices. -/
private theorem isAcyclic_of_two {V : Type*} (G : SimpleGraph V) (x y : V)
    (hall : ∀ v, v = x ∨ v = y) : G.IsAcyclic := by
  intro v c hc
  have h3 := hc.isCircuit.three_le_length
  have hsub : c.support.tail ⊆ [x, y] := fun w _ => by rcases hall w with rfl | rfl <;> simp
  have hl := (List.subperm_of_subset hc.support_nodup hsub).length_le
  simp only [List.length_tail, SimpleGraph.Walk.length_support, List.length_cons,
    List.length_nil] at hl
  omega

/-- An edge `x y` on a vertex type with no other vertices is a tree. -/
private theorem isTree_of_two {V : Type*} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (hall : ∀ v, v = x ∨ v = y) : G.IsTree := by
  refine ⟨(SimpleGraph.connected_iff G).2 ⟨fun u v => ?_, ⟨x⟩⟩, isAcyclic_of_two G x y hall⟩
  rcases hall u with rfl | rfl <;> rcases hall v with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hxy.reachable
  · exact hxy.symm.reachable
  · exact SimpleGraph.Reachable.refl _

/-- A tree on two vertices `x ≠ y` has exactly the edge `{x, y}`. -/
private theorem edgeSet_of_two {V : Type*} (T : SimpleGraph V) (hT : T.IsTree) (x y : V)
    (hne : x ≠ y) (hall : ∀ v, v = x ∨ v = y) : T.edgeSet = {s(x, y)} := by
  have hxy : T.Adj x y := by
    obtain ⟨p⟩ := hT.1.preconnected x y
    have hsnd := SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne (p := p) hne)
    rcases hall p.snd with h | h
    · exact absurd h.symm hsnd.ne
    · rwa [h] at hsnd
  ext e
  induction e using Sym2.ind with
  | _ u w =>
    rw [SimpleGraph.mem_edgeSet, Set.mem_singleton_iff]
    constructor
    · intro huw
      have := huw.ne
      rcases hall u with rfl | rfl <;> rcases hall w with rfl | rfl <;>
        first | exact absurd rfl this | rfl | exact Sym2.eq_swap
    · intro h
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm

/-- The edge finset of a tree on two vertices, for whichever `Fintype` instance it is built
with. -/
private theorem edgeFinset_of_two {V : Type*} (T : SimpleGraph V) {_ : Fintype T.edgeSet}
    (hT : T.IsTree) (x y : V) (hne : x ≠ y) (hall : ∀ v, v = x ∨ v = y) :
    T.edgeFinset = {s(x, y)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, edgeSet_of_two _ hT x y hne hall]
  simp

/-- Distinct integer points are at discretized distance at least `1`. -/
private theorem one_le_discreteDist {p q : ℤ × ℤ} (h : p ≠ q) : 1 ≤ discreteDist p q := by
  have hpos : 0 < (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
    refine lt_of_le_of_ne (by positivity) fun h0 => h ?_
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h0.symm
    exact Prod.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))
      (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))
  unfold discreteDist
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.lt_ceil, Nat.cast_zero, Real.sqrt_pos]
  exact_mod_cast hpos

open Classical in
/-- Points `(0, 0)` and `(1, 0)` with `B = 1`: with no Steiner points, the single segment of
length `1` is a spanning tree. -/
example :
    geometricSteinerTreeDec
      (bitEncode (([((0, 0), (0, 0)), ((1, 0), (0, 0))], 1) : GeometricSteinerTreeInstance)) =
        true := by
  rw [dec_bitEncode]
  have hmem : ∀ x, x ∈ points ([((0, 0), (0, 0)), ((1, 0), (0, 0))], 1) ∪ ∅ ↔
      x = (0, 0) ∨ x = (1, 0) := by
    intro x
    simp [points, point, toInt]
  let a : {x // x ∈ points ([((0, 0), (0, 0)), ((1, 0), (0, 0))], 1) ∪ ∅} :=
    ⟨(0, 0), (hmem _).2 (Or.inl rfl)⟩
  let b : {x // x ∈ points ([((0, 0), (0, 0)), ((1, 0), (0, 0))], 1) ∪ ∅} :=
    ⟨(1, 0), (hmem _).2 (Or.inr rfl)⟩
  have hall : ∀ v, v = a ∨ v = b := by
    rintro ⟨v, hv⟩
    rcases (hmem v).1 hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hab : a ≠ b := by simp [a, b]
  have htree := isTree_of_two (⊤ : SimpleGraph _) a b ((SimpleGraph.top_adj _ _).2 hab) hall
  refine ⟨by unfold WellFormed; decide, ∅, ⊤, htree, ?_⟩
  rw [edgeFinset_of_two _ htree a b hab hall, Finset.sum_singleton]
  simp only [a, b, Sym2.map_mk, edgeLength, Sym2.lift_mk, discreteDist]
  norm_num

open Classical in
/-- Points `(0, 0)` and `(2, 0)` with `B = 1`: the direct segment has length `2`, and a tree
through any Steiner point has at least two edges of length at least `1`. -/
example :
    geometricSteinerTreeDec
      (bitEncode (([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1) : GeometricSteinerTreeInstance)) =
        false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, Q, T, hT, hw⟩
  have ha : ((0, 0) : ℤ × ℤ) ∈ points ([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1) ∪ Q := by
    simp [points, point, toInt]
  have hb : ((2, 0) : ℤ × ℤ) ∈ points ([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1) ∪ Q := by
    simp [points, point, toInt]
  let a : {x // x ∈ points ([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1) ∪ Q} := ⟨(0, 0), ha⟩
  let b : {x // x ∈ points ([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1) ∪ Q} := ⟨(2, 0), hb⟩
  have hab : a ≠ b := by simp [a, b]
  have hlen : ∀ e ∈ T.edgeFinset, 1 ≤ edgeLength (e.map Subtype.val) := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u w =>
      have hne : u.1 ≠ w.1 := fun h => (SimpleGraph.mem_edgeSet T).1 he |>.ne (Subtype.ext h)
      simpa [edgeLength] using one_le_discreteDist hne
  by_cases hall : ∀ v, v = a ∨ v = b
  · rw [edgeFinset_of_two _ hT a b hab hall, Finset.sum_singleton] at hw
    revert hw
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp [a, b, edgeLength, discreteDist, h4]
  · simp only [not_forall, not_or] at hall
    obtain ⟨c, hca, hcb⟩ := hall
    have hcard3 : 2 < Fintype.card
        {x // x ∈ points ([((0, 0), (0, 0)), ((2, 0), (0, 0))], 1) ∪ Q} := by
      rw [← Finset.card_univ, Finset.two_lt_card]
      exact ⟨a, Finset.mem_univ _, b, Finset.mem_univ _, c, Finset.mem_univ _,
        hab, Ne.symm hca, Ne.symm hcb⟩
    have hcard := hT.card_edgeFinset
    have hsum := Finset.card_nsmul_le_sum _ _ 1 hlen
    simp only [smul_eq_mul, mul_one] at hsum
    omega

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeometricSteinerTreeInstance) bits = none) :
    geometricSteinerTreeDec bits = false := by
  simp [geometricSteinerTreeDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : geometricSteinerTreeDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeometricSteinerTree

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted bounded-width CNF reduces to consistency of small bags

Place the `k` chosen variables in increasing order. A negative literal is
falsified by one chosen position. The absence of a positive literal can be
witnessed by at most two positions, bracketing the gap where its variable would
have occurred. Thus every false clause of width at most `d` is locally witnessed
on at most `2*d` positions. This works also at either end of the order.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.WeightedClauses

/-- Sets of selection slots small enough to check ordering or a clause of the given width. -/
abbrev Bag (k width : ℕ) := {s : Finset (Fin k) // s.card ≤ max 2 width}

variable {V : Type*} [LinearOrder V] {k : ℕ}

/-- A pair records a variable and its polarity; `true` denotes a positive literal. -/
def literalTrue (selected : Set V) (lit : V × Bool) : Prop :=
  if lit.2 then lit.1 ∈ selected else lit.1 ∉ selected

/-- Local certificate that a literal is false. For a positive literal, every slot
is on one of the two outside portions certified by a value strictly below or
above the missing variable. -/
def forcesFalse (b : Finset (Fin k)) (p : b → V) (lit : V × Bool) : Prop :=
  if lit.2 then ∀ i : Fin k, ∃ j : b,
    (i ≤ j.val ∧ p j < lit.1) ∨ (j.val ≤ i ∧ lit.1 < p j)
  else ∃ j : b, p j = lit.1

private theorem forcesFalse_sound (a : Fin k → V) (ha : StrictMono a)
    (b : Finset (Fin k)) (lit : V × Bool)
    (h : forcesFalse b (fun i => a i.val) lit) : ¬ literalTrue (Set.range a) lit := by
  obtain ⟨v, pos⟩ := lit
  cases pos with
  | false =>
    obtain ⟨i, hi⟩ := h
    exact fun hn => hn ⟨i.val, hi⟩
  | true =>
    rintro ⟨i, rfl⟩
    obtain ⟨j, h | h⟩ := h i
    · exact (h.2.not_ge (ha.monotone h.1))
    · exact (h.2.not_ge (ha.monotone h.1))

private theorem forcesFalse_mono (a : Fin k → V) {b c : Finset (Fin k)} (hbc : b ⊆ c)
    (lit : V × Bool) (h : forcesFalse b (fun i => a i.val) lit) :
    forcesFalse c (fun i => a i.val) lit := by
  obtain ⟨v, pos⟩ := lit
  cases pos with
  | false =>
    obtain ⟨j, hj⟩ := h
    exact ⟨⟨j.val, hbc j.property⟩, hj⟩
  | true =>
    intro i
    obtain ⟨j, hj⟩ := h i
    exact ⟨⟨j.val, hbc j.property⟩, hj⟩

private theorem upperMarker {I : Type*} [LinearOrder I] (s : Finset I) :
    ∃ b : Finset I, b.card ≤ 1 ∧ ∀ i ∈ s, ∃ j ∈ b, i ≤ j ∧ j ∈ s := by
  by_cases hs : s.Nonempty
  · refine ⟨{s.max' hs}, by simp, fun i hi => ⟨_, by simp, s.le_max' i hi, s.max'_mem hs⟩⟩
  · exact ⟨∅, by simp, fun i hi => (hs ⟨i, hi⟩).elim⟩

private theorem lowerMarker {I : Type*} [LinearOrder I] (s : Finset I) :
    ∃ b : Finset I, b.card ≤ 1 ∧ ∀ i ∈ s, ∃ j ∈ b, j ≤ i ∧ j ∈ s := by
  by_cases hs : s.Nonempty
  · refine ⟨{s.min' hs}, by simp, fun i hi => ⟨_, by simp, s.min'_le i hi, s.min'_mem hs⟩⟩
  · exact ⟨∅, by simp, fun i hi => (hs ⟨i, hi⟩).elim⟩

private theorem small_false_witness (a : Fin k → V) (lit : V × Bool)
    (h : ¬ literalTrue (Set.range a) lit) :
    ∃ b : Finset (Fin k), b.card ≤ 2 ∧ forcesFalse b (fun i => a i.val) lit := by
  classical
  obtain ⟨v, pos⟩ := lit
  cases pos with
  | false =>
    have hv : v ∈ Set.range a := by simpa [literalTrue] using h
    obtain ⟨j, rfl⟩ := hv
    exact ⟨{j}, by simp, ⟨j, by simp⟩, rfl⟩
  | true =>
    let lo := Finset.univ.filter (fun i => a i < v)
    let hi := Finset.univ.filter (fun i => v < a i)
    obtain ⟨l, hl, hlast⟩ := upperMarker lo
    obtain ⟨r, hr, hfirst⟩ := lowerMarker hi
    refine ⟨l ∪ r, (Finset.card_union_le _ _).trans (by omega), fun i => ?_⟩
    rcases lt_or_gt_of_ne (show a i ≠ v from fun e => h ⟨i, e⟩) with hlt | hgt
    · obtain ⟨j, hj, hij, hjv⟩ := hlast i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      exact ⟨⟨j, Finset.mem_union_left _ hj⟩, Or.inl ⟨hij, (Finset.mem_filter.mp hjv).2⟩⟩
    · obtain ⟨j, hj, hji, hvj⟩ := hfirst i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
      exact ⟨⟨j, Finset.mem_union_right _ hj⟩, Or.inr ⟨hji, (Finset.mem_filter.mp hvj).2⟩⟩

/-- Suppose the `k` selected variables are listed in strictly increasing order and each
clause contains at most `d` distinct literals. The selection satisfies every clause if and only
if no set of at most `max 2 (2 * d)` selection positions witnesses the falsity of all the
literals of a single clause. -/
theorem all_bags_iff_models (d : ℕ) (a : Fin k → V) (inc : StrictMono a)
    (p : List (List (V × Bool))) (width : ∀ c ∈ p, c.toFinset.card ≤ d) :
    (∀ b : Bag k (2 * d), ∀ c ∈ p,
      ¬ ∀ l ∈ c, forcesFalse b.val (fun i => a i.val) l) ↔
      ∀ c ∈ p, ∃ l ∈ c, literalTrue (Set.range a) l := by
  classical
  constructor
  · intro h c hc
    by_contra missing
    have hf (l : c.toFinset) : ¬ literalTrue (Set.range a) l.val :=
      fun ht => missing ⟨l.val, List.mem_toFinset.mp l.property, ht⟩
    choose witness size failure using
      fun l : c.toFinset => small_false_witness a l.val (hf l)
    let s := Finset.univ.biUnion witness
    have hsize : s.card ≤ 2 * d :=
      (Finset.card_biUnion_le_card_mul _ _ 2 fun i _ => size i).trans
        (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 (width c hc))
    apply h ⟨s, hsize.trans (le_max_right ..)⟩ c hc
    intro l hl
    let i : c.toFinset := ⟨l, List.mem_toFinset.mpr hl⟩
    exact forcesFalse_mono a (Finset.subset_biUnion_of_mem witness (Finset.mem_univ i))
      l (failure i)
  · intro h b c hc bad
    obtain ⟨l, hl, ht⟩ := h c hc
    exact (forcesFalse_sound a inc _ l (bad l hl)) ht

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.WeightedClauses

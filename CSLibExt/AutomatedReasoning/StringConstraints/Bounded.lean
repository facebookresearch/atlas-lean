/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounded string constraints are decidable: the HAMPI algorithm
-/
module

public import CSLibExt.AutomatedReasoning.StringConstraints.Syntax
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.Ring

/-!
# Bounded string constraints are decidable: the HAMPI algorithm

HAMPI's core idea: bound the length of every string variable, then the
search space is finite and satisfiability is decidable by explicit
enumeration. This module formalizes that bounded-search idea (HAMPI
itself reduces to bit-vector constraints rather than enumerating) and
proves it sound and complete, together with a bound on the number of
candidate assignments it checks.

`boundedSatB vs φ B` enumerates every assignment of the variables in
`vs` to words of length at most `B` and checks `φ` on each one.

## Cost model

Cost is stated as a bound on the number of candidate assignments
(`assignLists_length`): at most `(|Σ| + 1) ^ (B * |vs|)`. This is a
combinatorial bound on the enumeration, not a `TimeM` time bound;
`TimeM` accounting for the checker is future work.

The enumeration functions are `noncomputable` because enumerating an
arbitrary `Fintype` uses choice (`Finset.toList`); the decidability
content is the proved `boundedSatB_iff`, not executability.
`boundedSatB_iff` is a classical soundness/completeness statement; no
executable decision procedure is provided.

## Main results

- `boundedSatB_iff`: soundness and completeness of the bounded solver.
- `assignLists_length`: the candidate-count bound.
- `wordsUpTo_length`: the number of words of length at most `B`
  (counted with multiplicity) is `(|Σ| + 1) ^ B`.

## References

* A. Kieżun, V. Ganesh, S. Artzi, P. J. Guo, P. Hooimeijer, M. D. Ernst,
  *HAMPI: A Solver for Word Equations over Strings, Regular
  Expressions, and Context-Free Grammars*, ACM TOSEM 21(4), Nov 2012,
  pp. 25:1–25:28. HAMPI bounds string lengths and reduces to bit-vector
  constraints; here the finite search is carried out directly.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

/-- The keys of the association list built from an assignment are the
variables themselves. -/
theorem map_fst_map_pair {α : Type*} {V : Type*} {vs : List V} {σ : V → List α} :
    (vs.map fun i => (i, σ i)).map Prod.fst = vs := by
  induction vs with
  | nil => rfl
  | cons j vs ih => simp [List.map_cons, ih]

section Words

variable {α : Type*} [Fintype α]

/-- All words of length at most `B` over a finite alphabet, listed with
multiplicity. -/
noncomputable def wordsUpTo : ℕ → List (List α)
  | 0 => [[]]
  | B + 1 =>
    wordsUpTo B ++
      (wordsUpTo B).flatMap (fun w =>
        (Finset.univ : Finset α).toList.map (fun a => w ++ [a]))

/-- The empty word is enumerated at every bound. -/
theorem nil_mem_wordsUpTo (B : ℕ) : [] ∈ wordsUpTo (α := α) B := by
  induction B with
  | zero => simp [wordsUpTo]
  | succ B ih => simp [wordsUpTo, ih, List.mem_append]

/-- Membership in the enumeration is exactly the length bound. -/
theorem mem_wordsUpTo {w : List α} {B : ℕ} :
    w ∈ wordsUpTo (α := α) B ↔ w.length ≤ B := by
  induction B generalizing w with
  | zero =>
    simp [wordsUpTo, List.length_eq_zero_iff]
  | succ B ih =>
    constructor
    · intro h
      rw [wordsUpTo, List.mem_append] at h
      rcases h with h | h
      · have := ih.mp h; omega
      · rw [List.mem_flatMap] at h
        obtain ⟨w', hw', hw⟩ := h
        rw [List.mem_map] at hw
        obtain ⟨a, _, rfl⟩ := hw
        have := ih.mp hw'
        simp only [List.length_append, List.length_singleton] at *
        omega
    · intro h
      rw [wordsUpTo, List.mem_append]
      by_cases hw : w = []
      · exact Or.inl (hw ▸ nil_mem_wordsUpTo B)
      · have hne : w ≠ [] := hw
        obtain ⟨w', a, rfl⟩ : ∃ w' a, w = w' ++ [a] := by
          refine ⟨w.dropLast, w.getLast hne, ?_⟩
          exact (List.dropLast_append_getLast hne).symm
        apply Or.inr
        rw [List.mem_flatMap]
        refine ⟨w', ?_, ?_⟩
        · apply ih.mpr
          have hlen : (w' ++ [a]).length ≤ B + 1 := h
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        · rw [List.mem_map]
          exact ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩

/-- Summing a constant over a list. -/
theorem sum_map_const {β : Type*} {l : List β} {c : ℕ} :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons _ l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Counting the enumeration: `(|Σ| + 1) ^ B` words with multiplicity. -/
theorem wordsUpTo_length (B : ℕ) :
    (wordsUpTo (α := α) B).length = (Fintype.card α + 1) ^ B := by
  induction B with
  | zero => simp [wordsUpTo]
  | succ B ih =>
    have hterm : ∀ w : List α,
        ((Finset.univ : Finset α).toList.map (fun a => w ++ [a])).length
          = Fintype.card α := by
      intro w
      simp [List.length_map, Finset.length_toList]
    have hmap : (wordsUpTo (α := α) B).map
        (fun w => ((Finset.univ : Finset α).toList.map (fun a => w ++ [a])).length)
        = (wordsUpTo (α := α) B).map (fun _ => Fintype.card α) := by
      congr 1
      funext w
      exact hterm w
    have hsum : ((wordsUpTo (α := α) B).map
        (fun w => ((Finset.univ : Finset α).toList.map
          (fun a => w ++ [a])).length)).sum
        = (Fintype.card α + 1) ^ B * Fintype.card α := by
      rw [hmap, sum_map_const, ih]
    rw [wordsUpTo, List.length_append, List.length_flatMap, ih, hsum, pow_succ]
    ring

end Words

section Lookup

variable {α : Type*} {V : Type*} [DecidableEq V]

/-- Lookup in an association list; unbound variables read as `[]`. -/
def getVal : List (V × List α) → V → List α
  | [], _ => []
  | (i, w) :: l, j => if j = i then w else getVal l j

/-- A lookup returns one of the values in the list, so it inherits the
length bound on values. -/
theorem getVal_length_le {l : List (V × List α)} {i : V} {B : ℕ}
    (hvalues : ∀ w ∈ l.map Prod.snd, w.length ≤ B) (hkeys : i ∈ l.map Prod.fst) :
    (getVal l i).length ≤ B := by
  induction l with
  | nil => simp at hkeys
  | cons p l ih =>
    obtain ⟨j, w⟩ := p
    have hw : w.length ≤ B := hvalues w List.mem_cons_self
    have hi' : i = j ∨ i ∈ l.map Prod.fst := by
      have hmem := hkeys
      simp only [List.map_cons, List.mem_cons] at hmem
      exact hmem
    change (if i = j then w else getVal l i).length ≤ B
    split_ifs with h
    · subst h
      exact hw
    · exact ih (fun w' hw' =>
        hvalues w' (List.mem_cons_of_mem w hw')) (Or.resolve_left hi' h)

/-- Lookup in the association list built from an assignment returns the
assignment. -/
theorem getVal_map {σ : V → List α} {vs : List V} {i : V} (hi : i ∈ vs) :
    getVal (vs.map fun j => (j, σ j)) i = σ i := by
  induction vs with
  | nil => simp at hi
  | cons j vs ih =>
    have hi' : i = j ∨ i ∈ vs := by
      have hmem := hi
      simp only [List.mem_cons] at hmem
      exact hmem
    change (if i = j then σ j else getVal (vs.map fun k => (k, σ k)) i) = σ i
    split_ifs with h
    · subst h
      simp
    · exact ih (Or.resolve_left hi' h)

end Lookup

section Assignments

variable {α : Type*} {V : Type*} [Fintype α]

/-- All assignments of the variables in `vs` to words of length at most
`B`, as association lists, listed with multiplicity (as in `wordsUpTo`). -/
noncomputable def assignLists : List V → ℕ → List (List (V × List α))
  | [], _ => [[]]
  | i :: vs, B => (assignLists vs B).flatMap
      (fun l => (wordsUpTo B).map (fun w => (i, w) :: l))

/-- Membership in the assignment enumeration: the keys are exactly `vs`
and every value has length at most `B`. -/
theorem mem_assignLists {vs : List V} {l : List (V × List α)} {B : ℕ} :
    l ∈ assignLists vs B ↔
      l.map Prod.fst = vs ∧ ∀ w ∈ l.map Prod.snd, w.length ≤ B := by
  induction vs generalizing l with
  | nil =>
    constructor
    · intro h
      simp only [assignLists, List.mem_singleton] at h
      subst h
      exact ⟨rfl, by simp⟩
    · intro h
      obtain ⟨hkeys, _⟩ := h
      have hl : l = [] := List.map_eq_nil_iff.mp hkeys
      simp [assignLists, hl]
  | cons i vs ih =>
    constructor
    · intro h
      rw [assignLists, List.mem_flatMap] at h
      obtain ⟨l', hl', hl⟩ := h
      rw [List.mem_map] at hl
      obtain ⟨w, hw, rfl⟩ := hl
      obtain ⟨hkeys, hvals⟩ := ih.mp hl'
      refine ⟨?_, ?_⟩
      · simp [hkeys]
      · intro w' hw'
        simp only [List.map_cons, List.mem_cons] at hw'
        rcases hw' with rfl | hw'
        · exact mem_wordsUpTo.mp hw
        · exact hvals w' hw'
    · intro h
      obtain ⟨hkeys, hvals⟩ := h
      cases l with
      | nil => simp at hkeys
      | cons p l' =>
        obtain ⟨j, w⟩ := p
        simp only [List.map_cons, List.cons.injEq] at hkeys
        obtain ⟨rfl, hkeys'⟩ := hkeys
        have hw : w.length ≤ B := hvals w (by simp)
        have hvals' : ∀ w' ∈ l'.map Prod.snd, w'.length ≤ B :=
          fun w' hw' => hvals w' (List.mem_cons_of_mem w hw')
        have hl' : l' ∈ assignLists vs B := ih.mpr ⟨hkeys', hvals'⟩
        rw [assignLists, List.mem_flatMap]
        exact ⟨l', hl', by
          rw [List.mem_map]
          exact ⟨w, mem_wordsUpTo.mpr hw, rfl⟩⟩

/-- Counting the assignment enumeration. -/
theorem assignLists_length (vs : List V) (B : ℕ) :
    (assignLists (α := α) vs B).length = (Fintype.card α + 1) ^ (B * vs.length) := by
  induction vs with
  | nil => simp [assignLists]
  | cons i vs ih =>
    have hexp : B * (i :: vs).length = B * vs.length + B := by
      simp [List.length_cons, Nat.mul_succ]
    have hterm : ∀ l : List (V × List α),
        ((wordsUpTo (α := α) B).map (fun w => (i, w) :: l)).length
          = (Fintype.card α + 1) ^ B := by
      intro l
      rw [List.length_map, wordsUpTo_length]
    have hmap : (assignLists (α := α) vs B).map
        (fun l => ((wordsUpTo (α := α) B).map (fun w => (i, w) :: l)).length)
        = (assignLists (α := α) vs B).map (fun _ => (Fintype.card α + 1) ^ B) := by
      congr 1
      funext l
      exact hterm l
    have hsum : ((assignLists (α := α) vs B).map
        (fun l => ((wordsUpTo (α := α) B).map (fun w => (i, w) :: l)).length)).sum
        = (Fintype.card α + 1) ^ (B * vs.length) * (Fintype.card α + 1) ^ B := by
      rw [hmap, sum_map_const, ih]
    rw [assignLists, List.length_flatMap, hexp, pow_add, hsum]

end Assignments

section Solver

variable {α : Type*} {V : Type*} [Fintype α] [DecidableEq α] [DecidableEq V]

/-- The bounded solver: enumerate bounded assignments and check `φ` on
each one. -/
noncomputable def boundedSatB (vs : List V) (φ : Formula α V) (B : ℕ) : Bool :=
  (assignLists vs B).any (fun l => satB (getVal l) φ)

/-- Soundness and completeness of the bounded solver: it reports `true`
exactly when `φ` has a solution whose values on `vs` have length at
most `B`. The hypothesis is that `vs` covers the variables of `φ`. -/
theorem boundedSatB_iff (vs : List V) (φ : Formula α V) (B : ℕ)
    (hvars : ∀ i ∈ varsOfFormula φ, i ∈ vs) :
    boundedSatB vs φ B = true ↔
      ∃ σ : V → List α, (∀ i ∈ vs, (σ i).length ≤ B) ∧ Sat σ φ := by
  constructor
  · intro h
    rw [boundedSatB, List.any_eq_true] at h
    obtain ⟨l, hl, hsat⟩ := h
    obtain ⟨hkeys, hvals⟩ := mem_assignLists.mp hl
    refine ⟨getVal l, ?_, satB_iff.mp hsat⟩
    intro i hi
    exact getVal_length_le hvals (by rw [hkeys]; exact hi)
  · rintro ⟨σ, hbound, hsat⟩
    rw [boundedSatB, List.any_eq_true]
    refine ⟨vs.map fun i => (i, σ i), ?_, ?_⟩
    · rw [mem_assignLists]
      refine ⟨?_, ?_⟩
      · exact map_fst_map_pair
      · intro w hw
        rw [List.mem_map] at hw
        obtain ⟨x, hx, rfl⟩ := hw
        rw [List.mem_map] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact hbound i hi
    · rw [satB_iff]
      exact (sat_congr (fun i hi => getVal_map (hvars i hi))).mpr hsat

end Solver

end Cslib.AutomatedReasoning.StringConstraints

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounded string constraints: finite-search specification
-/
module

public import CSLibExt.AutomatedReasoning.StringConstraints.Syntax
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.Ring

/-!
# Bounded string constraints: finite-search specification

Bound the length of every string variable, then the search space is
finite. This module formalizes that bounded-search idea as a classical
specification (HAMPI itself reduces to bit-vector constraints rather
than enumerating) and proves it sound and complete, together with the
exact number of candidate assignments it checks.

`boundedSatSpec vs φ B` enumerates every assignment of the variables in
`vs` to words of length at most `B` and checks `φ` on each one.

## Cost model

Cost is stated as the exact number of candidate assignments
(`assignLists_length`): `(∑_{n ≤ B} |Σ|^n) ^ |vs|`. This is a
combinatorial count of the enumeration, not a `TimeM` time bound;
`TimeM` accounting for the checker is future work.

The enumeration functions are `noncomputable` because enumerating an
arbitrary `Fintype` uses choice (`Finset.toList`); the content is the
proved `boundedSatSpec_iff`, not executability.
`boundedSatSpec_iff` is a classical soundness/completeness statement; no
executable decision procedure, solver, or decidability result is
provided. The exact-length layers of `wordsUpTo` enumerate each word
once, so the search does not repeat candidate assignments.

## Main results

- `boundedSatSpec_iff`: soundness and completeness of the bounded-search
  specification.
- `assignLists_length`: the exact candidate count.
- `wordsUpTo_length`: the number of words of length at most `B` is
  `∑_{n ≤ B} |Σ|^n`.

## References

* A. Kieżun, V. Ganesh, S. Artzi, P. J. Guo, P. Hooimeijer, M. D. Ernst,
  *HAMPI: A Solver for Word Equations over Strings, Regular
  Expressions, and Context-Free Grammars*, ACM TOSEM 21(4), Nov 2012,
  pp. 25:1–25:28. HAMPI bounds string lengths and reduces to bit-vector
  constraints; here the finite search is carried out directly, as a
  specification rather than as HAMPI's algorithm.
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

/-- All words of length exactly `n` over a finite alphabet, each occurring
once: each step extends only the words of the previous length, never the
whole `wordsUpTo` enumeration, so no word is duplicated. -/
noncomputable def wordsOfLength : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 =>
    (wordsOfLength n).flatMap (fun w =>
      (Finset.univ : Finset α).toList.map (fun a => w ++ [a]))

/-- Membership in the exact-length enumeration is exactly the length
equality. -/
theorem mem_wordsOfLength {w : List α} {n : ℕ} :
    w ∈ wordsOfLength (α := α) n ↔ w.length = n := by
  induction n generalizing w with
  | zero =>
    simp [wordsOfLength, List.length_eq_zero_iff]
  | succ n ih =>
    constructor
    · intro h
      rw [wordsOfLength, List.mem_flatMap] at h
      obtain ⟨w', hw', hw⟩ := h
      rw [List.mem_map] at hw
      obtain ⟨a, _, rfl⟩ := hw
      have := ih.mp hw'
      simp only [List.length_append, List.length_singleton] at *
      omega
    · intro h
      rw [wordsOfLength, List.mem_flatMap]
      by_cases hw : w = []
      · simp only [hw, List.length_nil] at h
        omega
      · have hne : w ≠ [] := hw
        obtain ⟨w', a, rfl⟩ : ∃ w' a, w = w' ++ [a] := by
          refine ⟨w.dropLast, w.getLast hne, ?_⟩
          exact (List.dropLast_append_getLast hne).symm
        refine ⟨w', ?_, ?_⟩
        · apply ih.mpr
          have hlen : (w' ++ [a]).length = n + 1 := h
          simp only [List.length_append, List.length_singleton] at hlen
          omega
        · rw [List.mem_map]
          exact ⟨a, Finset.mem_toList.mpr (Finset.mem_univ a), rfl⟩

/-- Counting the exact-length enumeration: `|Σ| ^ n` words. -/
theorem wordsOfLength_length (n : ℕ) :
    (wordsOfLength (α := α) n).length = (Fintype.card α) ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    have hterm : ∀ w : List α,
        ((Finset.univ : Finset α).toList.map (fun a => w ++ [a])).length
          = Fintype.card α := by
      intro w
      simp [List.length_map, Finset.length_toList]
    have hmap : (wordsOfLength (α := α) n).map
        (fun w => ((Finset.univ : Finset α).toList.map (fun a => w ++ [a])).length)
        = (wordsOfLength (α := α) n).map (fun _ => Fintype.card α) := by
      congr 1
      funext w
      exact hterm w
    have hsum : ((wordsOfLength (α := α) n).map
        (fun w => ((Finset.univ : Finset α).toList.map
          (fun a => w ++ [a])).length)).sum
        = (Fintype.card α) ^ n * Fintype.card α := by
      rw [hmap, sum_map_const, ih]
    rw [wordsOfLength, List.length_flatMap, hsum, pow_succ]

/-- The number of words of length at most `B`: `∑_{n ≤ B} |Σ| ^ n`. -/
noncomputable def wordsUpToCount (B : ℕ) : ℕ :=
  ((List.range (B + 1)).map fun n => (Fintype.card α) ^ n).sum

/-- All words of length at most `B` over a finite alphabet, each occurring
once: the concatenation of the exact-length layers `0, …, B`. -/
noncomputable def wordsUpTo (B : ℕ) : List (List α) :=
  (List.range (B + 1)).flatMap (fun n => wordsOfLength (α := α) n)

/-- The empty word is enumerated at every bound. -/
theorem nil_mem_wordsUpTo (B : ℕ) : [] ∈ wordsUpTo (α := α) B := by
  rw [wordsUpTo, List.mem_flatMap]
  exact ⟨0, List.mem_range.mpr (Nat.zero_lt_succ B), by simp [wordsOfLength]⟩

/-- Membership in the enumeration is exactly the length bound. -/
theorem mem_wordsUpTo {w : List α} {B : ℕ} :
    w ∈ wordsUpTo (α := α) B ↔ w.length ≤ B := by
  constructor
  · intro h
    rw [wordsUpTo, List.mem_flatMap] at h
    obtain ⟨n, hn, hw⟩ := h
    rw [List.mem_range] at hn
    rw [mem_wordsOfLength] at hw
    omega
  · intro h
    rw [wordsUpTo, List.mem_flatMap]
    exact ⟨w.length, List.mem_range.mpr (by omega), mem_wordsOfLength.mpr rfl⟩

/-- Summing a constant over a list. -/
theorem sum_map_const {β : Type*} {l : List β} {c : ℕ} :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons _ l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Counting the enumeration: `∑_{n ≤ B} |Σ| ^ n` words, the number of
distinct words of length at most `B`. -/
theorem wordsUpTo_length (B : ℕ) :
    (wordsUpTo (α := α) B).length = wordsUpToCount (α := α) B := by
  simp only [wordsUpToCount, wordsUpTo, List.length_flatMap, wordsOfLength_length]

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
`B`, as association lists, each occurring once (as in `wordsUpTo`). -/
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

/-- Counting the assignment enumeration: the exact number of candidate
assignments is `(wordsUpToCount B) ^ |vs|`. -/
theorem assignLists_length (vs : List V) (B : ℕ) :
    (assignLists (α := α) vs B).length
      = (wordsUpToCount (α := α) B) ^ vs.length := by
  induction vs with
  | nil => simp [assignLists]
  | cons i vs ih =>
    have hterm : ∀ l : List (V × List α),
        ((wordsUpTo (α := α) B).map (fun w => (i, w) :: l)).length
          = wordsUpToCount (α := α) B := by
      intro l
      rw [List.length_map, wordsUpTo_length]
    have hmap : (assignLists (α := α) vs B).map
        (fun l => ((wordsUpTo (α := α) B).map (fun w => (i, w) :: l)).length)
        = (assignLists (α := α) vs B).map (fun _ => wordsUpToCount (α := α) B) := by
      congr 1
      funext l
      exact hterm l
    have hsum : ((assignLists (α := α) vs B).map
        (fun l => ((wordsUpTo (α := α) B).map (fun w => (i, w) :: l)).length)).sum
        = (wordsUpToCount (α := α) B) ^ vs.length
          * (wordsUpToCount (α := α) B) := by
      rw [hmap, sum_map_const, ih]
    rw [assignLists, List.length_flatMap, hsum]
    simp only [List.length_cons, pow_succ]

end Assignments

section Specification

variable {α : Type*} {V : Type*} [Fintype α] [DecidableEq α] [DecidableEq V]

/-- The bounded-search specification: enumerate bounded assignments and
check `φ` on each one. This is a classical specification, not an
executable decision procedure: `assignLists` is `noncomputable`, so
this Boolean cannot be evaluated by `decide`. -/
noncomputable def boundedSatSpec (vs : List V) (φ : Formula α V) (B : ℕ) : Bool :=
  (assignLists vs B).any (fun l => satB (getVal l) φ)

/-- Soundness and completeness of the bounded-search specification: it
reports `true` exactly when `φ` has a solution whose values on `vs`
have length at most `B`. The hypothesis is that `vs` covers the
variables of `φ`. -/
theorem boundedSatSpec_iff (vs : List V) (φ : Formula α V) (B : ℕ)
    (hvars : ∀ i ∈ varsOfFormula φ, i ∈ vs) :
    boundedSatSpec vs φ B = true ↔
      ∃ σ : V → List α, (∀ i ∈ vs, (σ i).length ≤ B) ∧ Sat σ φ := by
  constructor
  · intro h
    rw [boundedSatSpec, List.any_eq_true] at h
    obtain ⟨l, hl, hsat⟩ := h
    obtain ⟨hkeys, hvals⟩ := mem_assignLists.mp hl
    refine ⟨getVal l, ?_, satB_iff.mp hsat⟩
    intro i hi
    exact getVal_length_le hvals (by rw [hkeys]; exact hi)
  · rintro ⟨σ, hbound, hsat⟩
    rw [boundedSatSpec, List.any_eq_true]
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

end Specification

end Cslib.AutomatedReasoning.StringConstraints

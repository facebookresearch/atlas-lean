/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.List.OfFn

/-!
# Factors of right-infinite words

This file represents a right-infinite word over `α` as a function `ℕ → α` and defines its
fixed-length factors and initial segments. This representation follows
[Blackman--Kristensen--Northey, arXiv:2306.09853v3](https://arxiv.org/abs/2306.09853v3).
The definitions of `factor`, `factorSet`, and `finite_factorSet` adapt corresponding CC0
definitions from
[`rwst/Confinement-Certificates`](https://github.com/rwst/Confinement-Certificates), revision
`eb810d8f86e49b2b8e058d02a9edac9e5fedafc8`, in
`ForMathlib/Combinatorics/SubwordComplexity.lean` and
`ForMathlib/Combinatorics/InfiniteComplexity.lean`.

The nonempty list-valued factor predicate follows the substring convention in
[Short--Stanier--van Son--Zabolotskii, arXiv:2608.13199v1](https://arxiv.org/abs/2608.13199v1),
line 562, where a substring is indexed by endpoints `r ≤ s` and is therefore nonempty.
The unqualified `IsFactor` additionally follows the conventional empty-allowed
definition and agrees with membership in `factorSet` at every length.

## Main definitions

* `InfiniteWord.factor` — the length-`k` consecutive block at position `i`.
* `InfiniteWord.factorSet` — the set of all length-`k` factors.
* `InfiniteWord.initial` — the initial length-`k` block.
* `InfiniteWord.factorList` — a list-valued version of `factor`.
* `InfiniteWord.IsFactor` — the assertion that a list occurs in an infinite word.
* `InfiniteWord.IsNonemptyFactor` — the source's nonempty substring convention.
-/

@[expose] public section

namespace InfiniteWord

variable {α : Type*}

/-- The length-`k` factor of a right-infinite word `u` at position `i`. -/
def factor (u : ℕ → α) (k i : ℕ) : Fin k → α := fun s => u (i + s)

@[simp]
theorem factor_apply (u : ℕ → α) (k i : ℕ) (s : Fin k) :
    factor u k i s = u (i + s) :=
  rfl

/-- The set of length-`k` factors occurring in `u`. -/
def factorSet (u : ℕ → α) (k : ℕ) : Set (Fin k → α) :=
  Set.range (factor u k)

@[simp]
theorem mem_factorSet {u : ℕ → α} {k : ℕ} {v : Fin k → α} :
    v ∈ factorSet u k ↔ ∃ i, factor u k i = v :=
  Iff.rfl

/-- The length-`k` initial segment of a right-infinite word `u`. -/
def initial (u : ℕ → α) (k : ℕ) : Fin k → α :=
  factor u k 0

theorem initial_eq_factor_zero (u : ℕ → α) (k : ℕ) :
    initial u k = factor u k 0 :=
  rfl

theorem initial_mem_factorSet (u : ℕ → α) (k : ℕ) :
    initial u k ∈ factorSet u k :=
  ⟨0, rfl⟩

/-- The set of length-`k` factors over a finite alphabet is finite. -/
theorem finite_factorSet [Finite α] (u : ℕ → α) (k : ℕ) :
    (factorSet u k).Finite :=
  Set.toFinite _

/-- The list-valued length-`k` factor of `u` at position `i`. -/
def factorList (u : ℕ → α) (k i : ℕ) : List α :=
  List.ofFn (factor u k i)

@[simp]
theorem factorList_length (u : ℕ → α) (k i : ℕ) :
    (factorList u k i).length = k := by
  simp [factorList]

/-- A finite list occurs as a contiguous factor of a right-infinite word. -/
def IsFactor (w : List α) (u : ℕ → α) : Prop :=
  ∃ i, factorList u w.length i = w

/-- A nonempty finite list occurs as a contiguous factor of a right-infinite word,
using the endpoint convention of the cited source. -/
def IsNonemptyFactor (w : List α) (u : ℕ → α) : Prop :=
  w ≠ [] ∧ ∃ i, ∀ j (hj : j < w.length), w[j]'hj = u (i + j)

/-- A list is a factor iff it equals a list-valued factor at some position. -/
theorem isFactor_iff_exists_factorList (w : List α) (u : ℕ → α) :
    IsFactor w u ↔ ∃ i, factorList u w.length i = w :=
  Iff.rfl

/-- The source's nonempty factor convention is the conventional factor predicate
together with nonemptiness. -/
theorem isNonemptyFactor_iff_exists_factorList (w : List α) (u : ℕ → α) :
    IsNonemptyFactor w u ↔
      w ≠ [] ∧ ∃ i, factorList u w.length i = w := by
  constructor
  · rintro ⟨hne, i, hi⟩
    refine ⟨hne, i, ?_⟩
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      have hn : n < w.length := h2
      simp only [factorList, List.getElem_ofFn, factor_apply, hi n hn]
  · rintro ⟨hne, i, hi⟩
    refine ⟨hne, i, fun j hj => ?_⟩
    have h_congr : (factorList u w.length i)[j]? = w[j]? :=
      congrArg (fun l : List α => l[j]?) hi
    have h_factor : (factorList u w.length i)[j]? = some (u (i + j)) := by
      simp [factorList, hj, factor_apply]
    have h_w : w[j]? = some (w[j]'hj) := by
      simp [hj]
    have h_opt : some (w[j]'hj) = some (u (i + j)) := by
      calc
        some (w[j]'hj) = w[j]? := h_w.symm
        _ = (factorList u w.length i)[j]? := h_congr.symm
        _ = some (u (i + j)) := h_factor
    exact Option.some_inj.mp h_opt

/-- The source's nonempty factor predicate is exactly the conventional factor
predicate together with nonemptiness. -/
theorem isNonemptyFactor_iff_isFactor_and_ne_nil (w : List α) (u : ℕ → α) :
    IsNonemptyFactor w u ↔ w ≠ [] ∧ IsFactor w u := by
  rw [isNonemptyFactor_iff_exists_factorList, isFactor_iff_exists_factorList]

@[simp]
theorem isFactor_nil (u : ℕ → α) : IsFactor [] u := by
  exact ⟨0, by simp [factorList]⟩

@[simp]
theorem not_isNonemptyFactor_nil (u : ℕ → α) : ¬IsNonemptyFactor [] u := by
  simp [IsNonemptyFactor]

/-- List-valued factors agree exactly with membership in `factorSet`, including
at length zero. -/
theorem isFactor_ofFn_iff_mem_factorSet {k : ℕ} (v : Fin k → α) (u : ℕ → α) :
    IsFactor (List.ofFn v) u ↔ v ∈ factorSet u k := by
  rw [isFactor_iff_exists_factorList, mem_factorSet]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hi' : (fun j : Fin k => u (i + j)) = v := by
      simpa [factorList] using hi
    change (fun j : Fin k => u (i + j)) = v
    exact hi'
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hi' : (fun j : Fin k => u (i + j)) = v := by
      change (fun j : Fin k => u (i + j)) = v at hi
      exact hi
    simpa [factorList] using congrArg List.ofFn hi'

end InfiniteWord

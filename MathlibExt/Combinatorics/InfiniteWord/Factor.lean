/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finite.Prod
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

/-- **Factor of an infinite word.** A right-infinite word over an alphabet $\alpha$ is a
sequence $u = u_0 u_1 u_2 \cdots$ of letters $u_n \in \alpha$. For natural numbers $k$ and $i$,
the length-$k$ factor of $u$ at position $i$ is the word $u_i u_{i+1} \cdots u_{i+k-1}$, given
as the map $\{0, \ldots, k-1\} \to \alpha$, $s \mapsto u_{i+s}$. -/
def factor (u : ℕ → α) (k i : ℕ) : Fin k → α := fun s => u (i + s)

@[simp]
theorem factor_apply (u : ℕ → α) (k i : ℕ) (s : Fin k) :
    factor u k i s = u (i + s) :=
  rfl

/-- **Set of factors of a given length.** For a right-infinite word $u = u_0 u_1 u_2 \cdots$
over an alphabet $\alpha$ and a natural number $k$, the set of length-$k$ factors of $u$ is the
set of the maps $\{0, \ldots, k-1\} \to \alpha$, $s \mapsto u_{i+s}$, for $i \in \mathbb{N}$. -/
def factorSet (u : ℕ → α) (k : ℕ) : Set (Fin k → α) :=
  Set.range (factor u k)

@[simp]
theorem mem_factorSet {u : ℕ → α} {k : ℕ} {v : Fin k → α} :
    v ∈ factorSet u k ↔ ∃ i, factor u k i = v :=
  Iff.rfl

/-- **Initial segment of an infinite word.** For a right-infinite word $u = u_0 u_1 u_2 \cdots$
over an alphabet $\alpha$ and a natural number $k$, the length-$k$ initial segment of $u$ is the
word $u_0 u_1 \cdots u_{k-1}$, given as the map $\{0, \ldots, k-1\} \to \alpha$, $s \mapsto u_s$;
it is the length-$k$ factor of $u$ at position $0$. -/
def initial (u : ℕ → α) (k : ℕ) : Fin k → α :=
  factor u k 0

theorem initial_eq_factor_zero (u : ℕ → α) (k : ℕ) :
    initial u k = factor u k 0 :=
  rfl

theorem initial_mem_factorSet (u : ℕ → α) (k : ℕ) :
    initial u k ∈ factorSet u k :=
  ⟨0, rfl⟩

/-- **Finitely many factors of each length.** If the alphabet $\alpha$ is finite, then for every
right-infinite word $u$ over $\alpha$ and every natural number $k$, the set of length-$k$
factors of $u$ is finite. -/
theorem finite_factorSet [Finite α] (u : ℕ → α) (k : ℕ) :
    (factorSet u k).Finite :=
  Set.toFinite _

/-- **Factor as a list.** For a right-infinite word $u = u_0 u_1 u_2 \cdots$ over an alphabet
$\alpha$ and natural numbers $k$ and $i$, the length-$k$ factor of $u$ at position $i$, as a
list, is $[u_i, u_{i+1}, \ldots, u_{i+k-1}]$ (the empty list when $k = 0$). -/
def factorList (u : ℕ → α) (k i : ℕ) : List α :=
  List.ofFn (factor u k i)

@[simp]
theorem factorList_length (u : ℕ → α) (k i : ℕ) :
    (factorList u k i).length = k := by
  simp [factorList]

/-- **Lists occurring in an infinite word.** A finite list $w$ over an alphabet $\alpha$ is a
factor of a right-infinite word $u = u_0 u_1 u_2 \cdots$ over $\alpha$ when, writing $\ell$ for
the length of $w$, there is a position $i \in \mathbb{N}$ with
$w = [u_i, u_{i+1}, \ldots, u_{i+\ell-1}]$. In particular, the empty list is a factor of every
right-infinite word over $\alpha$. -/
def IsFactor (w : List α) (u : ℕ → α) : Prop :=
  ∃ i, factorList u w.length i = w

/-- **Nonempty factors of an infinite word.** Let $u = u_0 u_1 u_2 \cdots$ be a right-infinite
word over an alphabet $\alpha$, viewed as a map $\mathbb{N} \to \alpha$. A finite word
$w = w_0 w_1 \cdots w_{n-1}$ over $\alpha$ is a nonempty factor of $u$ when $n \ge 1$ and there
is a position $i \in \mathbb{N}$ such that $w_j = u_{i+j}$ for every $j < n$.

The empty word is excluded, following the convention in which a factor is given by its
endpoints $r \le s$. -/
def IsNonemptyFactor (w : List α) (u : ℕ → α) : Prop :=
  w ≠ [] ∧ ∃ i, ∀ j (hj : j < w.length), w[j]'hj = u (i + j)

/-- **Occurrence via list-valued factors.** Let $w$ be a finite list of length $\ell$ over an
alphabet $\alpha$ and $u$ a right-infinite word over $\alpha$. Then $w$ is a factor of $u$ if and
only if there is a position $i \in \mathbb{N}$ such that the length-$\ell$ factor of $u$ at
position $i$, as a list, equals $w$. -/
theorem isFactor_iff_exists_factorList (w : List α) (u : ℕ → α) :
    IsFactor w u ↔ ∃ i, factorList u w.length i = w :=
  Iff.rfl

/-- **Nonempty factors via list-valued factors.** Let $w$ be a finite list of length $\ell$ over
an alphabet $\alpha$ and $u = u_0 u_1 u_2 \cdots$ a right-infinite word over $\alpha$. Then $w$
is a nonempty factor of $u$ if and only if $w$ is nonempty and there is a position
$i \in \mathbb{N}$ with $[u_i, u_{i+1}, \ldots, u_{i+\ell-1}] = w$. -/
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

/-- **Nonempty factors are the factors that are nonempty.** For a finite list $w$ over an
alphabet $\alpha$ and a right-infinite word $u$ over $\alpha$, $w$ is a nonempty factor of $u$ if
and only if $w$ is nonempty and $w$ is a factor of $u$. -/
theorem isNonemptyFactor_iff_isFactor_and_ne_nil (w : List α) (u : ℕ → α) :
    IsNonemptyFactor w u ↔ w ≠ [] ∧ IsFactor w u := by
  rw [isNonemptyFactor_iff_exists_factorList, isFactor_iff_exists_factorList]

@[simp]
theorem isFactor_nil (u : ℕ → α) : IsFactor [] u := by
  exact ⟨0, by simp [factorList]⟩

@[simp]
theorem not_isNonemptyFactor_nil (u : ℕ → α) : ¬IsNonemptyFactor [] u := by
  simp [IsNonemptyFactor]

/-- **Factors as lists and as tuples agree.** Let $k$ be a natural number, $v$ a map
$\{0, \ldots, k-1\} \to \alpha$, written $j \mapsto v_j$, and $u$ a right-infinite word over
$\alpha$. Then the list $[v_0, v_1, \ldots, v_{k-1}]$ is a factor of $u$ if and only if $v$
belongs to the set of length-$k$ factors of $u$. This holds also for $k = 0$. -/
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

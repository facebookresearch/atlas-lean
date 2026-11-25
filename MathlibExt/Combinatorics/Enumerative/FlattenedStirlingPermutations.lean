/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Partition.Finpartition
public import MathlibExt.Combinatorics.Enumerative.StirlingPermutation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic

/-!
# Flattened Stirling permutations

Runs are maximal weakly increasing subwords. A Stirling permutation with just one run
lists each letter twice in increasing order.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Start of a run.** Position $i$ of a word $w = w_0 w_1 \cdots w_{m-1}$ of natural numbers
starts a run when $i = 0$ or the letter before it is larger, that is, $w_{i-1} > w_i$. Runs are
the maximal contiguous weakly increasing subwords, so these are exactly the positions where a run
begins.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (runs). -/
def wordRunStart {m : ℕ} (w : Fin m → ℕ) (i : Fin m) : Prop :=
  i.val = 0 ∨ ∃ j : Fin m, j.val + 1 = i.val ∧ w i < w j

instance instDecidablePredFinWordRunStart {m : ℕ} (w : Fin m → ℕ) :
    DecidablePred (wordRunStart w) := fun _ => by
  unfold wordRunStart; infer_instance

/-- **Number of runs of a word.** A run of a word $w = w_0 w_1 \cdots w_{m-1}$ of natural numbers is
a maximal contiguous weakly increasing subword. The number of runs of $w$ is the number of
positions $i < m$ that start a run, that is, with $i = 0$ or $w_{i-1} > w_i$; the empty word has
no runs.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (runs). -/
def wordRunCount {m : ℕ} (w : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter (wordRunStart w)).card

/-- **Flattened words.** A word $w = w_1 w_2 \cdots w_m$ of natural numbers is flattened when
the leading letters of its runs, read left to right, are weakly increasing. Here a run is a
maximal contiguous weakly increasing subword, so position $i$ starts a run when $i = 1$ or
$w_{i-1} > w_i$; the condition is that $w_i \le w_j$ whenever $i < j$ and both positions
start runs.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (flattened). -/
def IsFlattenedWord {m : ℕ} (w : Fin m → ℕ) : Prop :=
  ∀ i j : Fin m, i < j → wordRunStart w i → wordRunStart w j → w i ≤ w j

instance instDecidableIsFlattenedWord {m : ℕ} (w : Fin m → ℕ) :
    Decidable (IsFlattenedWord w) := by
  unfold IsFlattenedWord; infer_instance

/-- **Number of flattened Stirling permutations.** For a natural number $n$,
$|\mathrm{flat}(Q_n)|$ is the number of flattened Stirling permutations of order $n$: words
$w_1 w_2 \cdots w_{2n}$ of natural numbers that are Stirling permutations of order $n$ and whose
runs (maximal contiguous weakly increasing subwords) have weakly increasing leading letters,
read from left to right.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1. -/
noncomputable def flattenedStirlingCount (n : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → ℕ | IsStirlingPermutation n w ∧ IsFlattenedWord w}

/-- **Counting flattened Stirling permutations by runs.** For natural numbers $n$ and $k$,
$|\mathrm{flat}_k(Q_n)|$ is the number of flattened Stirling permutations of order $n$ with
exactly $k$ runs, where a run is a maximal contiguous weakly increasing subword.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1. -/
noncomputable def flattenedStirlingRunCount (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → ℕ |
    IsStirlingPermutation n w ∧ IsFlattenedWord w ∧ wordRunCount w = k}

private theorem one_run_iff_monotone {m : ℕ} (w : Fin m → ℕ) (hm : 0 < m) :
    wordRunCount w = 1 ↔ Monotone w := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hzero : wordRunStart w 0 := Or.inl rfl
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have unique_start (i : Fin (m + 1)) (hi : wordRunStart w i) : i = a := by
      have hmem : i ∈ Finset.univ.filter (wordRunStart w) := Finset.mem_filter.mpr ⟨by simp, hi⟩
      simpa [ha] using hmem
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    by_contra! hdesc
    have hstart : wordRunStart w i.succ := Or.inr ⟨i.castSucc, rfl, hdesc⟩
    exact Fin.succ_ne_zero i ((unique_start _ hstart).trans (unique_start _ hzero).symm)
  · intro hw
    apply Finset.card_eq_one.mpr
    refine ⟨0, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro (hi | ⟨j, hj, hdesc⟩)
      · exact Fin.ext hi
      · exact (hdesc.not_ge (hw (show j ≤ i from Fin.le_iff_val_le_val.mpr (by omega)))).elim
    · rintro rfl
      exact hzero

private def pairedWord (n : ℕ) (i : Fin (2 * n)) : ℕ := i.val / 2 + 1

private theorem pairedWord_monotone (n : ℕ) : Monotone (pairedWord n) := by
  intro i j hij
  exact Nat.add_le_add_right (Nat.div_le_div_right hij) 1

private theorem pairedWord_stirling (n : ℕ) : IsStirlingPermutation n (pairedWord n) := by
  refine ⟨fun i => Finset.mem_Icc.mpr ⟨by simp [pairedWord], ?_⟩, ?_, ?_⟩
  · have := i.isLt
    dsimp [pairedWord]
    omega
  · intro v hv
    obtain ⟨hv₁, hv₂⟩ := Finset.mem_Icc.mp hv
    let a : Fin (2 * n) := ⟨2 * (v - 1), by omega⟩
    let b : Fin (2 * n) := ⟨2 * (v - 1) + 1, by omega⟩
    apply Finset.card_eq_two.mpr
    refine ⟨a, b, ?_, ?_⟩
    · simp [a, b, Fin.ext_iff]
    · apply Finset.ext
      intro i
      change i ∈ Finset.univ.filter (fun j => pairedWord n j = v) ↔ _
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      change i.val / 2 + 1 = v ↔ i.val = 2 * (v - 1) ∨ i.val = 2 * (v - 1) + 1
      omega
  · intro v _ a b c hab hbc ha hc
    change a.val < b.val at hab
    change b.val < c.val at hbc
    simp only [pairedWord] at ha hc ⊢
    omega

private theorem count_ofFn_stirling {n : ℕ} {w : Fin (2 * n) → ℕ}
    (hw : IsStirlingPermutation n w) (v : ℕ) :
    (List.ofFn w).count v = if v ∈ Finset.Icc 1 n then 2 else 0 := by
  by_cases hv : v ∈ Finset.Icc 1 n
  · rw [ite_eq_left hv, ← List.Vector.toList_ofFn, List.Vector.count_toList]
    simpa only [List.Vector.get_ofFn] using hw.2.1 v hv
  · rw [ite_eq_right hv, List.count_eq_zero]
    simpa only [List.mem_ofFn, Set.mem_range] using
      (show ¬ ∃ i, w i = v from fun ⟨i, hi⟩ => hv (hi ▸ hw.1 i))

/-- **Exactly one flattened Stirling permutation has one run.** For every natural number
$n \ge 1$, exactly one flattened Stirling permutation of order $n$ has exactly one run.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 2, part 1. -/
theorem flattenedStirlingRunCount_one (n : ℕ) (hn : 1 ≤ n) :
    flattenedStirlingRunCount n 1 = 1 := by
  have hm : 0 < 2 * n := by omega
  have hmono := pairedWord_monotone n
  have hst := pairedWord_stirling n
  apply Set.ncard_eq_one.mpr
  refine ⟨pairedWord n, ?_⟩
  ext w
  change (IsStirlingPermutation n w ∧ IsFlattenedWord w ∧ wordRunCount w = 1) ↔ w = pairedWord n
  constructor
  · rintro ⟨hw, _, hrun⟩
    have hwmono := (one_run_iff_monotone w hm).mp hrun
    apply List.ofFn_injective
    apply List.Perm.eq_of_sortedLE hwmono.sortedLE_ofFn hmono.sortedLE_ofFn
    exact List.perm_iff_count.mpr fun v =>
      (count_ofFn_stirling hw v).trans (count_ofFn_stirling hst v).symm
  · rintro rfl
    exact ⟨hst, fun _ _ hij _ _ => hmono hij.le, (one_run_iff_monotone _ hm).mpr hmono⟩

/-- **Flattened partitions counted by runs.** For natural numbers $n$ and $k$, $f_{n,k}$ is the
number of permutations $\sigma$ of $\{0, 1, \dots, n - 1\}$ such that the word
$\sigma(0) \sigma(1) \cdots \sigma(n - 1)$ is flattened (the leading letters of its runs, read
left to right, are weakly increasing) and has exactly $k$ runs, where a run is a maximal
contiguous weakly increasing subword. These are the flattened partitions of length $n$ of
Nabawanda, Rakotondrajao, and Bamunoba, with letters $0, \dots, n - 1$ in place of
$1, \dots, n$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (flattened
partitions, after Nabawanda, Rakotondrajao, and Bamunoba). -/
def flattenedPermRunCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    IsFlattenedWord (fun i => (σ i : ℕ)) ∧ wordRunCount (fun i => (σ i : ℕ)) = k).card

/-- **Type $B$ set partitions.** For a natural number $n$, a set partition $P$ of the integer
interval $[-n, n] = \{-n, \dots, n\}$ is of type $B$ if for every block $\beta$ of $P$ the set
$-\beta = \{-x : x \in \beta\}$ is again a block of $P$, and exactly one block $\beta$ of $P$
satisfies $-\beta = \beta$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Definition 1. -/
def IsTypeBSetPartition {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) : Prop :=
  (∀ b ∈ P.parts, b.image (fun x => -x) ∈ P.parts) ∧
    ∃! b, b ∈ P.parts ∧ b.image (fun x => -x) = b

/-- **A flattened word with four runs.** The word
$w = 1\,1\,2\,2\,9\,9\,3\,8\,8\,3\,4\,6\,6\,7\,7\,4\,5\,5$ of length $18$ is flattened (the
leading letters of its runs, read left to right, are weakly increasing), and it has exactly
$4$ runs, where a run is a maximal contiguous weakly increasing subword.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (example). -/
theorem isFlattenedWord_example :
    IsFlattenedWord ![1, 1, 2, 2, 9, 9, 3, 8, 8, 3, 4, 6, 6, 7, 7, 4, 5, 5] ∧
      wordRunCount ![1, 1, 2, 2, 9, 9, 3, 8, 8, 3, 4, 6, 6, 7, 7, 4, 5, 5] = 4 := by
  decide

/-- **A word that is not flattened.** The word $123321445566778899$ is not flattened.

This word is a Stirling permutation of order $9$; its runs $1233$, $2$, $1445566778899$ have
leading letters $1, 2, 1$, which do not weakly increase.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Section 1 (example). -/
theorem not_isFlattenedWord_example :
    ¬ IsFlattenedWord ![1, 2, 3, 3, 2, 1, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9] := by
  decide

/-- **The one-block partition is of type B.** For every natural number $n$, the partition of
the integer interval $[-n, n] = \{-n, \dots, n\}$ into a single block is a type $B$ set
partition: its only block is closed under negation, so it is the unique block equal to its own
negative (the zero-block).

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Definition 1; characteristic
check of `IsTypeBSetPartition`. -/
theorem isTypeBSetPartition_indiscrete (n : ℕ) :
    IsTypeBSetPartition
      (Finpartition.indiscrete (a := Finset.Icc (-(n : ℤ)) n)
        (by rw [Finset.bot_eq_empty]; exact (Finset.nonempty_Icc.2 (by omega)).ne_empty)) := by
  refine ⟨?_, ⟨Finset.Icc (-(n : ℤ)) n, ⟨by simp, ?_⟩, ?_⟩⟩
  · intro b hb
    simp only [Finpartition.indiscrete_parts, Finset.mem_singleton] at hb ⊢
    subst hb
    ext x; simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by simp⟩
  · ext x; simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by simp⟩
  · rintro b ⟨hb, -⟩
    simpa using hb

/-- **The shift map.** For a finite set $S$ of integers, $h(S) = \{|i| + 1 : i \in S\}$, a
finite set of natural numbers.

In particular, for every natural number $n$, $h$ sends subsets of $[-n, n]$ to subsets of
$\{1, \dots, n + 1\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 2 (the map `h`). -/
def typeBShift (S : Finset ℤ) : Finset ℕ :=
  S.image fun i => i.natAbs + 1

/-- **Doubled word.** For a finite set $S = \{s_1 < s_2 < \dots < s_k\}$ of natural numbers, the
doubled word of $S$ is $f(S) = s_1 s_1 s_2 s_2 \cdots s_k s_k$, which lists the elements of $S$
in increasing order with each one written twice; $f(\emptyset)$ is the empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
def doubledWord (S : Finset ℕ) : List ℕ :=
  (S.sort (· ≤ ·)).flatMap fun s => [s, s]

/-- **Wrapped word of a finite set.** For a finite set $S = \{s_1 < s_2 < \dots < s_k\}$ of natural
numbers, the wrapped word $g(S)$ is $s_1 s_2 s_2 \cdots s_k s_k s_1$: the smallest element, then
each larger element written twice in increasing order, then the smallest element again. For
$S = \emptyset$, $g(S)$ is the empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
def wrappedWord (S : Finset ℕ) : List ℕ :=
  match S.sort (· ≤ ·) with
  | [] => []
  | s :: t => s :: t.flatMap (fun x => [x, x]) ++ [s]

/-- **An example of the shift map.** For the map $h(S) = \{|i| + 1 : i \in S\}$ on finite sets
of integers, $h(\{-2, 0, 1\}) = \{1, 2, 3\}$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 2 (the map `h`). -/
theorem typeBShift_example : typeBShift {-2, 0, 1} = {1, 2, 3} := by
  decide

/-- **The doubled word of a singleton.** For every natural number $s$, the doubled word of the
singleton $\{s\}$ is $f(\{s\}) = s\,s$, the word of length two whose letters are both $s$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
theorem doubledWord_singleton (s : ℕ) : doubledWord {s} = [s, s] := by
  simp [doubledWord]

/-- **Length of the doubled word.** For every finite set $S$ of natural numbers with elements
$s_1 < \dots < s_k$, the doubled word $f(S) = s_1 s_1 s_2 s_2 \cdots s_k s_k$ has length $2|S|$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `f`). -/
theorem length_doubledWord (S : Finset ℕ) : (doubledWord S).length = 2 * S.card := by
  simp [doubledWord, List.length_flatMap, mul_comm]

/-- **Wrapped word of the empty set.** The wrapped word $g(\emptyset)$ of the empty set is the
empty word.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem wrappedWord_empty : wrappedWord ∅ = [] := by
  simp [wrappedWord]

/-- **Wrapped word of a singleton.** For every natural number $s$, the wrapped word of the
singleton $\{s\}$ is $g(\{s\}) = s\,s$, the word of length two both of whose letters are $s$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem wrappedWord_singleton (s : ℕ) : wrappedWord {s} = [s, s] := by
  simp [wrappedWord]

/-- **Length of the wrapped word.** For every finite set $S$ of natural numbers with elements
$s_1 < \dots < s_k$, the wrapped word $g(S) = s_1 s_2 s_2 \cdots s_k s_k s_1$ (the empty word when
$S = \emptyset$) has length $2|S|$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Lemma 3 (the map `g`). -/
theorem length_wrappedWord (S : Finset ℕ) : (wrappedWord S).length = 2 * S.card := by
  rw [← Finset.length_sort (· ≤ ·) (s := S)]
  unfold wrappedWord
  split <;> simp_all [List.length_flatMap]
  omega

/-- **Adler block labels.** Let $n$ be a natural number and $P$ a set partition of the integer
interval $\{-n, \dots, n\}$; for $x$ in this interval write $P(x)$ for the block of $P$
containing $x$. The Adler block labels of $P$ are the integers $p$ with $1 \le p \le n$ such
that $p \le q$ for every positive $q \in P(p)$ and $p < -q$ for every negative $q \in P(p)$;
that is, $p$ is the least positive element of its block and is smaller than the absolute value
of every negative element of that block.

For a type $B$ set partition the block containing $0$ is never labelled, and from each pair of
blocks $\beta \ne -\beta$ exactly the block containing the element of least absolute value as a
positive element is labelled, by its least positive element; sorting the labels orders these
kept blocks as $\beta_1, \dots, \beta_m$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3 (arXiv:2306.13034). -/
def adlerBlockLabels {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) : Finset ℤ :=
  (Finset.Icc 1 (n : ℤ)).filter fun p =>
    ∀ q ∈ P.part p, (0 < q → p ≤ q) ∧ (q < 0 → p < -q)

/-- **Adler labels lie in $\{1, \dots, n\}$.** For every natural number $n$ and every set
partition $P$ of $\{-n, \dots, n\}$, every Adler block label $p$ of $P$ is an integer with
$1 \le p \le n$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Notation 2.3. -/
theorem adlerBlockLabels_subset {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    adlerBlockLabels P ⊆ Finset.Icc 1 (n : ℤ) :=
  Finset.filter_subset _ _

/-- **The word of a set partition of $[-n, n]$, as a list.** Let $n$ be a natural number and let
$P$ be a set partition of $[-n, n] = \{-n, \dots, n\}$. For a finite set $S$ of integers let
$h(S) = \{|i| + 1 : i \in S\}$, and for a finite set $T$ of natural numbers with elements
$t_1 < \dots < t_k$ let $f(T) = t_1 t_1 t_2 t_2 \cdots t_k t_k$ and
$g(T) = t_1 t_2 t_2 \cdots t_k t_k t_1$ (both empty when $T = \emptyset$). Let $P_0$ be the set of
nonnegative elements of the block of $P$ containing $0$. Let $p_1 < \dots < p_m$ be the integers $p$
with $1 \le p \le n$ such that every positive element of the block of $P$ containing $p$ is at
least $p$ and every negative element $q$ of that block satisfies $p < -q$, and let $N_i$ and $P_i$
be the sets of negative and of positive elements of the block containing $p_i$. The list of $P$ is
the list of natural numbers
$$g(h(P_0))\, f(h(N_1))\, g(h(P_1)) \cdots f(h(N_m))\, g(h(P_m)).$$

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`), with
Definition 2. -/
def typeBFlattenedWordList {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    List ℕ :=
  wrappedWord (typeBShift ((P.part 0).filter (0 ≤ ·))) ++
    ((adlerBlockLabels P).sort (· ≤ ·)).flatMap fun p =>
      doubledWord (typeBShift ((P.part p).filter (· < 0))) ++
        wrappedWord (typeBShift ((P.part p).filter (0 < ·)))

/-- **The word of a set partition of $[-n, n]$.** For a natural number $n$ and a set partition
$P$ of $[-n, n] = \{-n, \dots, n\}$, let $L(P)$ be the list of $P$: the list of natural numbers
built from the blocks of $P$ (via the shift map and the doubled and wrapped words). The word
$\varphi(P) = w_1 w_2 \cdots w_{2(n+1)}$ has $w_i$ equal to the $i$-th entry of $L(P)$ when $L(P)$
has at least $i$ entries, and $w_i = 0$ otherwise.

Restricted to type $B$ set partitions, this is the map $\varphi$ of Proposition 1.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`). -/
def typeBFlattenedWord {n : ℕ} (P : Finpartition (Finset.Icc (-(n : ℤ)) n)) :
    Fin (2 * (n + 1)) → ℕ :=
  fun i => (typeBFlattenedWordList P).getD i 0
end

end MetaMathlibExt

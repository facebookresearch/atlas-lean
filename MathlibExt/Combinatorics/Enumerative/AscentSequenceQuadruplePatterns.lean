/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Combinatorics.Enumerative.RascalWords
import Mathlib.Data.List.GetD

/-!
# Pattern avoidance in weak ascent sequences

If a big entry in a weak ascent sequence avoiding 011, 100, 201 and 210 has a successor,
that successor is big or starts a suffix consisting of a smaller entry followed by big entries.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted (IsAscentSeq)

@[expose] public section

/-- **Number of weak ascents of a word.** For a word $a_1 a_2 \cdots a_m$ of natural numbers,
$\mathrm{wasc}(a_1 \cdots a_m)$ is the number of weak ascents, that is, of positions $j$ with
$1 \le j < m$ and $a_j \le a_{j+1}$; in particular the empty word and every word of length one
have no weak ascents.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1 (definition of `wasc`). -/
public def wordWeakAscents : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a ≤ b then 1 else 0) + wordWeakAscents (b :: t)

/-- **Weak ascent sequence.** A word $a_1 a_2 \cdots a_n$ over $\mathbb{N}$ is a weak ascent
sequence if either $n = 0$, or $a_1 = 0$ and $a_i \le 1 + \operatorname{wasc}(a_1 \cdots a_{i-1})$
for every $2 \le i \le n$, where $\operatorname{wasc}(u)$ is the number of weak ascents of $u$,
that is, of positions $j$ with $u_j \le u_{j+1}$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def IsWeakAscentSeq (w : List ℕ) : Prop :=
  (∀ h : 0 < w.length, w[0]'h = 0) ∧
    ∀ (i : ℕ) (h : i < w.length), w[i]'h ≤ wordWeakAscents (w.take i) + 1

/-- **Pattern containment in words.** A word $w$ over $\mathbb{N}$ contains a pattern $p$ (another
word over $\mathbb{N}$) if $w$ has a subsequence $s$, not necessarily contiguous, of the same
length as $p$ that is order-isomorphic to $p$: for all positions $i$ and $j$, $s_i < s_j$ if and
only if $p_i < p_j$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def ContainsPattern (w p : List ℕ) : Prop :=
  ∃ s : List ℕ, s.Sublist w ∧ s.length = p.length ∧
    ∀ i < p.length, ∀ j < p.length, (s.getD i 0 < s.getD j 0 ↔ p.getD i 0 < p.getD j 0)

/-- **The thirteen patterns of length three.** The set of patterns of length three consists of
the thirteen words $000$, $001$, $010$, $011$, $012$, $021$, $100$, $101$, $102$, $110$, $120$,
$201$ and $210$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def lengthThreePatterns : Finset (List ℕ) :=
  {[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 1], [1, 0, 0], [1, 0, 1],
    [1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1], [2, 1, 0]}

/-- **Ascent sequences avoiding a set of patterns.** For a finite set $P$ of patterns (words over
$\mathbb{N}$) and $n \in \mathbb{N}$, $A_n(P)$ is the set of ascent sequences of length $n$ that
contain no pattern of $P$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def ascentAvoiders (P : Finset (List ℕ)) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ IsAscentSeq w ∧ ∀ p ∈ P, ¬ ContainsPattern w p}

/-- **Weak ascent sequences avoiding a set of patterns.** For a finite set $P$ of patterns
(words over $\mathbb{N}$) and a natural number $n$, $\mathrm{WA}_n(P)$ is the set of weak ascent
sequences of length $n$ that contain none of the patterns in $P$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public def weakAscentAvoiders (P : Finset (List ℕ)) (n : ℕ) : Set (List ℕ) :=
  {w | w.length = n ∧ IsWeakAscentSeq w ∧ ∀ p ∈ P, ¬ ContainsPattern w p}

/-- **The weak ascent sequence $00203413$.** The word $00203413$ has five weak ascents and is a
weak ascent sequence.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem isWeakAscentSeq_example :
    wordWeakAscents [0, 0, 2, 0, 3, 4, 1, 3] = 5 ∧ IsWeakAscentSeq [0, 0, 2, 0, 3, 4, 1, 3] := by
  unfold IsWeakAscentSeq
  decide

/-- **The word $00203413$ contains $011$.** The word $00203413$ contains the pattern $011$.

For example, its subsequence $033$ is order-isomorphic to $011$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem containsPattern_example : ContainsPattern [0, 0, 2, 0, 3, 4, 1, 3] [0, 1, 1] := by
  refine ⟨[0, 3, 3], by decide, rfl, ?_⟩
  decide

/-- **Number of patterns of length three.** The set of patterns of length three,
$\{000, 001, 010, 011, 012, 021, 100, 101, 102, 110, 120, 201, 210\}$, has exactly $13$ elements.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Section 1. -/
public theorem card_lengthThreePatterns : lengthThreePatterns.card = 13 := by
  decide

/-- **Big entry.** Let $w = w_1 \cdots w_n$ be a word over $\mathbb{N}$ and $2 \le k \le n$. The
entry $w_k$ is a big entry of $w$ if it equals $1$ plus the number of weak ascents of
$w_1 \cdots w_{k-1}$, that is, of positions $j < k - 1$ with $w_j \le w_{j+1}$. In a weak ascent
sequence this is the largest value allowed at position $k$. The entry $w_k$ is referred to by its
zero-based index $i = k - 1$, so the index ranges over $1 \le i < n$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3
(definition of big entry). -/
public def IsBigEntry (w : List ℕ) (i : ℕ) : Prop :=
  1 ≤ i ∧ i < w.length ∧ w.getD i 0 = wordWeakAscents (w.take i) + 1

public instance (w : List ℕ) (i : ℕ) : Decidable (IsBigEntry w i) := by
  unfold IsBigEntry; infer_instance

/-- **Big entries of $00203413$.** In the word $w = 00203413$, with positions numbered from $1$,
the entries $w_3 = 2$ and $w_6 = 4$ are big entries and the entry $w_7 = 1$ is not.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3. -/
public theorem isBigEntry_example :
    IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 2 ∧ IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 5 ∧
      ¬ IsBigEntry [0, 0, 2, 0, 3, 4, 1, 3] 6 := by
  decide

/-- **Position of the last descent top.** For a finite sequence $w = w_1 w_2 \cdots w_m$ of
natural numbers, a descent of $w$ is an index $1 \le i < m$ with $w_i > w_{i+1}$, and $w_i$ is
its descent top. The position of the last descent top of $w$ is the largest index $i$ with
$w_i > w_{i+1}$ (positions counted from $1$), and it is $0$ if $w$ has no descent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3
(definition of `W_{n,k}`). -/
public def lastDescentTop (w : List ℕ) : ℕ :=
  ((Finset.range (w.length - 1)).filter fun i => w.getD (i + 1) 0 < w.getD i 0).sup (· + 1)

/-- **Examples of the last descent top.** Each of the sequences $0010$, $0020$, $0021$ and
$0120$ has its last descent top at position $3$, and the sequence $012$, which has no
descent, has last descent top position $0$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3. -/
public theorem lastDescentTop_example :
    lastDescentTop [0, 0, 1, 0] = 3 ∧ lastDescentTop [0, 0, 2, 0] = 3 ∧
      lastDescentTop [0, 0, 2, 1] = 3 ∧ lastDescentTop [0, 1, 2, 0] = 3 ∧
      lastDescentTop [0, 1, 2] = 0 := by
  decide

/-- **The sets $U_{n,j}$.** Let $W_n = WA_n(011, 100, 201, 210)$ be the set of weak ascent
sequences of length $n$ that avoid each of the patterns $011$, $100$, $201$ and $210$. For
natural numbers $n$ and $j$, $U_{n,j}$ is the set of sequences $w = w_1 w_2 \cdots w_n$ in
$W_n$ such that the last descent top of $w$ is at position $n - 1$, $w$ has a big entry, the
first $n - 2$ entries of $w$ are not all $0$, $w_{n-1} \ne n - 2$, and $w_{n-1} = w_n + j$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2
(definition of `U_{n,j}`). -/
public def quadrupleUSet (n j : ℕ) : Set (List ℕ) :=
  {w | w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n ∧
    lastDescentTop w = n - 1 ∧ (∃ i < n, IsBigEntry w i) ∧ (∃ i < n - 2, w.getD i 0 ≠ 0) ∧
    w.getD (n - 2) 0 ≠ n - 2 ∧ w.getD (n - 2) 0 = w.getD (n - 1) 0 + j}

/-- **$U_{0,j}$ is empty.** For every natural number $j$, the set $U_{0,j}$ is empty.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2. -/
public theorem quadrupleUSet_zero (j : ℕ) : quadrupleUSet 0 j = ∅ := by
  ext w
  simp [quadrupleUSet]

/-- **The sets $V_{n,j}$.** Let $W_n = WA_n(011, 100, 201, 210)$ be the set of weak ascent
sequences of length $n$ that avoid each of the patterns $011$, $100$, $201$ and $210$. For
natural numbers $n$ and $j$, $V_{n,j}$ is the set of sequences $w = w_1 w_2 \cdots w_n$ in
$W_n$ such that the last descent top of $w$ is at position $n - 2$, $w_n \le n - 3$,
$w_{n-1} \ne 0$, and $w_{n-2} = w_{n-1} + j$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2
(definition of `V_{n,j}`). -/
public def quadrupleVSet (n j : ℕ) : Set (List ℕ) :=
  {w | w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n ∧
    lastDescentTop w = n - 2 ∧ w.getD (n - 1) 0 ≤ n - 3 ∧ w.getD (n - 2) 0 ≠ 0 ∧
    w.getD (n - 3) 0 = w.getD (n - 2) 0 + j}

/-- **$V_{n,j}$ lies in $W_n$.** For all natural numbers $n$ and $j$, the set $V_{n,j}$ is
contained in $W_n = WA_n(011, 100, 201, 210)$, the set of weak ascent sequences of length $n$
that avoid each of the patterns $011$, $100$, $201$ and $210$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Section 4.3.2. -/
public theorem quadrupleVSet_subset (n j : ℕ) :
    quadrupleVSet n j ⊆ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n :=
  fun _ h => h.1

namespace isBigEntry_succ_or_descent

private theorem triple_sublist (w : List ℕ) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hk : k < w.length) :
    [w.getD i 0, w.getD j 0, w.getD k 0].Sublist w := by
  have hi := hij.trans (hjk.trans hk)
  have hj := hjk.trans hk
  let indices : List (Fin w.length) := [⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩]
  have hs : indices.Pairwise (· < ·) := by
    simp [indices, Fin.mk_lt_mk, hij, hjk, hij.trans hjk]
  rw [List.getD_eq_getElem w 0 hi, List.getD_eq_getElem w 0 hj, List.getD_eq_getElem w 0 hk]
  exact List.map_getElem_sublist hs

private theorem contains_of_triple {w : List ℕ} {a b c x y z : ℕ}
    (hs : [a, b, c].Sublist w)
    (h : (a < b ↔ x < y) ∧ (b < a ↔ y < x) ∧ (a < c ↔ x < z) ∧ (c < a ↔ z < x) ∧
      (b < c ↔ y < z) ∧ (c < b ↔ z < y)) : ContainsPattern w [x, y, z] := by
  refine ⟨[a, b, c], hs, rfl, ?_⟩
  simp only [List.length_cons, List.length_nil, Nat.forall_lt_succ_left]
  simpa [List.getD, and_assoc, and_left_comm, and_comm] using h

private theorem ne_of_avoid011 {w : List ℕ} {a b c : ℕ} (hs : [a, b, c].Sublist w)
    (hab : a < b) (h : ¬ ContainsPattern w [0, 1, 1]) : b ≠ c := by
  rintro rfl
  apply h
  exact contains_of_triple hs (by omega)

/-- If two later entries were both below the descent top, their relative order would give
one of the patterns 100, 201 and 210. -/
private theorem le_of_descent {w : List ℕ} {a b c : ℕ} (hs : [a, b, c].Sublist w)
    (hba : b < a) (h100 : ¬ ContainsPattern w [1, 0, 0])
    (h201 : ¬ ContainsPattern w [2, 0, 1]) (h210 : ¬ ContainsPattern w [2, 1, 0]) :
    a ≤ c := by
  by_contra! hca
  rcases lt_trichotomy b c with hbc | hbc | hbc
  · exact h201 (contains_of_triple hs (by omega))
  · exact h100 (contains_of_triple hs (by omega))
  · exact h210 (contains_of_triple hs (by omega))

private theorem weakAscents_take_step (w : List ℕ) (i : ℕ) (hi : i + 1 < w.length) :
    wordWeakAscents (w.take (i + 2)) = wordWeakAscents (w.take (i + 1)) +
      (if w.getD i 0 ≤ w.getD (i + 1) 0 then 1 else 0) := by
  induction i generalizing w with
  | zero =>
    match w with
    | a :: b :: t => simp [wordWeakAscents, List.getD]
  | succ i ih =>
    match w with
    | a :: b :: t =>
      have h := ih (b :: t) (by simpa using hi)
      simpa [List.take_succ_cons, wordWeakAscents, List.getD_cons_succ, Nat.add_assoc] using h

end isBigEntry_succ_or_descent

open isBigEntry_succ_or_descent

/-- **Successors of big entries in $W_n$.** Let $W_n$ be the set of weak ascent sequences of length
$n$ avoiding the patterns $011$, $100$, $201$ and $210$, and let $w = w_1 \cdots w_n \in W_n$. If
$2 \le k \le n - 1$ and $w_k$ is a big entry of $w$, then either $w_{k+1}$ is a big entry, or
$w_{k+1} < w_k$ and $w_j$ is a big entry for every $j$ with $k + 2 \le j \le n$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Lemma 1 (`integers-2025-A80-lem-1`). -/
public theorem isBigEntry_succ_or_descent (n : ℕ) (w : List ℕ)
    (hw : w ∈ weakAscentAvoiders {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} n) (k : ℕ)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (hbig : IsBigEntry w (k - 1)) :
    IsBigEntry w k ∨
      (w.getD k 0 < w.getD (k - 1) 0 ∧ ∀ j, k + 2 ≤ j → j ≤ n → IsBigEntry w (j - 1)) := by
  obtain ⟨hlen, hweak, hav⟩ := hw
  let a (i : ℕ) := w.getD i 0
  let bound (i : ℕ) := wordWeakAscents (w.take i) + 1
  have hle (i : ℕ) (hi : i < n) : a i ≤ bound i := by
    simpa only [a, List.getD_eq_getElem w 0 (by omega : i < w.length)] using hweak.2 i (by omega)
  have hstep (i : ℕ) (hi : 0 < i) (hin : i < n) :
      bound (i + 1) = bound i + (if a (i - 1) ≤ a i then 1 else 0) := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    dsimp only [bound, a]
    rw [weakAscents_take_step w i (by omega), Nat.add_right_comm]
    rfl
  -- The initial zero makes any repetition of a positive value an occurrence of 011.
  have hdistinct {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < n)
      (hpos : 0 < a i) : a i ≠ a j := by
    have hzero : a 0 = 0 := by
      change w.getD 0 0 = 0
      rw [List.getD_eq_getElem w 0 (by omega)]
      exact hweak.1 _
    exact ne_of_avoid011 (triple_sublist w hi hij (by omega))
      (show a 0 < a i by omega) (hav _ (by decide))
  have htop : a (k - 1) = bound (k - 1) := hbig.2.2
  have hpos : 0 < a (k - 1) := htop ▸ Nat.zero_lt_succ _
  have hgrowth : bound k ≤ a (k - 1) + 1 := by
    have hs := hstep (k - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hs
    split at hs <;> omega
  by_cases hdesc : a k < a (k - 1)
  · refine Or.inr ⟨hdesc, ?_⟩
    have hflat : bound (k + 1) = bound k := by
      simpa [hdesc.not_ge] using hstep k (by omega) (by omega)
    -- From the descent onward, each bound is a lower bound for the whole remaining suffix.
    have hsuffix (i : ℕ) (hi : k + 1 ≤ i) : ∀ j, i ≤ j → j < n → bound i ≤ a j := by
      induction i, hi using Nat.le_induction with
      | base =>
        intro j hj hjn
        have hge := le_of_descent (triple_sublist w (by omega : k - 1 < k)
          (by omega : k < j) (by omega)) hdesc
          (hav _ (by decide)) (hav _ (by decide)) (hav _ (by decide))
        have hne := hdistinct (by omega : 0 < k - 1) (by omega : k - 1 < j) hjn hpos
        change a (k - 1) ≤ a j at hge
        omega
      | succ i hi ih =>
        intro j hij hj
        have heq := le_antisymm (hle i (by omega)) (ih i le_rfl (by omega))
        have hne := hdistinct (by omega : 0 < i) (by omega : i < j) hj
          (show 0 < a i from heq ▸ Nat.zero_lt_succ _)
        have hlower := ih j (by omega) hj
        have hs := hstep i (by omega) (by omega)
        split at hs <;> omega
    intro j hj hjn
    exact ⟨by omega, by omega,
      le_antisymm (hle (j - 1) (by omega)) (hsuffix (j - 1) (by omega) _ le_rfl (by omega))⟩
  · have hne := hdistinct (by omega : 0 < k - 1) (by omega : k - 1 < k) (by omega) hpos
    have hbound := hle k (by omega)
    exact Or.inl ⟨by omega, by omega, show a k = bound k by omega⟩

end

end MetaMathlibExt

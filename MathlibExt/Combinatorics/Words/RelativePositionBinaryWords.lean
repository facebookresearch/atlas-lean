/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
import Mathlib.Data.Bool.Basic

/-!
# Relative position in binary words

The letter `a` is encoded by `true` and `b` by `false`. Occurrences are numbered from one,
and positions in the word from zero. In a word made of `ab` and `ba` blocks, each block
contains the next occurrence of each letter.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Binary words in which both letters occur infinitely often.** An infinite word
$w = \ell_0 \ell_1 \ell_2 \cdots$ over the letters $a$ and $b$ belongs to the set $\mathcal{W}$ when
both letters occur infinitely often in it, that is, when there are infinitely many positions $i$
with $\ell_i = a$ and infinitely many positions $i$ with $\ell_i = b$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of `𝒲`). -/
public def BothLettersInfinite (w : ℕ → Bool) : Prop :=
  {i | w i = true}.Infinite ∧ {i | w i = false}.Infinite

/-- **Position function of a letter.** For an infinite binary word $w = \ell_0 \ell_1 \cdots$,
a letter $\alpha$ and $n \ge 1$, $p_\alpha(n)$ is the position of the $n$-th occurrence of $\alpha$
in $w$, counting positions from $0$; that is, $p_\alpha(n)$ is the $n$-th smallest index $i$ with
$\ell_i = \alpha$.

By convention $p_\alpha(n) = 0$ when $\alpha$ occurs fewer than $n$ times in $w$, and
$p_\alpha(0) = p_\alpha(1)$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of position functions). -/
public noncomputable def letterPosition (w : ℕ → Bool) (α : Bool) (n : ℕ) : ℕ :=
  Nat.nth (fun i => w i = α) (n - 1)

/-- **Relative position function.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word over
$\{a, b\}$, and for a letter $\alpha$ and $n \ge 1$ let $p_\alpha(n)$ be the position (counting
from $0$) of the $n$-th occurrence of $\alpha$ in $w$, or $0$ if $\alpha$ occurs fewer than $n$
times. The relative position function of $w$ is the integer-valued function
$r(n) = p_b(n) - p_a(n)$, $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the relative position function). -/
public noncomputable def relativePosition (w : ℕ → Bool) (n : ℕ) : ℤ :=
  (letterPosition w false n : ℤ) - letterPosition w true n

/-- **Position of the first occurrence of the initial letter.** If an infinite binary word $w$
starts with the letter $\alpha$, then the first occurrence of $\alpha$ in $w$ is at position $0$,
that is, $p_\alpha(1) = 0$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of position functions). -/
public theorem letterPosition_one_of_head {w : ℕ → Bool} {α : Bool} (h : w 0 = α) :
    letterPosition w α 1 = 0 := by
  simp [letterPosition, Nat.nth_zero_of_zero (p := fun i => w i = α) h]

/-- **Relative position of a word starting with $ab$.** If an infinite word $w$ over $\{a, b\}$
starts with $ab$, then its relative position function satisfies $r(1) = 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the relative position function). -/
public theorem relativePosition_one_of_head_ab {w : ℕ → Bool} (h₀ : w 0 = true)
    (h₁ : w 1 = false) : relativePosition w 1 = 1 := by
  have hb : letterPosition w false 1 = 1 := by
    simp only [letterPosition, Nat.sub_self, Nat.nth_zero]
    refine le_antisymm (Nat.sInf_le h₁) (Nat.one_le_iff_ne_zero.2 fun h => ?_)
    rcases Nat.sInf_eq_zero.1 h with h | h
    · have h' : w 0 = false := h
      simp [h₀] at h'
    · exact (Set.eq_empty_iff_forall_notMem.1 h 1) h₁
  simp [relativePosition, hb, letterPosition_one_of_head h₀]

/-- **Deleting the first occurrence of a letter.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an
infinite word over the letters $a$ and $b$, let $\alpha$ be a letter, and let $p$ be the position
(counted from $0$) of the first occurrence of $\alpha$ in $w$, with $p = 0$ if $\alpha$ does not
occur in $w$. The word $D_\alpha(w)$ has letter $\ell_i$ at each position $i < p$ and letter
$\ell_{i+1}$ at each position $i \ge p$. So $D_\alpha(w)$ is $w$ with its first $\alpha$ deleted,
and, when $\alpha$ does not occur in $w$, it is $w$ with its first letter deleted.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the deletion operators `D_a`, `D_b`). -/
public noncomputable def deleteFirst (w : ℕ → Bool) (α : Bool) : ℕ → Bool :=
  fun i => if i < letterPosition w α 1 then w i else w (i + 1)

/-- **The deletion operator.** For an infinite word $w$ over the letters $a$ and $b$, the word
$D(w)$ is $D_a(D_b(w))$, where $D_\alpha$ deletes the first occurrence of the letter $\alpha$
(and deletes the first letter of a word in which $\alpha$ does not occur): first apply $D_b$,
then $D_a$. When both letters occur in $w$, $D(w)$ is $w$ with its first $b$ and its first $a$
deleted.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the deletion operator `D`). -/
public noncomputable def deletion (w : ℕ → Bool) : ℕ → Bool :=
  deleteFirst (deleteFirst w false) true

/-- **Deleting a leading letter.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word
over the letters $a$ and $b$, let $\alpha$ be a letter, and let $D_\alpha$ be the operator that
deletes the first occurrence of $\alpha$ from a word (and deletes the first letter of a word in
which $\alpha$ does not occur). If $\ell_0 = \alpha$, then $D_\alpha$ shifts $w$ by one:
$D_\alpha(w) = \ell_1 \ell_2 \ell_3 \cdots$, that is, the letter of $D_\alpha(w)$ at each
position $i$ is $\ell_{i+1}$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2
(definition of the deletion operators). -/
public theorem deleteFirst_of_head {w : ℕ → Bool} {α : Bool} (h : w 0 = α) :
    deleteFirst w α = fun i => w (i + 1) := by
  funext i
  simp [deleteFirst, letterPosition_one_of_head h]

/-- **Letter-counting function.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite binary
word, $\alpha$ a letter and $m$ a natural number. The counting function $\#_\alpha(m)$ is the
number of indices $i < m$ with $\ell_i = \alpha$, that is, the number of letters $\alpha$ among
the first $m$ letters $\ell_0, \dots, \ell_{m-1}$ of $w$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 3
(definition of the counting function). -/
public def letterCount (w : ℕ → Bool) (α : Bool) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun i => w i = α).card

/-- **The letter-counting function at zero.** For every infinite binary word $w$ and every
letter $\alpha$, $\#_\alpha(0) = 0$, where $\#_\alpha(m)$ is the number of letters $\alpha$ among
the first $m$ letters of $w$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 3
(definition of the counting function). -/
public theorem letterCount_zero (w : ℕ → Bool) (α : Bool) : letterCount w α 0 = 0 := by
  simp [letterCount]

/-- **Recursion for the letter-counting function.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an
infinite binary word, $\alpha$ a letter and $m$ a natural number, and let $\#_\alpha(m)$ be the
number of letters $\alpha$ among $\ell_0, \dots, \ell_{m-1}$. Then $\#_\alpha(m+1)$ equals
$\#_\alpha(m) + 1$ if $\ell_m = \alpha$, and $\#_\alpha(m)$ otherwise.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 3
(definition of the counting function). -/
public theorem letterCount_succ (w : ℕ → Bool) (α : Bool) (m : ℕ) :
    letterCount w α (m + 1) = letterCount w α m + if w m = α then 1 else 0 := by
  simp only [letterCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- **Image of an infinite word under a substitution.** Let $\varrho$ be a substitution on the
letters $a$ and $b$, sending each letter to a finite word and extended to finite words by
concatenation, and let $w = \ell_0 \ell_1 \ell_2 \cdots$ and $v$ be infinite binary words. Then
$v$ is the image $\varrho(w)$ of $w$ when, for every $m$, the finite word
$\varrho(\ell_0 \cdots \ell_{m-1})$ is a prefix of $v$, and these words are arbitrarily long:
for every $N$ there is an $m$ such that $\varrho(\ell_0 \cdots \ell_{m-1})$ has length at least
$N$. A word $w$ that is its own image $\varrho(w)$ is a fixed point of $\varrho$.

Without the length condition an erasing substitution, such as the one sending both letters to
the empty word, would make every infinite word an image of every other.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 1
(binary substitutions as homomorphisms of words) and Section 3 (images `ϱ(w)`). -/
public def IsSubstitutionImage (ϱ : Bool → List Bool) (w v : ℕ → Bool) : Prop :=
  (∀ N, ∃ m, N ≤ ((List.ofFn fun j : Fin m => w j).flatMap ϱ).length) ∧
  ∀ m i, i < ((List.ofFn fun j : Fin m => w j).flatMap ϱ).length →
    v i = ((List.ofFn fun j : Fin m => w j).flatMap ϱ).getD i false

/-- **Every word is fixed by the identity substitution.** Every infinite binary word $w$ is
its own image under the identity substitution $a \mapsto a$, $b \mapsto b$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 1
(binary substitutions as homomorphisms of words). -/
public theorem isSubstitutionImage_id (w : ℕ → Bool) :
    IsSubstitutionImage (fun x => [x]) w w := by
  refine ⟨fun N => ⟨N, by simp⟩, ?_⟩
  intro m i hi
  simp only [List.flatMap_singleton', List.length_ofFn] at hi ⊢
  simp [List.getD_eq_getElem?_getD, hi]

/-- **Relative positions of a word made of $ab$ and $ba$ blocks.** Let
$w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word over $\{a, b\}$ such that every block
$\ell_{2i} \ell_{2i+1}$ ($i \ge 0$) is $ab$ or $ba$, and let $r$ be its relative position
function. Then for every $n \ge 1$, $r(n) = 1$ if $\ell_{2n-2} = a$ and $r(n) = -1$ if
$\ell_{2n-2} = b$.

The block condition forces both letters to occur infinitely often, so no separate hypothesis on
$w$ is needed.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 69
(`jis-2025-25.1.5-prop-69`). -/
public theorem relativePosition_of_dimers {w : ℕ → Bool}
    (hdim : ∀ i, w (2 * i) ≠ w (2 * i + 1)) (n : ℕ) (hn : 1 ≤ n) :
    relativePosition w n = if w (2 * (n - 1)) then 1 else -1 := by
  have opposite (k : ℕ) : w (2 * k + 1) = !w (2 * k) :=
    Bool.eq_not_iff.mpr (hdim k).symm
  have count_blocks (α : Bool) (k : ℕ) : letterCount w α (2 * k) = k := by
    induction k with
    | zero => exact letterCount_zero w α
    | succ k ih =>
      rw [Nat.mul_succ, letterCount_succ, letterCount_succ, ih, opposite]
      cases w (2 * k) <;> cases α <;> simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have pos (i : ℕ) : letterPosition w (w i) (letterCount w (w i) i + 1) = i := by
    simpa only [letterPosition, Nat.add_sub_cancel, Nat.count_eq_card_filter_range, letterCount]
      using Nat.nth_count (p := fun j => w j = w i) (n := i) rfl
  have first := pos (2 * k)
  have second := pos (2 * k + 1)
  rw [count_blocks] at first
  rw [letterCount_succ, ite_eq_right (hdim k), Nat.add_zero, count_blocks] at second
  rw [opposite] at second
  cases h : w (2 * k) <;> simp_all [relativePosition]

end

/-- Consecutive copies of a letter are exactly consecutive occurrences at distance one. -/
private theorem run_iff_letterPosition_diff {w : ℕ → Bool} {α : Bool}
    (hInf : {i | w i = α}.Infinite) {k : ℕ} (hk : 1 ≤ k) :
    (∃ i, ∀ j < k, w (i + j) = α) ↔
      ∃ n, 1 ≤ n ∧ ∀ j < k - 1,
        letterPosition w α (n + j + 1) - letterPosition w α (n + j) = 1 := by
  let p (i : ℕ) : Prop := w i = α
  have hp : (Set.ofPred p).Infinite := hInf
  constructor
  · rintro ⟨i, hr⟩
    let n := Nat.count p i
    have pos (j : ℕ) (hj : j < k) : letterPosition w α (n + 1 + j) = i + j := by
      have hcount : Nat.count p (i + j) = n + j := by
        rw [Nat.count_add]
        change n + Nat.count (fun a => p (i + a)) j = n + j
        congr 1
        rw [Nat.count_eq_card_filter_range, Finset.filter_true_of_mem, Finset.card_range]
        intro a ha
        exact hr a ((Finset.mem_range.mp ha).trans hj)
      change Nat.nth p (n + 1 + j - 1) = i + j
      rw [show n + 1 + j - 1 = n + j by omega, ← hcount]
      exact Nat.nth_count (p := p) (hr j hj)
    refine ⟨n + 1, by omega, fun j hj => ?_⟩
    have hnext := pos (j + 1) (by omega)
    rw [← Nat.add_assoc (n + 1) j 1] at hnext
    rw [hnext, pos j (by omega)]
    omega
  · rintro ⟨n, _, hd⟩
    have pos (j : ℕ) (hj : j < k) :
        letterPosition w α (n + j) = letterPosition w α n + j := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hstep := hd j (by omega)
        have hprev := ih (by omega)
        change letterPosition w α (n + (j + 1)) = letterPosition w α n + (j + 1)
        rw [← Nat.add_assoc n j 1]
        omega
    refine ⟨letterPosition w α n, fun j hj => ?_⟩
    rw [← pos j hj]
    exact Nat.nth_mem_of_infinite hp (n + j - 1)

/-- **Runs of one letter and gaps between letter positions.** Let $w = \ell_0 \ell_1 \ell_2 \cdots$
be an infinite word over the letters $a$ and $b$ in which both letters occur infinitely often and
$\ell_0 = a$. For a letter $\alpha$ and $n \ge 1$, let $p_\alpha(n)$ be the position of the $n$-th
occurrence of $\alpha$ in $w$, counting positions from $0$. Let $k \ge 1$. Then the following are
equivalent: there is $i$ with $\ell_{i+j} = b$ for all $0 \le j < k$ (the block $b^k$ occurs in
$w$); there is $n \ge 1$ with $p_a(n+1) - p_a(n) > k$; and there is $n \ge 1$ with
$p_b(n+j+1) - p_b(n+j) = 1$ for all $0 \le j < k - 1$. Moreover, there is $i$ with
$\ell_{i+j} = a$ for all $0 \le j < k$ (the block $a^k$ occurs in $w$) if and only if there is
$n \ge 1$ with $p_a(n+j+1) - p_a(n+j) = 1$ for all $0 \le j < k - 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 13
(`jis-2025-25.1.5-lem-13`). -/
public theorem subword_run_iff_letterPosition_diff {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) {k : ℕ} (hk : 1 ≤ k) :
    ((∃ i, ∀ j < k, w (i + j) = false) ↔
        ∃ n, 1 ≤ n ∧ k < letterPosition w true (n + 1) - letterPosition w true n) ∧
      ((∃ i, ∀ j < k, w (i + j) = false) ↔
        ∃ n, 1 ≤ n ∧ ∀ j < k - 1,
          letterPosition w false (n + j + 1) - letterPosition w false (n + j) = 1) ∧
      ((∃ i, ∀ j < k, w (i + j) = true) ↔
        ∃ n, 1 ≤ n ∧ ∀ j < k - 1,
          letterPosition w true (n + j + 1) - letterPosition w true (n + j) = 1) := by
  refine ⟨?_, run_iff_letterPosition_diff hw.2 hk, run_iff_letterPosition_diff hw.1 hk⟩
  let p (i : ℕ) : Prop := w i = true
  have hp : (Set.ofPred p).Infinite := hw.1
  constructor
  · rintro ⟨i, hr⟩
    have hi : 0 < i := by
      by_contra! hi
      have he : i = 0 := by omega
      simpa [he, h₀] using hr 0 hk
    let n := Nat.count p i
    have hn : 1 ≤ n := by
      have hc := Nat.count_strict_mono (p := p) h₀ hi
      simpa only [n, Nat.count_zero] using Nat.succ_le_of_lt hc
    have hleft : Nat.nth p (n - 1) < i := Nat.nth_lt_of_lt_count (p := p) (by
      change n - 1 < n
      omega)
    have hir : i ≤ Nat.nth p n := Nat.le_nth_count hp i
    have hright : i + k ≤ Nat.nth p n := by
      by_contra! hl
      have hj : Nat.nth p n - i < k := by omega
      have hfalse := hr _ hj
      have he : i + (Nat.nth p n - i) = Nat.nth p n := by omega
      rw [he] at hfalse
      have htrue : w (Nat.nth p n) = true := Nat.nth_mem_of_infinite hp n
      rw [htrue] at hfalse
      contradiction
    refine ⟨n, hn, ?_⟩
    change k < Nat.nth p (n + 1 - 1) - Nat.nth p (n - 1)
    rw [Nat.add_sub_cancel]
    omega
  · rintro ⟨n, hn, hg⟩
    have hg' : k < Nat.nth p n - Nat.nth p (n - 1) := by
      simpa only [letterPosition, p, Nat.add_sub_cancel] using hg
    refine ⟨Nat.nth p (n - 1) + 1, fun j hj => ?_⟩
    let i := Nat.nth p (n - 1) + 1 + j
    have hno : ¬p i := by
      intro hi
      have hl : Nat.nth p (n - 1) < i := by dsimp [i]; omega
      have hu : i < Nat.nth p n := by dsimp [i]; omega
      have hwit := (Nat.nth_add_one_le_iff hp (n := n - 1) hi).mpr hl
      rw [show n - 1 + 1 = n by omega] at hwit
      exact (not_lt_of_ge hwit) hu
    simpa only [p, Bool.not_eq_true] using hno

end MetaMathlibExt

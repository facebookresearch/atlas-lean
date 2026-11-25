/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# The `q`-gram filtering lemma for approximate matching

Two strings of length `w` over an alphabet `α` are words `x y : Fin w → α`, and the number of
positions in which they differ is their Hamming distance `hammingDist x y`. For `q ≤ w` the
`q`-gram of `x` at offset `i ∈ {0, …, w - q}` is the window `x i, x (i + 1), …, x (i + q - 1)`
(`qGram x q i`); two words share a positionally aligned `q`-gram at `i` when their `q`-grams
at `i` are equal.

A mismatch at position `j` lies only in the windows starting at `j - q + 1, …, j`, so at most
`k` mismatches spoil at most `k q` of the `w - q + 1` aligned `q`-grams. This is the counting
behind exhaustive `q`-gram (seed) filters for approximate matching under the Hamming distance.

## Main results

* `sub_add_one_le_card_qGram_eq_add_mul`: **the `q`-gram lemma**: if `q ≤ w` and `x`, `y`
  differ in at most `k` positions, then `w - q + 1 ≤ s + k q`, where `s` is the number of
  offsets at which their `q`-grams agree; that is, they share at least `w - q + 1 - k q`
  aligned `q`-grams.
* `exists_qGram_eq_of_mul_lt`: in particular, if `k q < w - q + 1` they share one.
* `setOf_hammingDist_le_subset`: consequently, when `k q < w - q + 1`, a filter that reports
  every pair of words sharing an aligned `q`-gram reports every pair at Hamming distance at
  most `k`.

## Implementation notes

The bound is stated additively, `w - q + 1 ≤ s + k q` in `ℕ`, so that it reads the same when
the difference `w - q + 1 - k q` is negative. The hypothesis `q ≤ w` makes the truncated
subtraction in `w - q + 1` exact: it is the number of offsets. The offsets of `qGram` are
`Fin (w + 1 - q)`, which is `w - q + 1` offsets when `q ≤ w` and none when `q > w`, so that
`qGram` needs no hypothesis. The degenerate case `q = 0` is allowed: every offset then carries
the empty `q`-gram.

## References

* MIT 6.047 Computational Biology (Fall 2015), compiled lecture notes, Section 3.4 (the
  pigeonhole idea behind seed filtering in BLAST); the counting bound is the argument above.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Filtering.QGramLemma

open Finset

variable {α : Type*} {w : ℕ}

/-- **The $q$-gram of a word at an offset.** For a word $x = x_0 x_1 \cdots x_{w-1}$ of length $w$
and an offset $i$ with $0 \le i \le w - q$, the $q$-gram of $x$ at $i$ is the window
$x_i x_{i+1} \cdots x_{i+q-1}$ of length $q$, as a word indexed by $\{0, \dots, q - 1\}$. There
are $w - q + 1$ offsets when $q \le w$ and none when $q > w$. -/
def qGram (x : Fin w → α) (q : ℕ) (i : Fin (w + 1 - q)) : Fin q → α :=
  fun j => x ⟨i + j, by omega⟩

/-- **The $q$-gram (seed) filtering lemma.** Let $w$, $q$ and $k$ be natural numbers with
$q \le w$, and let $x$ and $y$ be words of length $w$ that differ in at most $k$ positions. Then
the number $s$ of offsets $i \in \{0, \dots, w - q\}$ at which $x$ and $y$ have equal $q$-grams
satisfies $w - q + 1 \le s + kq$: they share at least $w - q + 1 - kq$ positionally aligned
$q$-grams. -/
theorem sub_add_one_le_card_qGram_eq_add_mul [DecidableEq α] {q k : ℕ} (hqw : q ≤ w)
    {x y : Fin w → α} (hxy : hammingDist x y ≤ k) :
    w - q + 1 ≤ #{i | qGram x q i = qGram y q i} + k * q := by
  -- The offsets of the windows that contain position `j`.
  let windows : Fin w → Finset (Fin (w + 1 - q)) := fun j => {i | (i : ℕ) ≤ j ∧ (j : ℕ) < i + q}
  have hwindows (j : Fin w) : #(windows j) ≤ q := by
    calc #(windows j) ≤ #(Ico (j + 1 - q : ℕ) (j + 1)) := by
          refine card_le_card_of_injOn (fun i => (i : ℕ)) (fun i hi => ?_)
            (fun a _ b _ h => Fin.ext h)
          simp only [windows, mem_coe, mem_filter, mem_univ, true_and] at hi
          simp only [mem_coe, mem_Ico]
          omega
      _ ≤ q := by simp only [Nat.card_Ico]; omega
  -- Every offset with unequal `q`-grams lies in a window of some mismatch.
  have hbad : #{i | ¬qGram x q i = qGram y q i} ≤ k * q := by
    calc #{i | ¬qGram x q i = qGram y q i}
        ≤ #(({j | x j ≠ y j} : Finset (Fin w)).biUnion windows) := by
          refine card_le_card fun i hi => ?_
          simp only [mem_filter, mem_univ, true_and] at hi
          obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
          simp only [mem_biUnion, mem_filter, mem_univ, true_and]
          exact ⟨⟨i + j, by omega⟩, hj, by simp [windows]⟩
      _ ≤ hammingDist x y * q := card_biUnion_le_card_mul _ _ _ fun j _ => hwindows j
      _ ≤ k * q := Nat.mul_le_mul_right q hxy
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin (w + 1 - q))))
    fun i => qGram x q i = qGram y q i
  rw [card_univ, Fintype.card_fin] at hsplit
  omega

/-- **Words within Hamming distance $k$ share an aligned $q$-gram.** Let $w$, $q$ and $k$ be
natural numbers with $q \le w$ and $kq < w - q + 1$. Two words of length $w$ that differ in at most
$k$ positions share at least one positionally aligned $q$-gram: there is an offset
$i \in \{0, \dots, w - q\}$ at which their $q$-grams are equal. -/
theorem exists_qGram_eq_of_mul_lt [DecidableEq α] {q k : ℕ} (hqw : q ≤ w)
    (hkq : k * q < w - q + 1) {x y : Fin w → α} (hxy : hammingDist x y ≤ k) :
    ∃ i, qGram x q i = qGram y q i := by
  have hpos : 0 < #{i | qGram x q i = qGram y q i} := by
    have := sub_add_one_le_card_qGram_eq_add_mul hqw hxy
    omega
  obtain ⟨i, hi⟩ := card_pos.mp hpos
  exact ⟨i, (mem_filter.mp hi).2⟩

/-- **An exhaustive $q$-gram filter loses no pair within Hamming distance $k$.** Let $w$, $q$ and
$k$ be natural numbers with $q \le w$ and $kq < w - q + 1$, and let $R$ be a set of pairs of words
of length $w$ (the pairs a filter reports) that contains every pair sharing a positionally aligned
$q$-gram. Then $R$ contains every pair of words of length $w$ that differ in at most $k$
positions. -/
theorem setOf_hammingDist_le_subset [DecidableEq α] {q k : ℕ} (hqw : q ≤ w)
    (hkq : k * q < w - q + 1) {R : Set ((Fin w → α) × (Fin w → α))}
    (hR : {p | ∃ i, qGram p.1 q i = qGram p.2 q i} ⊆ R) :
    {p : (Fin w → α) × (Fin w → α) | hammingDist p.1 p.2 ≤ k} ⊆ R :=
  fun _ hp => hR (exists_qGram_eq_of_mul_lt hqw hkq hp)

end Cslib.Bioinformatics.Filtering.QGramLemma

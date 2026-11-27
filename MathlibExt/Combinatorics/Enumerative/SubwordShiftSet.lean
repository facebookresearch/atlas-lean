/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat

/-! # Well-based sets and binary subword shifts

`IsWellBased` is the split condition on a finite set of natural numbers, without a positivity
requirement. Allen's notion is `IsPositiveWellBased`, which also excludes zero.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Well-based sets.** A finite set `Q` of natural numbers satisfies the split condition if for
all $x \in Q$ and $0 < a < x$, at least one of $a$ and $x - a$ lies in $Q$. The condition allows `0`
in `Q`; for example, the singleton `{0}` satisfies it vacuously.

For a nonempty set of positive integers, the split condition is equivalent to the well-based
sequence condition of Kitaev and Valyuzhenich for its increasing enumeration. Such a set has
least element $1$ if it satisfies the split condition: otherwise neither part of the split
$x = 1 + (x - 1)$ of its least element $x$ could lie in `Q`.

Allen's formulation also counts the empty set as well based. `IsPositiveWellBased Q` encodes
Allen's convention by requiring `0 ∉ Q` and the split condition, but not nonemptiness.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public def IsWellBased (Q : Finset ℕ) : Prop :=
  ∀ x ∈ Q, ∀ a, 0 < a → a < x → a ∈ Q ∨ x - a ∈ Q

public def IsPositiveWellBased (Q : Finset ℕ) : Prop :=
  0 ∉ Q ∧ IsWellBased Q

public theorem isWellBased_Icc (q : ℕ) : IsWellBased (Finset.Icc 1 q) := by
  intro x hx a ha hax
  left
  simp only [Finset.mem_Icc] at hx ⊢
  omega

/-- **The set $\{1, \dots, q\}$ is well based.** For every natural number $q$, the set
$\{1, 2, \dots, q\}$ is well based.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public theorem isPositiveWellBased_Icc (q : ℕ) : IsPositiveWellBased (Finset.Icc 1 q) :=
  ⟨by simp [Finset.mem_Icc], isWellBased_Icc q⟩

public theorem not_isWellBased_one_three_four : ¬ IsWellBased {1, 3, 4} := by
  intro h
  have := h 4 (by decide) 2 (by decide) (by decide)
  simp at this

/-- **The set $\{1, 3, 4\}$ is not well based.** The set $\{1, 3, 4\}$ is not well based: in
$4 = 2 + 2$ neither part lies in the set.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1. -/
public theorem not_isPositiveWellBased_one_three_four : ¬ IsPositiveWellBased {1, 3, 4} :=
  fun h => not_isWellBased_one_three_four h.2

/-- **Shift set of a binary subword.** For natural numbers $\omega$ and $l$, the shift set of
$\omega$ with length $l$ is the set of $j \in \{1, \dots, l - 1\}$ with
$\lfloor \omega / 2^j \rfloor \ne \omega \bmod 2^{l-j}$. When $\omega < 2^l$ is read as a binary
word of length $l$, this says that the leftmost $l - j$ bits of $\omega$ differ from its rightmost
$l - j$ bits.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 21. -/
public def subwordShiftSet (ω l : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (l - 1)).filter fun j => ω / 2 ^ j ≠ ω % 2 ^ (l - j)

@[simp] public theorem zero_notMem_subwordShiftSet (ω l : ℕ) : 0 ∉ subwordShiftSet ω l := by
  simp [subwordShiftSet, Finset.mem_Icc]

/-- **Shift set of the subword 1010.** The shift set of the binary subword $1010$ of length $4$
(the number $10$) is $\{1, 3\}$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 5.1 (OEIS list after Theorem 21). -/
public theorem subwordShiftSet_1010 : subwordShiftSet 0b1010 4 = {1, 3} := by
  decide

-- A positive shift below the word length is excluded exactly when it is a period.
private theorem not_mem_subwordShiftSet_iff {ω l j : ℕ}
    (hω : ω < 2 ^ l) (hj : 0 < j) (hjl : j < l) :
    j ∉ subwordShiftSet ω l ↔ ∀ i, i + j < l → ω.testBit (i + j) = ω.testBit i := by
  have hjIcc : j ∈ Finset.Icc 1 (l - 1) := Finset.mem_Icc.mpr ⟨hj, by omega⟩
  simp only [subwordShiftSet, Finset.mem_filter, hjIcc, true_and, not_ne_iff]
  constructor
  · intro h i hi
    have hlow : i < l - j := by omega
    simpa [Nat.testBit_div_two_pow, hlow] using congrArg (fun n : ℕ => n.testBit i) h
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i + j < l
    · have hlow : i < l - j := by omega
      simp [hlow, h i hi]
    · -- Both truncated words have zero bits beyond the overlap.
      have hhigh : ω < 2 ^ (i + j) :=
        hω.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))
      simp [show ¬ i < l - j by omega, Nat.testBit_lt_two_pow hhigh]

public theorem isWellBased_subwordShiftSet (ω l : ℕ) (hω : ω < 2 ^ l) :
    IsWellBased (subwordShiftSet ω l) := by
  intro x hx a ha hax
  have hxIcc : x ∈ Finset.Icc 1 (l - 1) := (Finset.mem_filter.mp hx).1
  obtain ⟨hx₁, hxle⟩ := Finset.mem_Icc.mp hxIcc
  have hxl : x < l := by omega
  by_cases haQ : a ∈ subwordShiftSet ω l
  · exact Or.inl haQ
  · right
    by_contra hbQ
    have haPeriod := (not_mem_subwordShiftSet_iff hω ha (by omega)).mp haQ
    have hbPeriod := (not_mem_subwordShiftSet_iff hω (j := x - a) (by omega) (by omega)).mp hbQ
    apply ((not_mem_subwordShiftSet_iff hω (by omega) hxl).mpr ?_) hx
    -- Compose the two periods at i, i + a and i + x, all within the word.
    intro i hi
    have hsum : i + a + (x - a) = i + x := by omega
    rw [← hsum]
    exact (hbPeriod (i + a) (by omega)).trans (haPeriod i (by omega))

/-- **Subword shift sets are well based.** Let $l$ be a natural number and $\omega$ a binary word
of length $l$, read as a natural number $\omega < 2^l$. Then the set $Q$ of those
$j \in \{1, \dots, l-1\}$ for which the leftmost $l - j$ bits of $\omega$ differ from its
rightmost $l - j$ bits, that is $\lfloor \omega / 2^j \rfloor \ne \omega \bmod 2^{l-j}$, is well
based.

This is the well-based part of Theorem 22 of the paper. Its further claim, that no integer
linear combination of the elements $p_i$ of $\{1, \dots, q\} \setminus Q$ lies in $Q$ (with $q$
the largest element of $Q$), is omitted: for $\omega = 010100101$ and $l = 9$ one gets
$Q = \{1, 2, 3, 4, 6, 8\}$, $q = 8$, $p_1 = 5$, $p_2 = 7$, and $p_2 - p_1 = 2 \in Q$. The side
condition $q = l - 1$ of Theorem 21 is not needed.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 22. -/
public theorem isPositiveWellBased_subwordShiftSet (ω l : ℕ) (hω : ω < 2 ^ l) :
    IsPositiveWellBased (subwordShiftSet ω l) :=
  ⟨zero_notMem_subwordShiftSet ω l, isWellBased_subwordShiftSet ω l hω⟩

end

end MetaMathlibExt

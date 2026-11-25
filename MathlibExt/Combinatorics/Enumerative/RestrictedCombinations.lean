/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Combinations without specified separations: generating functions

The main result is `restrictedCombination_genFun_eq_tiling_genFun`: the bivariate
generating function of the restricted combinations is, up to the shift by the largest
forbidden difference and the initial segment of the tiling generating function, the
generating function of the restricted-overlap tilings.

Statements from Michael A. Allen, *Connections Between Combinations Without Specified
Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of
Integer Sequences 28 (2025), Article 25.3.7 (arXiv:2409.00624v4).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Restricted combinations.** For a finite set $Q$ of natural numbers and $n, k \ge 0$, the
restricted combinations are the $k$-element subsets $s$ of $\{1, \dots, n\}$ such that
$b - a \notin Q$ for all $a, b \in s$ with $a < b$. Since only distinct elements are compared,
whether $0 \in Q$ makes no difference.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinations (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powersetCard k).filter fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q

/-- **Number of restricted combinations.** For a finite set $Q$ of natural numbers and natural
numbers $n$ and $k$, $S^Q_{n,k}$ is the number of $k$-subsets of $\{1, \dots, n\}$ in which no
two distinct elements differ by an element of $Q$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedCombinations Q n k).card

/-- **Restricted-overlap tilings.** Let $Q$ be a finite set of natural numbers and let $q$ be its
largest element ($q = 0$ if $Q$ is empty). The $Q$-comb is a piece of length $q + 1$ whose cell
$0$ and cells $j \in Q$ are teeth and whose other cells are gaps. A restricted-overlap tiling of an
$n$-board (cells $0, \dots, n - 1$) with squares and $k$ $Q$-combs is recorded by the set $P$ of
the start cells of its combs, with squares filling the cells that no tooth covers. The
restricted-overlap tilings are the $k$-element sets $P$ of natural numbers $s$ with $s + q < n$
(each comb fits on the board) such that $s \ne s' + j$ for all $s, s' \in P$ and all nonzero
$j \in Q$ (no comb's leftmost cell is covered by a non-leftmost tooth of another comb).

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedOverlapTilings (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  (((Finset.range n).filter fun s => s + Q.sup id < n).powersetCard k).filter
    fun P => ∀ s ∈ P, ∀ s' ∈ P, ∀ j ∈ Q, j ≠ 0 → s ≠ s' + j

/-- **Number of restricted-overlap tilings.** For a finite set $Q$ of natural numbers and natural
numbers $n$ and $k$, $B^Q_{n,k}$ is the number of restricted-overlap tilings of an $n$-board with
squares and $k$ $Q$-combs.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedOverlapTilingCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedOverlapTilings Q n k).card

namespace restrictedCombination_genFun_eq_tiling_genFun

private theorem mem_restrictedCombinations (Q : Finset ℕ) (n k : ℕ) (s : Finset ℕ) :
    s ∈ restrictedCombinations Q n k ↔
      s ⊆ Finset.Icc 1 n ∧ s.card = k ∧
        ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q := by
  simp only [restrictedCombinations, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

private theorem mem_restrictedOverlapTilings (Q : Finset ℕ) (n k : ℕ) (P : Finset ℕ) :
    P ∈ restrictedOverlapTilings Q n k ↔
      P ⊆ (Finset.range n).filter (fun s => s + Q.sup id < n) ∧ P.card = k ∧
        ∀ s ∈ P, ∀ s' ∈ P, ∀ j ∈ Q, j ≠ 0 → s ≠ s' + j := by
  simp only [restrictedOverlapTilings, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

private theorem count_eq (Q : Finset ℕ) (n k : ℕ) :
    restrictedCombinationCount Q n k =
      restrictedOverlapTilingCount Q (n + Q.sup id) k := by
  unfold restrictedCombinationCount restrictedOverlapTilingCount
  apply Finset.card_nbij' (fun s => s.image (· - 1)) (fun P => P.image (· + 1))
  · intro s hs
    simp only [Finset.mem_coe] at hs
    rw [mem_restrictedCombinations] at hs
    change (s.image (· - 1)) ∈ restrictedOverlapTilings Q (n + Q.sup id) k
    rw [mem_restrictedOverlapTilings]
    obtain ⟨hsub, hcard, hcond⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have := hsub ha
      simp only [Finset.mem_Icc] at this
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · have hinj : Set.InjOn (· - 1) s := by
        intro a ha b hb hab
        have ha2 := hsub ha
        have hb2 := hsub hb
        simp only [Finset.mem_Icc] at ha2 hb2
        simp only at hab
        omega
      rw [Finset.card_image_of_injOn hinj]
      exact hcard
    · intro t ht t' ht' j hj hj0 h_eq
      simp only [Finset.mem_image] at ht ht'
      obtain ⟨a, ha, rfl⟩ := ht
      obtain ⟨b, hb, rfl⟩ := ht'
      have ha2 := hsub ha
      have hb2 := hsub hb
      simp only [Finset.mem_Icc] at ha2 hb2
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      by_cases hlt : b < a
      · have hnot := hcond b hb a ha hlt
        apply hnot
        rw [show a - b = j by omega]
        exact hj
      · omega
  · intro P hP
    simp only [Finset.mem_coe] at hP
    rw [mem_restrictedOverlapTilings] at hP
    change (P.image (· + 1)) ∈ restrictedCombinations Q n k
    rw [mem_restrictedCombinations]
    obtain ⟨hsub, hcard, hcond⟩ := hP
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      have ha2 := hsub ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha2
      simp only [Finset.mem_Icc]
      omega
    · have hinj : Set.InjOn (· + 1) P := by
        intro a _ b _ hab
        simp only at hab
        omega
      rw [Finset.card_image_of_injOn hinj]
      exact hcard
    · intro a ha b hb hab
      simp only [Finset.mem_image] at ha hb
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨p', hp', rfl⟩ := hb
      have hp2 := hsub hp
      have hp'2 := hsub hp'
      simp only [Finset.mem_filter, Finset.mem_range] at hp2 hp'2
      have hdiff : p' - p ∈ Q → False := by
        intro hmem
        have hne : p' - p ≠ 0 := by omega
        exact hcond p' hp' p hp (p' - p) hmem hne (by omega)
      intro hmem
      apply hdiff
      have hEq : p' - p = p' + 1 - (p + 1) := by omega
      rw [hEq]
      exact hmem
  · intro s hs
    simp only [Finset.mem_coe] at hs
    rw [mem_restrictedCombinations] at hs
    obtain ⟨hsub, hcard, hcond⟩ := hs
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      have := hsub ha
      simp only [Finset.mem_Icc] at this
      have : a - 1 + 1 = a := by omega
      rw [this] at *
      exact ha
    · intro hx
      exact ⟨x - 1, ⟨x, hx, by simp⟩, by
        have := hsub hx
        simp only [Finset.mem_Icc] at this
        omega⟩
  · intro P hP
    simp only [Finset.mem_coe] at hP
    rw [mem_restrictedOverlapTilings] at hP
    obtain ⟨hsub, hcard, hcond⟩ := hP
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      have : a + 1 - 1 = a := by omega
      rw [this] at *
      exact ha
    · intro hx
      exact ⟨x + 1, ⟨x, hx, by simp⟩, by simp⟩

private theorem tilingCount_eq_zero_of_lt (Q : Finset ℕ) {m k : ℕ}
    (hm : m < Q.sup id) (hk : 1 ≤ k) :
    restrictedOverlapTilingCount Q m k = 0 := by
  unfold restrictedOverlapTilingCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_restrictedOverlapTilings] at hP
  obtain ⟨hsub, hcard, -⟩ := hP
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
  have := hsub hs
  simp only [Finset.mem_filter, Finset.mem_range] at this
  omega

private theorem tilingCount_zero (Q : Finset ℕ) (m : ℕ) :
    restrictedOverlapTilingCount Q m 0 = 1 := by
  unfold restrictedOverlapTilingCount
  have hset : restrictedOverlapTilings Q m 0 = {∅} := by
    ext P
    simp only [Finset.mem_singleton]
    constructor
    · intro hP
      rw [mem_restrictedOverlapTilings] at hP
      exact Finset.card_eq_zero.mp hP.2.1
    · intro hP
      subst hP
      rw [mem_restrictedOverlapTilings]
      refine ⟨by simp, by simp, by simp⟩
  rw [hset, Finset.card_singleton]

private theorem tilingCount_eq_zero_of_gt (Q : Finset ℕ) {m k : ℕ}
    (hq : Q.sup id ≤ m) (hk : m - Q.sup id < k) :
    restrictedOverlapTilingCount Q m k = 0 := by
  unfold restrictedOverlapTilingCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_restrictedOverlapTilings] at hP
  obtain ⟨hsub, hcard, -⟩ := hP
  have hle : P.card ≤ m - Q.sup id := by
    calc P.card ≤ ((Finset.range m).filter (fun s => s + Q.sup id < m)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.range (m - Q.sup id)).card := by
          apply Finset.card_le_card
          intro x hx
          have hx' := hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx'
          obtain ⟨-, hlt⟩ := hx'
          simp only [Finset.mem_range]
          omega
      _ = m - Q.sup id := Finset.card_range _
  omega

private theorem polynomial_eq (Q : Finset ℕ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
        (restrictedOverlapTilingCount Q m k : Polynomial ℤ) * Polynomial.X ^ k) =
      if m < Q.sup id then 1 else
        ∑ k ∈ Finset.range (m - Q.sup id + 1),
          (restrictedCombinationCount Q (m - Q.sup id) k : Polynomial ℤ) *
            Polynomial.X ^ k := by
  by_cases hm : m < Q.sup id
  · simp only [hm, ↓reduceIte]
    rw [Finset.sum_eq_single 0]
    · simp [tilingCount_zero]
    · intro k _ hk0
      have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      rw [tilingCount_eq_zero_of_lt Q hm hk]
      simp
    · intro h0
      simp at h0
  · simp only [hm, ↓reduceIte]
    have hq : Q.sup id ≤ m := Nat.le_of_not_lt hm
    have hsum : (∑ k ∈ Finset.range (m - Q.sup id + 1),
          (restrictedOverlapTilingCount Q m k : Polynomial ℤ) * Polynomial.X ^ k) =
        ∑ k ∈ Finset.range (m + 1),
          (restrictedOverlapTilingCount Q m k : Polynomial ℤ) * Polynomial.X ^ k := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro k hk hknot
      have hknot2 : ¬ k < m - Q.sup id + 1 := fun hlt => hknot (Finset.mem_range.mpr hlt)
      rw [tilingCount_eq_zero_of_gt Q hq (by omega)]
      simp
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have hEq : restrictedOverlapTilingCount Q m k =
        restrictedCombinationCount Q (m - Q.sup id) k := by
      have h := count_eq Q (m - Q.sup id) k
      rw [show m - Q.sup id + Q.sup id = m by omega] at h
      exact h.symm
    rw [hEq]

private theorem coeff_sum_X_pow (Q : Finset ℕ) (m : ℕ) :
    PowerSeries.coeff (R := Polynomial ℤ) m
        (∑ n ∈ Finset.range (Q.sup id),
          (PowerSeries.X : PowerSeries (Polynomial ℤ)) ^ n) =
      if m < Q.sup id then (1 : Polynomial ℤ) else 0 := by
  rw [map_sum]
  simp only [PowerSeries.coeff_X_pow]
  by_cases hm : m < Q.sup id
  · simp only [hm, ↓reduceIte]
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hne
      simp [Ne.symm hne]
    · simp [hm]
  · simp only [hm, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [show m ≠ n by omega]

end restrictedCombination_genFun_eq_tiling_genFun

/-- **Generating functions of restricted combinations and restricted-overlap tilings.** Let $Q$
be a finite set of natural numbers and let $q$ be its largest element ($q = 0$ if $Q$ is empty).
Write $S^Q_{n,k}$ for the number of $k$-subsets of $\{1, \dots, n\}$ in which no two elements
differ by an element of $Q$, and $B^Q_{n,k}$ for the number of restricted-overlap tilings of an
$n$-board with squares and $k$ $Q$-combs. In the ring $\mathbb{Z}[y][[x]]$ of power series in
$x$ with coefficients in $\mathbb{Z}[y]$, let
$g^Q(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} S^Q_{n,k} x^n y^k$ and
$G(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} B^Q_{n,k} x^n y^k$. Then
$$x^q g^Q(x, y) = G(x, y) - \sum_{n=0}^{q-1} x^n.$$

This is the paper's formula $g^Q = \bigl(G - (1 - x^q)/(1 - x)\bigr)/x^q$ with the denominators
cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 7. -/
public theorem restrictedCombination_genFun_eq_tiling_genFun (Q : Finset ℕ) :
    PowerSeries.X ^ Q.sup id * PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) =
      PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedOverlapTilingCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) -
        ∑ n ∈ Finset.range (Q.sup id), PowerSeries.X ^ n := by
  apply PowerSeries.ext
  intro m
  have hsum : PowerSeries.coeff m
      (∑ n ∈ Finset.range (Q.sup id), (PowerSeries.X : PowerSeries (Polynomial ℤ)) ^ n) =
      if m < Q.sup id then 1 else 0 :=
    restrictedCombination_genFun_eq_tiling_genFun.coeff_sum_X_pow Q m
  rw [PowerSeries.coeff_X_pow_mul', map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  simp only [hsum, restrictedCombination_genFun_eq_tiling_genFun.polynomial_eq]
  by_cases hm : m < Q.sup id
  · have hle : ¬ Q.sup id ≤ m := by omega
    simp only [hle, hm, ↓reduceIte]
    simp
  · have hle : Q.sup id ≤ m := Nat.le_of_not_lt hm
    simp only [hle, hm, ↓reduceIte]
    simp

end

end MetaMathlibExt

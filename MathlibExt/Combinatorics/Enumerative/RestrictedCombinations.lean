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
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic.LinearCombination

/-!
# Combinations without specified separations: generating functions

The main result is `restrictedCombination_genFun_eq_tiling_genFun`: the bivariate
generating function of the restricted combinations is, up to the shift by the largest
forbidden difference and the initial segment of the tiling generating function, the
generating function of the restricted-overlap tilings.

For forbidden differences 1 and 4, the next membership bit depends only on the last four
bits. The eight reachable windows give a system of linear equations for the generating series.
For differences 1 and 5, recording only the future positions blocked by those bits gives eleven
reachable states and a corresponding system of linear equations.

## References

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and
  Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
  Sequences 28 (2025), Article 25.3.7, Theorem 1 and Corollary 7.
- Michael A. Allen, *Combinations without specified separations*, Communications in
  Combinatorics and Optimization 11(2) (2026), pp. 695–711, Section 2, Theorems 1 and 2.
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

/-- **Weighted enumeration of restricted combinations.** Summing a weight depending only on
subset size over all subsets of `{1, …, n}` avoiding the differences in `Q` is the same as
weighting the restricted combination counts by size. -/
public theorem sum_restrictedCombinationCount_mul {R : Type*} [Semiring R]
    (Q : Finset ℕ) (n : ℕ) (w : ℕ → R) :
    (∑ k ∈ Finset.range (n + 1), (restrictedCombinationCount Q n k : R) * w k) =
      ∑ s ∈ (Finset.Icc 1 n).powerset.filter
        (fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q), w s.card := by
  let u := (Finset.Icc 1 n).powerset.filter (fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q)
  have hu (s : Finset ℕ) (hs : s ∈ u) : s.card ∈ Finset.range (n + 1) := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h)
  change _ = ∑ s ∈ u, w s.card
  rw [← Finset.sum_fiberwise_of_maps_to' hu w]
  apply Finset.sum_congr rfl
  intro k _
  have hk : u.filter (fun s => s.card = k) = restrictedCombinations Q n k := by
    ext s
    simp only [u, restrictedCombinations, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    tauto
  simp only [hk, restrictedCombinationCount, Finset.sum_const, nsmul_eq_mul]

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

@[expose] public section

/-- **Number of subsets avoiding a set of differences.** For a finite set $Q$ of natural numbers
and $n \ge 0$, $S^Q_n$ is the number of subsets of $\{1, \dots, n\}$ in which no two distinct
elements differ by an element of $Q$. That is, $S^Q_n = \sum_{k=0}^{n} S^Q_{n,k}$, where
$S^Q_{n,k}$ is the number of such subsets with $k$ elements.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationTotal (Q : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), restrictedCombinationCount Q n k

/-- **Restricted combinations and restricted-overlap tilings.** Let $Q$ be a finite set of
natural numbers and let $q$ be its largest element ($q = 0$ if $Q$ is empty). Write
$S^Q_{n,k}$ for the number of $k$-subsets of $\{1, \dots, n\}$ in which no two distinct
elements differ by an element of $Q$, $S^Q_n = \sum_{k=0}^{n} S^Q_{n,k}$, and $B^Q_{m,k}$ for
the number of restricted-overlap tilings of an $m$-board with squares and $k$ $Q$-combs. Then
for all natural numbers $n$ and $k$, $S^Q_{n,k} = B^Q_{n+q,k}$ and
$S^Q_n = \sum_{j=0}^{n+q} B^Q_{n+q,j}$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Theorem 1. -/
public theorem restrictedCombinationCount_eq_restrictedOverlapTilingCount
    (Q : Finset ℕ) (n k : ℕ) :
    restrictedCombinationCount Q n k = restrictedOverlapTilingCount Q (n + Q.sup id) k ∧
      restrictedCombinationTotal Q n = ∑ j ∈ Finset.range (n + Q.sup id + 1),
        restrictedOverlapTilingCount Q (n + Q.sup id) j := by
  refine ⟨restrictedCombination_genFun_eq_tiling_genFun.count_eq Q n k, ?_⟩
  have h := congrArg (Polynomial.eval (1 : ℤ))
    (restrictedCombination_genFun_eq_tiling_genFun.polynomial_eq Q (n + Q.sup id))
  have hq : ¬ n + Q.sup id < Q.sup id := by omega
  simp only [hq, ↓reduceIte, Nat.add_sub_cancel, Polynomial.eval_finsetSum,
    Polynomial.eval_mul_X_pow, Polynomial.eval_natCast, one_pow, mul_one] at h
  unfold restrictedCombinationTotal
  exact_mod_cast h.symm

end

namespace RestrictedTransfer

private def succEmbedding : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

/-- Prepend a bit and shift all occupied suffix positions by one. -/
private def prepend (b : Bool) (s : Finset ℕ) : Finset ℕ :=
  if b then insert 1 (s.map succEmbedding) else s.map succEmbedding

private theorem mem_prepend {b : Bool} {s : Finset ℕ} {a : ℕ} :
    a ∈ prepend b s ↔ (a = 1 ∧ b = true) ∨ ∃ i ∈ s, a = i + 1 := by
  cases b <;> simp [prepend, succEmbedding, Finset.mem_map, eq_comm]

private theorem one_mem_prepend {b : Bool} {s : Finset ℕ} (hs : 0 ∉ s) :
    1 ∈ prepend b s ↔ b = true := by
  simp [mem_prepend, hs]

private theorem succ_mem_prepend {b : Bool} {s : Finset ℕ} {a : ℕ} (ha : 0 < a) :
    a + 1 ∈ prepend b s ↔ a ∈ s := by
  simp [mem_prepend, Nat.ne_of_gt ha]

private theorem prepend_subset {b : Bool} {s : Finset ℕ} {n : ℕ}
    (hs : s ⊆ Finset.Icc 1 n) : prepend b s ⊆ Finset.Icc 1 (n + 1) := by
  intro a ha
  rcases mem_prepend.mp ha with ⟨rfl, _⟩ | ⟨i, hi, rfl⟩
  · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  · have := Finset.mem_Icc.mp (hs hi)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

private theorem recover_prepend {b : Bool} {t : Finset ℕ} {n : ℕ}
    (ht : t ⊆ Finset.Icc 1 (n + 1)) (hb : 1 ∈ t ↔ b = true) :
    ∃ s ⊆ Finset.Icc 1 n, prepend b s = t := by
  let s := (t.erase 1).preimage succEmbedding succEmbedding.injective.injOn
  have hs (i : ℕ) : i ∈ s ↔ i + 1 ≠ 1 ∧ i + 1 ∈ t := by
    rw [Finset.mem_preimage, Finset.mem_erase]
    rfl
  refine ⟨s, ?_, ?_⟩
  · intro i hi
    obtain ⟨hne, hmem⟩ := (hs i).1 hi
    have := Finset.mem_Icc.mp (ht hmem)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · ext a
    simp only [mem_prepend, hs]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨i, ⟨_, hi⟩, rfl⟩)
      · exact hb.2 h
      · exact hi
    · intro ha
      by_cases he : a = 1
      · exact Or.inl ⟨he, hb.1 (he ▸ ha)⟩
      · have := (Finset.mem_Icc.mp (ht ha)).1
        exact Or.inr ⟨a - 1, ⟨by omega, by rwa [show a - 1 + 1 = a by omega]⟩, by omega⟩

private theorem card_filter_prepend (b : Bool) (n : ℕ)
    (suffix full : Finset (Finset ℕ)) (allowed : Prop) [Decidable allowed]
    (hsuffix : ∀ s ∈ suffix, s ⊆ Finset.Icc 1 n)
    (hfull : ∀ t ∈ full, t ⊆ Finset.Icc 1 (n + 1))
    (hprepend : ∀ s ⊆ Finset.Icc 1 n, prepend b s ∈ full ↔ allowed ∧ s ∈ suffix) :
    (full.filter fun t => (1 ∈ t ↔ b = true)).card = if allowed then suffix.card else 0 := by
  have zero_not_mem {s : Finset ℕ} (hs : s ⊆ Finset.Icc 1 n) : 0 ∉ s :=
    fun h => by simpa using (Finset.mem_Icc.mp (hs h)).1
  by_cases hb : allowed
  · rw [ite_eq_left hb]
    symm
    refine Finset.card_nbij (prepend b) ?_ ?_ ?_
    · intro s hs
      have hs' := hsuffix s hs
      exact Finset.mem_filter.mpr ⟨(hprepend s hs').2 ⟨hb, hs⟩, one_mem_prepend (zero_not_mem hs')⟩
    · intro s hs t ht he
      ext a
      by_cases ha : a = 0
      · simp [ha, zero_not_mem (hsuffix s hs), zero_not_mem (hsuffix t ht)]
      · have hpos := Nat.pos_of_ne_zero ha
        rw [← succ_mem_prepend (b := b) hpos, he, succ_mem_prepend hpos]
    · intro t ht
      obtain ⟨ht, hbit⟩ := Finset.mem_filter.mp ht
      obtain ⟨s, hs, rfl⟩ := recover_prepend (hfull t ht) hbit
      exact ⟨s, ((hprepend s hs).1 ht).2, rfl⟩
  · rw [ite_eq_right hb, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, hbit⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hs, rfl⟩ := recover_prepend (hfull t ht) hbit
    exact hb ((hprepend s hs).1 ht).1

end RestrictedTransfer

namespace OneFour

open RestrictedTransfer

/-- The four preceding membership bits, oldest first. -/
private structure Window where
  first : Bool
  second : Bool
  third : Bool
  fourth : Bool

private def Window.shift (w : Window) (b : Bool) : Window :=
  ⟨w.second, w.third, w.fourth, b⟩

private def Window.allows (w : Window) (b : Bool) : Bool :=
  !b || (!w.first && !w.fourth)

private def zeroWindow : Window := ⟨false, false, false, false⟩

private def Separated (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, a + 1 ∉ s ∧ a + 4 ∉ s

private instance (s : Finset ℕ) : Decidable (Separated s) :=
  inferInstanceAs (Decidable (∀ a ∈ s, a + 1 ∉ s ∧ a + 4 ∉ s))

private theorem separated_iff (s : Finset ℕ) :
    Separated s ↔ ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ ({1, 4} : Finset ℕ) := by
  simp only [Separated, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h a ha b hb hab hd
    rcases hd with hd | hd
    · exact (h a ha).1 (by rwa [show a + 1 = b by omega])
    · exact (h a ha).2 (by rwa [show a + 4 = b by omega])
  · intro h a ha
    exact ⟨fun hb => h a ha _ hb (by omega) (Or.inl (by omega)),
      fun hb => h a ha _ hb (by omega) (Or.inr (by omega))⟩

/-- A subset of the suffix is indicated by its occupied positions, numbered from 1.
The four implications rule out conflicts across the boundary with the preceding window. -/
private def Compatible (w : Window) (s : Finset ℕ) : Prop :=
  Separated s ∧ (w.first = true → 1 ∉ s) ∧ (w.second = true → 2 ∉ s) ∧
    (w.third = true → 3 ∉ s) ∧ (w.fourth = true → 1 ∉ s ∧ 4 ∉ s)

private instance (w : Window) (s : Finset ℕ) : Decidable (Compatible w s) := by
  unfold Compatible
  infer_instance

private def words (w : Window) (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (Compatible w)

private theorem mem_words {w : Window} {n : ℕ} {s : Finset ℕ} :
    s ∈ words w n ↔ s ⊆ Finset.Icc 1 n ∧ Compatible w s := by
  simp only [words, Finset.mem_filter, Finset.mem_powerset]

private theorem total_eq_card_words (n : ℕ) :
    restrictedCombinationTotal {1, 4} n = (words zeroWindow n).card := by
  unfold restrictedCombinationTotal restrictedCombinationCount
  have hcard : (↑(words zeroWindow n) : Set (Finset ℕ)).MapsTo
      Finset.card (Finset.range (n + 1)) := by
    intro s hs
    have hle := Finset.card_le_card (mem_words.mp hs).1
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hle
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hcard]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ext s
  simp only [restrictedCombinations, Finset.mem_filter, Finset.mem_powersetCard, mem_words,
    Compatible, zeroWindow, Bool.false_eq_true, false_implies, and_true, separated_iff]
  tauto

private theorem separated_prepend {b : Bool} {s : Finset ℕ} (hs : 0 ∉ s) :
    Separated (prepend b s) ↔ Separated s ∧ (b = true → 1 ∉ s ∧ 4 ∉ s) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha
      have ha' : 0 < a := Nat.pos_of_ne_zero (fun he => hs (he ▸ ha))
      have hh := h (a + 1) ((succ_mem_prepend ha').2 ha)
      exact ⟨fun ha₁ => hh.1 ((succ_mem_prepend (by omega)).2 ha₁),
        fun ha₄ => hh.2 (by simpa [Nat.add_right_comm a 4 1] using
          (succ_mem_prepend (by omega)).2 ha₄)⟩
    · intro hb
      have hh := h 1 ((one_mem_prepend hs).2 hb)
      exact ⟨fun h1 => hh.1 ((succ_mem_prepend (by decide : 0 < 1)).2 h1),
        fun h4 => hh.2 ((succ_mem_prepend (by decide : 0 < 4)).2 h4)⟩
  · rintro ⟨h, hfirst⟩ a ha
    rcases mem_prepend.mp ha with ⟨rfl, hb⟩ | ⟨i, hi, rfl⟩
    · exact ⟨fun h1 => (hfirst hb).1 ((succ_mem_prepend (by decide : 0 < 1)).1 h1),
        fun h4 => (hfirst hb).2 ((succ_mem_prepend (by decide : 0 < 4)).1 h4)⟩
    · have hh := h i hi
      exact ⟨fun h1 => hh.1 ((succ_mem_prepend (by omega)).1 h1),
        fun h4 => hh.2 ((succ_mem_prepend (by omega)).1
          (by simpa [Nat.add_right_comm i 4 1] using h4))⟩

private theorem compatible_prepend {w : Window} {b : Bool} {s : Finset ℕ} (hs : 0 ∉ s) :
    Compatible w (prepend b s) ↔ w.allows b = true ∧ Compatible (w.shift b) s := by
  cases b <;> obtain ⟨a, c, d, e⟩ := w <;> cases a <;> cases e <;>
    simp [Compatible, Window.allows, Window.shift, separated_prepend hs, one_mem_prepend hs,
      succ_mem_prepend (by decide : 0 < 1), succ_mem_prepend (by decide : 0 < 2),
      succ_mem_prepend (by decide : 0 < 3), and_assoc, and_left_comm, and_comm]

private theorem card_words_filter (w : Window) (n : ℕ) (b : Bool) :
    ((words w (n + 1)).filter fun s => (1 ∈ s ↔ b = true)).card =
      if w.allows b then (words (w.shift b) n).card else 0 := by
  apply card_filter_prepend b n _ _ (w.allows b = true)
    (fun _ hs => (mem_words.mp hs).1) (fun _ ht => (mem_words.mp ht).1)
  intro s hs
  have h0 : 0 ∉ s := fun h => by simpa using (Finset.mem_Icc.mp (hs h)).1
  simp only [mem_words, prepend_subset hs, hs, true_and, compatible_prepend h0]

private theorem card_words_succ (w : Window) (n : ℕ) :
    (words w (n + 1)).card = (words (w.shift false) n).card +
      if w.allows true then (words (w.shift true) n).card else 0 := by
  have hfalse : ((words w (n + 1)).filter fun s => 1 ∉ s).card =
      (words (w.shift false) n).card := by
    simpa [Window.allows] using card_words_filter w n false
  have htrue : ((words w (n + 1)).filter fun s => 1 ∈ s).card =
      if w.allows true then (words (w.shift true) n).card else 0 := by
    simpa using card_words_filter w n true
  rw [← hfalse, ← htrue]
  simpa only [add_comm] using
    (Finset.card_filter_add_card_filter_not (s := words w (n + 1)) (fun s => 1 ∈ s)).symm

private theorem card_words_zero (w : Window) : (words w 0).card = 1 := by
  have h : Compatible w ∅ := by simp [Compatible, Separated]
  simp [words, Finset.filter_singleton, h]

open PowerSeries in
private noncomputable def series (w : Window) : PowerSeries ℤ :=
  mk fun n => ((words w n).card : ℤ)

open PowerSeries in
private theorem series_eq (w : Window) :
    series w = 1 + X * (series (w.shift false) +
      if w.allows true then series (w.shift true) else 0) := by
  ext n
  cases n with
  | zero => simp [series, card_words_zero]
  | succ n =>
    simp only [map_add, coeff_one, Nat.succ_ne_zero, ite_false, zero_add, coeff_succ_X_mul,
      series, coeff_mk, card_words_succ, Nat.cast_add]
    split <;> simp_all

end OneFour

open OneFour in
/-- **Generating function for subsets avoiding differences 1 and 4.** Let $S^{\{1,4\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $4$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} S^{\{1,4\}}_n x^n\Bigr)(1 - x - x^3 + x^4 - 2x^5 + x^6 - x^7) =
1 + x + x^2 + x^3 + 2x^4 + x^6.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,4\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 9. -/
public theorem restrictedCombinationTotal_one_four_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 4} n : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 +
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 +
        PowerSeries.X ^ 6 := by
  simp_rw [total_eq_card_words]
  let x : PowerSeries ℤ := PowerSeries.X
  change series zeroWindow * (1 - x - x ^ 3 + x ^ 4 - 2 * x ^ 5 + x ^ 6 - x ^ 7) =
    1 + x + x ^ 2 + x ^ 3 + 2 * x ^ 4 + x ^ 6
  -- The empty window and the seven other windows without adjacent true bits.
  have h0000 := series_eq ⟨false, false, false, false⟩
  have h0001 := series_eq ⟨false, false, false, true⟩
  have h0010 := series_eq ⟨false, false, true, false⟩
  have h0100 := series_eq ⟨false, true, false, false⟩
  have h0101 := series_eq ⟨false, true, false, true⟩
  have h1000 := series_eq ⟨true, false, false, false⟩
  have h1001 := series_eq ⟨true, false, false, true⟩
  have h1010 := series_eq ⟨true, false, true, false⟩
  simp only [Window.shift, Window.allows, Bool.not_true, Bool.not_false, Bool.false_or,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_true, ite_false, add_zero] at *
  -- Eliminate the seven nonempty windows from their transfer equations.
  unfold zeroWindow
  linear_combination (1 - x ^ 3 - x ^ 5) * h0000 + (x - x ^ 4 - x ^ 6) * h0001 +
    x ^ 2 * h0010 + (x ^ 3 + x ^ 5) * h0100 + x ^ 3 * h0101 +
    (x ^ 4 + x ^ 6) * h1000 + (x ^ 4 + x ^ 6) * h1001 + x ^ 4 * h1010

namespace RestrictedTransfer

private def Separated (Q s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ c ∈ s, a < c → c - a ∉ Q

/-- The occupied positions in the suffix must avoid each other and the positions blocked by
previous choices. -/
private def Compatible (Q B s : Finset ℕ) : Prop :=
  Separated Q s ∧ ∀ i ∈ s, i ∉ B

private instance (Q B s : Finset ℕ) : Decidable (Compatible Q B s) := by
  unfold Compatible Separated
  infer_instance

private def words (Q B : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (Compatible Q B)

private theorem mem_words {Q B : Finset ℕ} {n : ℕ} {s : Finset ℕ} :
    s ∈ words Q B n ↔ s ⊆ Finset.Icc 1 n ∧ Compatible Q B s := by
  simp only [words, Finset.mem_filter, Finset.mem_powerset]

private theorem total_eq_card_words (Q : Finset ℕ) (n : ℕ) :
    restrictedCombinationTotal Q n = (words Q ∅ n).card := by
  unfold restrictedCombinationTotal restrictedCombinationCount
  have hcard : (↑(words Q ∅ n) : Set (Finset ℕ)).MapsTo
      Finset.card (Finset.range (n + 1)) := by
    intro s hs
    have hle := Finset.card_le_card (mem_words.mp hs).1
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hle
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hcard]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ext s
  simp only [restrictedCombinations, Finset.mem_filter, Finset.mem_powersetCard, mem_words,
    Compatible, Finset.notMem_empty, Separated]
  tauto

/-- Drop the first position and decrease the remaining blocked positions by one. -/
private def advance (B : Finset ℕ) : Finset ℕ :=
  (B.filter (fun i => 1 < i)).image (· - 1)

private theorem mem_advance {B : Finset ℕ} {i : ℕ} :
    i ∈ advance B ↔ 0 < i ∧ i + 1 ∈ B := by
  simp only [advance, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨j, ⟨hj, hj'⟩, rfl⟩
    exact ⟨by omega, by rwa [show j - 1 + 1 = j by omega]⟩
  · rintro ⟨h, hi⟩
    exact ⟨i + 1, ⟨hi, by omega⟩, by omega⟩

/-- Taking the first position additionally blocks offsets in `Q` in the renumbered suffix. -/
private def next (Q B : Finset ℕ) (b : Bool) : Finset ℕ :=
  if b then advance B ∪ Q else advance B

private theorem separated_prepend {Q s : Finset ℕ} {b : Bool} (hs : 0 ∉ s) :
    Separated Q (prepend b s) ↔ Separated Q s ∧ (b = true → ∀ i ∈ s, i ∉ Q) := by
  have lift_mem {a : ℕ} (ha : a ∈ s) : a + 1 ∈ prepend b s :=
    mem_prepend.mpr (Or.inr ⟨a, ha, rfl⟩)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha c hc hac
      rw [← show c + 1 - (a + 1) = c - a by omega]
      exact h (a + 1) (lift_mem ha) (c + 1) (lift_mem hc) (by omega)
    · intro hb i hi
      have hpos : 0 < i := Nat.pos_of_ne_zero (fun he => hs (he ▸ hi))
      simpa using h 1 ((one_mem_prepend hs).2 hb) (i + 1) (lift_mem hi) (by omega)
  · rintro ⟨h, hfirst⟩ a ha c hc hac
    rcases mem_prepend.mp ha with ⟨rfl, hb⟩ | ⟨i, hi, rfl⟩ <;>
      rcases mem_prepend.mp hc with ⟨rfl, _⟩ | ⟨j, hj, rfl⟩
    · omega
    · simpa using hfirst hb j hj
    · omega
    · rw [show j + 1 - (i + 1) = j - i by omega]
      exact h i hi j hj (by omega)

private theorem compatible_prepend {Q B s : Finset ℕ} {b : Bool} (hs : 0 ∉ s) :
    Compatible Q B (prepend b s) ↔ (b = true → 1 ∉ B) ∧ Compatible Q (next Q B b) s := by
  have blocked : (∀ i ∈ prepend b s, i ∉ B) ↔
      (b = true → 1 ∉ B) ∧ ∀ i ∈ s, i ∉ advance B := by
    constructor
    · intro h
      refine ⟨fun hb => h 1 ((one_mem_prepend hs).2 hb), ?_⟩
      intro i hi hm
      exact h (i + 1) (mem_prepend.mpr (Or.inr ⟨i, hi, rfl⟩)) (mem_advance.mp hm).2
    · rintro ⟨hfirst, h⟩ a ha
      rcases mem_prepend.mp ha with ⟨rfl, hb⟩ | ⟨i, hi, rfl⟩
      · exact hfirst hb
      · intro hm
        have hpos : 0 < i := Nat.pos_of_ne_zero (fun he => hs (he ▸ hi))
        exact h i hi (mem_advance.mpr ⟨hpos, hm⟩)
  simp only [Compatible, separated_prepend hs, blocked]
  cases b <;> simp [next, forall_and, and_assoc, and_left_comm, and_comm]

private theorem card_words_filter (Q B : Finset ℕ) (n : ℕ) (b : Bool) :
    ((words Q B (n + 1)).filter fun s => (1 ∈ s ↔ b = true)).card =
      if b = true → 1 ∉ B then (words Q (next Q B b) n).card else 0 := by
  apply card_filter_prepend b n _ _ (b = true → 1 ∉ B)
    (fun _ hs => (mem_words.mp hs).1) (fun _ ht => (mem_words.mp ht).1)
  intro s hs
  have h0 : 0 ∉ s := fun h => by simpa using (Finset.mem_Icc.mp (hs h)).1
  simp only [mem_words, prepend_subset hs, hs, true_and, compatible_prepend h0]

private theorem card_words_succ (Q B : Finset ℕ) (n : ℕ) :
    (words Q B (n + 1)).card = (words Q (advance B) n).card +
      if 1 ∉ B then (words Q (advance B ∪ Q) n).card else 0 := by
  have hfalse : ((words Q B (n + 1)).filter fun s => 1 ∉ s).card =
      (words Q (advance B) n).card := by
    simpa [next] using card_words_filter Q B n false
  have htrue : ((words Q B (n + 1)).filter fun s => 1 ∈ s).card =
      if 1 ∉ B then (words Q (advance B ∪ Q) n).card else 0 := by
    simpa [next] using card_words_filter Q B n true
  rw [← hfalse, ← htrue]
  simpa only [add_comm] using
    (Finset.card_filter_add_card_filter_not (s := words Q B (n + 1)) (fun s => 1 ∈ s)).symm

private theorem card_words_zero (Q B : Finset ℕ) : (words Q B 0).card = 1 := by
  have h : Compatible Q B ∅ := by simp [Compatible, Separated]
  simp [words, Finset.filter_singleton, h]

open PowerSeries in
private noncomputable def series (Q B : Finset ℕ) : PowerSeries ℤ :=
  mk fun n => ((words Q B n).card : ℤ)

open PowerSeries in
private theorem series_eq (Q B : Finset ℕ) :
    series Q B = 1 + X * (series Q (advance B) +
      if 1 ∉ B then series Q (advance B ∪ Q) else 0) := by
  ext n
  cases n with
  | zero => simp [series, card_words_zero]
  | succ n =>
    simp only [map_add, coeff_one, Nat.succ_ne_zero, ite_false, zero_add, coeff_succ_X_mul,
      series, coeff_mk, card_words_succ, Nat.cast_add]
    split <;> simp_all

open PowerSeries in
private theorem series_eq_of_free {Q B B₀ B₁ : Finset ℕ} (h : 1 ∉ B)
    (h₀ : advance B = B₀) (h₁ : advance B ∪ Q = B₁) :
    series Q B = 1 + X * (series Q B₀ + series Q B₁) := by
  rw [series_eq Q B, ite_eq_left h, h₁, h₀]

open PowerSeries in
private theorem series_eq_of_blocked {Q B B₀ : Finset ℕ} (h : 1 ∈ B) (h₀ : advance B = B₀) :
    series Q B = 1 + X * series Q B₀ := by
  rw [series_eq Q B, ite_eq_right (not_not_intro h), add_zero, h₀]

end RestrictedTransfer

namespace OneFive

-- The multipliers eliminate the ten nonempty blocked-position states.
private theorem transfer_elimination {R : Type*} [CommRing R]
    (x s0 s15 s4 s3 s135 s2 s125 s24 s1 s14 s13 : R)
    (h0 : s0 = 1 + x * (s0 + s15))
    (h15 : s15 = 1 + x * s4)
    (h4 : s4 = 1 + x * (s3 + s135))
    (h3 : s3 = 1 + x * (s2 + s125))
    (h135 : s135 = 1 + x * s24)
    (h2 : s2 = 1 + x * (s1 + s15))
    (h125 : s125 = 1 + x * s14)
    (h24 : s24 = 1 + x * (s13 + s135))
    (h1 : s1 = 1 + x * s0)
    (h14 : s14 = 1 + x * s3)
    (h13 : s13 = 1 + x * s2) :
    s0 * (1 - x ^ 2 - x ^ 3 - x ^ 4 + x ^ 5 - x ^ 6 - x ^ 7 - x ^ 8 - x ^ 10) =
      1 + 2 * x + 2 * x ^ 2 + 2 * x ^ 3 + 2 * x ^ 4 + 4 * x ^ 5 + 3 * x ^ 6 +
        2 * x ^ 7 + x ^ 8 + x ^ 9 := by
  linear_combination
    (1 + x - x ^ 3 - 2 * x ^ 4 - x ^ 5 - x ^ 6 - x ^ 7 - x ^ 8) * h0 +
    (x + x ^ 2 - x ^ 4 - x ^ 5) * h15 +
    (x ^ 2 + x ^ 3 - x ^ 5 - x ^ 6) * h4 + (x ^ 3 + x ^ 4) * h3 +
    (x ^ 3 + x ^ 4 + x ^ 5) * h135 + (x ^ 4 + x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8) * h2 +
    (x ^ 4 + x ^ 5) * h125 + (x ^ 4 + x ^ 5 + x ^ 6) * h24 +
    (x ^ 5 + x ^ 6 + x ^ 7 + x ^ 8 + x ^ 9) * h1 + (x ^ 5 + x ^ 6) * h14 +
    (x ^ 5 + x ^ 6 + x ^ 7) * h13

end OneFive

open RestrictedTransfer OneFive in
/-- **Generating function for subsets avoiding differences 1 and 5.** Let $S^{\{1,5\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $5$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} S^{\{1,5\}}_n x^n\Bigr)
(1 - x^2 - x^3 - x^4 + x^5 - x^6 - x^7 - x^8 - x^{10}) =
1 + 2x + 2x^2 + 2x^3 + 2x^4 + 4x^5 + 3x^6 + 2x^7 + x^8 + x^9.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,5\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 10. -/
public theorem restrictedCombinationTotal_one_five_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 5} n : ℤ)) *
        (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + PowerSeries.X ^ 5 -
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7 - PowerSeries.X ^ 8 - PowerSeries.X ^ 10) =
      1 + 2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6 +
        2 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8 + PowerSeries.X ^ 9 := by
  let Q : Finset ℕ := {1, 5}
  let S := series Q
  have hS : PowerSeries.mk (fun n => (restrictedCombinationTotal Q n : ℤ)) = S ∅ := by
    simp_rw [total_eq_card_words]
    rfl
  change PowerSeries.mk (fun n => (restrictedCombinationTotal Q n : ℤ)) * _ = _
  rw [hS]
  -- Each equation comes from dropping a free or blocked first position.
  exact transfer_elimination PowerSeries.X (S ∅) (S {1, 5}) (S {4}) (S {3}) (S {1, 3, 5})
    (S {2}) (S {1, 2, 5}) (S {2, 4}) (S {1}) (S {1, 4}) (S {1, 3})
    (series_eq_of_free (Q := Q) (B := ∅) (B₀ := ∅) (B₁ := {1, 5})
      (by decide) (by decide) (by decide))
    (series_eq_of_blocked (Q := Q) (B := {1, 5}) (B₀ := {4}) (by decide) (by decide))
    (series_eq_of_free (Q := Q) (B := {4}) (B₀ := {3}) (B₁ := {1, 3, 5})
      (by decide) (by decide) (by decide))
    (series_eq_of_free (Q := Q) (B := {3}) (B₀ := {2}) (B₁ := {1, 2, 5})
      (by decide) (by decide) (by decide))
    (series_eq_of_blocked (Q := Q) (B := {1, 3, 5}) (B₀ := {2, 4}) (by decide) (by decide))
    (series_eq_of_free (Q := Q) (B := {2}) (B₀ := {1}) (B₁ := {1, 5})
      (by decide) (by decide) (by decide))
    (series_eq_of_blocked (Q := Q) (B := {1, 2, 5}) (B₀ := {1, 4}) (by decide) (by decide))
    (series_eq_of_free (Q := Q) (B := {2, 4}) (B₀ := {1, 3}) (B₁ := {1, 3, 5})
      (by decide) (by decide) (by decide))
    (series_eq_of_blocked (Q := Q) (B := {1}) (B₀ := ∅) (by decide) (by decide))
    (series_eq_of_blocked (Q := Q) (B := {1, 4}) (B₀ := {3}) (by decide) (by decide))
    (series_eq_of_blocked (Q := Q) (B := {1, 3}) (B₀ := {2}) (by decide) (by decide))

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating functions of restricted combinations and restricted-overlap tilings

`restrictedCombination_genFun_eq_tiling_genFun` relates the two bivariate counting series by
shifting the board length by the largest forbidden difference.
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

end

namespace restrictedCombination_genFun_eq_tiling_genFun

-- Adding one to each comb start identifies the available cells with the one-based interval.
private theorem tilingCount_eq (Q : Finset ℕ) (n k : ℕ) :
    restrictedOverlapTilingCount Q n k = restrictedCombinationCount Q (n - Q.sup id) k := by
  let starts := (Finset.range n).filter fun s => s + Q.sup id < n
  let succ : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  have hcells : Finset.Icc 1 (n - Q.sup id) = starts.map succ := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, starts, Finset.mem_filter, Finset.mem_range,
      succ, Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩
      omega
  unfold restrictedCombinationCount restrictedCombinations
  rw [hcells, Finset.powersetCard_map, Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro P _
  change (∀ s ∈ P, ∀ t ∈ P, ∀ j ∈ Q, j ≠ 0 → s ≠ t + j) ↔
    (∀ a ∈ P.map succ, ∀ b ∈ P.map succ, a < b → b - a ∉ Q)
  simp only [Finset.forall_mem_map, succ, Function.Embedding.coeFn_mk, Nat.succ_lt_succ_iff,
    Nat.succ_sub_succ_eq_sub]
  constructor
  · intro h a ha b hb hab hdiff
    exact h b hb a ha (b - a) hdiff (by omega) (by omega)
  · intro h b hb a ha j hj hj' heq
    exact h a ha b hb (by omega) (by simpa [heq] using hj)

-- Once the comb starts are numbered from one, terms above the number of starts vanish.
private theorem tilingPolynomial_eq (Q : Finset ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (restrictedOverlapTilingCount Q n k : Polynomial ℤ) *
        Polynomial.X ^ k =
      ∑ k ∈ Finset.range (n - Q.sup id + 1),
        (restrictedCombinationCount Q (n - Q.sup id) k : Polynomial ℤ) * Polynomial.X ^ k := by
  simp_rw [tilingCount_eq]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k _ hk
  have h : (Finset.Icc 1 (n - Q.sup id)).card < k := by
    simp only [Finset.mem_range] at hk
    rw [Nat.card_Icc]
    omega
  simp [restrictedCombinationCount, restrictedCombinations, Finset.powersetCard_eq_empty.mpr h]

end restrictedCombination_genFun_eq_tiling_genFun

open restrictedCombination_genFun_eq_tiling_genFun

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
  intro n
  simp only [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, map_sub, map_sum,
    PowerSeries.coeff_X_pow, Finset.sum_ite_eq, Finset.mem_range, tilingPolynomial_eq]
  by_cases h : Q.sup id ≤ n
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h, Nat.sub_eq_zero_of_le (by omega : n ≤ Q.sup id),
      restrictedCombinationCount, restrictedCombinations, Finset.filter_singleton]

end MetaMathlibExt

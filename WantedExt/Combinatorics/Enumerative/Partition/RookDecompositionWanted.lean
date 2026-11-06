/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rook decomposition of the partition function

Statements from N. Guru Sharan, "Rook Decomposition of the Partition
Function", *Journal of Integer Sequences* 29 (2026), Article 26.2.6
(arXiv:2507.20260).

The max-rook number `R(π)` of a partition `π` is the largest number of
non-attacking rooks on its Ferrers board. `F(n)` is the largest max-rook
number over partitions of `n` (with the paper's convention `F(0) = 1`), and
`R_k(n)` counts the partitions of `n` with max-rook number `k`.

The paper states its generating functions for `|q| < 1`. Theorem 1 is stated
analytically over `ℂ` with the repository's `qPochhammerInf`; the rational
generating functions of Theorems 2, 4 and 5 are stated in `ℤ⟦X⟧` with the
denominator cleared, which is equivalent because `R_k(n)` grows polynomially.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **Max-rook number of a board.** For a finite board $B \subseteq \mathbb{N} \times \mathbb{N}$,
whose cell $(i, j)$ lies in row $i$ and column $j$, the max-rook number of $B$ is the largest
size of a subset of $B$ that contains at most one cell of each row and at most one cell of each
column, that is, the largest number of non-attacking rooks that can be placed on $B$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 2 (max-rook
number). -/
def boardMaxRookNumber (B : Finset (ℕ × ℕ)) : ℕ :=
  (B.powerset.filter fun S =>
    (S.image Prod.fst).card = S.card ∧ (S.image Prod.snd).card = S.card).sup Finset.card

/-- **Ferrers board of a partition.** Let $p$ be a partition of $n$, and number rows and columns
from $0$. The Ferrers board of $p$ is the finite set of cells
$(i, j) \in \mathbb{N} \times \mathbb{N}$ such that the $(i+1)$-st largest part of $p$ exceeds $j$,
that is, such that more than $i$ parts of $p$, counted with multiplicity, exceed $j$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 1 (Ferrers
diagram and Ferrers board). -/
def partitionFerrersBoard {n : ℕ} (p : Nat.Partition n) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter fun c =>
    c.1 < (p.parts.filter (c.2 < ·)).card

/-- **Max-rook number of a partition.** The max-rook number $R(\pi)$ of a partition $\pi$ of $n$
is the largest number of non-attacking rooks on the Ferrers board of $\pi$: the largest number
of cells of the board, no two in the same row and no two in the same column.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 2. -/
def partitionMaxRookNumber {n : ℕ} (p : Nat.Partition n) : ℕ :=
  boardMaxRookNumber (partitionFerrersBoard p)

/-- **Partitions with a given max-rook number.** For natural numbers $k$ and $n$, $R_k(n)$ is
the number of partitions of $n$ whose max-rook number, the largest number of non-attacking rooks
on the Ferrers board, equals $k$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Equation (2.2). -/
def maxRookPartitionCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n => partitionMaxRookNumber p = k).card

/-- **Largest max-rook number among partitions of $n$.** For a natural number $n \ge 1$, $F(n)$
is the largest max-rook number $R(\pi)$ over all partitions $\pi$ of $n$, where $R(\pi)$ is the
largest number of non-attacking rooks on the Ferrers board of $\pi$. By convention $F(0) = 1$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Equation (2.1). -/
def partitionMaxRookNumberMax (n : ℕ) : ℕ :=
  if n = 0 then 1 else Finset.univ.sup fun p : Nat.Partition n => partitionMaxRookNumber p

/-- **Ferrers board of the partition $(2, 1)$.** With rows and columns numbered from $0$, the
Ferrers board of the partition $(2, 1)$ of $3$ consists of exactly the three cells $(0, 0)$,
$(0, 1)$ and $(1, 0)$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 1 (Ferrers
board); characteristic check of `partitionFerrersBoard`. -/
theorem partitionFerrersBoard_two_one :
    partitionFerrersBoard (Nat.Partition.ofMultiset ({2, 1} : Multiset ℕ)) =
      {(0, 0), (0, 1), (1, 0)} := by
  decide +kernel

/-- **Max-rook number of the partition $(5, 3, 2, 1)$.** The partition $(5, 3, 2, 1)$ of $11$
has max-rook number $4$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Figure 1. -/
theorem partitionMaxRookNumber_five_three_two_one :
    partitionMaxRookNumber (Nat.Partition.ofMultiset ({5, 3, 2, 1} : Multiset ℕ)) = 4 := by
  decide +kernel

/-- **The convention $F(0) = 1$.** The function $F$, whose value $F(n)$ for $n \ge 1$ is the
largest max-rook number of a partition of $n$, takes the value $F(0) = 1$ at $n = 0$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, after Equation (2.1). -/
@[simp]
theorem partitionMaxRookNumberMax_zero : partitionMaxRookNumberMax 0 = 1 := rfl

/-- **Generating function of the largest max-rook number.** Let $F(n)$ be the largest max-rook
number of a partition of $n$ for $n \ge 1$, and $F(0) = 1$. For every complex number $q$ with
$|q| < 1$, the series $\sum_{n \ge 0} F(n) q^n$ is summable with sum
$$\frac{(q^2;q^2)_\infty \, (-q;q)_\infty - q}{1 - q},$$
where $(a;q)_\infty = \prod_{k \ge 0} (1 - a q^k)$ is the infinite q-Pochhammer symbol.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 1
(`jis-2026-26.2.6-thm-1`). -/
public theorem_wanted hasSum_partitionMaxRookNumberMax (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionMaxRookNumberMax n : ℂ) * q ^ n)
      ((1 - q)⁻¹ *
        (QPochhammer.qPochhammerInf (q ^ 2) (q ^ 2)
            (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero) *
          QPochhammer.qPochhammerInf (-q) q hq - q))

/-- **Generating function of $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with
max-rook number $3$. In the ring $\mathbb{Z}[[q]]$ of formal power series with integer
coefficients,

$$(1-q)^3(1+q+q^2) \sum_{n \ge 0} R_3(n)\, q^n = q^6(1+2q+q^2+2q^3-q^4-q^6-q^7+q^8).$$

This is the rational generating function of $R_3(n)$ with its denominator cleared.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 2
(`jis-2026-26.2.6-thm-2`). -/
public theorem_wanted maxRookPartitionCount_three_genFun :
    (1 - X) ^ 3 * (1 + X + X ^ 2) * mk (fun n => (maxRookPartitionCount 3 n : ℤ)) =
      X ^ 6 * (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - X ^ 4 - X ^ 6 - X ^ 7 + X ^ 8)

/-- **Linear recurrence for $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with
max-rook number $3$. For every natural number $n > 14$,
$R_3(n) = 2R_3(n-1) - R_3(n-2) + R_3(n-3) - 2R_3(n-4) + R_3(n-5)$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 3
(`jis-2026-26.2.6-cor-3`). -/
public theorem_wanted maxRookPartitionCount_three_recurrence (n : ℕ) (hn : 14 < n) :
    (maxRookPartitionCount 3 n : ℤ) =
      2 * maxRookPartitionCount 3 (n - 1) - maxRookPartitionCount 3 (n - 2) +
        maxRookPartitionCount 3 (n - 3) - 2 * maxRookPartitionCount 3 (n - 4) +
        maxRookPartitionCount 3 (n - 5)

/-- **Generating function of partitions with max-rook number 4.** Let $R_4(n)$ be the number of
partitions of $n$ with max-rook number $4$. In the ring of formal power series in $q$ with integer
coefficients,
$$(1-q)(1-q^2)(1-q^3)(1-q^4) \sum_{n \ge 0} R_4(n) q^n = q^{10} P(q),$$
where
$$P(q) = 1 + 4q + 6q^2 + 7q^3 + 6q^4 + 2q^5 - 5q^7 - 5q^8 - 5q^9 + q^{11} + 3q^{12} + 2q^{13} -
q^{16}.$$

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 4
(`jis-2026-26.2.6-thm-4`). -/
public theorem_wanted maxRookPartitionCount_four_genFun :
    (1 - X) * (1 - X ^ 2) * (1 - X ^ 3) * (1 - X ^ 4) *
        mk (fun n => (maxRookPartitionCount 4 n : ℤ)) =
      X ^ 10 * (1 + 4 * X + 6 * X ^ 2 + 7 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 - 5 * X ^ 7 -
        5 * X ^ 8 - 5 * X ^ 9 + X ^ 11 + 3 * X ^ 12 + 2 * X ^ 13 - X ^ 16)

/-- **Generating function of partitions with max-rook number 5.** Let $R_5(n)$ be the number of
partitions of $n$ with max-rook number $5$. In the ring of formal power series in $q$ with integer
coefficients,
$$(1-q)^2(1-q^3)(1-q^4)(1-q^5) \sum_{n \ge 0} R_5(n) q^n = q^{15} P(q),$$
where
$$P(q) = 1 + 4q + 6q^2 + 8q^3 + 8q^4 + 4q^5 + 4q^6 - 5q^7 - 5q^8 - 10q^9 - 7q^{10} -
5q^{11} + 4q^{13} + 6q^{14} + 7q^{15} + 2q^{17} - 4q^{18} - q^{19} - q^{20} - q^{21} +
q^{22} - q^{23} + q^{24}.$$

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 5
(`jis-2026-26.2.6-thm-5`). -/
public theorem_wanted maxRookPartitionCount_five_genFun :
    (1 - X) ^ 2 * (1 - X ^ 3) * (1 - X ^ 4) * (1 - X ^ 5) *
        mk (fun n => (maxRookPartitionCount 5 n : ℤ)) =
      X ^ 15 * (1 + 4 * X + 6 * X ^ 2 + 8 * X ^ 3 + 8 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6 -
        5 * X ^ 7 - 5 * X ^ 8 - 10 * X ^ 9 - 7 * X ^ 10 - 5 * X ^ 11 + 4 * X ^ 13 +
        6 * X ^ 14 + 7 * X ^ 15 + 2 * X ^ 17 - 4 * X ^ 18 - X ^ 19 - X ^ 20 - X ^ 21 +
        X ^ 22 - X ^ 23 + X ^ 24)

/-- **Quasi-polynomial formula for partitions with max-rook number 3.** Let $R_3(n)$ be the number
of partitions of $n$ with max-rook number $3$. For every natural number $m$ and every
$a \in \{0, 1, 2\}$ with $3m + a > 9$, $R_3(3m + a)$ equals $6m^2 - 15m + 7$, $6m^2 - 11m + 2$
or $6m^2 - 7m - 1$ according as $a = 0$, $a = 1$ or $a = 2$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 6, first part
(`jis-2026-26.2.6-thm-6`). -/
public theorem_wanted maxRookPartitionCount_three_formula (m : ℕ) (a : Fin 3)
    (h : 9 < 3 * m + (a : ℕ)) :
    (maxRookPartitionCount 3 (3 * m + (a : ℕ)) : ℤ) =
      6 * (m : ℤ) ^ 2 + ![-15, -11, -7] a * m + ![7, 2, -1] a

/-- **Periodicity of $R_3(n)$ modulo $p$.** Let $R_3(n)$ be the number of partitions of $n$
with max-rook number $3$. For all natural numbers $p \ge 2$ and $n > 9$,
$R_3(n + 3p) \equiv R_3(n) \pmod{p}$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 6, second part
(`jis-2026-26.2.6-thm-6`). -/
public theorem_wanted maxRookPartitionCount_three_modEq (p n : ℕ) (hp : 2 ≤ p) (hn : 9 < n) :
    maxRookPartitionCount 3 (n + 3 * p) ≡ maxRookPartitionCount 3 n [MOD p]

/-- **Asymptotic growth of $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with
max-rook number $3$. Then $R_3(n) \sim \frac{2}{3} n^2$ as $n \to \infty$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 7
(`jis-2026-26.2.6-cor-7`). -/
public theorem_wanted maxRookPartitionCount_three_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (maxRookPartitionCount 3 n : ℝ))
      (fun n => 2 / 3 * (n : ℝ) ^ 2)

/-- **Quasi-polynomial formula for partitions with max-rook number 4.** Let $R_4(n)$ be the number
of partitions of $n$ with max-rook number $4$. For all natural numbers $m$ and $a$ with
$0 \le a \le 11$ and $12m + a > 16$,
$$R_4(12m + a) = 192m^3 + b_a m^2 + c_a m + d_a,$$
where, listed for $a = 0, 1, \ldots, 11$,
$(b_a) = (-264, -216, -168, -120, -72, -24, 24, 72, 120, 168, 216, 264)$,
$(c_a) = (87, 44, 15, -12, -25, -36, -33, -28, -9, 12, 47, 84)$ and
$(d_a) = (-3, 5, 5, 7, 4, 3, -2, -3, -5, -5, -3, 3)$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 8, first part
(`jis-2026-26.2.6-thm-8`). -/
public theorem_wanted maxRookPartitionCount_four_formula (m : ℕ) (a : Fin 12)
    (h : 16 < 12 * m + (a : ℕ)) :
    (maxRookPartitionCount 4 (12 * m + (a : ℕ)) : ℤ) =
      192 * (m : ℤ) ^ 3 +
        ![-264, -216, -168, -120, -72, -24, 24, 72, 120, 168, 216, 264] a * (m : ℤ) ^ 2 +
        ![87, 44, 15, -12, -25, -36, -33, -28, -9, 12, 47, 84] a * m +
        ![-3, 5, 5, 7, 4, 3, -2, -3, -5, -5, -3, 3] a

/-- **A congruence for partitions with max-rook number 4.** Let $R_4(n)$ be the number of
partitions of $n$ with max-rook number $4$. For all natural numbers $p \ge 2$ and $n > 16$,
$R_4(n + 12p) \equiv R_4(n) \pmod p$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 8, second part
(`jis-2026-26.2.6-thm-8`). -/
public theorem_wanted maxRookPartitionCount_four_modEq (p n : ℕ) (hp : 2 ≤ p) (hn : 16 < n) :
    maxRookPartitionCount 4 (n + 12 * p) ≡ maxRookPartitionCount 4 n [MOD p]

/-- **Asymptotics of partitions with max-rook number 4.** Let $R_4(n)$ be the number of partitions
of $n$ with max-rook number $4$. Then $R_4(n) \sim n^3/9$ as $n \to \infty$.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 9
(`jis-2026-26.2.6-cor-9`). -/
public theorem_wanted maxRookPartitionCount_four_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (maxRookPartitionCount 4 n : ℝ))
      (fun n => (n : ℝ) ^ 3 / 9)

/-- **Parity of $R_3(n)$.** Let $R_3(n)$ be the number of partitions of $n$ with max-rook number
$3$. For every natural number $n > 9$, $R_3(n)$ is even if $n$ is odd and odd if $n$ is even.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 10
(`jis-2026-26.2.6-thm-10`). -/
public theorem_wanted maxRookPartitionCount_three_mod_two (n : ℕ) (hn : 9 < n) :
    maxRookPartitionCount 3 n % 2 = if n % 2 = 1 then 0 else 1

/-- **Parity of the number of partitions with max-rook number 4.** Let $R_4(n)$ be the number of
partitions of $n$ with max-rook number $4$. For every natural number $n > 16$, $R_4(n)$ is even if
$n \equiv 4 \pmod 8$ or $n \equiv 6 \pmod 8$, and odd otherwise.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 11
(`jis-2026-26.2.6-thm-11`). -/
public theorem_wanted maxRookPartitionCount_four_mod_two (n : ℕ) (hn : 16 < n) :
    maxRookPartitionCount 4 n % 2 = if n % 8 = 4 ∨ n % 8 = 6 then 0 else 1

/-- **Parity of the number of partitions with max-rook number 5.** Let $R_5(n)$ be the number of
partitions of $n$ with max-rook number $5$. For every natural number $n > 25$, $R_5(n)$ is even if
$n \equiv 5 \pmod 8$ or $n \equiv 7 \pmod 8$, and odd otherwise.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 13
(`jis-2026-26.2.6-thm-13`). -/
public theorem_wanted maxRookPartitionCount_five_mod_two (n : ℕ) (hn : 25 < n) :
    maxRookPartitionCount 5 n % 2 = if n % 8 = 5 ∨ n % 8 = 7 then 0 else 1

end

end MetaMathlibExt

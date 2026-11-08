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

/-- The largest number of non-attacking rooks on a finite board `B ⊆ ℕ × ℕ`:
the largest subset of `B` that meets every row (first coordinate) and every
column (second coordinate) at most once.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 2 (max-rook
number). -/
def boardMaxRookNumber (B : Finset (ℕ × ℕ)) : ℕ :=
  (B.powerset.filter fun S =>
    (S.image Prod.fst).card = S.card ∧ (S.image Prod.snd).card = S.card).sup Finset.card

/-- The Ferrers board of a partition `p` of `n`: cell `(i, j)` (row `i`,
column `j`, both zero-based) is present iff the `(i+1)`-st largest part
exceeds `j`, i.e. iff more than `i` parts exceed `j`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 1 (Ferrers
diagram and Ferrers board). -/
def partitionFerrersBoard {n : ℕ} (p : Nat.Partition n) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter fun c =>
    c.1 < (p.parts.filter (c.2 < ·)).card

/-- The max-rook number `R(π)` of a partition: the largest number of
non-attacking rooks on its Ferrers board.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 2. -/
def partitionMaxRookNumber {n : ℕ} (p : Nat.Partition n) : ℕ :=
  boardMaxRookNumber (partitionFerrersBoard p)

/-- The paper's `R_k(n)`: the number of partitions of `n` with max-rook
number `k`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Equation (2.2). -/
def maxRookPartitionCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n => partitionMaxRookNumber p = k).card

/-- The paper's `F(n)`: the largest max-rook number of a partition of `n`,
with the paper's convention `F(0) = 1`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Equation (2.1). -/
def partitionMaxRookNumberMax (n : ℕ) : ℕ :=
  if n = 0 then 1 else Finset.univ.sup fun p : Nat.Partition n => partitionMaxRookNumber p

/-- The Ferrers board of `(2, 1)` is the three cells `(0,0), (0,1), (1,0)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Section 1 (Ferrers
board); characteristic check of `partitionFerrersBoard`. -/
theorem partitionFerrersBoard_two_one :
    partitionFerrersBoard (Nat.Partition.ofMultiset ({2, 1} : Multiset ℕ)) =
      {(0, 0), (0, 1), (1, 0)} := by
  decide +kernel

/-- The partition `(5, 3, 2, 1)` of `11` has max-rook number `4`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Figure 1. -/
theorem partitionMaxRookNumber_five_three_two_one :
    partitionMaxRookNumber (Nat.Partition.ofMultiset ({5, 3, 2, 1} : Multiset ℕ)) = 4 := by
  decide +kernel

/-- The convention `F(0) = 1`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, after Equation (2.1). -/
@[simp]
theorem partitionMaxRookNumberMax_zero : partitionMaxRookNumberMax 0 = 1 := rfl

/-- Generating function of `F(n)`: for `|q| < 1`,
`∑_{n ≥ 0} F(n) qⁿ = ((q²;q²)_∞ (-q;q)_∞ - q) / (1 - q)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 1
(`jis-2026-26.2.6-thm-1`). -/
public theorem_wanted hasSum_partitionMaxRookNumberMax (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionMaxRookNumberMax n : ℂ) * q ^ n)
      ((1 - q)⁻¹ *
        (QPochhammer.qPochhammerInf (q ^ 2) (q ^ 2)
            (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero) *
          QPochhammer.qPochhammerInf (-q) q hq - q))

/-- Generating function of `R_3(n)`, denominator cleared:
`(1-q)³(1+q+q²) ∑ R_3(n) qⁿ = q⁶(1+2q+q²+2q³-q⁴-q⁶-q⁷+q⁸)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 2
(`jis-2026-26.2.6-thm-2`). -/
public theorem_wanted maxRookPartitionCount_three_genFun :
    (1 - X) ^ 3 * (1 + X + X ^ 2) * mk (fun n => (maxRookPartitionCount 3 n : ℤ)) =
      X ^ 6 * (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - X ^ 4 - X ^ 6 - X ^ 7 + X ^ 8)

/-- For `n > 14`,
`R_3(n) = 2R_3(n-1) - R_3(n-2) + R_3(n-3) - 2R_3(n-4) + R_3(n-5)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 3
(`jis-2026-26.2.6-cor-3`). -/
public theorem_wanted maxRookPartitionCount_three_recurrence (n : ℕ) (hn : 14 < n) :
    (maxRookPartitionCount 3 n : ℤ) =
      2 * maxRookPartitionCount 3 (n - 1) - maxRookPartitionCount 3 (n - 2) +
        maxRookPartitionCount 3 (n - 3) - 2 * maxRookPartitionCount 3 (n - 4) +
        maxRookPartitionCount 3 (n - 5)

/-- Generating function of `R_4(n)`, denominator cleared:
`(1-q)(1-q²)(1-q³)(1-q⁴) ∑ R_4(n) qⁿ = q¹⁰(1+4q+6q²+7q³+6q⁴+2q⁵-5q⁷-5q⁸-5q⁹+q¹¹+3q¹²+2q¹³-q¹⁶)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 4
(`jis-2026-26.2.6-thm-4`). -/
public theorem_wanted maxRookPartitionCount_four_genFun :
    (1 - X) * (1 - X ^ 2) * (1 - X ^ 3) * (1 - X ^ 4) *
        mk (fun n => (maxRookPartitionCount 4 n : ℤ)) =
      X ^ 10 * (1 + 4 * X + 6 * X ^ 2 + 7 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5 - 5 * X ^ 7 -
        5 * X ^ 8 - 5 * X ^ 9 + X ^ 11 + 3 * X ^ 12 + 2 * X ^ 13 - X ^ 16)

/-- Generating function of `R_5(n)`, denominator cleared:
`(1-q)²(1-q³)(1-q⁴)(1-q⁵) ∑ R_5(n) qⁿ = q¹⁵ P(q)` with the paper's
degree-24 polynomial `P`.

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

/-- Exact formula for `R_3(n)`, `n = 3m + a > 9`, `0 ≤ a ≤ 2`:
`6m² - 15m + 7`, `6m² - 11m + 2`, `6m² - 7m - 1` for `a = 0, 1, 2`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 6, first part
(`jis-2026-26.2.6-thm-6`). -/
public theorem_wanted maxRookPartitionCount_three_formula (m : ℕ) (a : Fin 3)
    (h : 9 < 3 * m + (a : ℕ)) :
    (maxRookPartitionCount 3 (3 * m + (a : ℕ)) : ℤ) =
      6 * (m : ℤ) ^ 2 + ![-15, -11, -7] a * m + ![7, 2, -1] a

/-- For `n > 9` and `p ≥ 2`, `R_3(n + 3p) ≡ R_3(n) (mod p)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 6, second part
(`jis-2026-26.2.6-thm-6`). -/
public theorem_wanted maxRookPartitionCount_three_modEq (p n : ℕ) (hp : 2 ≤ p) (hn : 9 < n) :
    maxRookPartitionCount 3 (n + 3 * p) ≡ maxRookPartitionCount 3 n [MOD p]

/-- `R_3(n) ∼ (2/3) n²` as `n → ∞`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 7
(`jis-2026-26.2.6-cor-7`). -/
public theorem_wanted maxRookPartitionCount_three_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (maxRookPartitionCount 3 n : ℝ))
      (fun n => 2 / 3 * (n : ℝ) ^ 2)

/-- Exact formula for `R_4(n)`, `n = 12m + a > 16`, `0 ≤ a ≤ 11`:
`192m³ + b_a m² + c_a m + d_a` with the paper's twelve coefficient triples.

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

/-- For `n > 16` and `p ≥ 2`, `R_4(n + 12p) ≡ R_4(n) (mod p)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 8, second part
(`jis-2026-26.2.6-thm-8`). -/
public theorem_wanted maxRookPartitionCount_four_modEq (p n : ℕ) (hp : 2 ≤ p) (hn : 16 < n) :
    maxRookPartitionCount 4 (n + 12 * p) ≡ maxRookPartitionCount 4 n [MOD p]

/-- `R_4(n) ∼ n³ / 9` as `n → ∞`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Corollary 9
(`jis-2026-26.2.6-cor-9`). -/
public theorem_wanted maxRookPartitionCount_four_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (maxRookPartitionCount 4 n : ℝ))
      (fun n => (n : ℝ) ^ 3 / 9)

/-- Parity of `R_3(n)` for `n > 9`: even for odd `n`, odd for even `n`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 10
(`jis-2026-26.2.6-thm-10`). -/
public theorem_wanted maxRookPartitionCount_three_mod_two (n : ℕ) (hn : 9 < n) :
    maxRookPartitionCount 3 n % 2 = if n % 2 = 1 then 0 else 1

/-- Parity of `R_4(n)` for `n > 16`: even iff `n ≡ 4, 6 (mod 8)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 11
(`jis-2026-26.2.6-thm-11`). -/
public theorem_wanted maxRookPartitionCount_four_mod_two (n : ℕ) (hn : 16 < n) :
    maxRookPartitionCount 4 n % 2 = if n % 8 = 4 ∨ n % 8 = 6 then 0 else 1

/-- Parity of `R_5(n)` for `n > 25`: even iff `n ≡ 5, 7 (mod 8)`.

Source: N. Guru Sharan, *Rook Decomposition of the Partition Function*,
Journal of Integer Sequences 29 (2026), Article 26.2.6, Theorem 13
(`jis-2026-26.2.6-thm-13`). -/
public theorem_wanted maxRookPartitionCount_five_mod_two (n : ℕ) (hn : 25 < n) :
    maxRookPartitionCount 5 n % 2 = if n % 8 = 5 ∨ n % 8 = 7 then 0 else 1

end

end MetaMathlibExt

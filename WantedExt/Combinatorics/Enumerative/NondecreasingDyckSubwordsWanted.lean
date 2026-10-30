/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Subwords in non-decreasing Dyck paths

Statements from Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in
Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article
25.1.6. Dyck paths are Mathlib's `DyckWord`s. A Dyck path is non-decreasing when
the heights of its valley vertices (the low points of the factors `DU`), read
from left to right, form a non-decreasing sequence; this is the `0`-Dyck case
of Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. A subword is a contiguous factor, and
`nondecreasingDyckSubwordTotal w n` is the total number of occurrences of `w`
(overlapping occurrences counted separately) summed over the non-decreasing
Dyck paths of semilength `n`. The bivariate generating function
`F_w(x, y) = ∑_{n ≥ 1} ∑_{P} x^n y^{#w(P)}` is a power series in `x` with
coefficients in `ℤ[y]`, and the univariate `D_w(x) = ∑ d_w(n) x^n`. Generating
function identities are stated with the denominator cleared, and the closed
forms with the rational factor cleared, over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- The heights of the valley vertices of a step list, read from left to right:
for each factor `DU`, the height reached after its `D`.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1, the definition of non-decreasing Dyck paths used by
Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck
Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6. -/
public def dyckValleyHeights (l : List DyckStep) : List ℕ :=
  ((List.range l.length).filter fun i => decide (l[i]? = some D ∧ l[i + 1]? = some U)).map
    fun i => (l.take (i + 1)).count U - (l.take (i + 1)).count D

/-- The path `UUDUDDUD` has valley heights `1, 0`, so it is not non-decreasing.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public theorem dyckValleyHeights_UUDUDDUD :
    dyckValleyHeights [U, U, D, U, D, D, U, D] = [1, 0] := by decide

/-- The path `UDUUDUDD` has valley heights `0, 1`.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public theorem dyckValleyHeights_UDUUDUDD :
    dyckValleyHeights [U, D, U, U, D, U, D, D] = [0, 1] := by decide

/-- A Dyck path is non-decreasing when its valley heights are non-decreasing
from left to right.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1 (the `0`-Dyck paths), as used by Flórez, Junes,
Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of
Integer Sequences 28 (2025), Article 25.1.6. -/
public def IsNondecreasingDyckPath (p : DyckWord) : Prop :=
  (dyckValleyHeights p.toList).Pairwise (· ≤ ·)

/-- Non-decreasing is decidable.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public instance : DecidablePred IsNondecreasingDyckPath := fun p => by
  unfold IsNondecreasingDyckPath
  infer_instance

/-- The set `D_n` of non-decreasing Dyck paths of semilength `n`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def nondecreasingDyckWords (n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p => IsNondecreasingDyckPath p.1

/-- All five Dyck paths of semilength `3` are non-decreasing.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem card_nondecreasingDyckWords_three : (nondecreasingDyckWords 3).card = 5 := by
  decide +kernel

/-- There are `13` non-decreasing Dyck paths of semilength `4` (all `14` Dyck paths
except `UUDUDDUD`).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem card_nondecreasingDyckWords_four : (nondecreasingDyckWords 4).card = 13 := by
  decide +kernel

/-- The number of occurrences of the contiguous subword `w` in the step list
`l`, overlapping occurrences counted separately.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def dyckSubwordCount (w l : List DyckStep) : ℕ :=
  l.tails.countP fun t => w.isPrefixOf t

/-- `UUUDDD` contains the subword `UU` twice (the occurrences overlap).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem dyckSubwordCount_UU_UUUDDD :
    dyckSubwordCount [U, U] [U, U, U, D, D, D] = 2 := by decide

/-- `UDUDUD` contains the subword `UDU` twice.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem dyckSubwordCount_UDU_UDUDUD :
    dyckSubwordCount [U, D, U] [U, D, U, D, U, D] = 2 := by decide

/-- `d_w(n)`: the total number of occurrences of the subword `w` over all
non-decreasing Dyck paths of semilength `n`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def nondecreasingDyckSubwordTotal (w : List DyckStep) (n : ℕ) : ℕ :=
  ∑ p ∈ nondecreasingDyckWords n, dyckSubwordCount w p.1.toList

/-- The `10` peaks over the five paths of semilength `3`: `d_UD(3) = 10`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem nondecreasingDyckSubwordTotal_UD_three :
    nondecreasingDyckSubwordTotal [U, D] 3 = 10 := by
  decide +kernel

/-- The bivariate generating function `F_w(x, y)`: the coefficient of `x^n`
(`n ≥ 1`) is `∑_{P ∈ D_n} y^{#w(P)}` in `ℤ[y]`; the empty path is not counted.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public noncomputable def nondecreasingDyckSubwordBivariateGF (w : List DyckStep) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else ∑ p ∈ nondecreasingDyckWords n, Polynomial.X ^ dyckSubwordCount w p.1.toList

/-- The univariate generating function `D_w(x) = ∑ d_w(n) x^n`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public noncomputable def nondecreasingDyckSubwordTotalGF (w : List DyckStep) :
    PowerSeries ℤ :=
  PowerSeries.mk fun n => (nondecreasingDyckSubwordTotal w n : ℤ)

/-- The height of the last peak (factor `UD`) of a step list, if it has one.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public def dyckLastPeakHeight (l : List DyckStep) : Option ℕ :=
  ((List.range l.length).filter fun i =>
      decide (l[i]? = some U ∧ l[i + 1]? = some D)).getLast?.map
    fun i => (l.take (i + 1)).count U - (l.take (i + 1)).count D

/-- The last peak of `UDUUDD` has height `2`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public theorem dyckLastPeakHeight_UDUUDD :
    dyckLastPeakHeight [U, D, U, U, D, D] = some 2 := by decide

/-- `l_{n,k}`: the number of non-decreasing Dyck paths of semilength `n` whose
last peak has height `k`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public def nondecreasingDyckLastPeakCount (n k : ℕ) : ℕ :=
  ((nondecreasingDyckWords n).filter fun p => dyckLastPeakHeight p.1.toList = some k).card

/-- Four of the paths in `D_4` have last peak of height `1`: `l_{4,1} = 4`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public theorem nondecreasingDyckLastPeakCount_four_one :
    nondecreasingDyckLastPeakCount 4 1 = 4 := by
  decide +kernel

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `y` of the bivariate generating functions, a constant in `ℤ[y]`. -/
local notation "𝒚" => PowerSeries.C (Polynomial.X : Polynomial ℤ)
/-- The variable `x` of the univariate generating functions. -/
local notation "𝒛" => (PowerSeries.X : PowerSeries ℤ)

/-- Subword `UD` in non-decreasing Dyck paths: `F_UD(x, y)`, `D_UD(x)`, and the closed form of
`d_UD(n)` for `n ≥ 1`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 1
(`jis-2025-25.1.6-thm-1`). -/
public theorem_wanted nondecreasingDyck_subword_UD :
    (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, D] = (1 - 𝒙) * 𝒙 * 𝒚 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D] = 𝒛 * (1 - 𝒛) ^ 3 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, D] n : ℤ) =
        (5 * (n : ℤ) - 7) * (Nat.fib (2 * n) : ℤ) - ((n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- Subword `DU` in non-decreasing Dyck paths: `F_DU(x, y)`, `D_DU(x)`, and the closed form of
`d_DU(n)` for `n ≥ 1`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 2
(`jis-2025-25.1.6-thm-2`). -/
public theorem_wanted nondecreasingDyck_subword_DU :
    (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * nondecreasingDyckSubwordBivariateGF [D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U] = (1 - 𝒛) * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, U] n : ℤ) =
        (5 * (n : ℤ) - 2) * (Nat.fib (2 * n) : ℤ) - (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- Subwords `UU` and `DD` in non-decreasing Dyck paths: for `w ∈ {UU, DD}`,
`F_w(x, y)`, `D_w(x)`, and the closed form of `d_w(n)` for `n ≥ 1`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 3
(`jis-2025-25.1.6-thm-3`). -/
public theorem_wanted nondecreasingDyck_subword_UU_DD (w : List DyckStep)
    (hw : w = [U, U] ∨ w = [D, D]) :
    (1 - 𝒙 - 2 * 𝒙 * 𝒚 + 𝒙 ^ 2 * 𝒚 ^ 2) * nondecreasingDyckSubwordBivariateGF w =
      𝒙 * (1 - 𝒙 * 𝒚) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF w = 𝒛 ^ 2 * (1 - 𝒛 + 𝒛 ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal w n : ℤ) =
        (7 - 10 * (n : ℤ)) * (Nat.fib (2 * n) : ℤ) + (6 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- Subword `UUU` in non-decreasing Dyck paths: `F_UUU(x, y)`, `D_UUU(x)`, and the closed form of
`d_UUU(n)` for `n ≥ 1`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 4
(`jis-2025-25.1.6-thm-4`). -/
public theorem_wanted nondecreasingDyck_subword_UUU :
    (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, U, U]
        = (1 - 𝒙 * 𝒚) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, U] = 𝒛 ^ 3 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, U, U] n : ℤ) =
        -(5 * (n : ℤ) + 4) * (Nat.fib (2 * n) : ℤ) + 3 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- Subword `UDU` in non-decreasing Dyck paths: `F_UDU(x, y)`, `D_UDU(x)`, and the closed form of
`d_UDU(n)` for `n ≥ 1`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 5
(`jis-2025-25.1.6-thm-5`). -/
public theorem_wanted nondecreasingDyck_subword_UDU :
    (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D, U] = 𝒛 ^ 2 * (1 - 𝒛) ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, D, U] n : ℤ) =
        (-5 * (n : ℤ) + 11) * (Nat.fib (2 * n) : ℤ) + (3 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- Subword `UDD` in non-decreasing Dyck paths: `F_UDD(x, y)`, `D_UDD(x)`, and the closed form of
`d_UDD(n)` for `n ≥ 2`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 6
(`jis-2025-25.1.6-thm-6`). -/
public theorem_wanted nondecreasingDyck_subword_UDD :
    ((1 - 3 * 𝒙 + 𝒙 ^ 2 * (2 - 𝒚)) * (1 - 2 * 𝒙 + 𝒙 ^ 2 * (1 - 𝒚)))
        * nondecreasingDyckSubwordBivariateGF [U, D, D]
        = (1 - 𝒙) * (1 - 2 * 𝒙) * (1 - 𝒙 * (1 - 𝒚)) * 𝒙 ∧
    ((1 - 2 * 𝒛) * (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D, D]
        = (1 - 𝒛) * (1 - 3 * 𝒛 + 2 * 𝒛 ^ 2 - 𝒛 ^ 3) * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      5 * (nondecreasingDyckSubwordTotal [U, D, D] n : ℤ) =
        (5 * (n : ℤ) - 9) * (Nat.fib (2 * n) : ℤ) + (-2 * (n : ℤ) + 5) * (lucasNumber (2 * n) : ℤ)
            - 5 * 2 ^ (n - 2)

/-- Subword `DUU` in non-decreasing Dyck paths: `F_DUU(x, y)`, `D_DUU(x)`, and the closed form of
`d_DUU(n)` for `n ≥ 3`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 7
(`jis-2025-25.1.6-thm-7`). -/
public theorem_wanted nondecreasingDyck_subword_DUU :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (3 - 2 * 𝒚) - 𝒙 ^ 3 * (1 - 𝒚))
        * nondecreasingDyckSubwordBivariateGF [D, U, U] = 𝒙 - 𝒙 ^ 2 + 𝒙 ^ 3 * (1 - 𝒚) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U, U] = 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, U, U] n : ℤ) =
        -(5 * (n : ℤ) + 4) * (Nat.fib (2 * n) : ℤ) + 3 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- Subword `DUD` in non-decreasing Dyck paths: `F_DUD(x, y)`, `D_DUD(x)`, and the closed form of
`d_DUD(n)` for `n ≥ 3`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 8
(`jis-2025-25.1.6-thm-8`). -/
public theorem_wanted nondecreasingDyck_subword_DUD :
    (1 - 𝒙 ^ 2 * (1 - 2 * 𝒚) + 𝒙 ^ 3 * (1 - 𝒚) - 𝒙 * (2 + 𝒚))
        * nondecreasingDyckSubwordBivariateGF [D, U, D] = 𝒙 * (1 - 𝒙 - 𝒙 ^ 2 * (1 - 𝒚)) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U, D] = 𝒛 ^ 2 - 2 * 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      5 * (nondecreasingDyckSubwordTotal [D, U, D] n : ℤ) =
        (5 * (n : ℤ) + 1) * (Nat.fib (2 * n) : ℤ) - 2 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- Subword `DDU` in non-decreasing Dyck paths: `F_DDU(x, y)`, `D_DDU(x)`, and the closed form of
`d_DDU(n)` for `n ≥ 3`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 9
(`jis-2025-25.1.6-thm-9`). -/
public theorem_wanted nondecreasingDyck_subword_DDU :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (2 - 𝒚)) * nondecreasingDyckSubwordBivariateGF [D, D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, D, U] = (1 - 𝒛) * 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, D, U] n : ℤ) =
        (10 * (n : ℤ) - 13) * (Nat.fib (2 * n) : ℤ) + (-4 * (n : ℤ) + 5) * (lucasNumber (2 * n) : ℤ)

/-- Subword `DDD` in non-decreasing Dyck paths: `F_DDD(x, y)`, `D_DDD(x)`, and the closed form of
`d_DDD(n)` for `n ≥ 3`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 10
(`jis-2025-25.1.6-thm-10`). -/
public theorem_wanted nondecreasingDyck_subword_DDD :
    ((1 - 𝒙 * (1 + 𝒚) - 𝒙 ^ 2 * (1 - 𝒚)) * (1 - 𝒙 * (1 + 2 * 𝒚) - 𝒙 ^ 2 * (1 - 𝒚 - 𝒚 ^ 2)))
        * nondecreasingDyckSubwordBivariateGF [D, D, D]
        = 𝒙 * (1 - 𝒙 * 𝒚) * (1 - 2 * 𝒙 * 𝒚 - 𝒙 ^ 2 * (1 - 𝒚 ^ 2)) ∧
    ((1 - 2 * 𝒛) * (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, D, D]
        = 𝒛 ^ 3 * (1 - 2 * 𝒛 + 𝒛 ^ 2 - 𝒛 ^ 3) ∧
    ∀ n : ℕ, 3 ≤ n →
      4 * (nondecreasingDyckSubwordTotal [D, D, D] n : ℤ) =
        (-8 * (n : ℤ) + 10) * (Nat.fib (2 * n) : ℤ) + (4 * (n : ℤ) - 6) * (lucasNumber (2 * n) : ℤ)
            + 2 ^ n

/-- Subword `UUD` in non-decreasing Dyck paths: `F_UUD(x, y)`, `D_UUD(x)`, and the closed form of
`d_UUD(n)` for `n ≥ 3`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 11
(`jis-2025-25.1.6-thm-11`). -/
public theorem_wanted nondecreasingDyck_subword_UUD :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (3 - 2 * 𝒚) - 𝒙 ^ 3 * (1 - 𝒚))
        * nondecreasingDyckSubwordBivariateGF [U, U, D] = (1 - 𝒙) * 𝒙 * (1 - 𝒙 * (1 - 𝒚)) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, D] = (1 - 𝒛) ^ 2 * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, U, D] n : ℤ) =
        (-5 * (n : ℤ) + 11) * (Nat.fib (2 * n) : ℤ) + (3 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- Subword `UUUD` in non-decreasing Dyck paths: `F_UUUD(x, y)`, `D_UUUD(x)`, and the closed form of
`d_UUUD(n)` for `n ≥ 3`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 12
(`jis-2025-25.1.6-thm-12`). -/
public theorem_wanted nondecreasingDyck_subword_UUUD :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 + (3 - 3 * 𝒚) * 𝒙 ^ 3 - 2 * (1 - 𝒚) * 𝒙 ^ 4)
        * nondecreasingDyckSubwordBivariateGF [U, U, U, D] = (1 - 𝒙) * (𝒙 + 𝒙 ^ 3 * (𝒚 - 1)) ∧
    ((1 + 𝒛 * (𝒛 - 3)) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, U, D]
        = (𝒛 - 1) ^ 2 * 𝒛 ^ 3 * (𝒛 + 1) ∧
    ∀ n : ℕ, 3 ≤ n →
      (nondecreasingDyckSubwordTotal [U, U, U, D] n : ℤ) =
        (n : ℤ) * (Nat.fib (2 * n - 5) : ℤ) - (lucasNumber (2 * n - 6) : ℤ)

/-- Subword `U^m` (`m ≥ 1`) in non-decreasing Dyck paths: for `n > m`,
`d_{U^m}(n) = 3 d_{U^m}(n-1) - d_{U^m}(n-2) + F_{2(n-m)} + F_{2(n-2)}
- ∑_{k=1}^{m-2} k F_{2(n-k-2)}`; `d_{U^m}(n) = 0` for `n < m`; and
`d_{U^m}(m) = 1`. The source writes `n ≤ m` for the vanishing case, which
contradicts `d_{U^n}(n) = 1` at `n = m`; the vanishing case is stated for
`n < m`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 13
(`jis-2025-25.1.6-thm-13`). -/
public theorem_wanted nondecreasingDyck_subword_U_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n →
      (nondecreasingDyckSubwordTotal (List.replicate m U) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m)) : ℤ) + (Nat.fib (2 * (n - 2)) : ℤ)
          - ∑ k ∈ Finset.Icc 1 (m - 2), (k : ℤ) * (Nat.fib (2 * (n - k - 2)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U) m = 1

/-- Subword `U^m D` (`m ≥ 1`) in non-decreasing Dyck paths: for `n ≥ m + 2`,
`d_{U^mD}(n) = 3 d_{U^mD}(n-1) - d_{U^mD}(n-2) + F_{2(n-m)-3} + m F_{2(n-m-1)}`;
`d_{U^mD}(n) = 0` for `n < m`; `d_{U^mD}(m) = 1`; and `d_{U^mD}(m+1) = m + 2`.
The source states the recurrence for `n ≥ m`, where `n = m` and `n = m + 1` give
negative Fibonacci indices; those two values are the separately stated initial
values, and the recurrence is stated for `n ≥ m + 2`.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 15
(`jis-2025-25.1.6-thm-15`). -/
public theorem_wanted nondecreasingDyck_subword_U_pow_D (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m + 2 ≤ n →
      (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m) - 3) : ℤ) + (m : ℤ) * (Nat.fib (2 * (n - m - 1)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) m = 1 ∧
    nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (m + 1) = m + 2

/-- Subword `U D^m` (`m ≥ 1`) in non-decreasing Dyck paths: for `n > m` and
`n ≥ 3`, `d_{UD^m}(n) = 3 d_{UD^m}(n-1) - d_{UD^m}(n-2) + F_{2(n-m)-1}
+ l_{n-1,m-1} - l_{n-2,m-1}`, where `l_{n,k}` counts the paths in `D_n` whose last
peak has height `k`; `d_{UD^m}(n) = 0` for `n < m`; and `d_{UD^m}(m) = 1`. The
source states the recurrence for `n ≥ m`; `n = m` is the separately stated
initial value, and the added `n ≥ 3` excludes only `(m, n) = (1, 2)`, where
`d_{UD}(2) = 3` but the right side is `3·1 - 0 + F_1 + l_{1,0} - l_{0,0} = 4`
(the empty path has no peak).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16
(`jis-2025-25.1.6-thm-16`). -/
public theorem_wanted nondecreasingDyck_subword_U_D_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n → 3 ≤ n →
      (nondecreasingDyckSubwordTotal (U :: List.replicate m D) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (U :: List.replicate m D) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (U :: List.replicate m D) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m) - 1) : ℤ)
          + (nondecreasingDyckLastPeakCount (n - 1) (m - 1) : ℤ)
          - (nondecreasingDyckLastPeakCount (n - 2) (m - 1) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (U :: List.replicate m D) n = 0) ∧
    nondecreasingDyckSubwordTotal (U :: List.replicate m D) m = 1

end

end MetaMathlibExt

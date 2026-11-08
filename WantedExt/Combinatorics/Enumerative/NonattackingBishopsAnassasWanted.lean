/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Binomial
public import MathlibExt.Combinatorics.AssociatedStirlingSecond

/-!
# Counting nonattacking placements of bishops and anassas

Statements from Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and
Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6 (preprint arXiv:2411.16492,
from which the definitions are taken).

* A board is a finite set of squares `(i, j) ∈ ℤ²`; a piece with basic moves `M` attacks along
  the lines through its square in the directions of `M`, so a placement is nonattacking when no
  two of its squares differ by a rational multiple of a move (`nonattackingPlacements`).
* `squareBoard m = [1, m]²`. The paper's white and black boards `W_m`, `K_m` are the
  diagonals of the white and black squares of `S_m` drawn as rows and columns, so rooks on
  `W_m` (resp. `K_m`) are bishops on the squares of `S_m` with `i + j` even (resp. odd); the
  counts `R_W`, `R_K` are taken in that form (`whiteSquares`, `blackSquares`; the single square
  of `S_1` is white).
* The bishop has moves `(1, 1), (-1, 1)`; the anassa `(0, 1), (1, 1)`, and "strictly below the
  main diagonal" means `j < i`.
* The paper uses the extended Stirling numbers of the second kind of Knuth, defined for all
  integer arguments by `{n, k} = [-k, -n]` (unsigned first kind) for negative arguments and `0`
  for mixed signs (`extStirlingSecond`); its associated Stirling numbers of the second kind
  `{{n, k}}` are the canonical `twoAssocStirlingSecond` (integer-valued), and `Ring.choose` is the binomial coefficient with arbitrary
  top argument.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- The nonattacking placements of `k` pieces with basic moves `M` on the board `B`:
`k`-subsets of `B` no two of whose squares lie on a common line in the direction of a move.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public def nonattackingPlacements (B : Finset (ℤ × ℤ)) (M : List (ℤ × ℤ)) (k : ℕ) :
    Finset (Finset (ℤ × ℤ)) :=
  (B.powersetCard k).filter fun S =>
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ v ∈ M, (q.1 - p.1) * v.2 ≠ (q.2 - p.2) * v.1

/-- There is exactly one placement of no pieces.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public theorem card_nonattackingPlacements_zero (B : Finset (ℤ × ℤ)) (M : List (ℤ × ℤ)) :
    (nonattackingPlacements B M 0).card = 1 := by
  simp [nonattackingPlacements, Finset.filter_singleton]

/-- The square board `S_m = [1, m]²`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2. -/
public def squareBoard (m : ℕ) : Finset (ℤ × ℤ) :=
  Icc (1 : ℤ) m ×ˢ Icc (1 : ℤ) m

/-- The white squares (`i + j` even) of `S_m`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2, Table 1. -/
public def whiteSquares (m : ℕ) : Finset (ℤ × ℤ) :=
  (squareBoard m).filter fun s => Even (s.1 + s.2)

/-- The black squares (`i + j` odd) of `S_m`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2, Table 1. -/
public def blackSquares (m : ℕ) : Finset (ℤ × ℤ) :=
  (squareBoard m).filter fun s => Odd (s.1 + s.2)

/-- The bishop's basic moves `(1, 1), (-1, 1)`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 2. -/
public def bishopMoves : List (ℤ × ℤ) := [(1, 1), (-1, 1)]

/-- The anassa's basic moves `(0, 1), (1, 1)`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 3. -/
public def anassaMoves : List (ℤ × ℤ) := [(0, 1), (1, 1)]

/-- `B_S(m, k)`: nonattacking placements of `k` bishops on `S_m`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.1. -/
public def bishopsSquare (m k : ℕ) : ℕ :=
  (nonattackingPlacements (squareBoard m) bishopMoves k).card

/-- `R_W(m, k)`: nonattacking placements of `k` rooks on the white board `W_m`, i.e. of `k`
bishops on the white squares of `S_m`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.2. -/
public def bishopsWhite (m k : ℕ) : ℕ :=
  (nonattackingPlacements (whiteSquares m) bishopMoves k).card

/-- `R_K(m, k)`: nonattacking placements of `k` rooks on the black board `K_m`, i.e. of `k`
bishops on the black squares of `S_m`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.2. -/
public def bishopsBlack (m k : ℕ) : ℕ :=
  (nonattackingPlacements (blackSquares m) bishopMoves k).card

/-- `A_S(m, k, p)`: nonattacking placements of `k` anassas on `S_m` with exactly `p` of them
strictly below the main diagonal (`j < i`).

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3.1. -/
public def anassasBelow (m k p : ℕ) : ℕ :=
  ((nonattackingPlacements (squareBoard m) anassaMoves k).filter fun S =>
    (S.filter fun s => s.2 < s.1).card = p).card

/-- Knuth's extension of the Stirling numbers of the second kind to integer arguments:
`{n, k}` for `n, k ≥ 0`, the unsigned Stirling number of the first kind `[-k, -n]` for
`n, k < 0`, and `0` otherwise.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1 (extended Stirling numbers,
with the identity `{-j, -k} = [k, j]`). -/
public def extStirlingSecond (n k : ℤ) : ℕ :=
  if 0 ≤ n ∧ 0 ≤ k then Nat.stirlingSecond n.toNat k.toNat
  else if n < 0 ∧ k < 0 then Nat.stirlingFirst (-k).toNat (-n).toNat
  else 0

/-- At natural arguments `extStirlingSecond` is `Nat.stirlingSecond`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Section 1. -/
public theorem extStirlingSecond_natCast (n k : ℕ) :
    extStirlingSecond n k = Nat.stirlingSecond n k := by
  simp [extStirlingSecond]

/-- `{-a, -b} = [b, a]` for positive `a`, `b`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, proof of Theorem 2.2. -/
public theorem extStirlingSecond_neg_neg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    extStirlingSecond (-(a : ℤ)) (-(b : ℤ)) = Nat.stirlingFirst b a := by
  simp [extStirlingSecond, ha, hb, ha.ne', hb.ne']

/-- The coefficient
`β_i(p, q, z) = 2^{-2q} ∑_{b=max(0,i-p)}^{q} 2^b binom(2q-b, q)
∑_{a=0}^{b} binom(p+b-q-z, a) binom(q+z, b-a) binom(a-q, p+b-i)` of Lemma 2.7, for complex `z`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7, equation (9). -/
public noncomputable def santosBeta (i p q : ℕ) (z : ℂ) : ℂ :=
  1 / 2 ^ (2 * q) *
    ∑ b ∈ Icc (i - p) q, 2 ^ b * ((2 * q - b).choose q : ℂ) *
      ∑ a ∈ range (b + 1),
        Ring.choose ((p : ℂ) + b - q - z) a * Ring.choose ((q : ℂ) + z) (b - a) *
          Ring.choose ((a : ℂ) - q) (p + b - i)

/-- `β_0(0, 0, z) = 1`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7. -/
public theorem santosBeta_zero (z : ℂ) : santosBeta 0 0 0 z = 1 := by
  simp [santosBeta]

/-- The constituent coefficient `[m^d]` of Theorem 2.8, equations (13), (14):
`∑_{i=d}^{2k} (-1)^{i-d}/i! [i, d] ∑_{p=max(0,i-k)}^{k} ∑_{j=p}^{k} {{p+j, p}} β_i(p+j, k-j, z)`,
with `z = -π(m)` for the white board and `z = π(m)` for the black board.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8. -/
public noncomputable def bishopColorQuasiCoeff (k d : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Icc d (2 * k), (-1) ^ (i - d) / (i.factorial : ℂ) * (Nat.stirlingFirst i d : ℂ) *
    ∑ p ∈ Icc (i - k) k, ∑ j ∈ Icc p k,
      (twoAssocStirlingSecond (p + j) p : ℂ) * santosBeta i (p + j) (k - j) z

/-- `[m^0] R(m, 0) = 1`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 2.8. -/
public theorem bishopColorQuasiCoeff_zero_zero (z : ℂ) : bishopColorQuasiCoeff 0 0 z = 1 := by
  simp [bishopColorQuasiCoeff, twoAssocStirlingSecond, santosBeta_zero]

/-! ## Collapsible boards -/

/-! Theorem 1.2 (`jis-2025-25.8.6-thm-2`) is not stated: see the audit table. -/

/-! ## The bishop -/

/-- Arshon's formula as refined by Kotěšovec:
`B_S(m, k) = ∑_{j=0}^{m} ∑_{i=0}^{⌊(m+1)/2⌋} binom(⌊(m+1)/2⌋, i) {i + ⌊m/2⌋, m - j}
∑_{l=0}^{⌊m/2⌋} binom(⌊m/2⌋, l) {l + ⌊(m+1)/2⌋, m - k + j}`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 3 (Arshon, Kotěšovec)
(`jis-2025-25.8.6-thm-3`). -/
public theorem_wanted bishopsSquare_eq_arshon (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (m + 1), ∑ i ∈ range ((m + 1) / 2 + 1),
        ((m + 1) / 2).choose i * extStirlingSecond (i + m / 2 : ℕ) ((m : ℤ) - j) *
          ∑ l ∈ range (m / 2 + 1),
            (m / 2).choose l * extStirlingSecond (l + (m + 1) / 2 : ℕ) ((m : ℤ) - k + j)

/-- Equation (1): `R_W(m, k) = R_W(m-1, k) + (m - k + π(m)) R_W(m-1, k-1)` for `m, k ≥ 1`,
with `R_W(m, 0) = 1` and `R_W(0, k) = δ_{k0}`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsWhite_recurrence (m k : ℕ) :
    (bishopsWhite (m + 1) (k + 1) : ℤ) =
        bishopsWhite m (k + 1) + ((m : ℤ) - k + ((m + 1) % 2 : ℕ)) * bishopsWhite m k ∧
      bishopsWhite m 0 = 1 ∧ bishopsWhite 0 (k + 1) = 0

/-- Equation (2): `R_K(m, k) = R_K(m-1, k) + (m - k + 1 - π(m)) R_K(m-1, k-1)` for
`m, k ≥ 1`, with `R_K(m, 0) = 1` and `R_K(0, k) = δ_{k0}`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsBlack_recurrence (m k : ℕ) :
    (bishopsBlack (m + 1) (k + 1) : ℤ) =
        bishopsBlack m (k + 1) + ((m : ℤ) - k + 1 - ((m + 1) % 2 : ℕ)) * bishopsBlack m k ∧
      bishopsBlack m 0 = 1 ∧ bishopsBlack 0 (k + 1) = 0

/-- Equation (3): `R_W(m, k) = ∑_{j=0}^{k} binom(⌈m/2⌉, j) {m - j, m - k}` for all
`m, k ≥ 0` (extended Stirling numbers).

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsWhite_eq_sum (m k : ℕ) :
    bishopsWhite m k =
      ∑ j ∈ range (k + 1), ((m + 1) / 2).choose j * extStirlingSecond ((m : ℤ) - j) ((m : ℤ) - k)

/-- Equation (4): `R_K(m, k) = ∑_{j=0}^{k} binom(⌊m/2⌋, j) {m - j, m - k}` for all
`m, k ≥ 0` (extended Stirling numbers).

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 4 (`jis-2025-25.8.6-thm-4`). -/
public theorem_wanted bishopsBlack_eq_sum (m k : ℕ) :
    bishopsBlack m k =
      ∑ j ∈ range (k + 1), (m / 2).choose j * extStirlingSecond ((m : ℤ) - j) ((m : ℤ) - k)

/-- Equation (5): `B_S(m, k) = ∑_{j=0}^{k} ∑_{i=0}^{j} binom(⌊m/2⌋, i) {m - i, m - j}
∑_{l=0}^{k-j} binom(⌈m/2⌉, l) {m - l, m - k + j}` for all `m, k ≥ 0`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 6 (`jis-2025-25.8.6-thm-6`). -/
public theorem_wanted bishopsSquare_eq_sum (m k : ℕ) :
    bishopsSquare m k =
      ∑ j ∈ range (k + 1), ∑ i ∈ range (j + 1),
        (m / 2).choose i * extStirlingSecond ((m : ℤ) - i) ((m : ℤ) - j) *
          ∑ l ∈ range (k - j + 1),
            ((m + 1) / 2).choose l * extStirlingSecond ((m : ℤ) - l) ((m : ℤ) - k + j)

/-- Ward's identity (7): `{m, m - k} = ∑_{p=0}^{k} {{k + p, p}} binom(m, k + p)` for
`0 ≤ k ≤ m`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 8 (`jis-2025-25.8.6-lem-8`). -/
public theorem_wanted stirlingSecond_sub_eq_sum_associated (m k : ℕ) (hk : k ≤ m) :
    (Nat.stirlingSecond m (m - k) : ℤ) =
      ∑ p ∈ range (k + 1), twoAssocStirlingSecond (k + p) p * m.choose (k + p)

/-- Equation (8): for natural `p`, `q` and complex `x`, `z`,
`binom(2x + z - q, p) binom(x, q) = ∑_{i=0}^{p+q} β_i(p, q, z) binom(2x + z, i)`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 9 (`jis-2025-25.8.6-lem-9`). -/
public theorem_wanted choose_mul_choose_eq_sum_santosBeta (p q : ℕ) (x z : ℂ) :
    Ring.choose (2 * x + z - q) p * Ring.choose x q =
      ∑ i ∈ range (p + q + 1), santosBeta i p q z * Ring.choose (2 * x + z) i

/-- Equation (13): `R_W(m, k) = ∑_{d=0}^{2k} c_d m^d` with the constituent coefficients
`c_d = [m^d] R_W(m, k)` of equation (13), `z = -π(m)`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`). -/
public theorem_wanted bishopsWhite_eq_quasi (m k : ℕ) :
    (bishopsWhite m k : ℂ) =
      ∑ d ∈ range (2 * k + 1), bishopColorQuasiCoeff k d (-((m % 2 : ℕ) : ℂ)) * (m : ℂ) ^ d

/-- Equation (14): `R_K(m, k) = ∑_{d=0}^{2k} c_d m^d` with the constituent coefficients of
equation (14), `z = π(m)`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`). -/
public theorem_wanted bishopsBlack_eq_quasi (m k : ℕ) :
    (bishopsBlack m k : ℂ) =
      ∑ d ∈ range (2 * k + 1), bishopColorQuasiCoeff k d ((m % 2 : ℕ) : ℂ) * (m : ℂ) ^ d

/-- Equation (15): `B_S(m, k) = ∑_{d=0}^{2k} c_d m^d` with
`c_d = ∑_{j=0}^{k} ∑_{i=0}^{d} ([m^i] R_W(m, j)) ([m^{d-i}] R_K(m, k - j))`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 10 (`jis-2025-25.8.6-thm-10`). -/
public theorem_wanted bishopsSquare_eq_quasi (m k : ℕ) :
    (bishopsSquare m k : ℂ) =
      ∑ d ∈ range (2 * k + 1),
        (∑ j ∈ range (k + 1), ∑ i ∈ range (d + 1),
          bishopColorQuasiCoeff j i (-((m % 2 : ℕ) : ℂ)) *
            bishopColorQuasiCoeff (k - j) (d - i) ((m % 2 : ℕ) : ℂ)) * (m : ℂ) ^ d

/-! ## The anassa -/

/-- Recurrence (16) with its initial conditions: for `m ≥ 1`, `k ≥ 2`, `p ≥ 1`,
`A(m, k, p) = A(m-1, k, p) + (m-k+1) A(m-1, k-1, p) + (m-p) A(m-1, k-1, p-1)
+ (m-p)(m-k+1) A(m-1, k-2, p-1)`, and `A(0, k, p) = δ_{k0} δ_{p0}`, `A(m, 0, p) = δ_{p0}`,
`A(m, 1, p) = {m+1, m} δ_{p0} + {m, m-1} δ_{p1}`, `A(m, k, 0) = {m+1, m-k+1}`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`). -/
public theorem_wanted anassasBelow_recurrence (m k p : ℕ) :
    ((anassasBelow (m + 1) (k + 2) (p + 1) : ℤ) =
        anassasBelow m (k + 2) (p + 1) + ((m : ℤ) - k) * anassasBelow m (k + 1) (p + 1) +
          ((m : ℤ) - p) * anassasBelow m (k + 1) p +
          ((m : ℤ) - p) * ((m : ℤ) - k) * anassasBelow m k p) ∧
      anassasBelow 0 k p = (if k = 0 ∧ p = 0 then 1 else 0) ∧
      anassasBelow m 0 p = (if p = 0 then 1 else 0) ∧
      anassasBelow m 1 p =
        (if p = 0 then Nat.stirlingSecond (m + 1) m else 0) +
          (if p = 1 then extStirlingSecond m ((m : ℤ) - 1) else 0) ∧
      anassasBelow m k 0 = extStirlingSecond (m + 1 : ℕ) ((m : ℤ) - k + 1)

/-- Equation (17): for `p ≤ k`,
`A(m, k, p) = ∑_{j=0}^{p} (m-k+j)_j binom(k-p-1, j) binom(k-j, k-p) {m+1, m-k+j+1}`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 11 (`jis-2025-25.8.6-thm-11`). -/
public theorem_wanted anassasBelow_eq_sum (m k p : ℕ) (hp : p ≤ k) :
    (anassasBelow m k p : ℤ) =
      ∑ j ∈ range (p + 1),
        (∏ t ∈ range j, ((m : ℤ) - k + j - t)) * Ring.choose ((k : ℤ) - p - 1) j *
          ((k - j).choose (k - p) : ℤ) * extStirlingSecond (m + 1 : ℕ) ((m : ℤ) - k + j + 1)

/-- `A_S(m, k) = ∑_p A_S(m, k, p) = ∑_{j=0}^{⌈k/2⌉} (m-k+j)_j {m, m-k+j} 2^{k-2j}
(binom(k-j, j-1) + binom(k-j+1, j))`, where `binom(k, -1) = 0`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 13 (`jis-2025-25.8.6-thm-13`). -/
public theorem_wanted sum_anassasBelow_eq (m k : ℕ) :
    (∑ p ∈ range (k + 1), (anassasBelow m k p : ℚ)) =
      ∑ j ∈ range ((k + 1) / 2 + 1),
        (∏ t ∈ range j, ((m : ℚ) - k + j - t)) * extStirlingSecond m ((m : ℤ) - k + j) *
          (2 : ℚ) ^ ((k : ℤ) - 2 * j) *
          ((if j = 0 then 0 else ((k - j).choose (j - 1) : ℚ)) + ((k - j + 1).choose j : ℚ))

/-- Theorem 16: `A_S(m, k) = ∑_{d=0}^{2k} c_d m^d` with
`c_d = ∑_{i=d}^{2k} (-1)^{i-d}/i! [i, d] ∑_{j=0}^{U(i,k)} α(k, j) ∑_{p=L(i,k)}^{k-j}
{{p+k-j, p}} ∑_{b=0}^{j} binom(p, b) binom(k, j-b) binom(b, k+p-i)`,
`α(k, j) = 2^{k-2j} (binom(k-j, j-1) + binom(k-j+1, j)) j!`,
`U(i, k) = min(⌈k/2⌉, 2k-i)`, `L(i, k) = max(0, i-k)`.

Source: Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*,
Journal of Integer Sequences 28 (2025), Article 25.8.6, Theorem 16 (`jis-2025-25.8.6-thm-16`). -/
public theorem_wanted sum_anassasBelow_eq_poly (m k : ℕ) :
    (∑ p ∈ range (k + 1), (anassasBelow m k p : ℚ)) =
      ∑ d ∈ range (2 * k + 1),
        (∑ i ∈ Icc d (2 * k), (-1) ^ (i - d) / (i.factorial : ℚ) * (Nat.stirlingFirst i d : ℚ) *
          ∑ j ∈ range (min ((k + 1) / 2) (2 * k - i) + 1),
            (2 : ℚ) ^ ((k : ℤ) - 2 * j) *
              ((if j = 0 then 0 else ((k - j).choose (j - 1) : ℚ)) + ((k - j + 1).choose j : ℚ)) *
              (j.factorial : ℚ) *
              ∑ p ∈ Icc (i - k) (k - j), (twoAssocStirlingSecond (p + k - j) p : ℚ) *
                ∑ b ∈ range (j + 1),
                  (p.choose b : ℚ) * (k.choose (j - b) : ℚ) * (b.choose (k + p - i) : ℚ)) *
          (m : ℚ) ^ d

end

end MetaMathlibExt

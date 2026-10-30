/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.PermutationStatistics
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import WantedExt.Combinatorics.Enumerative.OddFibonacciWanted

/-!
# Permutations avoiding two patterns of length three

The enumeration of `S_n(τ, ρ)` for pairs of length-`3` patterns (Simion and
Schmidt), as recalled in Han, *Joint Distributions of 10 Classical Statistics
over Permutations Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article
A18, Theorem 1. Patterns are permutations of `Fin 3` built from zero-based
one-line values by `pattern3` (e.g. `pattern3 ![0, 1, 2]` is `123`); containment is
the classical `HasPattern` of `OddFibonacciWanted`.

The joint distribution of the ten statistics `asc`, `des`, `lrmax`, `rlmax`, `lrmin`, `rlmin`,
`dasc`, `ddes`, `pk`, `vl` (Section 1 of the source) is the power series `classicalStatGF` over
`MvPolynomial (Fin 10) ℚ`; its rational closed forms (Theorems 2, 3, 5) are stated after clearing
denominators. Theorems 4 and 6 and Corollary 5 are false as printed and are not stated.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

@[expose] public section

/-- A length-`3` pattern from its zero-based one-line values, e.g.
`pattern3 ![0, 2, 1]` is the pattern `132`; bijectivity is checked by `decide`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
public def pattern3 (v : Fin 3 → Fin 3) (hv : Function.Bijective v := by decide) :
    Equiv.Perm (Fin 3) where
  toFun := v
  invFun := Fintype.bijInv hv
  left_inv := Fintype.leftInverse_bijInv hv
  right_inv := Fintype.rightInverse_bijInv hv

/-- Classical pattern containment `HasPattern σ π` is decidable.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
public instance {n k : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin k → Fin k) :
    Decidable (HasPattern σ π) := by
  unfold HasPattern
  infer_instance

/-- `A_n(τ, ρ)`: the number of permutations of length `n` avoiding both classical
patterns `τ` and `ρ` (containment is
`MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted.HasPattern`).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1. -/
public def twoPatternAvoiderCount (n : ℕ) (τ ρ : Equiv.Perm (Fin 3)) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ).card

/-- `A_3(123, 132) = 4`: of the six permutations of length `3`, only `123` and
`132` are excluded.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1. -/
public theorem twoPatternAvoiderCount_three_123_132 :
    twoPatternAvoiderCount 3 (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) = 4 := by
  decide +kernel

/-- `A_4(132, 321) = 7 = 1 + binom(4, 2)`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1. -/
public theorem twoPatternAvoiderCount_four_132_321 :
    twoPatternAvoiderCount 4 (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) = 7 := by
  decide +kernel

/-- Simion and Schmidt's enumeration, as recalled by the source, for `n ≥ 1`:
(a) `A_n(123,132) = A_n(123,213) = A_n(321,231) = A_n(321,312) = 2^{n-1}`;
(b) `A_n(231,312) = A_n(132,213) = 2^{n-1}`;
(c) `A_n(213,312) = A_n(132,231) = 2^{n-1}`;
(d) `A_n(213,231) = A_n(132,312) = 2^{n-1}`;
(e) `A_n(132,321) = A_n(123,231) = A_n(123,312) = A_n(213,321) = 1 + binom(n, 2)`;
(f) `A_n(123,321)` is `n` for `n ≤ 2`, `4` for `n = 3, 4`, and `0` for `n ≥ 5`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1
(`integers-2026-A18-thm-1`), citing Simion and Schmidt. -/
public theorem_wanted twoPatternAvoiderCount_length_three {n : ℕ} (hn : 1 ≤ n) :
    (twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![1, 0, 2]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![2, 1, 0]) (pattern3 ![1, 2, 0]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![2, 1, 0]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![1, 0, 2]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![1, 0, 2]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![1, 2, 0]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) = 1 + n.choose 2 ∧
      twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![1, 2, 0]) = 1 + n.choose 2 ∧
      twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![2, 0, 1]) = 1 + n.choose 2 ∧
      twoPatternAvoiderCount n (pattern3 ![1, 0, 2]) (pattern3 ![2, 1, 0]) = 1 + n.choose 2) ∧
    twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![2, 1, 0]) =
      if n ≤ 2 then n else if n ≤ 4 then 4 else 0

/-- `asc σ`: the number of ascents of `σ`, positions `i` with `i + 1 < n` and `σ i < σ (i + 1)`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public def permAscents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, σ i < σ ⟨i.val + 1, h⟩).card

/-- `des σ`: the number of descents of `σ`, positions `i` with `i + 1 < n` and
`σ (i + 1) < σ i`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public def permDescents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, σ ⟨i.val + 1, h⟩ < σ i).card

/-- The identity of length `3` (`123`) has two ascents and no descents; `132` has one of each.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public theorem permAscents_permDescents_small :
    permAscents (1 : Equiv.Perm (Fin 3)) = 2 ∧ permDescents (1 : Equiv.Perm (Fin 3)) = 0 ∧
      permAscents (pattern3 ![0, 2, 1]) = 1 ∧ permDescents (pattern3 ![0, 2, 1]) = 1 := by
  decide +kernel

/-- The joint generating function `∑_{n ≥ 0} ∑_{σ ∈ S_n(τ, ρ)} xⁿ p^{asc σ} q^{des σ}` in
`(MvPolynomial (Fin 2) ℚ)⟦x⟧`, with `p = X 0`, `q = X 1` (the empty permutation contributes `1`).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public noncomputable def ascDesGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 2) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permAscents σ * MvPolynomial.X 1 ^ permDescents σ

/-- Corollary 1, equation (5): over `S_n(123, 132)`,
`∑ xⁿ p^{asc} q^{des} = (1 + x - 2qx + px² - qx² - pqx² + q²x²) / (1 - 2qx - pqx² + q²x²)`,
stated after clearing the denominator. Only the `(asc, des)` identity of the corollary is
stated (its `(dasc, ddes)` and `(pk, vl)` identities use statistics defined in the paper body).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 1
(`integers-2026-A18-cor-1`). -/
public theorem_wanted ascDesGF_123_132 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - 2 * q * PowerSeries.X - p * q * PowerSeries.X ^ 2 + q ^ 2 * PowerSeries.X ^ 2) *
        ascDesGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) =
      1 + PowerSeries.X - 2 * q * PowerSeries.X + p * PowerSeries.X ^ 2 -
        q * PowerSeries.X ^ 2 - p * q * PowerSeries.X ^ 2 + q ^ 2 * PowerSeries.X ^ 2

/-- Corollary 2, equation (13): over `S_n(132, 321)`,
`∑ xⁿ p^{asc} q^{des} = (1 + x - 3px - 2px² + 3p²x² + qx² + p²x³ - p³x³) / (1 - px)³`, stated after
clearing the denominator; only the `(asc, des)` identity is stated.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 2
(`integers-2026-A18-cor-2`). -/
public theorem_wanted ascDesGF_132_321 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - p * PowerSeries.X) ^ 3 * ascDesGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) =
      1 + PowerSeries.X - 3 * p * PowerSeries.X - 2 * p * PowerSeries.X ^ 2 +
        3 * p ^ 2 * PowerSeries.X ^ 2 + q * PowerSeries.X ^ 2 + p ^ 2 * PowerSeries.X ^ 3 -
        p ^ 3 * PowerSeries.X ^ 3

/-- Corollary 4, equation (30): over `S_n(213, 231)`,
`∑ xⁿ p^{asc} q^{des} = (1 + x - px - qx) / (1 - px - qx)`, stated after clearing the
denominator; only the `(asc, des)` identity is stated. (The record's lead-in names
`S_n(213, 312)`, the sums `S_n(213, 231)`; both classes have this distribution.)

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 4
(`integers-2026-A18-cor-4`). -/
public theorem_wanted ascDesGF_213_231 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - p * PowerSeries.X - q * PowerSeries.X) *
        ascDesGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) =
      1 + PowerSeries.X - p * PowerSeries.X - q * PowerSeries.X

/-- The left-to-right and right-to-left extrema of `132` and `213`: `132` has
`lrmax = rlmax = rlmin = 2` and `lrmin = 1`; `213` has `lrmax = lrmin = rlmin = 2` and `rlmax = 1`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1
(`lrmax`, `rlmax`, `lrmin`, `rlmin`). -/
public theorem permExtrema_small :
    permLeftToRightMaxCount (pattern3 ![0, 2, 1]) = 2 ∧
      permRightToLeftMaxCount (pattern3 ![0, 2, 1]) = 2 ∧
      permLeftToRightMinCount (pattern3 ![0, 2, 1]) = 1 ∧
      permRightToLeftMinCount (pattern3 ![0, 2, 1]) = 2 ∧
      permLeftToRightMaxCount (pattern3 ![1, 0, 2]) = 2 ∧
      permRightToLeftMaxCount (pattern3 ![1, 0, 2]) = 1 ∧
      permLeftToRightMinCount (pattern3 ![1, 0, 2]) = 2 ∧
      permRightToLeftMinCount (pattern3 ![1, 0, 2]) = 2 := by
  decide +kernel

/-- Double ascents, double descents, peaks and valleys on length `3`: `123` has one double
ascent, `321` one double descent, `132` one peak and no valley, `213` one valley and no peak, and
`132` has no double ascent or double descent.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1
(`dasc`, `ddes`, `pk`, `vl`). -/
public theorem permDoubleAscents_peaks_small :
    permDoubleAscents (pattern3 ![0, 1, 2]) = 1 ∧
      permDoubleDescents (pattern3 ![2, 1, 0]) = 1 ∧
      permDoubleAscents (pattern3 ![0, 2, 1]) = 0 ∧
      permDoubleDescents (pattern3 ![0, 2, 1]) = 0 ∧
      permPeaks (pattern3 ![0, 2, 1]) = 1 ∧ permValleys (pattern3 ![0, 2, 1]) = 0 ∧
      permPeaks (pattern3 ![1, 0, 2]) = 0 ∧ permValleys (pattern3 ![1, 0, 2]) = 1 := by
  decide +kernel

/-- The joint generating function `F_(τ,ρ)(x, p, q, u, v, s, t, y, z, ℓ, m) = ∑_{n ≥ 0}
∑_{σ ∈ S_n(τ, ρ)} xⁿ p^{asc} q^{des} u^{lrmax} v^{rlmax} s^{lrmin} t^{rlmin} y^{dasc}
z^{ddes} ℓ^{pk} m^{vl}` in `(MvPolynomial (Fin 10) ℚ)⟦x⟧`, with `p, q, u, v, s, t, y, z, ℓ, m`
the variables `X 0, …, X 9` in that order (the empty permutation contributes `1`).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1
(the g.f. `F_(τ,ρ)`). -/
public noncomputable def classicalStatGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 10) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permAscents σ * MvPolynomial.X 1 ^ permDescents σ *
        MvPolynomial.X 2 ^ permLeftToRightMaxCount σ *
        MvPolynomial.X 3 ^ permRightToLeftMaxCount σ *
        MvPolynomial.X 4 ^ permLeftToRightMinCount σ *
        MvPolynomial.X 5 ^ permRightToLeftMinCount σ *
        MvPolynomial.X 6 ^ permDoubleAscents σ * MvPolynomial.X 7 ^ permDoubleDescents σ *
        MvPolynomial.X 8 ^ permPeaks σ * MvPolynomial.X 9 ^ permValleys σ

/-- The joint generating function `∑_{n ≥ 0} ∑_{σ ∈ S_n(τ, ρ)} xⁿ y^{dasc σ} z^{ddes σ}` in
`(MvPolynomial (Fin 2) ℚ)⟦x⟧`, with `y = X 0`, `z = X 1` (the empty permutation contributes `1`).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`, `ddes`). -/
public noncomputable def dascDdesGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 2) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permDoubleAscents σ * MvPolynomial.X 1 ^ permDoubleDescents σ

/-- Theorem 2, equation (1): over `S_n(123, 132)`, `F = A / (1 - ℓmpqsvx² - qsxz - qsvxz +
q²s²vx²z²)` with the paper's numerator `A`, stated after clearing the denominator.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 2
(`integers-2026-A18-thm-2`). -/
public theorem_wanted classicalStatGF_123_132 :
    let x : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.X
    let p : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    let u : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 2)
    let v : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 3)
    let s : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 4)
    let t : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 5)
    let y : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 6)
    let z : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 7)
    let ℓ : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 8)
    let m : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 9)
    (1 - ℓ * m * p * q * s * v * x ^ 2 - q * s * x * z - q * s * v * x * z + q ^ 2 * s ^ 2 * v *
        x ^ 2 * z ^ 2) *
        classicalStatGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) =
      1 + s * x * (t * u * v + p * t ^ 2 * u ^ 2 * v * x - q * (ℓ * m * p * v * x + z + v * z))
        + q ^ 2 * s ^ 3 * t * u * v ^ 2 * x ^ 3 * (ℓ * p * u * x * (m - z) + z * (-1 - m * p * t * u
        * x + z + p * t * u * x * z)) + q * s ^ 2 * v * x ^ 2 * (q * z ^ 2 + p * t ^ 2 * u * x * (m
        * (u + v) - u * (1 + v) * z) + t * u * (-z - v * (-1 + ℓ * p * (m - u) * x + z)))

set_option maxHeartbeats 400000 in
/-- Theorem 3, equation (8): over `S_n(132, 321)`, `F = A / ((1 - ptxy)(1 - puxy)(1 - ptuxy))`
with the paper's numerator `A` (expanded polynomial), stated after clearing the denominator.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 3
(`integers-2026-A18-thm-3`). -/
public theorem_wanted classicalStatGF_132_321 :
    let x : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.X
    let p : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    let u : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 2)
    let v : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 3)
    let s : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 4)
    let t : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 5)
    let y : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 6)
    let z : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 7)
    let ℓ : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 8)
    let m : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 9)
    ((1 - p * t * x * y) * (1 - p * u * x * y) * (1 - p * t * u * x * y)) *
        classicalStatGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) =
      1 + s * t * u * v * x + p * s * t ^ 2 * u ^ 2 * v * x ^ 2 + q * s ^ 2 * t * u * v ^ 2 * x ^ 2
        + m * p * q * s ^ 2 * t ^ 2 * u ^ 2 * v * x ^ 3 + m * p * q * s ^ 2 * t ^ 2 * u * v ^ 2 *
        x ^ 3 + ℓ * p * q * s ^ 2 * t * u ^ 2 * v ^ 2 * x ^ 3 + ℓ * m * p ^ 2 * q * s ^ 2 * t ^ 2 *
        u ^ 3 * v * x ^ 4 + ℓ * m * p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 2 * v ^ 2 * x ^ 4 - p * t * x *
        y - p * u * x * y - p * q * s ^ 2 * t * u ^ 2 * v ^ 2 * x ^ 3 * y - p * s * t ^ 2 * u * v *
        x ^ 2 * y - p * s * t * u ^ 2 * v * x ^ 2 * y - p * s * t ^ 2 * u ^ 2 * v * x ^ 2 * y
        - p ^ 2 * s * t ^ 3 * u ^ 2 * v * x ^ 3 * y - p ^ 2 * s * t ^ 2 * u ^ 3 * v * x ^ 3 * y - p
        * q * s ^ 2 * t ^ 2 * u * v ^ 2 * x ^ 3 * y - p * t * u * x * y - p * q * s ^ 2 * t ^ 2 *
        u ^ 2 * v ^ 2 * x ^ 3 * y - m * p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 3 * v * x ^ 4 * y - ℓ *
        p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 2 * v ^ 2 * x ^ 4 * y - m * p ^ 2 * q * s ^ 2 * t ^ 2 *
        u ^ 2 * v ^ 2 * x ^ 4 * y - m * p ^ 2 * q * s ^ 2 * t ^ 3 * u ^ 2 * v ^ 2 * x ^ 4 * y - ℓ *
        p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 3 * v ^ 2 * x ^ 4 * y - ℓ * m * p ^ 3 * q * s ^ 2 * t ^ 3 *
        u ^ 3 * v ^ 2 * x ^ 5 * y + p ^ 2 * t * u * x ^ 2 * y ^ 2 + p ^ 2 * t ^ 2 * u * x ^ 2 *
        y ^ 2 + p ^ 2 * t * u ^ 2 * x ^ 2 * y ^ 2 + p ^ 2 * s * t ^ 2 * u ^ 2 * v * x ^ 3 * y ^ 2
        + p ^ 2 * s * t ^ 3 * u ^ 2 * v * x ^ 3 * y ^ 2 + p ^ 2 * s * t ^ 2 * u ^ 3 * v * x ^ 3 *
        y ^ 2 + p ^ 3 * s * t ^ 3 * u ^ 3 * v * x ^ 4 * y ^ 2 + p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 2 *
        v ^ 2 * x ^ 4 * y ^ 2 + p ^ 2 * q * s ^ 2 * t ^ 3 * u ^ 2 * v ^ 2 * x ^ 4 * y ^ 2 + p ^ 2 *
        q * s ^ 2 * t ^ 2 * u ^ 3 * v ^ 2 * x ^ 4 * y ^ 2 + ℓ * p ^ 3 * q * s ^ 2 * t ^ 3 * u ^ 3 *
        v ^ 2 * x ^ 5 * y ^ 2 + m * p ^ 3 * q * s ^ 2 * t ^ 3 * u ^ 3 * v ^ 2 * x ^ 5 * y ^ 2
        - p ^ 3 * t ^ 2 * u ^ 2 * x ^ 3 * y ^ 3 - p ^ 3 * s * t ^ 3 * u ^ 3 * v * x ^ 4 * y ^ 3
        - p ^ 3 * q * s ^ 2 * t ^ 3 * u ^ 3 * v ^ 2 * x ^ 5 * y ^ 3

/-- Theorem 5, equation (25): over `S_n(213, 231)`, `F = A / B` with the paper's `A` and
`B = (1 - ptuxy)(1 - qsvxz)((1 - ptxy)(1 - qvxz) - ℓmpqtvx²)`, stated after clearing the
denominator.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 5
(`integers-2026-A18-thm-5`). -/
public theorem_wanted classicalStatGF_213_231 :
    let x : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.X
    let p : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    let u : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 2)
    let v : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 3)
    let s : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 4)
    let t : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 5)
    let y : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 6)
    let z : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 7)
    let ℓ : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 8)
    let m : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 9)
    ((1 - p * t * u * x * y) * (1 - q * s * v * x * z) * ((1 - p * t * x * y) * (1 - q * v * x * z)
        - ℓ * m * p * q * t * v * x ^ 2)) *
        classicalStatGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) =
      s * v * x * (q * z * (q * v * x * z - 1) + p ^ 2 * t ^ 3 * u ^ 2 * x ^ 2 * y * (ℓ * (m - 1) *
        q * v * x - (y - 1) * (q * v * x * z - 1)) + t * (u * (1 - q * v * x * z) * (1 + p * q * x *
        y * z) + p * q * x * z * (ℓ * m * q * v * x + y - q * v * x * y * z)) - p * t ^ 2 * u * x *
        (-ℓ * q * u * v * x - u * (y - 1) * (q * v * x * z - 1) + (1 + p * q * x * y * z) * (ℓ * m *
        q * v * x + y - q * v * x * y * z))) - q * s ^ 2 * t * u * v ^ 2 * x ^ 2 * (m * p * t * x *
        (p * t * u * x * y - 1) * (1 + (ℓ - 1) * q * v * x * z) - (p * t * x * y - 1) * ((1 - z) *
        (q * v * x * z - 1) + p * t * u * x * (z * (1 + ℓ * q * v * x - q * v * x * z) + y * (z - 1)
        * (q * v * x * z - 1)))) + (p * t * u * x * y - 1) * (ℓ * m * p * q * t * v * x ^ 2 - (1 - p
        * t * x * y) * (1 - q * v * x * z))

/-- Corollary 3, equation (23): over `S_n(231, 312)`,
`∑ xⁿ y^{dasc} z^{ddes} = (1 + x²(1 + x)(1 - y)(1 - z) + x(1 - y - z)) /
(1 - x(y + z) - x²(1 - yz))`,
stated after clearing the denominator. Only (23) is stated: the corollary's `(asc, des)` identity
(22) and `(pk, vl)` identity (24) are false as printed (at `p = 2`, `q = 1` the `x⁵` coefficient of
(22) is `75`, the true value `81`; at `ℓ = 2`, `m = 1` the `x⁵` coefficient of (24) is `28`, the
true value `29`).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 3
(`integers-2026-A18-cor-3`). -/
public theorem_wanted dascDdesGF_231_312 :
    let x : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.X
    let y : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let z : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - x * (y + z) - x ^ 2 * (1 - y * z)) *
        dascDdesGF (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1]) =
      1 + x ^ 2 * (1 + x) * (1 - y) * (1 - z) + x * (1 - y - z)

end

end MetaMathlibExt

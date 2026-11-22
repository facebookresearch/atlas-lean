/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Higher `a`-numbers in `ℤ_p`-towers via lattice points

The periodic-sum lemmas of Section 2.2 of Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran,
James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*,
INTEGERS 26 (2026), Article A78. Sequences are indexed by `i ≥ 1`; the value at `0` is never used.
The record's `f̄` (overline lost in extraction) is the average of `f` over one period; it is the
only value for which the identity holds at `N = L`.

The remaining statements follow the paper's Sections 2-4: base-`p` digits of rationals and their
periods (`basePDigit`, `basePPeriod`, `basePDelay`), the rounding indicator `δ` and its variant
`δ₀`, sums of floors and of `δ`, and the expansion of the higher `a`-numbers. Statements about
`a^r(X_n)` use the lattice-point expression of Theorem 1 (`higherANumberLatticeCount`). Statements
follow the arXiv text (arXiv:2407.13969v3); Theorem 4 follows the journal version.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- If `(f_i)_{i ≥ 1}` is periodic with period `L`, then for every `N ≥ 0`,
`∑_{i=1}^N f_i = N f̄ + ∑_{k=1}^{N mod L} (f_k - f̄)`, where `f̄ = (1/L) ∑_{k=1}^L f_k`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 1 (Sum of a periodic sequence) (`integers-2026-A78-lem-1`). -/
public theorem_wanted sum_Icc_of_periodic {K : Type*} [Field K] [CharZero K] (f : ℕ → K)
    {L : ℕ} (hL : 0 < L) (hf : ∀ i, 1 ≤ i → f (i + L) = f i) (N : ℕ) :
    ∑ i ∈ Icc 1 N, f i =
      N * ((∑ k ∈ Icc 1 L, f k) / L) +
        ∑ k ∈ Icc 1 (N % L), (f k - (∑ k ∈ Icc 1 L, f k) / L)

/-- If `(f_i)_{i ≥ 1}` is periodic for `i ≥ D` with period `L`, then for `N ≥ D - 1`,
`∑_{i=1}^N f_i = ∑_{i=1}^{D-1} f_i + (N - D + 1) f̄ + ∑_{k=1}^{(N-D+1) mod L} (f_{k+D-1} - f̄)`,
where `f̄ = (1/L) ∑_{k=D}^{D+L-1} f_k` is the average over one period. The delay satisfies
`D ≥ 1` since the sequence is indexed from `1`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 1 (Sum of an eventually periodic sequence) (`integers-2026-A78-cor-1`). -/
public theorem_wanted sum_Icc_of_eventually_periodic {K : Type*} [Field K] [CharZero K]
    (f : ℕ → K) {L D : ℕ} (hL : 0 < L) (hD : 1 ≤ D) (hf : ∀ i, D ≤ i → f (i + L) = f i)
    {N : ℕ} (hN : D - 1 ≤ N) :
    ∑ i ∈ Icc 1 N, f i =
      ∑ i ∈ Icc 1 (D - 1), f i + ((N + 1 - D : ℕ) : K) * ((∑ k ∈ Ico D (D + L), f k) / L) +
        ∑ k ∈ Icc 1 ((N + 1 - D) % L), (f (k + D - 1) - (∑ k ∈ Ico D (D + L), f k) / L)


/-- The `k`-th base-`p` digit `[p^k](x) ∈ {0, …, p - 1}` of a rational `x`, defined by
`[p^k](x) ≡ ⌊x / p^k⌋ (mod p)`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Section 2.2 (definition of `[p^k](x)`). -/
def basePDigit (p : ℕ) (x : ℚ) (k : ℤ) : ℤ := ⌊x / (p : ℚ) ^ k⌋ % p

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Section 2.2 (base-`5` example
`2/3 = .3131…`). -/
theorem basePDigit_five_two_thirds :
    basePDigit 5 (2 / 3) (-1) = 3 ∧ basePDigit 5 (2 / 3) (-2) = 1 ∧ basePDigit 5 (2 / 3) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [basePDigit, zpow_neg]

/-- The prime-to-`p` part `x_D` of the denominator of a rational `x`, so that
`x = p^{v_p(x)} x_N / x_D` with `x_N, x_D` coprime to `p` (Notation 2).

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_D`). -/
def primeToPDen (p : ℕ) (x : ℚ) : ℕ := x.den / p ^ padicValNat p x.den

/-- The prime-to-`p` part `x_N` of the numerator of a rational `x` (Notation 2).

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_N`). -/
def primeToPNum (p : ℕ) (x : ℚ) : ℕ := x.num.natAbs / p ^ padicValNat p x.num.natAbs

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_N`, `x_D` of `1`). -/
theorem primeToPDen_one_primeToPNum_one (p : ℕ) : primeToPDen p 1 = 1 ∧ primeToPNum p 1 = 1 := by
  simp [primeToPDen, primeToPNum]

/-- The period `L_x` of the repeating part of the base-`p` expansion of `x`, taken as the order
of `p` in `(ℤ/x_Dℤ)^×`; Lemma 2 (`basePDigit_eventually_periodic_iff`) identifies it with the
minimal period of the digit sequence.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `L_x` and Lemma 2. -/
noncomputable def basePPeriod (p : ℕ) (x : ℚ) : ℕ := orderOf (p : ZMod (primeToPDen p x))

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Lemma 2 (`L_x = 1` when `x_D = 1`). -/
theorem basePPeriod_one (p : ℕ) : basePPeriod p 1 = 1 := by
  rw [basePPeriod, (primeToPDen_one_primeToPNum_one p).1]
  exact orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)

/-- The delay `D_x = -v_p(x)` of the base-`p` expansion of `x`; Lemma 2
(`basePDigit_eventually_periodic_iff`) identifies it with the minimal delay.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `D_x` and Lemma 2. -/
noncomputable def basePDelay (p : ℕ) (x : ℚ) : ℤ := -padicValRat p x

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Lemma 2 (`D_{1/p} = 1`). -/
theorem basePDelay_inv_self (p : ℕ) [Fact p.Prime] : basePDelay p (p : ℚ)⁻¹ = 1 := by
  simp [basePDelay, padicValRat.inv]

/-- The average value `x̄` of the repeating digits of the base-`p` expansion of `x`, i.e.
`(1/L_x) ∑_{k=D_x+1}^{D_x+L_x} [p^{-k}](x)`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `x̄`. -/
noncomputable def basePDigitAverage (p : ℕ) (x : ℚ) : ℚ :=
  (∑ k ∈ Icc (basePDelay p x + 1) (basePDelay p x + basePPeriod p x), (basePDigit p x (-k) : ℚ)) /
    basePPeriod p x

/-- `τ = (p + 1)/d`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (i). -/
def towerTau (p d : ℕ) : ℚ := ((p : ℚ) + 1) / d

/-- `γ = ((p - 1) r + (p + 1))/d`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (ii). -/
def towerGamma (p d r : ℕ) : ℚ := (((p : ℚ) - 1) * r + (p + 1)) / d

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (`p = 5`, `d = 4`,
`r = 2`). -/
theorem towerTau_towerGamma_five_four : towerTau 5 4 = 3 / 2 ∧ towerGamma 5 4 2 = 7 / 2 := by
  constructor <;> norm_num [towerTau, towerGamma]

/-- The lexicographic order on integer sequences used in Definition 1: `a > b` when they agree
below some index `m` and `a m > b m`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Equation (1). -/
def SeqLexGt (a b : ℕ → ℤ) : Prop := ∃ m, (∀ j < m, a j = b j) ∧ b m < a m

/-- The indicator `δ(i)`: `0` if the integer-part digits `([p^n](τ i))_{n ≥ 0}` are
lexicographically larger than the fractional digits `([p^{-1-n}](τ i))_{n ≥ 0}`, and `1`
otherwise, with `τ = (p + 1)/d`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `δ`. -/
noncomputable def higherANumberDelta (p d i : ℕ) : ℕ :=
  open Classical in
  if SeqLexGt (fun n => basePDigit p (towerTau p d * i) n)
      (fun n => basePDigit p (towerTau p d * i) (-1 - n)) then 0 else 1

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Table 1 (`δ(1) = 1`, `δ(2) = 0` for
`p = 5`, `d = 4`). -/
theorem higherANumberDelta_five_four :
    higherANumberDelta 5 4 1 = 1 ∧ higherANumberDelta 5 4 2 = 0 := by
  constructor
  · unfold higherANumberDelta
    split_ifs with h
    · obtain ⟨m, hm, hlt⟩ := h
      rcases m with _ | m
      · norm_num [basePDigit, towerTau, zpow_neg] at hlt
      · have := hm 0 (by omega)
        norm_num [basePDigit, towerTau, zpow_neg] at this
    · rfl
  · unfold higherANumberDelta
    split_ifs with h
    · rfl
    · exact absurd ⟨0, by simp, by norm_num [basePDigit, towerTau, zpow_neg]⟩ h

/-- The denominator `τ_D` of `τ = (p + 1)/d` in lowest terms.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Notation 2 (`τ_D`). -/
def tauDen (p d : ℕ) : ℕ := (towerTau p d).den

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Notation 2 (`τ_D = 1` when `d = 1`). -/
theorem tauDen_one (p : ℕ) : tauDen p 1 = 1 := by
  simp only [tauDen, towerTau, Nat.cast_one, div_one]
  exact_mod_cast Rat.den_natCast (p + 1)

/-- The variant `δ₀(i)`: `0` if `p ∣ i`, and `δ(i)` otherwise.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition of `δ₀`. -/
noncomputable def higherANumberDeltaZero (p d i : ℕ) : ℕ :=
  if p ∣ i then 0 else higherANumberDelta p d i

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition of `δ₀` (`δ₀(0) = 0`). -/
theorem higherANumberDeltaZero_zero (p d : ℕ) : higherANumberDeltaZero p d 0 = 0 := by
  simp [higherANumberDeltaZero]

/-- The lattice boundary `μ(i)`: `⌊τ i⌋` if the integer-part digits of `τ i` are
lexicographically larger than its fractional digits, and `⌈τ i⌉` otherwise.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 1 (`μ`). -/
noncomputable def towerMu (p d i : ℕ) : ℤ :=
  open Classical in
  if SeqLexGt (fun n => basePDigit p (towerTau p d * i) n)
      (fun n => basePDigit p (towerTau p d * i) (-1 - n)) then ⌊towerTau p d * i⌋
  else ⌈towerTau p d * i⌉

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 1 (`μ(2) = 3` for `p = 5`, `d = 4`, where `τ · 2 = 3`). -/
theorem towerMu_five_four_two : towerMu 5 4 2 = 3 := by
  unfold towerMu
  split_ifs <;> norm_num [towerTau]

/-- The lattice-point expression `r (p - 1) t_n (t_n + 1)/(2d) + #Δ_n` of Theorem 1, where
`t_n = ⌊γ^-1 p^n⌋` and `Δ_n = {(i, j) ∈ ℤ_{>0}² : i > t_n, μ(i) ≤ j ≤ p^n - 1}`. Theorem 1
(Booher, Cais, Kramer-Miller, Upton) identifies it with the higher `a`-number `a^r(X_n)` of a
`ℤ_p`-tower with minimal break ratios and ramification invariant `d ∣ p - 1`. First coordinates
are taken in `[1, p^n]`, which loses nothing since `μ(i) ≥ ⌊τ i⌋ ≥ i` for `τ > 1`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 2 and Theorem 1. -/
noncomputable def higherANumberLatticeCount (p d r n : ℕ) : ℚ :=
  (r : ℚ) * ((p : ℚ) - 1) * ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ *
      (⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ + 1) / (2 * d) +
    (((Icc 1 (p ^ n) ×ˢ Icc 1 (p ^ n - 1)).filter fun ij : ℕ × ℕ =>
        ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ < ij.1 ∧ towerMu p d ij.1 ≤ ij.2).card : ℚ)

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 2 (`n = 0`, `p = 3`, `d = 2`, `r = 1`: no lattice points). -/
theorem higherANumberLatticeCount_three_two_one_zero : higherANumberLatticeCount 3 2 1 0 = 0 := by
  have h0 : ⌊(1 : ℚ) / 3⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  have h1 : Icc 1 (3 ^ 0 - 1) = (∅ : Finset ℕ) := by decide
  norm_num [higherANumberLatticeCount, towerGamma]
  rw [h0, h1]
  simp

/-- The periodic correction `A_{x^{-1}}(n)` of Proposition 4:
`½ (-(1 - 1/x_D) + x (1 - {x^{-1} p^n})) {x^{-1} p^n} +
∑_{k=1}^{⌊x^{-1} p^n⌋ mod x_D} ({x k} - ½ (1 - 1/x_D))`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 4 (`A_{x^{-1}}`). -/
noncomputable def floorSumCorrection (p : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  1 / 2 * (-(1 - 1 / (primeToPDen p x : ℚ)) + x * (1 - Int.fract ((p : ℚ) ^ n / x))) *
      Int.fract ((p : ℚ) ^ n / x) +
    ∑ k ∈ Icc 1 (⌊(p : ℚ) ^ n / x⌋₊ % primeToPDen p x),
      (Int.fract (x * k) - 1 / 2 * (1 - 1 / (primeToPDen p x : ℚ)))

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 4 (`A_1 = 0`). -/
theorem floorSumCorrection_one (p n : ℕ) : floorSumCorrection p 1 n = 0 := by
  have h := (primeToPDen_one_primeToPNum_one p).1
  simp only [floorSumCorrection, h]
  simp only [div_one, Nat.cast_one, one_mul, sub_self, neg_zero, zero_add]
  have hf : Int.fract ((p : ℚ) ^ n) = 0 := by exact_mod_cast Int.fract_natCast (p ^ n)
  have hm : ⌊(p : ℚ) ^ n⌋₊ % 1 = 0 := Nat.mod_one _
  simp [hf, hm]

/-- The correction `F_y(e) = ∑_{k=1}^{⌊y p^e⌋ mod τ_D p} (δ₀(k) - ½ (1 - 1/p)(1 - 1/τ_D))` of
Lemma 9, written with `y = x^{-1}` as in the paper's `F_{x^{-1}}`.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 9 (`F_{x^{-1}}`). -/
noncomputable def deltaZeroSumCorrection (p d : ℕ) (y : ℚ) (e : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 (⌊y * (p : ℚ) ^ e⌋₊ % (tauDen p d * p)),
    ((higherANumberDeltaZero p d k : ℚ) - 1 / 2 * (1 - 1 / (p : ℚ)) * (1 - 1 / (tauDen p d : ℚ)))

/-- Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 9 (`F_0 = 0`). -/
theorem deltaZeroSumCorrection_zero (p d e : ℕ) : deltaZeroSumCorrection p d 0 e = 0 := by
  simp [deltaZeroSumCorrection]

/-- For every positive integer `m`, the base-`p` expansion of `m/d` is periodic with period `1`
right after the radix point: `[p^{-(k+1)}](m/d) = [p^{-k}](m/d)` for all `k ≥ 1`. The paper's
odd prime `p` is relaxed to any prime (for `p = 2` only `d = 1` occurs).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 2 (`integers-2026-A78-cor-2`). -/
public theorem_wanted basePDigit_div_periodic_one (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (m : ℕ) (hm : 0 < m) (k : ℤ) (hk : 1 ≤ k) :
    basePDigit p ((m : ℚ) / d) (-(k + 1)) = basePDigit p ((m : ℚ) / d) (-k)

/-- For a positive rational `x`, the digit sequence `k ↦ [p^{-k}](x)` is periodic with period
`L > 0` for all `k ≥ D + 1` exactly when the order `L_x` of `p` in `(ℤ/x_Dℤ)^×` divides `L` and
`D ≥ -v_p(x)`; that is, `L_x` is the minimal period and `-v_p(x)` the minimal delay. Indices
`k` and `D` range over `ℤ` (for `v_p(x) > 0` the delay is negative).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 2 (`integers-2026-A78-lem-2`). -/
public theorem_wanted basePDigit_eventually_periodic_iff (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : 0 < x) (D : ℤ) {L : ℕ} (hL : 0 < L) :
    (∀ k : ℤ, D + 1 ≤ k → basePDigit p x (-(k + L)) = basePDigit p x (-k)) ↔
      basePPeriod p x ∣ L ∧ basePDelay p x ≤ D

/-- For `τ = (p + 1)/d` with `d ∣ p - 1`, `[p^{-1}](τ i) = [p^0](τ i)` if and only if `p ∣ i`.
The paper's positivity of `i` is dropped (the claim holds at `i = 0`) and `p` is any prime.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 3 (`integers-2026-A78-lem-3`). -/
public theorem_wanted basePDigit_towerTau_neg_one_eq_zero_iff (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (i : ℕ) :
    basePDigit p (towerTau p d * i) (-1) = basePDigit p (towerTau p d * i) 0 ↔ p ∣ i

/-- If `p ∤ i`, then `[p^{-1}](τ i) > [p^0](τ i)` if and only if `δ(i) = 1`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 4 (`integers-2026-A78-lem-4`). -/
public theorem_wanted higherANumberDelta_eq_one_iff (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {i : ℕ} (hi : ¬ p ∣ i) :
    basePDigit p (towerTau p d * i) 0 < basePDigit p (towerTau p d * i) (-1) ↔
      higherANumberDelta p d i = 1

/-- For `0 ≤ i < τ_D p` with `p ∤ i`: (i) if `τ_D ∤ i` then `δ(i) + δ(τ_D p - i) = 1`; (ii) if
`τ_D ∣ i` then `δ(i) = δ(τ_D p - i) = 0`. For `0 ≤ j < d` with `p ∤ j`: (iii) if `τ_D ∤ j` then
`δ(j) + δ(d - j) = 1`; (iv) if `τ_D ∣ j` then `δ(j) = 0`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 1 (`integers-2026-A78-prop-1`). -/
public theorem_wanted higherANumberDelta_reflection (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) :
    (∀ i < tauDen p d * p, ¬ p ∣ i → ¬ tauDen p d ∣ i →
        higherANumberDelta p d i + higherANumberDelta p d (tauDen p d * p - i) = 1) ∧
      (∀ i < tauDen p d * p, ¬ p ∣ i → tauDen p d ∣ i →
        higherANumberDelta p d i = 0 ∧ higherANumberDelta p d (tauDen p d * p - i) = 0) ∧
      (∀ j < d, ¬ p ∣ j → ¬ tauDen p d ∣ j →
        higherANumberDelta p d j + higherANumberDelta p d (d - j) = 1) ∧
      (∀ j < d, ¬ p ∣ j → tauDen p d ∣ j → higherANumberDelta p d j = 0)

/-- (i) `δ(p^n i) = δ(i)`; (ii) `δ₀(i) = δ₀(i + τ_D p)`; (iii) if `τ_D ∤ i` and `p ∤ i` then
`δ₀(i) + δ₀(τ_D p - i) = 1`; (iv) if `τ_D ∣ i` or `p ∣ i` then `δ₀(i) = δ₀(τ_D p - i) = 0`.
Parts (iii) and (iv) assume `i ≤ τ_D p`, so that `τ_D p - i` is the natural number the paper
means; the paper's positivity of `i` and `n` is dropped (the claims hold at `0`).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Theorem 3 (`integers-2026-A78-thm-3`). -/
public theorem_wanted higherANumberDelta_periodicity (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) :
    (∀ i n : ℕ, higherANumberDelta p d (p ^ n * i) = higherANumberDelta p d i) ∧
      (∀ i : ℕ, higherANumberDeltaZero p d i = higherANumberDeltaZero p d (i + tauDen p d * p)) ∧
      (∀ i ≤ tauDen p d * p, ¬ tauDen p d ∣ i → ¬ p ∣ i →
        higherANumberDeltaZero p d i + higherANumberDeltaZero p d (tauDen p d * p - i) = 1) ∧
      (∀ i ≤ tauDen p d * p, (tauDen p d ∣ i ∨ p ∣ i) →
        higherANumberDeltaZero p d i = 0 ∧ higherANumberDeltaZero p d (tauDen p d * p - i) = 0)

/-- The average of `δ₀` over its period `τ_D p` is `½ (1 - 1/p)(1 - 1/τ_D)`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 2 (`integers-2026-A78-prop-2`). -/
public theorem_wanted higherANumberDeltaZero_average (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) :
    (∑ i ∈ Icc 1 (tauDen p d * p), (higherANumberDeltaZero p d i : ℚ)) / (tauDen p d * p) =
      1 / 2 * (1 - 1 / (p : ℚ)) * (1 - 1 / (tauDen p d : ℚ))

/-- For positive rational `x`, `{x p^n}` is periodic in `n ≥ D_x` with period `L_x`, and its
average over one period is `x̄/(p - 1)`. Here `n ∈ ℤ` (the delay `D_x = -v_p(x)` can be negative),
`L_x`, `D_x` are as identified by Lemma 2, and the average is taken over `n ∈ [D_x, D_x + L_x)`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 6 (`integers-2026-A78-lem-6`). -/
public theorem_wanted fract_mul_pow_periodic (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) :
    (∀ n : ℤ, basePDelay p x ≤ n →
        Int.fract (x * (p : ℚ) ^ (n + basePPeriod p x)) = Int.fract (x * (p : ℚ) ^ n)) ∧
      (∑ n ∈ Ico (basePDelay p x) (basePDelay p x + basePPeriod p x), Int.fract (x * (p : ℚ) ^ n)) /
          basePPeriod p x = basePDigitAverage p x / ((p : ℚ) - 1)

/-- For positive rational `x`: (i) `⌊x p^n⌋ ≡ ⌊x p^{n+L_x}⌋ (mod x_N)` for `n ≥ D_x`, and
(ii) `⌊x p^n⌋ ≡ ⌊x p^{n+L_x}⌋ (mod p)` for `n ≥ D_x + 1`, with `n ∈ ℤ`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 7 (`integers-2026-A78-lem-7`). -/
public theorem_wanted floor_mul_pow_modEq (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) :
    (∀ n : ℤ, basePDelay p x ≤ n →
        ⌊x * (p : ℚ) ^ n⌋ ≡ ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ [ZMOD primeToPNum p x]) ∧
      (∀ n : ℤ, basePDelay p x + 1 ≤ n →
        ⌊x * (p : ℚ) ^ n⌋ ≡ ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ [ZMOD p])

/-- For rational `x ≥ 1`,
`∑_{i=1}^{⌊x^{-1} p^n⌋} δ(i) = ∑_{e=0}^n ∑_{1 ≤ i ≤ ⌊x^{-1} p^e⌋, p ∤ i} δ(i) =
∑_{e=0}^n ∑_{i=1}^{⌊x^{-1} p^e⌋} δ₀(i)`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 8 (`integers-2026-A78-lem-8`). -/
public theorem_wanted sum_higherANumberDelta_by_exponent (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, higherANumberDelta p d i =
        ∑ e ∈ range (n + 1), ∑ i ∈ (Icc 1 ⌊(p : ℚ) ^ e / x⌋₊).filter (fun i => ¬ p ∣ i),
          higherANumberDelta p d i ∧
      ∑ e ∈ range (n + 1), ∑ i ∈ (Icc 1 ⌊(p : ℚ) ^ e / x⌋₊).filter (fun i => ¬ p ∣ i),
          higherANumberDelta p d i =
        ∑ e ∈ range (n + 1), ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ e / x⌋₊, higherANumberDeltaZero p d i

/-- For positive rational `x` with `v_p(x) ≥ 0`,
`∑_{i=1}^{⌊x^{-1} p^n⌋} (p^n - ⌊x i⌋) = ½ x^{-1} p^{2n} + ½ (x^{-1} (1 - 1/x_D) - 1) p^n +
A_{x^{-1}}(n)`, and `A_{x^{-1}}(n)` is periodic for `n ≥ D_{x^{-1}}` with period
`L_{x^{-1}}`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 4 (`integers-2026-A78-prop-4`). -/
public theorem_wanted sum_pow_sub_floor (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x)
    (hv : 0 ≤ padicValRat p x) :
    (∀ n : ℕ, ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, ((p : ℚ) ^ n - ⌊x * i⌋) =
        1 / 2 * x⁻¹ * (p : ℚ) ^ (2 * n) +
          1 / 2 * (x⁻¹ * (1 - 1 / (primeToPDen p x : ℚ)) - 1) * (p : ℚ) ^ n +
          floorSumCorrection p x n) ∧
      ∀ n : ℕ, basePDelay p x⁻¹ ≤ n →
        floorSumCorrection p x (n + basePPeriod p x⁻¹) = floorSumCorrection p x n

/-- With `τ = (p + 1)/d` and `γ = ((p - 1) r + (p + 1))/d`,
`∑_{i=1}^{⌊τ^{-1} p^n⌋} (p^n - ⌊τ i⌋) - ∑_{i=1}^{⌊γ^{-1} p^n⌋} (p^n - ⌊γ i⌋) =
½ (τ^{-1} - γ^{-1}) p^{2n} + ½ (τ^{-1} - γ^{-1})(1 - 1/τ_D) p^n +
(A_{τ^{-1}}(n) - A_{γ^{-1}}(n))`. Any prime `p` and any `r ≥ 0` are admitted.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 3 (`integers-2026-A78-cor-3`). -/
public theorem_wanted sum_floor_difference (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) (r n : ℕ) :
    ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerTau p d⌋₊, ((p : ℚ) ^ n - ⌊towerTau p d * i⌋) -
        ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊, ((p : ℚ) ^ n - ⌊towerGamma p d r * i⌋) =
      1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n) +
        1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (1 - 1 / (tauDen p d : ℚ)) *
          (p : ℚ) ^ n +
        (floorSumCorrection p (towerTau p d) n - floorSumCorrection p (towerGamma p d r) n)

/-- The higher `a`-number, in the lattice-point form of Theorem 1 (`higherANumberLatticeCount`),
equals `∑_{i=1}^{t_n} (γ - τ) i + ∑_{i=t_n+1}^{⌊τ^{-1} p^n⌋} (p^n - ⌊τ i⌋) -
∑_{i=t_n+1}^{⌊τ^{-1} p^n⌋} δ(i)` and also
`(∑_{i=1}^{⌊τ^{-1} p^n⌋} (p^n - ⌊τ i⌋) - ∑_{i=1}^{⌊γ^{-1} p^n⌋} (p^n - ⌊γ i⌋)) -
(∑_{i=1}^{⌊τ^{-1} p^n⌋} δ(i) - ∑_{i=1}^{⌊γ^{-1} p^n⌋} δ(i))`, where
`t_n = ⌊γ^{-1} p^n⌋`. The paper states this for `a^r(X_n)`; here `a^r(X_n)` is replaced by the
Theorem 1 expression, and all `n ≥ 0`, `r ≥ 0` and primes `p` are admitted.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 3 (`integers-2026-A78-prop-3`). -/
public theorem_wanted higherANumberLatticeCount_eq_sums (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (r n : ℕ) :
    higherANumberLatticeCount p d r n =
        ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊, (towerGamma p d r - towerTau p d) * i +
          ∑ i ∈ Ioc ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ ⌊(p : ℚ) ^ n / towerTau p d⌋₊,
            ((p : ℚ) ^ n - ⌊towerTau p d * i⌋) -
          ∑ i ∈ Ioc ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ ⌊(p : ℚ) ^ n / towerTau p d⌋₊,
            (higherANumberDelta p d i : ℚ) ∧
      higherANumberLatticeCount p d r n =
        (∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerTau p d⌋₊, ((p : ℚ) ^ n - ⌊towerTau p d * i⌋) -
            ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊,
              ((p : ℚ) ^ n - ⌊towerGamma p d r * i⌋)) -
          (∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerTau p d⌋₊, (higherANumberDelta p d i : ℚ) -
            ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊, (higherANumberDelta p d i : ℚ))

/-- For rational `x ≥ 1`,
`∑_{i=1}^{⌊x^{-1} p^n⌋} δ(i) = ½ (1 - 1/τ_D)(p^n - 1/p) x^{-1} -
½ (1 - 1/p)(1 - 1/τ_D) ∑_{e=0}^n {x^{-1} p^e} + ∑_{e=0}^n F_{x^{-1}}(e)`. The paper's
positivity of `n` is dropped (the identity holds at `n = 0`).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 4 (`integers-2026-A78-cor-4`). -/
public theorem_wanted sum_higherANumberDelta_eq (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, (higherANumberDelta p d i : ℚ) =
      1 / 2 * (1 - 1 / (tauDen p d : ℚ)) * ((p : ℚ) ^ n - 1 / p) * x⁻¹ -
        1 / 2 * (1 - 1 / (p : ℚ)) * (1 - 1 / (tauDen p d : ℚ)) *
          ∑ e ∈ range (n + 1), Int.fract (x⁻¹ * (p : ℚ) ^ e) +
        ∑ e ∈ range (n + 1), deltaZeroSumCorrection p d x⁻¹ e

/-- Suppose `x_D = τ_D`. Then `F_{x^{-1}}(e)` is periodic for `e ≥ D_{x^{-1}} + 1` with period
`L_{x^{-1}}`, and for `n ≥ D_{x^{-1}}`,
`∑_{i=1}^{⌊x^{-1} p^n⌋} δ(i) = ½ x^{-1} (1 - 1/τ_D) p^n +
(F̄_{x^{-1}} - x̄^{-1}/(2p) (1 - 1/τ_D)) n + B_{x^{-1}}(n)` for a function `B_{x^{-1}}` periodic
for `n ≥ D_{x^{-1}}` with period `L_{x^{-1}}`. `F̄` is the average of `F` over `L_{x^{-1}}`
consecutive indices from `max(D_{x^{-1}} + 1, 0)`; the paper's explicit `B` (Equation (6)) is
replaced by an existential.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 5 (`integers-2026-A78-prop-5`). -/
public theorem_wanted sum_higherANumberDelta_periodic (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {x : ℚ} (hx : 0 < x) (hxD : primeToPDen p x = tauDen p d) :
    (∀ e : ℕ, basePDelay p x⁻¹ + 1 ≤ e →
        deltaZeroSumCorrection p d x⁻¹ (e + basePPeriod p x⁻¹) =
          deltaZeroSumCorrection p d x⁻¹ e) ∧
      ∃ B : ℕ → ℚ, (∀ n : ℕ, basePDelay p x⁻¹ ≤ n → B (n + basePPeriod p x⁻¹) = B n) ∧
        ∀ n : ℕ, basePDelay p x⁻¹ ≤ n →
          ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, (higherANumberDelta p d i : ℚ) =
            1 / 2 * x⁻¹ * (1 - 1 / (tauDen p d : ℚ)) * (p : ℚ) ^ n +
              ((∑ e ∈ Ico (basePDelay p x⁻¹ + 1).toNat
                    ((basePDelay p x⁻¹ + 1).toNat + basePPeriod p x⁻¹),
                    deltaZeroSumCorrection p d x⁻¹ e) / basePPeriod p x⁻¹ -
                basePDigitAverage p x⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ))) * n +
              B n

/-- The coefficient of `n` in Proposition 5 vanishes for `x = τ`:
`F̄_{τ^{-1}} - τ̄^{-1}/(2p) (1 - 1/τ_D) = 0`, with `F̄_{τ^{-1}}` the average of
`F_{τ^{-1}}(e)` over `1 ≤ e ≤ L_{τ^{-1}}` (the delay `D_{τ^{-1}}` is `0`).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 6 (`integers-2026-A78-prop-6`). -/
public theorem_wanted deltaZeroSumCorrection_average_towerTau (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) :
    (∑ e ∈ Icc 1 (basePPeriod p (towerTau p d)⁻¹),
          deltaZeroSumCorrection p d (towerTau p d)⁻¹ e) / basePPeriod p (towerTau p d)⁻¹ -
        basePDigitAverage p (towerTau p d)⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ)) = 0

/-- `∑_{i=⌊γ^{-1} p^n⌋+1}^{⌊τ^{-1} p^n⌋} δ(i) = ½ (τ^{-1} - γ^{-1})(1 - 1/τ_D) p^n +
(γ̄^{-1}/(2p) (1 - 1/τ_D) - F̄_{γ^{-1}}) n + C(n)` with `C = B_{τ^{-1}} - B_{γ^{-1}}`
periodic for `n ≥ D_{γ^{-1}}` with period `lcm(L_{τ^{-1}}, L_{γ^{-1}})`; the paper's explicit
`B` functions are replaced by this existential, and `F̄_{γ^{-1}}` is averaged as in
Proposition 5.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 5 (`integers-2026-A78-cor-5`). -/
public theorem_wanted sum_higherANumberDelta_difference (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (r : ℕ) (hr : 0 < r) :
    ∃ C : ℕ → ℚ,
      (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        C (n + Nat.lcm (basePPeriod p (towerTau p d)⁻¹) (basePPeriod p (towerGamma p d r)⁻¹)) =
          C n) ∧
      ∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        ∑ i ∈ Ioc ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ ⌊(p : ℚ) ^ n / towerTau p d⌋₊,
            (higherANumberDelta p d i : ℚ) =
          1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (1 - 1 / (tauDen p d : ℚ)) *
              (p : ℚ) ^ n +
            (basePDigitAverage p (towerGamma p d r)⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ)) -
              (∑ e ∈ Ico (basePDelay p (towerGamma p d r)⁻¹ + 1).toNat
                    ((basePDelay p (towerGamma p d r)⁻¹ + 1).toNat +
                      basePPeriod p (towerGamma p d r)⁻¹),
                  deltaZeroSumCorrection p d (towerGamma p d r)⁻¹ e) /
                basePPeriod p (towerGamma p d r)⁻¹) * n +
            C n

/-- Main theorem: for `d ∣ p - 1` and `r ≥ 1` there are a positive integer `N_r`, a rational
`λ_r` and a function `ν_r` such that for `n ≥ N_r`,
`a^r(X_n) = r/(r + (p+1)/(p-1)) · d/(2(p+1)) · p^{2n} + λ_r n + ν_r(n)`, and the minimal period
of `ν_r` divides `lcm(2, ord_{D_r} p)`, where `D_r` is the prime-to-`p` part of the denominator
of `d/(r(p-1) + (p+1))`. Stated as `ν_r(n + lcm(2, ord_{D_r} p)) = ν_r(n)` for `n ≥ N_r`, with
`a^r(X_n)` replaced by the Theorem 1 lattice expression (`higherANumberLatticeCount`).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Theorem 2 (`integers-2026-A78-thm-2`). -/
public theorem_wanted higherANumberLatticeCount_asymptotic (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (r : ℕ) (hr : 0 < r) :
    ∃ N : ℕ, 0 < N ∧ ∃ lam : ℚ, ∃ ν : ℕ → ℚ,
      (∀ n ≥ N, ν (n + Nat.lcm 2
          (orderOf (p : ZMod (primeToPDen p ((d : ℚ) / (((p : ℚ) - 1) * r + (p + 1))))))) = ν n) ∧
      ∀ n ≥ N, higherANumberLatticeCount p d r n =
        r / (r + ((p : ℚ) + 1) / ((p : ℚ) - 1)) * (d / (2 * ((p : ℚ) + 1))) * (p : ℚ) ^ (2 * n) +
          lam * n + ν n

/-- **Theorem 4.** For `d ∣ p - 1` and `r ≥ 1` there is `ν_r : ℕ → ℚ` with
`a^r(X_n) = ½ (τ^{-1} - γ^{-1}) p^{2n} + λ_r n + ν_r(n)`, where
`λ_r = F̄_{γ^{-1}} - γ̄^{-1}/(2p) (1 - 1/τ_D)`, and `ν_r` is periodic for `n ≥ D_{γ^{-1}}` with
minimal period `lcm(L_{γ^{-1}}, 2)` or `½ lcm(L_{γ^{-1}}, 2)`. Stated with `a^r(X_n)` replaced by
the Theorem 1 lattice expression (`higherANumberLatticeCount`); `F̄_{γ^{-1}}` is averaged as in
Proposition 5; the minimal-period claim is stated as: `lcm(L_{γ^{-1}}, 2)` is a period from
`D_{γ^{-1}}` on, and every period `L'` from `D_{γ^{-1}}` on has `lcm(L_{γ^{-1}}, 2) ∣ 2 L'`.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Theorem 4 (`integers-2026-A78-thm-4`). -/
public theorem_wanted higherANumberLatticeCount_eq_explicit_linear_add_periodic (p d : ℕ)
    [Fact p.Prime] (hd : d ∣ p - 1) (r : ℕ) (hr : 0 < r) :
    ∃ ν : ℕ → ℚ,
      (∀ n : ℕ, higherANumberLatticeCount p d r n =
        1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n) +
          ((∑ e ∈ Ico (basePDelay p (towerGamma p d r)⁻¹ + 1).toNat
                  ((basePDelay p (towerGamma p d r)⁻¹ + 1).toNat +
                    basePPeriod p (towerGamma p d r)⁻¹),
                deltaZeroSumCorrection p d (towerGamma p d r)⁻¹ e) /
              basePPeriod p (towerGamma p d r)⁻¹ -
            basePDigitAverage p (towerGamma p d r)⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ))) * n +
          ν n) ∧
      (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        ν (n + Nat.lcm (basePPeriod p (towerGamma p d r)⁻¹) 2) = ν n) ∧
      ∀ L' : ℕ, 0 < L' → (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n → ν (n + L') = ν n) →
        Nat.lcm (basePPeriod p (towerGamma p d r)⁻¹) 2 ∣ 2 * L'

/-- When `d = 1` or `d = 2`: (i) `λ_r = 0`, and (ii) the minimal period of `a^r(X_n)` is
`L_{γ^{-1}}` if that is odd, and `L_{γ^{-1}}` or `L_{γ^{-1}}/2` if it is even. Stated with
`a^r(X_n)` replaced by the Theorem 1 lattice expression: the remainder
`ν(n) = a^r(X_n) - ½ (τ^{-1} - γ^{-1}) p^{2n}` (no linear term, which is (i)) is periodic for
`n ≥ D_{γ^{-1}}` with period `L_{γ^{-1}}`, and every eventual period `L'` of it satisfies
`L_{γ^{-1}} ∣ 2 L'` (together, (ii)).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 6 (`integers-2026-A78-cor-6`). -/
public theorem_wanted higherANumberLatticeCount_period_small_d (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (hd12 : d = 1 ∨ d = 2) (r : ℕ) (hr : 0 < r) :
    (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        higherANumberLatticeCount p d r (n + basePPeriod p (towerGamma p d r)⁻¹) -
            1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) *
              (p : ℚ) ^ (2 * (n + basePPeriod p (towerGamma p d r)⁻¹)) =
          higherANumberLatticeCount p d r n -
            1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n)) ∧
      ∀ L' N : ℕ, 0 < L' → (∀ n ≥ N,
          higherANumberLatticeCount p d r (n + L') -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * (n + L')) =
            higherANumberLatticeCount p d r n -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n)) →
        basePPeriod p (towerGamma p d r)⁻¹ ∣ 2 * L'

/-- When `r = p + 1`: `λ_r = 0`, the minimal period is `1`, and
`ν_r(n) = ½ (p - 1)(τ^{-1} - 1)` for `n ≥ 1`; that is,
`a^r(X_n) = ½ (τ^{-1} - γ^{-1}) p^{2n} + ½ (p - 1)(τ^{-1} - 1)` for `n ≥ 1`, with `a^r(X_n)`
replaced by the Theorem 1 lattice expression.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 7 (`integers-2026-A78-cor-7`). -/
public theorem_wanted higherANumberLatticeCount_r_eq_succ (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (n : ℕ) (hn : 1 ≤ n) :
    higherANumberLatticeCount p d (p + 1) n =
      1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d (p + 1))⁻¹) * (p : ℚ) ^ (2 * n) +
        1 / 2 * ((p : ℚ) - 1) * ((towerTau p d)⁻¹ - 1)

/-- `λ_r · L` is an integer: whenever `a^r(X_n) = ½ (τ^{-1} - γ^{-1}) p^{2n} + λ n + ν(n)` for
`n ≥ N` with `ν` periodic of period `L > 0` there, `λ L ∈ ℤ`. Stated for every period `L` (the
minimal one included), with `a^r(X_n)` replaced by the Theorem 1 lattice expression.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 8 (`integers-2026-A78-cor-8`). -/
public theorem_wanted higherANumberLatticeCount_linear_coeff_mul_period (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (r : ℕ) (hr : 0 < r) (lam : ℚ) (ν : ℕ → ℚ) (N L : ℕ) (hL : 0 < L)
    (hν : ∀ n ≥ N, ν (n + L) = ν n)
    (hexp : ∀ n ≥ N, higherANumberLatticeCount p d r n =
      1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n) + lam * n + ν n) :
    ∃ z : ℤ, lam * L = z

/-- For `r₁ = (r₀ + 1) p + 1`, the linear coefficients agree (`λ₁ = λ₀`) and the delays satisfy
`D_{γ₁^{-1}} = D_{γ₀^{-1}} + 1`. The first part is stated as: every `λ` for which
`a^{r₀}(X_n) - ½ (τ^{-1} - γ₀^{-1}) p^{2n} - λ n` is eventually periodic also works for `r₁`,
with `a^r(X_n)` replaced by the Theorem 1 lattice expression.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 7 (`integers-2026-A78-prop-7`). -/
public theorem_wanted higherANumberLatticeCount_shift (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (r₀ : ℕ) :
    (∀ lam : ℚ,
        (∃ N L : ℕ, 0 < L ∧ ∀ n ≥ N,
          higherANumberLatticeCount p d r₀ (n + L) -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r₀)⁻¹) * (p : ℚ) ^ (2 * (n + L)) -
              lam * (n + L : ℕ) =
            higherANumberLatticeCount p d r₀ n -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r₀)⁻¹) * (p : ℚ) ^ (2 * n) - lam * n) →
        ∃ N L : ℕ, 0 < L ∧ ∀ n ≥ N,
          higherANumberLatticeCount p d ((r₀ + 1) * p + 1) (n + L) -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d ((r₀ + 1) * p + 1))⁻¹) *
                (p : ℚ) ^ (2 * (n + L)) - lam * (n + L : ℕ) =
            higherANumberLatticeCount p d ((r₀ + 1) * p + 1) n -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d ((r₀ + 1) * p + 1))⁻¹) *
                (p : ℚ) ^ (2 * n) - lam * n) ∧
      basePDelay p (towerGamma p d ((r₀ + 1) * p + 1))⁻¹ = basePDelay p (towerGamma p d r₀)⁻¹ + 1

end

end MetaMathlibExt

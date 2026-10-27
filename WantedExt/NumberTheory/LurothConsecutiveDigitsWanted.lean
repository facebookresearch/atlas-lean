/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Functions of consecutive digits in Lüroth series

Statements from Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67.

The first Lüroth digit of `x ∈ (0, 1]` is `d₁(x) = ⌊1 / x⌋ + 1 ≥ 2` and the Lüroth map is
`L(x) = d₁(x) (d₁(x) - 1) x - (d₁(x) - 1)` (with `L(0) = 0`, which the formula gives in
Lean since `1 / 0 = 0`); the `n`-th digit is `d_n(x) = d₁(L^{n-1}(x))`. In Lean the digits
are indexed from `0`: `lurothDigitSeq x k = d_{k+1}(x)`. Sequences `Ψ` are indexed from `0`
as well; the paper's sums over `n ≥ 1` and "infinitely many `n`" are shift-invariant.

Theorems 1 and 2 are quoted in the paper from its references [3] and [2]. Not stated (see
the source audit table): the endpoint formula of Proposition 1 (the paper's `⟨c₁, …, cₙ⟩` is
not defined in the extracted text).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MetaMathlibExt

@[expose] public section

/-- The first Lüroth digit `d₁(x) = ⌊1 / x⌋ + 1`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2. -/
noncomputable def lurothDigit (x : ℝ) : ℕ :=
  ⌊1 / x⌋₊ + 1

/-- The Lüroth map `L(x) = d₁(x) (d₁(x) - 1) x - (d₁(x) - 1)`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2. -/
noncomputable def lurothMap (x : ℝ) : ℝ :=
  (lurothDigit x : ℝ) * ((lurothDigit x : ℝ) - 1) * x - ((lurothDigit x : ℝ) - 1)

/-- The Lüroth digits of `x`, indexed from `0`: `lurothDigitSeq x k = d₁(L^k(x))`, the
paper's `d_{k+1}(x)`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2. -/
noncomputable def lurothDigitSeq (x : ℝ) (k : ℕ) : ℕ :=
  lurothDigit (lurothMap^[k] x)

/-- `d₁(1) = 2`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `d₁`). -/
theorem lurothDigit_one : lurothDigit 1 = 2 := by
  simp [lurothDigit]

/-- `d₁(1/2) = 3`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `d₁`). -/
theorem lurothDigit_half : lurothDigit (1 / 2) = 3 := by
  norm_num [lurothDigit]

/-- `L(1) = 1`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `L`). -/
theorem lurothMap_one : lurothMap 1 = 1 := by
  norm_num [lurothMap, lurothDigit_one]

/-- `L(1/2) = 1`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `L`). -/
theorem lurothMap_half : lurothMap (1 / 2) = 1 := by
  norm_num [lurothMap, lurothDigit_half]

/-- `L(0) = 0`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `L`). -/
theorem lurothMap_zero : lurothMap 0 = 0 := by
  simp [lurothMap, lurothDigit]

/-- The digits of `L(x)` are the digits of `x` shifted by one: `d_{k+1}(L x) = d_{k+2}(x)`.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `d_n`). -/
theorem lurothDigitSeq_succ (x : ℝ) (k : ℕ) :
    lurothDigitSeq x (k + 1) = lurothDigitSeq (lurothMap x) k := by
  simp [lurothDigitSeq, Function.iterate_succ_apply]

/-- The Lüroth cylinder `I_n(c) = {x ∈ (0, 1] : d_j(x) = c_j, 1 ≤ j ≤ n}` has Lebesgue
measure `∏ 1 / (c_j (c_j - 1))`. Stated for every `c`; when some `c_j < 2` both sides
vanish.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Proposition 1,
(10) (`integers-2024-A67-prop-1`). -/
public theorem_wanted volume_lurothCylinder {n : ℕ} (c : Fin n → ℕ) :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      ∏ j, ENNReal.ofReal (1 / ((c j : ℝ) * ((c j : ℝ) - 1)))

/-- Lüroth analogue of the Borel-Bernstein theorem: for positive `Ψ`, the set of `x ∈ (0, 1]`
with `d_n(x) ≥ Ψ(n)` for infinitely many `n` has Lebesgue measure `0` if `∑ Ψ(n)⁻¹ < ∞` and
`1` if `∑ Ψ(n)⁻¹ = ∞` (convergence of a positive series as `Summable`). Quoted in the paper
from Jager and de Vroedt (its reference [3]).

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 1 (`integers-2024-A67-thm-1`). -/
public theorem_wanted volume_lurothDigit_ge_zero_one (Ψ : ℕ → ℝ) (hΨ : ∀ n, 0 < Ψ n) :
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 | ∃ᶠ n in atTop, Ψ n ≤ lurothDigitSeq x n}
    (Summable (fun n => (Ψ n)⁻¹) → volume E = 0) ∧
      (¬ Summable (fun n => (Ψ n)⁻¹) → volume E = 1)

/-- Weighted products of consecutive Lüroth digits: for `m ≥ 1`, weights `t_i > 0`,
`T = max t_i`, `ℓ(t) = #{j : t_j = T}` and positive `Ψ` with `liminf Ψ(n) > 1` (written as
`Ψ(n) ≥ c` eventually for some `c > 1`), the set of `x ∈ (0, 1]` with
`∏ d_{n+i}(x)^{t_i} ≥ Ψ(n)` for infinitely many `n` has Lebesgue measure `0` if
`∑ (log Ψ(n))^{ℓ(t)-1} / Ψ(n)^{1/T} < ∞` and `1` if that series diverges (convergence as
`Summable`). Quoted in the paper from Brown-Sarre, Robert and Hussain (its reference [2]).

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 2, with `T` and `ℓ(t)` from (2) (`integers-2024-A67-thm-2`). -/
public theorem_wanted volume_lurothWeightedProduct_ge_zero_one {m : ℕ} (hm : 0 < m)
    (t : Fin m → ℝ) (ht : ∀ i, 0 < t i) (Ψ : ℕ → ℝ) (hΨ : ∀ n, 0 < Ψ n)
    (hlim : ∃ c : ℝ, 1 < c ∧ ∀ᶠ n in atTop, c ≤ Ψ n) :
    let T := ⨆ i, t i
    let ℓ := (Finset.univ.filter fun j => t j = T).card
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ ∏ i : Fin m, (lurothDigitSeq x (n + i) : ℝ) ^ t i}
    (Summable (fun n => Real.log (Ψ n) ^ (ℓ - 1) / Ψ n ^ (1 / T)) → volume E = 0) ∧
      (¬ Summable (fun n => Real.log (Ψ n) ^ (ℓ - 1) / Ψ n ^ (1 / T)) → volume E = 1)

/-- Zero-one law for a function of `m` consecutive Lüroth digits: with
`H(y) = ∑_{d ∈ D^m, F(d) ≥ y} ∏ 1 / (d_i (d_i - 1))` (`D = ℕ_{≥ 2}`), the set of
`x ∈ (0, 1]` with `F(d_n(x), …, d_{n+m-1}(x)) ≥ Ψ(n)` for infinitely many `n` has measure
`0` if `∑ H(Ψ(n)) < ∞` and `1` if `∑ H(Ψ(n)) = ∞`. The paper's positivity of `F` and `Ψ`
is not needed and is dropped.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 3, with
`H` from (4) (`integers-2024-A67-thm-3`). -/
public theorem_wanted volume_lurothConsecutiveDigits_zero_one {m : ℕ}
    (F : (Fin m → ℕ) → ℝ) (Ψ : ℕ → ℝ) :
    let H : ℝ → ℝ≥0∞ := fun y => ∑' d : Fin m → ℕ,
      if (∀ i, 2 ≤ d i) ∧ y ≤ F d then ∏ i, ENNReal.ofReal (1 / ((d i : ℝ) * ((d i : ℝ) - 1)))
      else 0
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ F (fun i => lurothDigitSeq x (n + i))}
    (∑' n, H (Ψ n) < ∞ → volume E = 0) ∧ (∑' n, H (Ψ n) = ∞ → volume E = 1)

/-- Integral form of the zero-one law: let `F` be positive, measurable and non-decreasing
on `[2, ∞)^m` with `F(x) ≤ M F(⌊x⌋)` there (condition (6)), and
`G(y) = ∫_{x_i ≥ 2, F(x) ≥ y} ∏ 1 / x_i²`. The set of `x ∈ (0, 1]` with
`F(d_n(x), …, d_{n+m-1}(x)) ≥ Ψ(n)` for infinitely many `n` has measure `0` if
`∑ G(Ψ(n)) < ∞` and `1` if `∑ G(M Ψ(n)) = ∞`. Here `M` is any constant satisfying (6)
(the paper takes the supremum; a larger `M` only weakens the divergence condition). The
paper's positivity of `Ψ` is dropped.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 4, with (6)
and `G` from (7) (`integers-2024-A67-thm-4`). -/
public theorem_wanted volume_lurothConsecutiveDigits_zero_one_integral {m : ℕ}
    (F : (Fin m → ℝ) → ℝ) (hFm : Measurable F)
    (hpos : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → 0 < F x)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (M : ℝ)
    (hM : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → F x ≤ M * F (fun i => (⌊x i⌋₊ : ℝ)))
    (Ψ : ℕ → ℝ) :
    let G : ℝ → ℝ≥0∞ := fun y =>
      ∫⁻ x in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x}, ENNReal.ofReal (∏ i, 1 / x i ^ 2)
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ F (fun i => (lurothDigitSeq x (n + i) : ℝ))}
    (∑' n, G (Ψ n) < ∞ → volume E = 0) ∧ (∑' n, G (M * Ψ n) = ∞ → volume E = 1)

/-- Borel–Cantelli dichotomy for the Lüroth map: if each `A_n` is a union of cylinders of
level `m`, i.e. `A_n = {x ∈ (0, 1] : (d_1(x), …, d_m(x)) ∈ S_n}`, then
`λ(limsup L^{-n} A_n)` is `0` if `∑ λ(A_n) < ∞` and `1` if `∑ λ(A_n) = ∞`
(`x ∈ L^{-n} A_n` means `(d_{n+1}(x), …, d_{n+m}(x)) ∈ S_n`).

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 5
(`integers-2024-A67-thm-5`). -/
public theorem_wanted volume_limsup_lurothPreimage_zero_one {m : ℕ}
    (S : ℕ → Set (Fin m → ℕ)) :
    let A : ℕ → Set ℝ := fun n =>
      {x ∈ Set.Ioc (0 : ℝ) 1 | (fun i : Fin m => lurothDigitSeq x i) ∈ S n}
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, (fun i : Fin m => lurothDigitSeq x (n + i)) ∈ S n}
    (∑' n, volume (A n) < ∞ → volume E = 0) ∧ (∑' n, volume (A n) = ∞ → volume E = 1)

/-- Upper bound: for `F` non-decreasing on `[2, ∞)^m` and every real `y`,
`λ{x ∈ (0, 1] : F(d_1(x), …, d_m(x)) ≥ y} ≤ 3^m G(y)` with `G` as in (7). The paper
states it for `y = Ψ(n)` under the hypotheses of Theorem 4; only monotonicity is used.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 6
(`integers-2024-A67-thm-6`). -/
public theorem_wanted volume_lurothDigits_ge_le {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (y : ℝ) :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))} ≤
      3 ^ m * ∫⁻ x in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x},
        ENNReal.ofReal (∏ i, 1 / x i ^ 2)

/-- Lower bound: for `F` positive on `[2, ∞)^m` with `F(x) ≤ M F(⌊x⌋)` there (condition
(6)) and every real `y`, `G(M y) ≤ λ{x ∈ (0, 1] : F(d_1(x), …, d_m(x)) ≥ y}` with `G` as in
(7). The paper states it for `y = Ψ(n)` under the hypotheses of Theorem 4.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 7
(`integers-2024-A67-thm-7`). -/
public theorem_wanted le_volume_lurothDigits_ge {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hpos : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → 0 < F x) (M : ℝ)
    (hM : ∀ x : Fin m → ℝ, (∀ i, 2 ≤ x i) → F x ≤ M * F (fun i => (⌊x i⌋₊ : ℝ))) (y : ℝ) :
    (∫⁻ x in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ M * y ≤ F x},
        ENNReal.ofReal (∏ i, 1 / x i ^ 2)) ≤
      volume {x ∈ Set.Ioc (0 : ℝ) 1 | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))}

end

end MetaMathlibExt

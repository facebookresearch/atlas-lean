/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Quadratic Gauss sum modulo five

For an integer `k`, the quadratic Gauss sum `g(k; 5)` is the finite sum
`∑_{n=0}^{4} exp (2 * π * I * k * n ^ 2 / 5)`.

Provenance: Greg Dresden and Yike Li, "Periodic Weighted Sums of Binomial
Coefficients," Journal of Integer Sequences 26 (2023), source TeX
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Dresden/dresden26.tex>,
lines 284–291, which defines `g(k; 5)` as above and records the evaluation
`g(k; 5) = (k / 5) * √5` for `k` not a multiple of five. That evaluation is
classical; the JIS source cites Berndt, Evans, and Williams, Theorem 1.5.2,
and this module makes no claim that the JIS authors originated it.
-/

@[expose] public section

namespace MetaMathlibExt

/-- Primality of `5` for the Legendre-symbol API. Scoped (not global), so
importers only see it under `open scoped MetaMathlibExt`. -/
scoped instance : Fact (Nat.Prime 5) := ⟨by decide⟩

open scoped MetaMathlibExt

/-- **Quadratic Gauss sum modulo $5$.** For an integer $k$, the quadratic Gauss sum $g(k; 5)$ is
the complex number $g(k; 5) = \sum_{n=0}^{4} e^{2\pi i k n^2 / 5}$. -/
public noncomputable def quadraticGaussSum5 (k : ℤ) : ℂ :=
  Finset.sum (Finset.range 5) (fun n =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (n : ℂ) ^ 2 / 5))

private lemma exp_two : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
  have harg :
      2 * (Real.pi : ℂ) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    simp
  rw [harg, Complex.exp_ofReal_mul_I, Real.cos_two_pi, Real.sin_two_pi]
  simp

private lemma exp_nat (m : ℕ) :
    Complex.exp (((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  induction m with
  | zero =>
    have h0 : (((0 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 0 := by
      simp
    rw [h0, Complex.exp_zero]
  | succ n ih =>
    have hsucc :
        (((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
          (((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            (2 * (Real.pi : ℂ) * Complex.I) := by
      simp
      ring
    rw [hsucc, Complex.exp_add, ih, exp_two, mul_one]

private lemma exp_neg_nat (m : ℕ) :
    Complex.exp (-(((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
  have hpos :
      Complex.exp (((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    exp_nat m
  have hadd :
      (-(((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) +
        ((((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 0 := by
    ring
  have hmul :
      Complex.exp (-(((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) *
        Complex.exp (((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [←Complex.exp_add, hadd, Complex.exp_zero]
  rw [hpos, mul_one] at hmul
  exact hmul

private lemma add_five (a : ℤ) :
    quadraticGaussSum5 (a + 5) = quadraticGaussSum5 a := by
  unfold quadraticGaussSum5
  apply Finset.sum_congr rfl
  intro n hn
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((a + 5 : ℤ) : ℂ) * (n : ℂ) ^ 2 / 5 =
        2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (n : ℂ) ^ 2 / 5 +
          (n : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp
    ring
  have hexp :
      Complex.exp ((n : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    have h :
        Complex.exp (((n ^ 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
      exp_nat (n ^ 2)
    simpa [Nat.cast_pow] using h
  rw [harg, Complex.exp_add, hexp, mul_one]

private lemma sub_five (a : ℤ) :
    quadraticGaussSum5 (a - 5) = quadraticGaussSum5 a := by
  unfold quadraticGaussSum5
  apply Finset.sum_congr rfl
  intro n hn
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((a - 5 : ℤ) : ℂ) * (n : ℂ) ^ 2 / 5 =
        2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (n : ℂ) ^ 2 / 5 +
          (-((n : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * Complex.I))) := by
    simp
    ring
  have hexp :
      Complex.exp (-((n : ℂ) ^ 2 * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
    have h :
        Complex.exp (-(((n ^ 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 :=
      exp_neg_nat (n ^ 2)
    simpa [Nat.cast_pow] using h
  rw [harg, Complex.exp_add, hexp, mul_one]

private lemma nat_add_lemma (r : ℤ) (m : ℕ) :
    quadraticGaussSum5 (r + 5 * (m : ℤ)) = quadraticGaussSum5 r := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : r + 5 * (((n + 1 : ℕ) : ℤ)) = (r + 5 * (n : ℤ)) + 5 := by
      simp
      ring
    rw [h, add_five, ih]

private lemma nat_sub_lemma (r : ℤ) (m : ℕ) :
    quadraticGaussSum5 (r - 5 * (m : ℤ)) = quadraticGaussSum5 r := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : r - 5 * (((n + 1 : ℕ) : ℤ)) = (r - 5 * (n : ℤ)) - 5 := by
      simp
      ring
    rw [h, sub_five, ih]

private lemma gauss_period_int (r q : ℤ) :
    quadraticGaussSum5 (r + 5 * q) = quadraticGaussSum5 r := by
  cases q with
  | ofNat n =>
    have heq : Int.ofNat n = ((n : ℕ) : ℤ) := rfl
    rw [heq]
    exact nat_add_lemma r n
  | negSucc n =>
    have heq : Int.negSucc n = -(((n + 1 : ℕ) : ℤ)) := rfl
    rw [heq]
    have harg : r + 5 * (-(((n + 1 : ℕ) : ℤ))) = r - 5 * ((n + 1 : ℕ) : ℤ) := by
      ring
    rw [harg]
    exact nat_sub_lemma r (n + 1)

private noncomputable def gaussFifthRoot (r : ℕ) : ℂ :=
  Complex.exp (((r : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5))

private lemma term_nat (k n : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) : ℂ) * (n : ℂ) ^ 2 / 5) =
      gaussFifthRoot ((k * n ^ 2) % 5) := by
  have h1 : ((k : ℕ) : ℂ) * (n : ℂ) ^ 2 = ((k * n ^ 2 : ℕ) : ℂ) := by
    rw [←Nat.cast_pow, ←Nat.cast_mul]
  have hdiv : 5 * ((k * n ^ 2) / 5) + (k * n ^ 2) % 5 = k * n ^ 2 :=
    Nat.div_add_mod (k * n ^ 2) 5
  have h2 :
      ((k * n ^ 2 : ℕ) : ℂ) =
        5 * (((k * n ^ 2) / 5 : ℕ) : ℂ) + (((k * n ^ 2) % 5 : ℕ) : ℂ) := by
    have hcast := congrArg (fun m : ℕ => (m : ℂ)) hdiv
    simpa [Nat.cast_add, Nat.cast_mul] using hcast.symm
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) : ℂ) * (n : ℂ) ^ 2 / 5 =
        (((k * n ^ 2) % 5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) +
          (((k * n ^ 2) / 5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    calc 2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) : ℂ) * (n : ℂ) ^ 2 / 5 =
        2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * (n : ℂ) ^ 2) / 5 := by ring
      _ = 2 * (Real.pi : ℂ) * Complex.I * ((k * n ^ 2 : ℕ) : ℂ) / 5 := by rw [h1]
      _ = 2 * (Real.pi : ℂ) * Complex.I *
          (5 * (((k * n ^ 2) / 5 : ℕ) : ℂ) + (((k * n ^ 2) % 5 : ℕ) : ℂ)) / 5 := by
          rw [h2]
      _ = (((k * n ^ 2) % 5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) +
          (((k * n ^ 2) / 5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  have hexp :
      Complex.exp ((((k * n ^ 2) / 5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    exp_nat ((k * n ^ 2) / 5)
  unfold gaussFifthRoot
  rw [harg, Complex.exp_add, hexp, mul_one]

private lemma hc1 : 1 + 4 * Real.cos (2 * Real.pi / 5) = Real.sqrt 5 := by
  have hcos5 := Real.cos_pi_div_five
  have hdouble :
      Real.cos (2 * (Real.pi / 5)) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 :=
    Real.cos_two_mul (Real.pi / 5)
  have h2pi : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h2pi, hdouble, hcos5]
  ring_nf
  rw [hsq]
  ring

private lemma hc2 : 1 + 4 * Real.cos (4 * Real.pi / 5) = -Real.sqrt 5 := by
  have hcos5 := Real.cos_pi_div_five
  have h4pi : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by ring
  have hcos4 :
      Real.cos (4 * Real.pi / 5) = -Real.cos (Real.pi / 5) := by
    rw [h4pi, Real.cos_sub, Real.cos_pi, Real.sin_pi]
    simp
  rw [hcos4, hcos5]
  ring

private lemma hcos84 :
    Real.cos (8 * Real.pi / 5) = Real.cos (2 * Real.pi / 5) := by
  have h : 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by ring
  rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  simp

private lemma hsin84 :
    Real.sin (8 * Real.pi / 5) = -Real.sin (2 * Real.pi / 5) := by
  have h : 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by ring
  rw [h, Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi]
  simp

private lemma hcos63 :
    Real.cos (6 * Real.pi / 5) = Real.cos (4 * Real.pi / 5) := by
  have h : 6 * Real.pi / 5 = 2 * Real.pi - 4 * Real.pi / 5 := by ring
  rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  simp

private lemma hsin63 :
    Real.sin (6 * Real.pi / 5) = -Real.sin (4 * Real.pi / 5) := by
  have h : 6 * Real.pi / 5 = 2 * Real.pi - 4 * Real.pi / 5 := by ring
  rw [h, Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi]
  simp

private lemma E0 : gaussFifthRoot 0 = 1 := by
  unfold gaussFifthRoot
  simp [Complex.exp_zero]

private lemma E1 :
    gaussFifthRoot 1 =
      ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) +
        ((Real.sin (2 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
  have harg :
      ((1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) =
        ((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    simp
    ring
  unfold gaussFifthRoot
  rw [harg, Complex.exp_ofReal_mul_I]

private lemma E2 :
    gaussFifthRoot 2 =
      ((Real.cos (4 * Real.pi / 5) : ℝ) : ℂ) +
        ((Real.sin (4 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
  have harg :
      ((2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) =
        ((4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    simp
    ring
  unfold gaussFifthRoot
  rw [harg, Complex.exp_ofReal_mul_I]

private lemma E3 :
    gaussFifthRoot 3 =
      ((Real.cos (6 * Real.pi / 5) : ℝ) : ℂ) +
        ((Real.sin (6 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
  have harg :
      ((3 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) =
        ((6 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    simp
    ring
  unfold gaussFifthRoot
  rw [harg, Complex.exp_ofReal_mul_I]

private lemma E4 :
    gaussFifthRoot 4 =
      ((Real.cos (8 * Real.pi / 5) : ℝ) : ℂ) +
        ((Real.sin (8 * Real.pi / 5) : ℝ) : ℂ) * Complex.I := by
  have harg :
      ((4 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) =
        ((8 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    simp
    ring
  unfold gaussFifthRoot
  rw [harg, Complex.exp_ofReal_mul_I]

private lemma E14 :
    gaussFifthRoot 1 + gaussFifthRoot 4 =
      2 * ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) := by
  rw [E1, E4, hcos84, hsin84]
  simp
  ring

private lemma E23 :
    gaussFifthRoot 2 + gaussFifthRoot 3 =
      2 * ((Real.cos (4 * Real.pi / 5) : ℝ) : ℂ) := by
  rw [E2, E3, hcos63, hsin63]
  simp
  ring

private lemma S1E :
    ((((gaussFifthRoot 0 + gaussFifthRoot 1) + gaussFifthRoot 4) +
      gaussFifthRoot 4) + gaussFifthRoot 1) =
      ((Real.sqrt 5 : ℝ) : ℂ) := by
  have h1 :
      ((((gaussFifthRoot 0 + gaussFifthRoot 1) + gaussFifthRoot 4) +
        gaussFifthRoot 4) + gaussFifthRoot 1) =
        (1 : ℂ) + 4 * ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) := by
    calc ((((gaussFifthRoot 0 + gaussFifthRoot 1) + gaussFifthRoot 4) +
        gaussFifthRoot 4) + gaussFifthRoot 1) =
        gaussFifthRoot 0 + 2 * (gaussFifthRoot 1 + gaussFifthRoot 4) := by ring
      _ = (1 : ℂ) + 2 * (2 * ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ)) := by
          rw [E0, E14]
      _ = (1 : ℂ) + 4 * ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) := by ring
  calc ((((gaussFifthRoot 0 + gaussFifthRoot 1) + gaussFifthRoot 4) +
      gaussFifthRoot 4) + gaussFifthRoot 1) =
      (1 : ℂ) + 4 * ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) := h1
    _ = ((1 + 4 * Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) := by simp
    _ = ((Real.sqrt 5 : ℝ) : ℂ) := by rw [hc1]

private lemma S2E :
    ((((gaussFifthRoot 0 + gaussFifthRoot 2) + gaussFifthRoot 3) +
      gaussFifthRoot 3) + gaussFifthRoot 2) =
      -((Real.sqrt 5 : ℝ) : ℂ) := by
  have h1 :
      ((((gaussFifthRoot 0 + gaussFifthRoot 2) + gaussFifthRoot 3) +
        gaussFifthRoot 3) + gaussFifthRoot 2) =
        (1 : ℂ) + 4 * ((Real.cos (4 * Real.pi / 5) : ℝ) : ℂ) := by
    calc ((((gaussFifthRoot 0 + gaussFifthRoot 2) + gaussFifthRoot 3) +
        gaussFifthRoot 3) + gaussFifthRoot 2) =
        gaussFifthRoot 0 + 2 * (gaussFifthRoot 2 + gaussFifthRoot 3) := by ring
      _ = (1 : ℂ) + 2 * (2 * ((Real.cos (4 * Real.pi / 5) : ℝ) : ℂ)) := by
          rw [E0, E23]
      _ = (1 : ℂ) + 4 * ((Real.cos (4 * Real.pi / 5) : ℝ) : ℂ) := by ring
  calc ((((gaussFifthRoot 0 + gaussFifthRoot 2) + gaussFifthRoot 3) +
      gaussFifthRoot 3) + gaussFifthRoot 2) =
      (1 : ℂ) + 4 * ((Real.cos (4 * Real.pi / 5) : ℝ) : ℂ) := h1
    _ = ((1 + 4 * Real.cos (4 * Real.pi / 5) : ℝ) : ℂ) := by simp
    _ = -((Real.sqrt 5 : ℝ) : ℂ) := by
      rw [hc2]
      simp

private lemma sum1 : quadraticGaussSum5 1 = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have t0 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) *
        ((0 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 0 := by
    have h := term_nat 1 0
    have hm : (1 * 0 ^ 2) % 5 = 0 := by decide
    rw [hm] at h
    simpa using h
  have t1 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) *
        ((1 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 1 := by
    have h := term_nat 1 1
    have hm : (1 * 1 ^ 2) % 5 = 1 := by decide
    rw [hm] at h
    simpa using h
  have t2 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) *
        ((2 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 4 := by
    have h := term_nat 1 2
    have hm : (1 * 2 ^ 2) % 5 = 4 := by decide
    rw [hm] at h
    simpa using h
  have t3 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) *
        ((3 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 4 := by
    have h := term_nat 1 3
    have hm : (1 * 3 ^ 2) % 5 = 4 := by decide
    rw [hm] at h
    simpa using h
  have t4 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) *
        ((4 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 1 := by
    have h := term_nat 1 4
    have hm : (1 * 4 ^ 2) % 5 = 1 := by decide
    rw [hm] at h
    simpa using h
  unfold quadraticGaussSum5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [t0, t1, t2, t3, t4]
  exact S1E

private lemma sum2 : quadraticGaussSum5 2 = -((Real.sqrt 5 : ℝ) : ℂ) := by
  have t0 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) *
        ((0 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 0 := by
    have h := term_nat 2 0
    have hm : (2 * 0 ^ 2) % 5 = 0 := by decide
    rw [hm] at h
    simpa using h
  have t1 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) *
        ((1 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 2 := by
    have h := term_nat 2 1
    have hm : (2 * 1 ^ 2) % 5 = 2 := by decide
    rw [hm] at h
    simpa using h
  have t2 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) *
        ((2 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 3 := by
    have h := term_nat 2 2
    have hm : (2 * 2 ^ 2) % 5 = 3 := by decide
    rw [hm] at h
    simpa using h
  have t3 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) *
        ((3 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 3 := by
    have h := term_nat 2 3
    have hm : (2 * 3 ^ 2) % 5 = 3 := by decide
    rw [hm] at h
    simpa using h
  have t4 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) *
        ((4 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 2 := by
    have h := term_nat 2 4
    have hm : (2 * 4 ^ 2) % 5 = 2 := by decide
    rw [hm] at h
    simpa using h
  unfold quadraticGaussSum5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [t0, t1, t2, t3, t4]
  exact S2E

private lemma sum3 : quadraticGaussSum5 3 = -((Real.sqrt 5 : ℝ) : ℂ) := by
  have t0 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℤ) : ℂ) *
        ((0 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 0 := by
    have h := term_nat 3 0
    have hm : (3 * 0 ^ 2) % 5 = 0 := by decide
    rw [hm] at h
    simpa using h
  have t1 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℤ) : ℂ) *
        ((1 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 3 := by
    have h := term_nat 3 1
    have hm : (3 * 1 ^ 2) % 5 = 3 := by decide
    rw [hm] at h
    simpa using h
  have t2 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℤ) : ℂ) *
        ((2 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 2 := by
    have h := term_nat 3 2
    have hm : (3 * 2 ^ 2) % 5 = 2 := by decide
    rw [hm] at h
    simpa using h
  have t3 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℤ) : ℂ) *
        ((3 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 2 := by
    have h := term_nat 3 3
    have hm : (3 * 3 ^ 2) % 5 = 2 := by decide
    rw [hm] at h
    simpa using h
  have t4 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℤ) : ℂ) *
        ((4 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 3 := by
    have h := term_nat 3 4
    have hm : (3 * 4 ^ 2) % 5 = 3 := by decide
    rw [hm] at h
    simpa using h
  unfold quadraticGaussSum5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [t0, t1, t2, t3, t4]
  calc ((((gaussFifthRoot 0 + gaussFifthRoot 3) + gaussFifthRoot 2) +
      gaussFifthRoot 2) + gaussFifthRoot 3) =
      ((((gaussFifthRoot 0 + gaussFifthRoot 2) + gaussFifthRoot 3) +
        gaussFifthRoot 3) + gaussFifthRoot 2) := by ring
    _ = -((Real.sqrt 5 : ℝ) : ℂ) := S2E

private lemma sum4 : quadraticGaussSum5 4 = ((Real.sqrt 5 : ℝ) : ℂ) := by
  have t0 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((4 : ℤ) : ℂ) *
        ((0 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 0 := by
    have h := term_nat 4 0
    have hm : (4 * 0 ^ 2) % 5 = 0 := by decide
    rw [hm] at h
    simpa using h
  have t1 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((4 : ℤ) : ℂ) *
        ((1 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 4 := by
    have h := term_nat 4 1
    have hm : (4 * 1 ^ 2) % 5 = 4 := by decide
    rw [hm] at h
    simpa using h
  have t2 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((4 : ℤ) : ℂ) *
        ((2 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 1 := by
    have h := term_nat 4 2
    have hm : (4 * 2 ^ 2) % 5 = 1 := by decide
    rw [hm] at h
    simpa using h
  have t3 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((4 : ℤ) : ℂ) *
        ((3 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 1 := by
    have h := term_nat 4 3
    have hm : (4 * 3 ^ 2) % 5 = 1 := by decide
    rw [hm] at h
    simpa using h
  have t4 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((4 : ℤ) : ℂ) *
        ((4 : ℕ) : ℂ) ^ 2 / 5) = gaussFifthRoot 4 := by
    have h := term_nat 4 4
    have hm : (4 * 4 ^ 2) % 5 = 4 := by decide
    rw [hm] at h
    simpa using h
  unfold quadraticGaussSum5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [t0, t1, t2, t3, t4]
  calc ((((gaussFifthRoot 0 + gaussFifthRoot 4) + gaussFifthRoot 1) +
      gaussFifthRoot 1) + gaussFifthRoot 4) =
      ((((gaussFifthRoot 0 + gaussFifthRoot 1) + gaussFifthRoot 4) +
        gaussFifthRoot 4) + gaussFifthRoot 1) := by ring
    _ = ((Real.sqrt 5 : ℝ) : ℂ) := S1E

private lemma leg1 : legendreSym 5 1 = 1 := by norm_num
private lemma leg2 : legendreSym 5 2 = -1 := by norm_num
private lemma leg3 : legendreSym 5 3 = -1 := by norm_num
private lemma leg4 : legendreSym 5 4 = 1 := by norm_num

private lemma case1 :
    quadraticGaussSum5 1 =
      ((legendreSym 5 1 : ℤ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
  rw [leg1, sum1]
  simp

private lemma case2 :
    quadraticGaussSum5 2 =
      ((legendreSym 5 2 : ℤ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
  rw [leg2, sum2]
  simp

private lemma case3 :
    quadraticGaussSum5 3 =
      ((legendreSym 5 3 : ℤ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
  rw [leg3, sum3]
  simp

private lemma case4 :
    quadraticGaussSum5 4 =
      ((legendreSym 5 4 : ℤ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
  rw [leg4, sum4]
  simp

/-- **Evaluation of the quadratic Gauss sum modulo $5$.** For every integer $k$ not divisible by
$5$, the quadratic Gauss sum $g(k; 5) = \sum_{n=0}^{4} e^{2\pi i k n^2 / 5}$ equals
$\left(\frac{k}{5}\right)\sqrt{5}$, where $\left(\frac{k}{5}\right)$ is the Legendre symbol.

Source: the classical evaluation recorded in Dresden–Li, Journal of Integer Sequences 26 (2023),
citing Berndt, Evans, and Williams, Theorem 1.5.2. -/
public theorem quadraticGaussSum5_eval (k : ℤ) (hk : ¬ (5 : ℤ) ∣ k) :
    quadraticGaussSum5 k =
      ((legendreSym 5 k : ℤ) : ℂ) * ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hdiv : 5 * (k / 5) + k % 5 = k := by omega
  have hkk : k = (k % 5) + 5 * (k / 5) := by omega
  have hgauss : quadraticGaussSum5 k = quadraticGaussSum5 (k % 5) := by
    nth_rewrite 1 [hkk]
    exact gauss_period_int (k % 5) (k / 5)
  have hleg : legendreSym 5 k = legendreSym 5 (k % 5) := by
    have h := legendreSym.mod (p := 5) (a := k)
    simpa using h
  have hbounds : 0 ≤ k % 5 ∧ k % 5 < 5 := by omega
  have hne : k % 5 ≠ 0 := by omega
  have hcases : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hcases with h1|h2|h3|h4
  · rw [h1] at hgauss hleg; rw [hgauss, hleg]; exact case1
  · rw [h2] at hgauss hleg; rw [hgauss, hleg]; exact case2
  · rw [h3] at hgauss hleg; rw [hgauss, hleg]; exact case3
  · rw [h4] at hgauss hleg; rw [hgauss, hleg]; exact case4

end MetaMathlibExt

end

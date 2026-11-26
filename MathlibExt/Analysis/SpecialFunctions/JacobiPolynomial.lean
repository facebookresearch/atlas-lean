/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Nat.Choose.Cast

/-! # Shifted Jacobi and Gegenbauer polynomials

The shifted Jacobi polynomials `R_n^{(a,b)}` on `[0, 1]`, orthogonal for the weight
`x^(a-1) (1-x)^(b-1)` (`a, b > 0`): their Sturm–Liouville equation, integrability of the
weight against polynomials, orthogonality and norms, the shifted Legendre case `a = b = 1`,
the first polynomial, and the Gegenbauer polynomials `C_n^{(3/2)}(1 - 2x)` as the
`a = b = 2` case. -/

@[expose] public section

open Real MeasureTheory

namespace Polynomial

/-- The **shifted Jacobi polynomial** `R_n^{(a,b)}` on `[0, 1]`, orthogonal for the weight
`x^(a-1) (1-x)^(b-1)` when `a, b > 0`:
`R_n^{(a,b)}(x) = ∑_{k=0}^n (-1)^k C(n,k) (n+a+b-1)_k / (a)_k · x^k`, with rising
factorials `(c)_k = (ascPochhammer ℝ k).eval c`. It is normalized by `R_n(0) = 1`.
When `(a)_k ≠ 0` for all `k ≤ n` (in particular when `0 < a`), this is the
hypergeometric polynomial `₂F₁(-n, n+a+b-1; a; x)`, and in terms of the classical
Jacobi polynomial `R_n^{(a,b)}(x) = n! / (a)_n · P_n^{(a-1,b-1)}(1 - 2x)`. At
singular `a` those classical identities are undefined; the formula is then read with
Lean's totalized division, so terms with `(a)_k = 0` contribute `0` (for example
`shiftedJacobi 0 b 1 = 1`). -/
noncomputable def shiftedJacobi (a b : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((-1) ^ k * (n.choose k : ℝ) * (ascPochhammer ℝ k).eval ((n : ℝ) + a + b - 1) /
      (ascPochhammer ℝ k).eval a) * X ^ k

/-- Consecutive Gegenbauer polynomials `(C_n^{(ν)}, C_{n+1}^{(ν)})`, computed in one pass:
each step applies the three-term recurrence once, so reducing a concrete
`gegenbauer ν n` takes linearly many polynomial operations, not exponentially many. -/
noncomputable def gegenbauerPair (ν : ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, C (2 * ν) * X)
  | n + 1 =>
      let p := gegenbauerPair ν n
      (p.2, C ((n + 2 : ℝ)⁻¹) * (C (2 * (n + 1 + ν)) * X * p.2 - C (n + 2 * ν) * p.1))

/-- The **Gegenbauer (ultraspherical) polynomials** `C_n^{(ν)}`, by the three-term recurrence
`C_0 = 1`, `C_1 = 2νX`, `(n + 2) C_{n+2} = 2 (n + 1 + ν) X C_{n+1} - (n + 2ν) C_n`
(see `gegenbauer_two_add`), computed through `gegenbauerPair`. -/
noncomputable def gegenbauer (ν : ℝ) (n : ℕ) : ℝ[X] := (gegenbauerPair ν n).1

@[simp]
theorem gegenbauer_zero (ν : ℝ) : gegenbauer ν 0 = 1 := rfl

@[simp]
theorem gegenbauer_one (ν : ℝ) : gegenbauer ν 1 = C (2 * ν) * X := rfl

/-- The three-term recurrence for the Gegenbauer polynomials `C_n = gegenbauer ν n`: for
real `ν` and `n : ℕ`,
`C_{n+2} = (n + 2)⁻¹ * (2 * (n + 1 + ν) * X * C_{n+1} - (n + 2 * ν) * C_n)`. -/
theorem gegenbauer_two_add (ν : ℝ) (n : ℕ) :
    gegenbauer ν (n + 2) = C ((n + 2 : ℝ)⁻¹) *
      (C (2 * (n + 1 + ν)) * X * gegenbauer ν (n + 1) - C (n + 2 * ν) * gegenbauer ν n) :=
  rfl

private lemma coeff_shiftedJacobi (a b : ℝ) (n j : ℕ) :
    (shiftedJacobi a b n).coeff j =
      (-1) ^ j * (n.choose j : ℝ) * (ascPochhammer ℝ j).eval ((n : ℝ) + a + b - 1) /
        (ascPochhammer ℝ j).eval a := by
  simp only [shiftedJacobi, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h)]; simp

private lemma choose_succ_mul_real (n j : ℕ) :
    (n.choose (j + 1) : ℝ) * (j + 1) = n.choose j * (n - j) := by
  rcases le_or_gt j n with h | h
  · have h' : ((n.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((n.choose j * (n - j) : ℕ) : ℝ) := by
      rw [Nat.choose_succ_right_eq]
    push_cast [Nat.cast_sub h] at h'
    exact h'
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp

private lemma coeff_X_mul_derivative (p : ℝ[X]) (j : ℕ) :
    (X * derivative p).coeff j = p.coeff j * j := by
  cases j with
  | zero => simp
  | succ i => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

private lemma coeff_X_mul_X_mul_derivative_derivative (p : ℝ[X]) (j : ℕ) :
    (X * (X * derivative (derivative p))).coeff j = p.coeff j * j * (j - 1) := by
  cases j with
  | zero => simp
  | succ i => rw [coeff_X_mul, coeff_X_mul_derivative, coeff_derivative]; push_cast; ring

private lemma coeff_shiftedJacobi_succ {a : ℝ} (ha : 0 < a) (b : ℝ) (n j : ℕ) :
    (shiftedJacobi a b n).coeff (j + 1) * ((j + 1) * (j + a)) =
      (shiftedJacobi a b n).coeff j * ((j - n) * (j + n + a + b - 1)) := by
  rw [coeff_shiftedJacobi, coeff_shiftedJacobi, ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  have h1 := choose_succ_mul_real n j
  have h2 : (ascPochhammer ℝ j).eval a ≠ 0 := (ascPochhammer_pos j a ha).ne'
  have h3 : a + j ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero h2 h3) h2]
  linear_combination (-1) ^ (j + 1) * (ascPochhammer ℝ j).eval ((n : ℝ) + a + b - 1) *
    ((n : ℝ) + a + b - 1 + j) * (j + a) * (ascPochhammer ℝ j).eval a * h1

/-- **Sturm–Liouville equation.** For `a > 0`,
`x (1 - x) R'' + (a - (a + b) x) R' = -n (n + a + b - 1) R` (as polynomials). -/
theorem shiftedJacobi_ode {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) :
    X * (1 - X) * derivative (derivative (shiftedJacobi a b n)) +
        (C a - C (a + b) * X) * derivative (shiftedJacobi a b n) =
      -C ((n : ℝ) * (n + a + b - 1)) * shiftedJacobi a b n := by
  set R := shiftedJacobi a b n
  have e1 : X * (1 - X) * derivative (derivative R) + (C a - C (a + b) * X) * derivative R =
      X * derivative (derivative R) - X * (X * derivative (derivative R)) + C a * derivative R -
        C (a + b) * (X * derivative R) := by ring
  rw [e1]
  ext j
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_derivative,
    coeff_X_mul_X_mul_derivative_derivative, coeff_derivative, neg_mul, coeff_neg]
  linear_combination coeff_shiftedJacobi_succ ha b n j

private lemma hasDerivAt_eval (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => p.eval y) ((derivative p).eval x) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, derivative_add]
    exact hp.add hq
  | monomial k c =>
    simp only [eval_monomial, derivative_monomial]
    convert (hasDerivAt_pow k x).const_mul c using 1
    ring

private lemma continuous_eval (p : ℝ[X]) : Continuous fun x : ℝ => p.eval x :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_eval p x).continuousAt

/-- For `a, b > 0` every polynomial is integrable against the weight `x^(a-1) (1-x)^(b-1)` on
`[0, 1]`, so the orthogonality and norm integrals below are genuine (not Lean's junk `0`). -/
theorem intervalIntegrable_eval_mul_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℝ[X]) :
    IntervalIntegrable (fun x => p.eval x * (x ^ (a - 1) * (1 - x) ^ (b - 1))) volume 0 1 := by
  have h1 : IntervalIntegrable (fun x => p.eval x * (x ^ (a - 1) * (1 - x) ^ (b - 1)))
      volume 0 (1 / 2) := by
    have hi : IntervalIntegrable (fun x : ℝ => x ^ (a - 1)) volume 0 (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hc : ContinuousOn (fun x : ℝ => p.eval x * (1 - x) ^ (b - 1)) (Set.uIcc 0 (1 / 2)) := by
      refine (continuous_eval p).continuousOn.mul fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact ((continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl (show (1 : ℝ) - x ≠ 0 by linarith [hx.2]))).continuousWithinAt
    have e : (fun x => p.eval x * (x ^ (a - 1) * (1 - x) ^ (b - 1))) =
        fun x => x ^ (a - 1) * (p.eval x * (1 - x) ^ (b - 1)) := by
      funext x; ring
    rw [e]
    exact hi.mul_continuousOn hc
  have h2 : IntervalIntegrable (fun x => p.eval x * (x ^ (a - 1) * (1 - x) ^ (b - 1)))
      volume (1 / 2) 1 := by
    have hi : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (b - 1)) volume (1 / 2) 1 := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / 2)
        (show -1 < b - 1 by linarith)).comp_sub_left 1
      norm_num at this
      exact this.symm
    have hc : ContinuousOn (fun x : ℝ => p.eval x * x ^ (a - 1)) (Set.uIcc (1 / 2) 1) := by
      refine (continuous_eval p).continuousOn.mul fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact (continuousAt_id.rpow_const
        (Or.inl (show x ≠ 0 by linarith [hx.1]))).continuousWithinAt
    have e : (fun x => p.eval x * (x ^ (a - 1) * (1 - x) ^ (b - 1))) =
        fun x => (1 - x) ^ (b - 1) * (p.eval x * x ^ (a - 1)) := by
      funext x; ring
    rw [e]
    exact hi.mul_continuousOn hc
  exact h1.trans h2

private lemma integral_green {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (P Q : ℝ[X]) :
    ∫ x in (0 : ℝ)..1, eval x ((X * (1 - X) * derivative (derivative P) +
        (C a - C (a + b) * X) * derivative P) * Q) * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      -∫ x in (0 : ℝ)..1, eval x (X * (1 - X) * derivative P * derivative Q) *
        (x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
  set A : ℝ[X] := (X * (1 - X) * derivative (derivative P) +
        (C a - C (a + b) * X) * derivative P) * Q with hA
  set B : ℝ[X] := X * (1 - X) * derivative P * derivative Q with hB
  have hFTC : ∫ x in (0 : ℝ)..1, eval x (A + B) * (x ^ (a - 1) * (1 - x) ^ (b - 1)) = 0 := by
    have hcont : ContinuousOn (fun x : ℝ => x ^ a * (1 - x) ^ b *
        ((derivative P).eval x * Q.eval x)) (Set.Icc 0 1) := by
      have h1 : Continuous fun x : ℝ => x ^ a := continuous_id.rpow_const fun _ => Or.inr ha.le
      have h2 : Continuous fun x : ℝ => (1 - x) ^ b :=
        (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hb.le
      exact ((h1.mul h2).mul ((continuous_eval _).mul (continuous_eval _))).continuousOn
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ a * (1 - x) ^ b *
        ((derivative P).eval x * Q.eval x))
        (eval x (A + B) * (x ^ (a - 1) * (1 - x) ^ (b - 1))) x := by
      intro x hx
      have hx0 : x ≠ 0 := hx.1.ne'
      have hx1 : 1 - x ≠ 0 := sub_ne_zero.2 hx.2.ne'
      have d1 : HasDerivAt (fun y : ℝ => y ^ a) (a * x ^ (a - 1)) x :=
        Real.hasDerivAt_rpow_const (Or.inl hx0)
      have d2 : HasDerivAt (fun y : ℝ => (1 - y) ^ b) (-1 * b * (1 - x) ^ (b - 1)) x :=
        ((hasDerivAt_id' x).const_sub 1).rpow_const (Or.inl hx1)
      have d3 := (hasDerivAt_eval (derivative P) x).mul (hasDerivAt_eval Q x)
      convert (d1.mul d2).mul d3 using 1
      simp only [Pi.mul_apply]
      have ea : x ^ a = x ^ (a - 1) * x := by rw [← Real.rpow_add_one hx0, sub_add_cancel]
      have eb : (1 - x) ^ b = (1 - x) ^ (b - 1) * (1 - x) := by
        rw [← Real.rpow_add_one hx1, sub_add_cancel]
      rw [ea, eb]
      simp only [hA, hB, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
      (intervalIntegrable_eval_mul_weight ha hb (A + B))]
    simp [Real.zero_rpow ha.ne', Real.zero_rpow hb.ne']
  have hsplit : ∫ x in (0 : ℝ)..1, eval x (A + B) * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      (∫ x in (0 : ℝ)..1, eval x A * (x ^ (a - 1) * (1 - x) ^ (b - 1))) +
        ∫ x in (0 : ℝ)..1, eval x B * (x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_eval_mul_weight ha hb A)
      (intervalIntegrable_eval_mul_weight ha hb B)]
    congr 1; funext x; rw [eval_add]; ring
  linarith

/-- **Orthogonality.** For `a, b > 0` and `m ≠ n`,
`∫₀¹ R_m(x) R_n(x) x^(a-1) (1-x)^(b-1) dx = 0`. -/
theorem integral_shiftedJacobi_mul_shiftedJacobi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m n : ℕ}
    (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b m).eval x * (shiftedJacobi a b n).eval x *
      (x ^ (a - 1) * (1 - x) ^ (b - 1)) = 0 := by
  set I := ∫ x in (0 : ℝ)..1, (shiftedJacobi a b m).eval x * (shiftedJacobi a b n).eval x *
      (x ^ (a - 1) * (1 - x) ^ (b - 1)) with hI
  have g1 := integral_green ha hb (shiftedJacobi a b m) (shiftedJacobi a b n)
  have g2 := integral_green ha hb (shiftedJacobi a b n) (shiftedJacobi a b m)
  rw [shiftedJacobi_ode ha b m] at g1
  rw [shiftedJacobi_ode ha b n] at g2
  have e : X * (1 - X) * derivative (shiftedJacobi a b n) * derivative (shiftedJacobi a b m) =
      X * (1 - X) * derivative (shiftedJacobi a b m) * derivative (shiftedJacobi a b n) := by ring
  rw [e] at g2
  have h1 : ∫ x in (0 : ℝ)..1, eval x (-C ((m : ℝ) * (m + a + b - 1)) * shiftedJacobi a b m *
      shiftedJacobi a b n) * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
        -((m : ℝ) * (m + a + b - 1)) * I := by
    rw [hI, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; simp only [eval_mul, eval_neg, eval_C]; ring
  have h2 : ∫ x in (0 : ℝ)..1, eval x (-C ((n : ℝ) * (n + a + b - 1)) * shiftedJacobi a b n *
      shiftedJacobi a b m) * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
        -((n : ℝ) * (n + a + b - 1)) * I := by
    rw [hI, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; simp only [eval_mul, eval_neg, eval_C]; ring
  rw [h1] at g1
  rw [h2] at g2
  have hne : (n : ℝ) * (n + a + b - 1) - m * (m + a + b - 1) ≠ 0 := by
    have e2 : (n : ℝ) * (n + a + b - 1) - m * (m + a + b - 1) = (n - m) * (n + m + a + b - 1) := by
      ring
    rw [e2]
    refine mul_ne_zero (sub_ne_zero.2 (Nat.cast_injective.ne hmn.symm)) ?_
    have : (1 : ℝ) ≤ n + m := by norm_cast; omega
    linarith
  have : ((n : ℝ) * (n + a + b - 1) - m * (m + a + b - 1)) * I = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left hne

private lemma integrableOn_rpow_mul_exp_neg_mul {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (c - 1) * exp (-(r * t))) (Set.Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => exp (-x) * x ^ (c - 1)) 0 hr).2
    (by simpa using Real.GammaIntegral_convergent hc)
  refine IntegrableOn.congr_fun (h.const_mul (r ^ (c - 1))⁻¹) (fun t ht => ?_) measurableSet_Ioi
  have hr' : r ^ (c - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  rw [Real.mul_rpow hr.le (le_of_lt ht)]
  field_simp

private lemma Gamma_mul_Gamma_eq_integral_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Gamma a * Gamma b =
      (∫ s in Set.Ioi (0 : ℝ), s ^ (b - 1) * (1 / (1 + s)) ^ (a + b)) * Gamma (a + b) := by
  set F : ℝ → ℝ → ℝ := fun x s => x ^ (a + b - 1) * s ^ (b - 1) * exp (-(x * (1 + s)))
    with hF
  have eF : ∀ x s, F x s = x ^ (a + b - 1) * exp (-x) * (s ^ (b - 1) * exp (-(x * s))) := by
    intro x s; simp only [hF]; rw [mul_add, mul_one, neg_add, Real.exp_add]; ring
  have hs_int : ∀ x : ℝ, 0 < x →
      ∫ s in Set.Ioi (0 : ℝ), F x s = exp (-x) * x ^ (a - 1) * Gamma b := by
    intro x hx
    simp_rw [eF]
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hb hx,
      Real.div_rpow zero_le_one hx.le, Real.one_rpow]
    have e : x ^ (a + b - 1) = x ^ (a - 1) * x ^ b := by
      rw [← Real.rpow_add hx]; ring_nf
    rw [e]
    have hxb : x ^ b ≠ 0 := (Real.rpow_pos_of_pos hx b).ne'
    field_simp
  have hx_int : ∀ s : ℝ, 0 < s → ∫ x in Set.Ioi (0 : ℝ), F x s =
      s ^ (b - 1) * (1 / (1 + s)) ^ (a + b) * Gamma (a + b) := by
    intro s hs
    have e : ∀ x, F x s = s ^ (b - 1) * (x ^ (a + b - 1) * exp (-((1 + s) * x))) := by
      intro x; simp only [hF]; ring_nf
    simp_rw [e]
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by linarith)]
    ring
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hmeas : Measurable (Function.uncurry F) := by
      show Measurable fun p : ℝ × ℝ => p.1 ^ (a + b - 1) * p.2 ^ (b - 1) * exp (-(p.1 * (1 + p.2)))
      fun_prop
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h := (integrableOn_rpow_mul_exp_neg_mul hb hx).const_mul (x ^ (a + b - 1) * exp (-x))
      exact h.congr (Filter.Eventually.of_forall fun s => (eF x s).symm)
    · have hG : IntegrableOn (fun x : ℝ => exp (-x) * x ^ (a - 1) * Gamma b) (Set.Ioi 0) :=
        (Real.GammaIntegral_convergent ha).mul_const _
      refine hG.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [← hs_int x hx]
      refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      have hs' : (0 : ℝ) < s := hs
      have hx' : (0 : ℝ) < x := hx
      rw [Real.norm_of_nonneg]
      · rfl
      · show 0 ≤ x ^ (a + b - 1) * s ^ (b - 1) * exp (-(x * (1 + s)))
        positivity
  calc Gamma a * Gamma b = ∫ x in Set.Ioi (0 : ℝ), exp (-x) * x ^ (a - 1) * Gamma b := by
        rw [Real.Gamma_eq_integral ha, integral_mul_const]
    _ = ∫ x in Set.Ioi (0 : ℝ), ∫ s in Set.Ioi (0 : ℝ), F x s :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => (hs_int x hx).symm)
    _ = ∫ s in Set.Ioi (0 : ℝ), ∫ x in Set.Ioi (0 : ℝ), F x s := integral_integral_swap hint
    _ = ∫ s in Set.Ioi (0 : ℝ), s ^ (b - 1) * (1 / (1 + s)) ^ (a + b) * Gamma (a + b) :=
        setIntegral_congr_fun measurableSet_Ioi (fun s hs => hx_int s hs)
    _ = _ := integral_mul_const _ _

private lemma integral_Ioi_eq_integral_beta (a b : ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ (b - 1) * (1 / (1 + s)) ^ (a + b) =
      ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have himg : (fun t : ℝ => (1 + t)⁻¹) '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (0 : ℝ) < t := ht
      exact ⟨by positivity, inv_lt_one_of_one_lt₀ (by linarith)⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨x⁻¹ - 1, ?_, ?_⟩
      · simp only [Set.mem_Ioi, sub_pos]
        exact (one_lt_inv₀ hx0).2 hx1
      · simp
  rw [← himg, integral_image_eq_integral_abs_deriv_smul (f := fun t => (1 + t)⁻¹)
    (f' := fun t => -1 / (1 + t) ^ 2)
    measurableSet_Ioi
    (fun t ht => (((hasDerivAt_id' t).const_add 1).inv
      (by have ht' : (0 : ℝ) < t := ht; linarith)).hasDerivWithinAt)
    (fun t₁ _ t₂ _ h => by simpa using h)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht' : (0 : ℝ) < t := ht
  have h1t : 0 < 1 + t := by linarith
  have hu0 : 0 < (1 + t)⁻¹ := inv_pos.2 h1t
  have e1 : 1 - (1 + t)⁻¹ = t * (1 + t)⁻¹ := by field_simp; ring
  have e2 : |(-1 / (1 + t) ^ 2)| = ((1 + t)⁻¹) ^ 2 := by
    rw [abs_div, abs_neg, abs_one, abs_pow, abs_of_pos h1t, inv_pow, one_div]
  have e3 : ((1 + t)⁻¹) ^ (a + b) =
      ((1 + t)⁻¹) ^ (a - 1) * ((1 + t)⁻¹) ^ (b - 1) * ((1 + t)⁻¹) ^ 2 := by
    rw [show a + b = (a - 1) + (b - 1) + 2 by ring, Real.rpow_add hu0, Real.rpow_add hu0,
      Real.rpow_two]
  simp only [smul_eq_mul]
  rw [one_div, e3, e2, e1, Real.mul_rpow ht'.le hu0.le]
  ring

private lemma integral_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = Gamma a * Gamma b / Gamma (a + b) := by
  rw [Gamma_mul_Gamma_eq_integral_Ioi ha hb, integral_Ioi_eq_integral_beta a b,
    mul_div_assoc, div_self (Real.Gamma_pos_of_pos (by linarith)).ne', mul_one]

private lemma shiftedJacobi_zero (a b : ℝ) : shiftedJacobi a b 0 = 1 := by
  simp [shiftedJacobi]

/-- **Norm, `n = 0`.** `R_0 = 1` and `∫₀¹ x^(a-1) (1-x)^(b-1) dx = Γ(a) Γ(b) / Γ(a + b)`. -/
theorem integral_shiftedJacobi_zero_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b 0).eval x ^ 2 * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      Gamma a * Gamma b / Gamma (a + b) := by
  simp only [shiftedJacobi_zero, eval_one, one_pow, one_mul]
  exact integral_weight ha hb

private lemma derivative_shiftedJacobi_succ (a b : ℝ) (n : ℕ) :
    derivative (shiftedJacobi a b (n + 1)) =
      C (-(((n : ℝ) + 1) * ((n : ℝ) + a + b) / a)) * shiftedJacobi (a + 1) (b + 1) n := by
  ext j
  rw [coeff_derivative, coeff_C_mul, coeff_shiftedJacobi, coeff_shiftedJacobi,
    ascPochhammer_succ_left]
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  have h1 : ((n + 1).choose (j + 1) : ℝ) * (j + 1) = (n + 1) * n.choose j := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n j).symm
  push_cast
  rw [show (n : ℝ) + 1 + a + b - 1 + 1 = n + (a + 1) + (b + 1) - 1 by ring]
  linear_combination ((-1) ^ (j + 1) * ((n : ℝ) + 1 + a + b - 1) *
    (ascPochhammer ℝ j).eval ((n : ℝ) + (a + 1) + (b + 1) - 1) /
      (a * (ascPochhammer ℝ j).eval (a + 1))) * h1

private lemma integral_sq_succ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b (n + 1)).eval x ^ 2 *
        (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      ((n : ℝ) + 1) * (n + a + b) / a ^ 2 *
        ∫ x in (0 : ℝ)..1, (shiftedJacobi (a + 1) (b + 1) n).eval x ^ 2 *
          (x ^ (a + 1 - 1) * (1 - x) ^ (b + 1 - 1)) := by
  have g := integral_green ha hb (shiftedJacobi a b (n + 1)) (shiftedJacobi a b (n + 1))
  rw [shiftedJacobi_ode ha b (n + 1), derivative_shiftedJacobi_succ a b n] at g
  have hL : ∫ x in (0 : ℝ)..1, eval x (-C (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + a + b - 1)) *
      shiftedJacobi a b (n + 1) * shiftedJacobi a b (n + 1)) *
        (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      -(((n : ℝ) + 1) * (n + a + b)) * ∫ x in (0 : ℝ)..1, (shiftedJacobi a b (n + 1)).eval x ^ 2 *
        (x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; simp only [eval_mul, eval_neg, eval_C]; push_cast; ring
  have hR : ∫ x in (0 : ℝ)..1, eval x (X * (1 - X) *
      (C (-(((n : ℝ) + 1) * ((n : ℝ) + a + b) / a)) * shiftedJacobi (a + 1) (b + 1) n) *
      (C (-(((n : ℝ) + 1) * ((n : ℝ) + a + b) / a)) * shiftedJacobi (a + 1) (b + 1) n)) *
        (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      (((n : ℝ) + 1) * ((n : ℝ) + a + b) / a) ^ 2 *
        ∫ x in (0 : ℝ)..1, (shiftedJacobi (a + 1) (b + 1) n).eval x ^ 2 *
          (x ^ (a + 1 - 1) * (1 - x) ^ (b + 1 - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    have e1 : x ^ (a + 1 - 1) = x * x ^ (a - 1) := by
      rw [add_sub_cancel_right]
      conv_lhs => rw [← sub_add_cancel a 1]
      rw [Real.rpow_add' hx.1 (by linarith), Real.rpow_one]; ring
    have e2 : (1 - x) ^ (b + 1 - 1) = (1 - x) * (1 - x) ^ (b - 1) := by
      rw [add_sub_cancel_right]
      conv_lhs => rw [← sub_add_cancel b 1]
      rw [Real.rpow_add' (by linarith [hx.2]) (by linarith), Real.rpow_one]; ring
    simp only [eval_mul, eval_sub, eval_one, eval_X, eval_C]
    rw [e1, e2]; ring
  rw [hL, hR] at g
  have hlam : ((n : ℝ) + 1) * (n + a + b) ≠ 0 := by positivity
  apply mul_left_cancel₀ hlam
  have e : (((n : ℝ) + 1) * ((n : ℝ) + a + b) / a) ^ 2 =
      ((n : ℝ) + 1) * (n + a + b) * (((n : ℝ) + 1) * (n + a + b) / a ^ 2) := by ring
  rw [e] at g
  linarith

private lemma integral_sq_eq (n : ℕ) : ∀ {a b : ℝ}, 0 < a → 0 < b →
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b n).eval x ^ 2 * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      (n.factorial : ℝ) * (ascPochhammer ℝ n).eval ((n : ℝ) + a + b - 1) * Gamma a ^ 2 *
        Gamma (n + b) / (Gamma (n + a) * Gamma (2 * n + a + b)) := by
  induction n with
  | zero =>
    intro a b ha hb
    rw [integral_shiftedJacobi_zero_sq ha hb]
    have hGa : Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    simp only [Nat.factorial_zero, Nat.cast_one, ascPochhammer_zero, eval_one, CharP.cast_eq_zero,
      zero_add, mul_zero, one_mul]
    field_simp
  | succ m ih =>
    intro a b ha hb
    rw [integral_sq_succ ha hb m, ih (by linarith) (by linarith), Real.Gamma_add_one ha.ne',
      ascPochhammer_succ_left, Nat.factorial_succ]
    simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
    push_cast
    rw [show (m : ℝ) + (a + 1) + (b + 1) - 1 = m + 1 + a + b - 1 + 1 by ring,
      show (m : ℝ) + (b + 1) = m + 1 + b by ring, show (m : ℝ) + (a + 1) = m + 1 + a by ring,
      show 2 * (m : ℝ) + (a + 1) + (b + 1) = 2 * (m + 1) + a + b by ring]
    have hG1 : Gamma ((m : ℝ) + 1 + a) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hG2 : Gamma (2 * ((m : ℝ) + 1) + a + b) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    field_simp
    ring

private lemma Gamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma (x + n) = (ascPochhammer ℝ n).eval x * Gamma x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih,
      ascPochhammer_succ_eval]
    ring

/-- **Norms, `n ≥ 1`.** For `a, b > 0`,
`∫₀¹ R_n(x)² x^(a-1) (1-x)^(b-1) dx = n! Γ(a)² Γ(n+b) / (Γ(n+a) (2n+a+b-1) Γ(n+a+b-1))`. -/
theorem integral_shiftedJacobi_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b n).eval x ^ 2 * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      (n.factorial : ℝ) * Gamma a ^ 2 * Gamma (n + b) /
        (Gamma (n + a) * (2 * n + a + b - 1) * Gamma (n + a + b - 1)) := by
  rw [integral_sq_eq n ha hb]
  have hx : 0 < (n : ℝ) + a + b - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : Gamma (2 * n + a + b) = (2 * n + a + b - 1) *
      ((ascPochhammer ℝ n).eval ((n : ℝ) + a + b - 1) * Gamma ((n : ℝ) + a + b - 1)) := by
    rw [← Gamma_add_nat hx n, show (2 * n + a + b : ℝ) = ((n : ℝ) + a + b - 1 + n) + 1 by ring,
      Real.Gamma_add_one (by positivity)]
    ring_nf
  rw [h1]
  have hP : (ascPochhammer ℝ n).eval ((n : ℝ) + a + b - 1) ≠ 0 := (ascPochhammer_pos n _ hx).ne'
  have hG1 : Gamma ((n : ℝ) + a) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hG2 : Gamma ((n : ℝ) + a + b - 1) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have h3 : (2 * (n : ℝ) + a + b - 1) ≠ 0 := by linarith
  field_simp

/-- **Shifted Legendre case.** `R_n^{(1,1)}` is Mathlib's `shiftedLegendre n` (normalization
constant `1`). -/
theorem shiftedJacobi_one_one (n : ℕ) :
    shiftedJacobi 1 1 n = (shiftedLegendre n).map (Int.castRingHom ℝ) := by
  rw [shiftedJacobi, shiftedLegendre, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]
  congr 2
  have h1 : ((n : ℝ) + 1 + 1 - 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have h2 : (ascPochhammer ℝ k).eval ((n + 1 : ℕ) : ℝ) =
      (k.factorial : ℝ) * ((n + k).choose k) := by
    rw [← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [h1, h2, ascPochhammer_eval_one, Nat.choose_symm_add]
  simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  field_simp

/-- **First polynomial.** `R_1^{(a,b)} = 1 - ((a + b) / a) X`; with `shiftedJacobi_ode` its
eigenvalue is `1 · (1 + a + b - 1) = a + b`. -/
theorem shiftedJacobi_one (a b : ℝ) : shiftedJacobi a b 1 = 1 - C ((a + b) / a) * X := by
  simp only [shiftedJacobi, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    ascPochhammer_zero, ascPochhammer_one, eval_one, eval_X, pow_zero, pow_one,
    Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, zero_add, mul_one, div_one, map_one]
  rw [show (-1 : ℝ) * ((1 : ℝ) + a + b - 1) / a = -((a + b) / a) by ring, map_neg]
  ring


private lemma coeff_shiftedJacobi_two (n j : ℕ) :
    (shiftedJacobi 2 2 n).coeff j =
      (-1) ^ j * (n.choose j : ℝ) * (ascPochhammer ℝ j).eval ((n : ℝ) + 3) /
        (ascPochhammer ℝ j).eval 2 := by
  rw [coeff_shiftedJacobi, show (n : ℝ) + 2 + 2 - 1 = n + 3 by ring]

private lemma shiftedJacobi_two_two_rec (n : ℕ) :
    C ((n : ℝ) + 4) * shiftedJacobi 2 2 (n + 2) =
      C (2 * (n : ℝ) + 5) * ((1 - C 2 * X) * shiftedJacobi 2 2 (n + 1)) -
        C ((n : ℝ) + 1) * shiftedJacobi 2 2 n := by
  have e : (1 - C 2 * X) * shiftedJacobi 2 2 (n + 1) =
      shiftedJacobi 2 2 (n + 1) - C 2 * (X * shiftedJacobi 2 2 (n + 1)) := by ring
  rw [e]
  ext j
  simp only [coeff_sub, coeff_C_mul]
  cases j with
  | zero =>
    simp [coeff_shiftedJacobi_two]
    ring
  | succ i =>
    rw [coeff_X_mul, coeff_shiftedJacobi_two, coeff_shiftedJacobi_two, coeff_shiftedJacobi_two,
      coeff_shiftedJacobi_two, show n + 2 = n + 1 + 1 from rfl]
    push_cast
    set P := (ascPochhammer ℝ i).eval ((n : ℝ) + 4) with hP
    set Q := (ascPochhammer ℝ i).eval (2 : ℝ)
    set B := ((n + 1).choose i : ℝ)
    have hP0 : 0 < P := ascPochhammer_pos i _ (by positivity)
    have hQ0 : 0 < Q := ascPochhammer_pos i _ (by positivity)
    have hA : (ascPochhammer ℝ (i + 1)).eval ((n : ℝ) + 1 + 1 + 3) =
        P * (n + 4 + i) * (n + 5 + i) / (n + 4) := by
      have h := congrArg (eval ((n : ℝ) + 4)) (ascPochhammer_succ_left (S := ℝ) (i + 1))
      simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one] at h
      rw [ascPochhammer_succ_eval (i + 1) ((n : ℝ) + 4), ascPochhammer_succ_eval i ((n : ℝ) + 4),
        ← hP] at h
      rw [eq_div_iff (by positivity), show (n : ℝ) + 1 + 1 + 3 = n + 4 + 1 by ring]
      push_cast at h
      linear_combination -h
    have hB1 : (ascPochhammer ℝ (i + 1)).eval ((n : ℝ) + 1 + 3) = P * (n + 4 + i) := by
      rw [ascPochhammer_succ_eval, show (n : ℝ) + 1 + 3 = n + 4 by ring]
    have hB0 : (ascPochhammer ℝ i).eval ((n : ℝ) + 1 + 3) = P := by
      rw [show (n : ℝ) + 1 + 3 = n + 4 by ring]
    have hC : (ascPochhammer ℝ (i + 1)).eval ((n : ℝ) + 3) = (n + 3) * P := by
      rw [ascPochhammer_succ_left]
      simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
      rw [show (n : ℝ) + 3 + 1 = n + 4 by ring]
    have hD : (ascPochhammer ℝ (i + 1)).eval (2 : ℝ) = Q * (2 + i) := by
      rw [ascPochhammer_succ_eval]
    have h1 : ((n + 1 + 1).choose (i + 1) : ℝ) = (n + 2) * B / (i + 1) := by
      rw [eq_div_iff (by positivity)]
      have h := Nat.add_one_mul_choose_eq (n + 1) i
      have h' : (((n + 1 + 1).choose (i + 1) * (i + 1) : ℕ) : ℝ) =
          (((n + 1 + 1) * (n + 1).choose i : ℕ) : ℝ) := by rw [h]
      push_cast at h'
      linear_combination h'
    have h2' : ((n + 1).choose (i + 1) : ℝ) * (i + 1) = (n + 1 - i) * B := by
      have h := choose_succ_mul_real (n + 1) i
      push_cast at h
      linear_combination h
    have h2 : ((n + 1).choose (i + 1) : ℝ) = (n + 1 - i) * B / (i + 1) := by
      rw [eq_div_iff (by positivity)]
      exact h2'
    have h3 : (n.choose (i + 1) : ℝ) = (n - i) * (n + 1 - i) * B / ((n + 1) * (i + 1)) := by
      have hpas : ((n + 1).choose (i + 1) : ℝ) = n.choose i + n.choose (i + 1) := by
        exact_mod_cast Nat.choose_succ_succ n i
      have h0 := choose_succ_mul_real n i
      have h4 : ((n : ℝ) + 1) * n.choose (i + 1) = (n - i) * (n + 1).choose (i + 1) := by
        linear_combination h0 - ((n : ℝ) - i) * hpas
      rw [eq_div_iff (by positivity)]
      linear_combination ((i : ℝ) + 1) * h4 + ((n : ℝ) - i) * h2'
    rw [hA, hB1, hB0, hC, hD, h1, h2, h3, pow_succ]
    field_simp
    ring

private lemma comp_step {u x y z w c p q r k : ℝ} {A S0 S1 S2 : ℝ[X]}
    (hrec : C p * S2 = C q * (A * S1) - C r * S0)
    (h1 : u * x * y = k * q) (h2 : u * z * w = k * r) (h3 : c = k * p) :
    C u * (C x * A * (C y * S1) - C z * (C w * S0)) = C c * S2 := by
  have e1 : C u * (C x * A * (C y * S1) - C z * (C w * S0)) =
      C (u * x * y) * (A * S1) - C (u * z * w) * S0 := by
    simp only [C_mul]; ring
  rw [e1, h1, h2, h3, C_mul, C_mul, C_mul, mul_assoc (C k) (C p) S2, hrec]
  ring

/-- **Gegenbauer case.** `C_n^{(3/2)}(1 - 2x) = C(n + 2, 2) · R_n^{(2,2)}(x)`. -/
theorem gegenbauer_three_halves_comp (n : ℕ) :
    (gegenbauer (3 / 2) n).comp (1 - C 2 * X) =
      C (((n + 2).choose 2 : ℕ) : ℝ) * shiftedJacobi 2 2 n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [shiftedJacobi_zero]
  | one =>
    rw [shiftedJacobi_one]
    simp only [gegenbauer_one, mul_comp, C_comp, X_comp]
    rw [show Nat.choose (1 + 2) 2 = 3 from rfl]
    norm_num
  | more m ih1 ih2 =>
    simp only [gegenbauer_two_add, mul_comp, sub_comp, C_comp, X_comp, ih1, ih2]
    have hm : (m : ℝ) + 2 ≠ 0 := by positivity
    refine comp_step (k := ((m : ℝ) + 3) / 2) (shiftedJacobi_two_two_rec m) ?_ ?_ ?_
    · rw [Nat.cast_choose_two]; push_cast; field_simp; ring
    · rw [Nat.cast_choose_two]; push_cast; field_simp; ring
    · rw [Nat.cast_choose_two]; push_cast; ring

end Polynomial

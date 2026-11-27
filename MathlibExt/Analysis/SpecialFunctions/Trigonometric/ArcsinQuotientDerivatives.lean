/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.LinearCombination

/-!
# Derivatives of arcsine quotients

The odd derivatives of `arcsin x / (1 - x)` and the positive even derivatives of
`arcsin x ^ 2 / (2 * (1 - x))` at zero are factorials times partial sums of double-factorial
ratios. We obtain the coefficients of both numerators from the same differential equation.
-/

namespace MetaMathlibExt

open Real Filter Topology
open scoped ContDiff

namespace iteratedDeriv_arcsin_div_one_sub_doubleFactorial

/-- In Leibniz's formula at zero, only the first derivative of the factor `x` contributes. -/
private lemma deriv_mul_coord {f : ℝ → ℝ} (n : ℕ) (hf : ContDiffAt ℝ ∞ f 0) :
    iteratedDeriv (n + 1) (fun x => x * f x) 0 = (n + 1 : ℝ) * iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (f := fun x : ℝ => x) contDiffAt_fun_id (hf.of_le (by simp))]
  simp [iteratedDeriv_fun_id_zero, mul_ite, ite_mul]

/-- The first derivatives of our two numerators have this form for `(a,b) = (1,0), (0,1)`. -/
private noncomputable def numeratorDeriv (a b x : ℝ) : ℝ :=
  (a + b * arcsin x) / √(1 - x ^ 2)

private lemma numeratorDeriv_smooth (a b : ℝ) : ContDiffAt ℝ ∞ (numeratorDeriv a b) 0 := by
  have ha : ContDiffAt ℝ ∞ arcsin 0 := contDiffAt_arcsin (by norm_num) (by norm_num)
  unfold numeratorDeriv
  fun_prop (disch := norm_num)

/-- For `v = numeratorDeriv a b`, differentiating `√(1-x²) v = a + b arcsin x` gives
`(1-x²) v' = b + x v`, or equivalently `v' = b + x (x v)'`. -/
private lemma numeratorDeriv_eqn (a b : ℝ) :
    deriv (numeratorDeriv a b) =ᶠ[𝓝 0]
      fun x => b + x * deriv (fun t => t * numeratorDeriv a b t) x := by
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
    with x hx
  have hpos : 0 < 1 - x ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hx.2) (sub_pos.mpr hx.1)]
  have hs := ((hasDerivAt_pow 2 x).const_sub 1).sqrt hpos.ne'
  have had := hasDerivAt_arcsin hx.1.ne' hx.2.ne
  have hv : DifferentiableAt ℝ (numeratorDeriv a b) x :=
    (((had.const_mul b).const_add a).div hs (sqrt_pos.2 hpos).ne').differentiableAt
  have heq : (fun t => √(1 - t ^ 2) * numeratorDeriv a b t) =ᶠ[𝓝 x]
      fun t => a + b * arcsin t := by
    have hnear : ∀ᶠ t : ℝ in 𝓝 x, 0 < 1 - t ^ 2 :=
      (isOpen_lt continuous_const (continuous_const.sub (continuous_id.pow 2))).mem_nhds hpos
    filter_upwards [hnear] with t ht
    unfold numeratorDeriv
    field_simp [(sqrt_pos.2 ht).ne']
  have hd := ((hs.mul hv.hasDerivAt).congr_of_eventuallyEq heq.symm).unique
    ((had.const_mul b).const_add a)
  rw [show deriv (fun t => t * numeratorDeriv a b t) x =
      numeratorDeriv a b x + x * deriv (numeratorDeriv a b) x by
    simpa [Pi.mul_def, id_def] using ((hasDerivAt_id x).mul hv.hasDerivAt).deriv]
  have hs0 := (sqrt_pos.2 hpos).ne'
  field_simp [hs0] at hd
  linear_combination (norm := ring_nf) hd / 2 -
    deriv (numeratorDeriv a b) x * (sq_sqrt hpos.le)

/-- Applying the product rule twice to the differential equation gives a two-step recurrence. -/
private lemma iteratedDeriv_step (a b : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (numeratorDeriv a b) 0 =
      (n + 1 : ℝ) ^ 2 * iteratedDeriv n (numeratorDeriv a b) 0 := by
  have hv := numeratorDeriv_smooth a b
  have hxv : ContDiffAt ℝ ∞ (fun x => x * numeratorDeriv a b x) 0 := contDiffAt_id.mul hv
  have hd := (numeratorDeriv_eqn a b).iteratedDeriv_eq (n + 1)
  rw [iteratedDeriv_const_add (by omega) b,
    deriv_mul_coord n (hxv.derivWithin (by simp)), ← iteratedDeriv_succ' (n := n),
    deriv_mul_coord n hv, ← iteratedDeriv_succ'] at hd
  linear_combination hd

private lemma iteratedDeriv_numeratorDeriv (a b : ℝ) (m : ℕ) :
    iteratedDeriv m (numeratorDeriv a b) 0 =
      ((m - 1).doubleFactorial : ℝ) ^ 2 * (if Even m then a else b) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [numeratorDeriv]
  | one => simpa [iteratedDeriv_one] using (numeratorDeriv_eqn a b).eq_of_nhds
  | more m ih _ =>
    rw [iteratedDeriv_step, ih, show m + 2 - 1 = m + 1 by omega, Nat.doubleFactorial_add_one]
    simp [Nat.even_add, mul_pow, mul_assoc]

/-- The Taylor coefficient of degree `m+1` in the numerator, before selecting its parity. -/
private noncomputable def weight (m : ℕ) : ℝ :=
  ((m - 1).doubleFactorial : ℝ) / (m.doubleFactorial * ((m : ℝ) + 1))

private lemma taylor_coeff (a b : ℝ) (m : ℕ) :
    iteratedDeriv m (numeratorDeriv a b) 0 / (m + 1).factorial =
      weight m * (if Even m then a else b) := by
  rw [iteratedDeriv_numeratorDeriv, weight, Nat.factorial_eq_mul_doubleFactorial,
    Nat.doubleFactorial_add_one]
  push_cast
  field_simp

/-- Multiplication by `1/(1-x)` takes partial sums of the Taylor coefficients. -/
private lemma quotient_deriv {f : ℝ → ℝ} (hf : ContDiffAt ℝ ∞ f 0) (hf0 : f 0 = 0)
    {a b : ℝ} (hd : deriv f =ᶠ[𝓝 0] numeratorDeriv a b) (n : ℕ) :
    iteratedDeriv n (fun x => f x / (1 - x)) 0 / n.factorial =
      ∑ m ∈ Finset.range n, weight m * (if Even m then a else b) := by
  let q (x : ℝ) := f x / (1 - x)
  have hq : ContDiffAt ℝ ∞ q 0 := hf.div (contDiffAt_const.sub contDiffAt_id) (by simp)
  have hprod : f =ᶠ[𝓝 0] fun x => q x - x * q x := by
    filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    dsimp [q]
    field_simp [(sub_pos.mpr hx).ne']
  change iteratedDeriv n q 0 / n.factorial = _
  induction n with
  | zero => simp [q, hf0]
  | succ n ih =>
    have heq := hprod.iteratedDeriv_eq (n + 1)
    rw [iteratedDeriv_fun_sub (hq.of_le (by simp))
      ((contDiffAt_fun_id.mul hq).of_le (by simp)), deriv_mul_coord n hq] at heq
    rw [Finset.sum_range_succ, ← ih, ← taylor_coeff, ← hd.iteratedDeriv_eq n,
      ← iteratedDeriv_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    linear_combination -heq

private lemma sum_pairs (F : ℕ → ℝ) (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k), F m =
      ∑ j ∈ Finset.range k, (F (2 * j) + F (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

end iteratedDeriv_arcsin_div_one_sub_doubleFactorial

open iteratedDeriv_arcsin_div_one_sub_doubleFactorial

/-- **Double-factorial sums as derivatives of arcsine quotients.** Let $n$ be a natural number.
If $n$ is odd, the $n$th derivative at $0$ of $x \mapsto \arcsin x / (1 - x)$ is
$$n! \sum_{j=0}^{(n-1)/2} \frac{(2j-1)!!}{(2j)!!\,(2j+1)},$$
and if $n \ge 2$ is even, the $n$th derivative at $0$ of $x \mapsto (\arcsin x)^2 / (2(1 - x))$ is
$$n! \sum_{j=0}^{(n-2)/2} \frac{(2j)!!}{(2j+1)!!\,(2j+2)},$$
where $(-1)!! = 1$ and $0!! = 1$.

These are the $n$th terms of the exponential generating functions of $\arcsin x / (1 - x)$
(OEIS A296726) and of $(\arcsin x)^2 / (2(1 - x))$ (OEIS A372324).

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4
(`jis-2025-25.2.3-thm-4`). -/
public theorem iteratedDeriv_arcsin_div_one_sub_doubleFactorial (n : ℕ) :
    (Odd n → iteratedDeriv n (fun x => arcsin x / (1 - x)) 0 =
      n.factorial * ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
        ((2 * j - 1).doubleFactorial : ℝ) / ((2 * j).doubleFactorial * (2 * j + 1))) ∧
    (Even n → 0 < n → iteratedDeriv n (fun x => arcsin x ^ 2 / (2 * (1 - x))) 0 =
      n.factorial * ∑ j ∈ Finset.range ((n - 2) / 2 + 1),
        ((2 * j).doubleFactorial : ℝ) / ((2 * j + 1).doubleFactorial * (2 * j + 2))) := by
  have ha : ContDiffAt ℝ ∞ arcsin 0 := contDiffAt_arcsin (by norm_num) (by norm_num)
  have hfac (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨k, rfl⟩
    have hd : deriv arcsin =ᶠ[𝓝 0] numeratorDeriv 1 0 :=
      Eventually.of_forall fun x => by simp [numeratorDeriv, deriv_arcsin]
    rw [mul_comm ((2 * k + 1).factorial : ℝ), ← div_eq_iff (hfac _),
      quotient_deriv ha arcsin_zero hd, Finset.sum_range_succ, sum_pairs,
      show (2 * k + 1 - 1) / 2 = k by omega, Finset.sum_range_succ]
    simp [weight]
  · rintro ⟨k, hk⟩ hn
    rw [← two_mul] at hk
    subst n
    let f (x : ℝ) := arcsin x ^ 2 / 2
    have hf : ContDiffAt ℝ ∞ f 0 := (ha.pow 2).div_const 2
    have hd : deriv f =ᶠ[𝓝 0] numeratorDeriv 0 1 := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with x hx
      have h := hasDerivAt_arcsin hx.1.ne' hx.2.ne
      rw [show deriv f x = _ from ((h.pow 2).div_const 2).deriv]
      simp [numeratorDeriv]
      ring
    have hquot : (fun x => arcsin x ^ 2 / (2 * (1 - x))) = fun x => f x / (1 - x) := by
      funext x
      exact (div_div _ _ _).symm
    rw [hquot, mul_comm ((2 * k).factorial : ℝ), ← div_eq_iff (hfac _),
      quotient_deriv hf (by simp [f]) hd, sum_pairs, show (2 * k - 2) / 2 + 1 = k by omega]
    simp [weight, add_assoc, one_add_one_eq_two]

end MetaMathlibExt

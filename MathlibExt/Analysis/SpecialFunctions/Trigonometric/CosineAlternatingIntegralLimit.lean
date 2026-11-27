/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CotangentLimit
import MathlibExt.Analysis.SpecialFunctions.Trigonometric.HalfPeriodSineSumEven

/-!
# Alternating cosine integrals for odd and even multipliers

For Lemma 12 of Dombrowski and Dresden, we telescope the endpoint values of the
antiderivative, then use the sine sums for the odd moduli `2 * m ± 1`. The two
cotangents in the odd half-multiplier case must be taken to the limit together.

Lemma 11 (`tendsto_sum_integral_cos_sub_cos_even_odd`), for an odd multiplier `q`, follows from
Lemma 12 for the multiplier `2 * q` instead of repeating the paper's argument: the substitution
`x = 2 * y` halves the grids `2 * ℓ * π / (2 * m ± 1)` and doubles the multiplier, so the sum is
twice the sum of Lemma 12, which tends to `16 / ((2 * q) ^ 2 * π)` since `2 * q ≡ 2 (mod 4)`.
-/

namespace MetaMathlibExt

open Real Filter Topology

namespace tendsto_sum_integral_cos_sub_cos_even_even

private noncomputable def primitive (q k x : ℝ) : ℝ :=
  sin (q * x) / q - sin (q * k * x) / (q * k)

private lemma integral_eq_primitive_sub {q k : ℝ} (hq : q ≠ 0) (hk : k ≠ 0) (a b : ℝ) :
    (∫ x in a..b, (cos (q * x) - cos (q * k * x))) = primitive q k b - primitive q k a := by
  have hcos (c x : ℝ) (hc : c ≠ 0) :
      HasDerivAt (fun t : ℝ => sin (c * t) / c) (cos (c * x)) x := by
    simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ hc] using
      (((hasDerivAt_id x).const_mul c).sin.div_const c)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (hcos q x hq).sub (hcos (q * k) x (mul_ne_zero hq hk)))
    ((by fun_prop : Continuous (fun x : ℝ => cos (q * x) - cos (q * k * x))).intervalIntegrable a b)

private lemma primitive_succ_grid (r l : ℕ) {k : ℝ} (hk : k ≠ 0) (hp : k + 1 ≠ 0) :
    primitive (2 * r) k (l * π / (k + 1)) =
      (1 / (2 * r)) * (1 / k + 1) * sin (r * l * 2 * π / (k + 1)) := by
  have hphase : 2 * (r : ℝ) * k * (l * π / (k + 1)) =
      -(r * l * 2 * π / (k + 1)) + ((r * l : ℕ) : ℝ) * (2 * π) := by
    push_cast
    field_simp
    ring
  rw [primitive, hphase, sin_add_nat_mul_two_pi, sin_neg,
    show 2 * (r : ℝ) * (l * π / (k + 1)) = r * l * 2 * π / (k + 1) by ring]
  simp only [div_eq_mul_inv]
  field_simp
  ring

private lemma primitive_pred_grid (r l : ℕ) {k : ℝ} (hk : k ≠ 0) (hm : k - 1 ≠ 0) :
    primitive (2 * r) k (l * π / (k - 1)) =
      (1 / (2 * r)) * (1 - 1 / k) * sin (r * l * 2 * π / (k - 1)) := by
  have hphase : 2 * (r : ℝ) * k * (l * π / (k - 1)) =
      r * l * 2 * π / (k - 1) + ((r * l : ℕ) : ℝ) * (2 * π) := by
    push_cast
    field_simp
    ring
  rw [primitive, hphase, sin_add_nat_mul_two_pi,
    show 2 * (r : ℝ) * (l * π / (k - 1)) = r * l * 2 * π / (k - 1) by ring]
  simp only [div_eq_mul_inv]
  field_simp

-- Keep the last value on the minus grid separate, so the remaining sum has length `m - 1`.
private lemma sum_alternating_endpoints (A B : ℕ → ℝ) (n : ℕ) :
    (∑ l ∈ Finset.Icc 1 (n + 1), (A l - B (l - 1) - (B l - A l))) =
      2 * (∑ l ∈ Finset.Icc 1 (n + 1), A l) -
      2 * (∑ l ∈ Finset.Icc 1 n, B l) - B 0 - B (n + 1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (b := n + 1) (by omega) (fun l => A l - B (l - 1) - (B l - A l)),
      ih, Finset.sum_Icc_succ_top (b := n + 1) (by omega) A,
      Finset.sum_Icc_succ_top (b := n) (by omega) B]
    simp only [Nat.add_sub_cancel]
    ring

private noncomputable def halfSum (r N : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (r * l * 2 * π / N)

private noncomputable def weightedHalfSums (r m : ℕ) : ℝ :=
  (1 / (2 * m : ℝ) - 1) * halfSum r (2 * m - 1) +
    (1 / (2 * m : ℝ) + 1) * halfSum r (2 * m + 1)

-- Lemma 6 is applied after the truncation of the minus-grid sum.
private lemma alternating_eq (r m : ℕ) (hr : r ≠ 0) (hm : 1 ≤ m) :
    (∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * π / ((2 * m : ℝ) - 1))..((l : ℝ) * π / ((2 * m : ℝ) + 1)),
          (cos ((2 * r : ℝ) * x) - cos ((2 * r : ℝ) * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * π / ((2 * m : ℝ) + 1))..((l : ℝ) * π / ((2 * m : ℝ) - 1)),
          (cos ((2 * r : ℝ) * x) - cos ((2 * r : ℝ) * (2 * m : ℝ) * x)))) =
      (2 / (2 * r)) * weightedHalfSums r m -
        primitive (2 * r) (2 * m) (m * π / ((2 * m : ℝ) - 1)) := by
  have hr' : (2 * r : ℝ) ≠ 0 := by positivity
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk : (2 * m : ℝ) ≠ 0 := by positivity
  have hp : (2 * m : ℝ) + 1 ≠ 0 := by positivity
  have hn : (2 * m : ℝ) - 1 ≠ 0 := by linarith
  let A (l : ℕ) := primitive (2 * r) (2 * m) (l * π / ((2 * m : ℝ) + 1))
  let B (l : ℕ) := primitive (2 * r) (2 * m) (l * π / ((2 * m : ℝ) - 1))
  trans (∑ l ∈ Finset.Icc 1 m, (A l - B (l - 1) - (B l - A l)))
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [integral_eq_primitive_sub hr' hk, integral_eq_primitive_sub hr' hk]
    dsimp [A, B]
    rw [Nat.cast_sub (Finset.mem_Icc.mp hl).1, Nat.cast_one]
  have hA : (∑ l ∈ Finset.Icc 1 m, A l) =
      1 / (2 * r) * (1 / (2 * m : ℝ) + 1) * halfSum r (2 * m + 1) := by
    rw [halfSum, show (2 * m + 1 - 1) / 2 = m by omega, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    dsimp only [A]
    rw [primitive_succ_grid r l hk hp]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hB : (∑ l ∈ Finset.Icc 1 (m - 1), B l) =
      1 / (2 * r) * (1 - 1 / (2 * m : ℝ)) * halfSum r (2 * m - 1) := by
    rw [halfSum, show (2 * m - 1 - 1) / 2 = m - 1 by omega, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    dsimp only [B]
    rw [primitive_pred_grid r l hk hn, Nat.cast_sub (show 1 ≤ 2 * m by omega)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have htel := sum_alternating_endpoints A B (m - 1)
  rw [Nat.sub_add_cancel hm, hA, hB, show B 0 = 0 by simp [B, primitive]] at htel
  rw [htel, weightedHalfSums]
  change _ = _ - B m
  ring

private lemma tendsto_twice : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
  tendsto_atTop_mono (fun m => show m ≤ 2 * m by omega) tendsto_id

private lemma tendsto_one_div_natCast : Tendsto (fun k : ℕ => 1 / (k : ℝ)) atTop (𝓝 0) :=
  tendsto_natCast_atTop_atTop.const_div_atTop 1

private lemma tendsto_div_pred (x : ℝ) :
    Tendsto (fun k : ℕ => x / ((k : ℝ) - 1)) atTop (𝓝 0) := by
  simpa only [sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop).const_div_atTop x

private lemma tendsto_div_succ (x : ℝ) :
    Tendsto (fun k : ℕ => x / ((k : ℝ) + 1)) atTop (𝓝 0) :=
  (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).const_div_atTop x

private lemma tendsto_primitive_endpoint (r : ℕ) :
    Tendsto (fun m : ℕ => primitive (2 * r) (2 * m) (m * π / ((2 * m : ℝ) - 1))) atTop (𝓝 0) := by
  have ha : Tendsto (fun m : ℕ => r * π + r * π / ((2 * m : ℝ) - 1)) atTop (𝓝 (r * π)) := by
    simpa [Function.comp_def] using
      ((tendsto_div_pred (r * π)).comp tendsto_twice |>.const_add (r * π))
  have hs : Tendsto (fun m : ℕ => sin (r * π + r * π / ((2 * m : ℝ) - 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sin_nat_mul_pi] using (continuous_sin.tendsto _).comp ha
  have hw : Tendsto (fun m : ℕ => (1 / (2 * r : ℝ)) * (1 - 1 / (2 * m : ℝ))) atTop
      (𝓝 (1 / (2 * r))) := by
    simpa [Function.comp_def] using
      ((tendsto_one_div_natCast.comp tendsto_twice).const_sub 1).const_mul (1 / (2 * r : ℝ))
  have h := hw.mul hs
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk : (2 * m : ℝ) ≠ 0 := by positivity
  have hn : (2 * m : ℝ) - 1 ≠ 0 := by linarith
  have hphase : (r : ℝ) * m * 2 * π / ((2 * m : ℝ) - 1) =
      r * π + r * π / ((2 * m : ℝ) - 1) := by
    apply (div_eq_iff hn).2
    rw [add_mul, div_mul_cancel₀ _ hn]
    ring
  rw [primitive_pred_grid r m hk hn, hphase]

private lemma tendsto_weighted_half_sums (r : ℕ) (hr : r ≠ 0) :
    Tendsto (weightedHalfSums r) atTop (𝓝 (if Even r then 0 else 2 / ((r : ℝ) * π / 2))) := by
  let trig := if Even r then tan else cot
  let c : ℝ := if Even r then -(1 / 2) else 1 / 2
  let x : ℝ := (r : ℝ) * π / 2
  let w (k : ℕ) := c * ((1 / (k : ℝ) - 1) * trig (x / ((k : ℝ) - 1)) +
    (1 / (k : ℝ) + 1) * trig (x / ((k : ℝ) + 1)))
  have hw : Tendsto w atTop (𝓝 (if Even r then 0 else 2 / x)) := by
    by_cases he : Even r
    · have ht : ContinuousAt tan 0 := by
        rw [show tan = sin / cos from funext tan_eq_sin_div_cos]
        exact continuous_sin.continuousAt.div continuous_cos.continuousAt (by simp)
      have ha := ht.tendsto.comp (tendsto_div_pred x)
      have hb := ht.tendsto.comp (tendsto_div_succ x)
      simpa [w, trig, c, he, Function.comp_def] using
        ((((tendsto_one_div_natCast.sub_const 1).mul ha).add
          ((tendsto_one_div_natCast.add_const 1).mul hb)).const_mul (-(1 / 2) : ℝ))
    · have hx : x ≠ 0 := by dsimp [x]; positivity
      have key := (tendsto_cot_div_pred_add_cot_div_succ hx).const_mul (1 / 2)
      have hl : (1 / 2 : ℝ) * (4 / x) = 2 / x := by ring
      simpa only [hl, w, c, trig, ite_eq_right he] using key
  refine (hw.comp tendsto_twice).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hNp : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hNm : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  have hsum (N : ℕ) (hN : Odd N) : halfSum r N = c * trig (x / N) := by
    rw [halfSum, sum_sin_two_pi_mul_div_of_odd hN r]
    rw [show (r : ℝ) * π / (2 * N) = r * π / 2 / N by ring]
    by_cases he : Even r <;> simp [c, trig, he, x]
  rw [weightedHalfSums, hsum _ hNm, hsum _ hNp, Nat.cast_sub (show 1 ≤ 2 * m by omega)]
  simp only [Function.comp_apply, w, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    mul_add]
  ac_rfl

end tendsto_sum_integral_cos_sub_cos_even_even

open tendsto_sum_integral_cos_sub_cos_even_even in
/-- **Alternating integral sums of $\cos qx - \cos qkx$ for even $q$ and even $k$.** Let $q$ be an
even natural number, for each natural number $m$ put $k = 2m$, and let
$f(x) = \cos(qx) - \cos(qkx)$. Then, as $m \to \infty$,
$$\sum_{\ell=1}^{m} \left(\int_{(\ell-1)\pi/(k-1)}^{\ell\pi/(k+1)} f(x)\,dx -
\int_{\ell\pi/(k+1)}^{\ell\pi/(k-1)} f(x)\,dx\right)$$
tends to $0$ if $q \equiv 0 \pmod 4$ and to $16/(q^2\pi)$ if $q \equiv 2 \pmod 4$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 12
(`jis-2025-25.2.3-lem-12`). -/
public theorem tendsto_sum_integral_cos_sub_cos_even_even {q : ℕ} (hq : Even q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * π / ((2 * m : ℝ) - 1))..((l : ℝ) * π / ((2 * m : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * π / ((2 * m : ℝ) + 1))..((l : ℝ) * π / ((2 * m : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x)))) atTop
      (𝓝 (if q % 4 = 0 then 0 else 16 / ((q : ℝ) ^ 2 * π))) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = 2 * r := by
    obtain ⟨r, hr⟩ := hq
    exact ⟨r, by omega⟩
  by_cases hr : r = 0
  · subst r
    simp
  have hparity : (2 * r) % 4 = 0 ↔ Even r := by
    rw [Nat.even_iff]
    omega
  have hlim := ((tendsto_weighted_half_sums r hr).const_mul (2 / (2 * r : ℝ))).sub
    (tendsto_primitive_endpoint r)
  rw [show (2 / (2 * r : ℝ)) * (if Even r then 0 else 2 / ((r : ℝ) * π / 2)) - 0 =
      (if (2 * r) % 4 = 0 then 0 else 16 / ((2 * r : ℝ) ^ 2 * π)) by
    simp only [hparity]
    split_ifs
    · ring
    · have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
      field_simp [pi_ne_zero]
      ring] at hlim
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (alternating_eq r m hr hm).symm

/-- **Alternating integral sums of $\cos qx - \cos qkx$ for odd $q$ and even $k$.** Let $q$ be an
odd natural number, for each natural number $m$ put $k = 2m$, and let
$f(x) = \cos(qx) - \cos(qkx)$. Then, as $m \to \infty$,
$$\sum_{\ell=1}^{m} \left(\int_{2(\ell-1)\pi/(k-1)}^{2\ell\pi/(k+1)} f(x)\,dx -
\int_{2\ell\pi/(k+1)}^{2\ell\pi/(k-1)} f(x)\,dx\right) \to \frac{8}{q^2\pi}.$$

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 11
(`jis-2025-25.2.3-lem-11`). -/
public theorem tendsto_sum_integral_cos_sub_cos_even_odd {q : ℕ} (hq : Odd q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * 2 * π / ((2 * m : ℝ) - 1))..((l : ℝ) * 2 * π / ((2 * m : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * 2 * π / ((2 * m : ℝ) + 1))..((l : ℝ) * 2 * π / ((2 * m : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x)))) atTop
      (𝓝 (8 / ((q : ℝ) ^ 2 * π))) := by
  -- The substitution `x = 2 y` turns each integral into twice one of Lemma 12 for `2 q`.
  have hsub (m : ℕ) (s t D E : ℝ) :
      (∫ x in (s * 2 * π / D)..(t * 2 * π / E), (cos (q * x) - cos (q * (2 * m : ℝ) * x))) =
        2 * ∫ y in (s * π / D)..(t * π / E),
          (cos (((2 * q : ℕ) : ℝ) * y) - cos (((2 * q : ℕ) : ℝ) * (2 * m : ℝ) * y)) := by
    rw [show s * 2 * π / D = 2 * (s * π / D) by ring, show t * 2 * π / E = 2 * (t * π / E) by ring,
      ← intervalIntegral.smul_integral_comp_mul_left, smul_eq_mul]
    refine congrArg (2 * ·) (intervalIntegral.integral_congr fun y _ => ?_)
    push_cast
    ring_nf
  have h := (tendsto_sum_integral_cos_sub_cos_even_even (even_two_mul q)).const_mul 2
  -- As `q` is odd, `2 q ≡ 2 (mod 4)` and the limit is `2 * (16 / ((2 q) ^ 2 π)) = 8 / (q ^ 2 π)`.
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.pos.ne'
  rw [ite_eq_right (by obtain ⟨j, rfl⟩ := hq; omega),
    show (2 : ℝ) * (16 / (((2 * q : ℕ) : ℝ) ^ 2 * π)) = 8 / ((q : ℝ) ^ 2 * π) by
      push_cast
      field_simp
      ring] at h
  refine h.congr fun m => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsub, hsub, mul_sub]

end MetaMathlibExt

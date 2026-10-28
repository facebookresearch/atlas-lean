/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Fourier partial sums of the sawtooth and of piecewise smooth functions

The sawtooth `x ↦ {x} - 1/2` has Fourier series `-∑_{k ≥ 1} sin (2 π k x) / (π k)`. We prove
the quantitative convergence of its partial sums away from the integers:

`|{x} - 1/2 + ∑_{k = 1}^{M} sin (2 π k x) / (π k)| ≤ 1 / (2 π M ‖x‖)`,

where `‖x‖` is the distance from `x` to the nearest integer. The proof writes the partial sum
through the Dirichlet kernel and applies the second mean value theorem for integrals.

Integrating by parts against the sawtooth, we deduce the behaviour of the symmetric Fourier
partial sums of a function `f` on `[0, 1]` at the jump of its periodic extension: if `f` is
continuous on `[0, 1]` and `|f'| ≤ K` on `(0, 1)`, then for `M ≥ 2`

`|∑_{|m| ≤ M} f̂(m) - (f(0) + f(1)) / 2| ≤ 20 K log M / M`.

## Main statements

* `abs_fract_sub_half_add_sum_sin_le`: the truncated Fourier expansion of the sawtooth.
* `norm_sum_fourierCoeffOn_sub_average_le`: the symmetric Fourier partial sums at the endpoint
  of `[0, 1]` approach the average of the endpoint values.
-/

@[expose] public section

open Finset Real MeasureTheory

/-- The bound on `(0, 1/2]`, via the Dirichlet kernel and the second mean value theorem. -/
private lemma abs_sub_half_add_sum_sin_le_of_le_half {M : ℕ} (hM : 0 < M) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1 / 2) :
    |s - 1 / 2 + ∑ k ∈ range M, Real.sin (2 * π * ((k : ℝ) + 1) * s) / (π * ((k : ℝ) + 1))| ≤
      1 / (2 * π * M * s) := by
  set K : ℝ := (2 * (M : ℝ) + 1) * π with hKdef
  have hK : 0 < K := by positivity
  set F : ℝ → ℝ := fun u ↦ u + ∑ k ∈ range M,
    Real.sin (2 * π * ((k : ℝ) + 1) * u) / (π * ((k : ℝ) + 1)) with hFdef
  set F' : ℝ → ℝ := fun u ↦
    1 + ∑ k ∈ range M, 2 * Real.cos (2 * π * ((k : ℝ) + 1) * u) with hF'def
  have hF : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    apply (hasDerivAt_id u).add
    apply HasDerivAt.fun_sum
    intro k _
    have := (((hasDerivAt_id' u).const_mul (2 * π * ((k : ℝ) + 1))).sin).div_const
      (π * ((k : ℝ) + 1))
    exact this.congr_deriv (by rw [div_eq_iff (by positivity)]; ring)
  -- The Dirichlet kernel identity.
  have dir : ∀ N : ℕ, ∀ u : ℝ,
      (1 + ∑ k ∈ range N, 2 * Real.cos (2 * π * ((k : ℝ) + 1) * u)) * Real.sin (π * u) =
        Real.sin ((2 * (N : ℝ) + 1) * π * u) := by
    intro N u
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ← add_assoc, add_mul, ih]
      push_cast
      rw [show (2 * ((n : ℝ) + 1) + 1) * π * u = 2 * π * ((n : ℝ) + 1) * u + π * u by ring,
        show (2 * (n : ℝ) + 1) * π * u = 2 * π * ((n : ℝ) + 1) * u - π * u by ring,
        Real.sin_add, Real.sin_sub]
      ring
  have hsinpos : ∀ u, 0 < u → u ≤ 1 / 2 → 0 < Real.sin (π * u) := fun u h0 h1 ↦
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
  have hFTC : ∫ u in s..1 / 2, F' u = F (1 / 2) - F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hF u)
      (by apply Continuous.intervalIntegrable; simp only [hF'def]; fun_prop)
  have hcongr : ∫ u in s..1 / 2, F' u = ∫ u in s..1 / 2,
      (fun u ↦ 1 / Real.sin (π * u)) u * (fun u ↦ Real.sin (K * u)) u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hs1] at hu
    have hp := hsinpos u (by linarith [hu.1]) hu.2
    have := dir M u
    simp only
    rw [show K * u = (2 * (M : ℝ) + 1) * π * u by rw [hKdef], ← this, hF'def, one_div,
      inv_mul_eq_div, mul_div_assoc, div_self hp.ne', mul_one]
  obtain ⟨ξ, hξ, hEq⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
    (f := fun u ↦ 1 / Real.sin (π * u)) (g := fun u ↦ Real.sin (K * u)) hs1
    (by have := hsinpos (1 / 2) (by norm_num) le_rfl; positivity)
    (by
      intro a ha b hb hab
      have h1 := hsinpos a (by linarith [ha.1]) ha.2
      simp only
      apply one_div_le_one_div_of_le h1
      apply Real.strictMonoOn_sin.monotoneOn
      · constructor <;> nlinarith [pi_pos, ha.1, ha.2]
      · constructor <;> nlinarith [pi_pos, hb.1, hb.2]
      · nlinarith [pi_pos])
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hI : |∫ u in s..ξ, Real.sin (K * u)| ≤ 2 / K := by
    rw [intervalIntegral.integral_comp_mul_left (fun x ↦ Real.sin x) hK.ne', integral_sin,
      smul_eq_mul, abs_mul, abs_inv, abs_of_pos hK, div_eq_inv_mul]
    gcongr
    rw [abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (K * s), Real.cos_le_one (K * s),
      Real.neg_one_le_cos (K * ξ), Real.cos_le_one (K * ξ)]
  have hFhalf : F (1 / 2) = 1 / 2 := by
    simp only [hFdef]
    rw [sum_eq_zero, add_zero]
    intro k _
    rw [show 2 * π * ((k : ℝ) + 1) * (1 / 2) = ((k + 1 : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, zero_div]
  have hg : s - 1 / 2 + ∑ k ∈ range M, Real.sin (2 * π * ((k : ℝ) + 1) * s) /
      (π * ((k : ℝ) + 1)) = F s - F (1 / 2) := by
    rw [hFhalf]; simp only [hFdef]; ring
  have hss := hsinpos s hs0 hs1
  have hjordan : 2 * s ≤ Real.sin (π * s) := by
    have := Real.mul_le_sin (x := π * s) (by positivity) (by nlinarith [pi_pos])
    rwa [show 2 / π * (π * s) = 2 * s by field_simp] at this
  rw [hg, abs_sub_comm, ← hFTC, hcongr, hEq, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sin (π * s))]
  calc 1 / Real.sin (π * s) * |∫ u in s..ξ, Real.sin (K * u)|
      ≤ 1 / (2 * s) * (2 / K) := by gcongr
    _ = 1 / (s * K) := by field_simp
    _ ≤ 1 / (2 * π * M * s) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hKdef]; nlinarith [pi_pos]

/-- The partial sums `s - 1/2 + ∑_{k ≤ M} sin (2 π k s) / (π k)` are odd about `1/2`. -/
private lemma sub_half_add_sum_sin_one_sub (M : ℕ) (t : ℝ) :
    (1 - t) - 1 / 2 + ∑ k ∈ range M, Real.sin (2 * π * ((k : ℝ) + 1) * (1 - t)) /
        (π * ((k : ℝ) + 1)) =
      -(t - 1 / 2 + ∑ k ∈ range M, Real.sin (2 * π * ((k : ℝ) + 1) * t) /
        (π * ((k : ℝ) + 1))) := by
  have : ∀ k : ℕ, Real.sin (2 * π * ((k : ℝ) + 1) * (1 - t)) =
      -Real.sin (2 * π * ((k : ℝ) + 1) * t) := by
    intro k
    rw [show 2 * π * ((k : ℝ) + 1) * (1 - t) =
        -(2 * π * ((k : ℝ) + 1) * t) + (((k : ℤ) + 1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      Real.sin_add_int_mul_two_pi, Real.sin_neg]
  simp only [this, neg_div, sum_neg_distrib]
  ring

/-- **The truncated Fourier expansion of the sawtooth.** For `M ≥ 1` and `x ∉ ℤ`,
`|{x} - 1/2 + ∑_{k = 1}^{M} sin (2 π k x) / (π k)| ≤ 1 / (2 π M ‖x‖)`, where `‖x‖` is the
distance from `x` to the nearest integer. -/
theorem abs_fract_sub_half_add_sum_sin_le {x : ℝ} {M : ℕ} (hM : 0 < M) (hx : Int.fract x ≠ 0) :
    |Int.fract x - 1 / 2 + ∑ k ∈ range M,
        Real.sin (2 * π * ((k : ℝ) + 1) * x) / (π * ((k : ℝ) + 1))| ≤
      1 / (2 * π * M * ‖(x : AddCircle (1 : ℝ))‖) := by
  set t := Int.fract x with ht
  have ht0 : 0 < t := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
  have ht1 : t < 1 := Int.fract_lt_one x
  have hper : ∀ k : ℕ, Real.sin (2 * π * ((k : ℝ) + 1) * x) =
      Real.sin (2 * π * ((k : ℝ) + 1) * t) := by
    intro k
    rw [show 2 * π * ((k : ℝ) + 1) * x = 2 * π * ((k : ℝ) + 1) * t +
        (((k : ℤ) + 1) * ⌊x⌋ : ℤ) * (2 * π) by
      rw [ht, ← Int.self_sub_floor]; push_cast; ring, Real.sin_add_int_mul_two_pi]
  simp only [hper]
  have hpos : 0 < ‖(x : AddCircle (1 : ℝ))‖ := by
    refine norm_pos_iff.2 fun h ↦ hx ?_
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h
    rw [ht, ← hn]; simp
  have hle : ∀ n : ℤ, ‖(x : AddCircle (1 : ℝ))‖ ≤ |x - n| := by
    intro n
    rw [AddCircle.norm_eq]; simp only [inv_one, one_mul, mul_one]
    exact round_le x n
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hfin : ∀ s : ℝ, ‖(x : AddCircle (1 : ℝ))‖ ≤ s →
      1 / (2 * π * M * s) ≤ 1 / (2 * π * M * ‖(x : AddCircle (1 : ℝ))‖) := by
    intro s hs
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  rcases le_or_gt t (1 / 2) with h | h
  · refine (abs_sub_half_add_sum_sin_le_of_le_half hM ht0 h).trans (hfin t ?_)
    have := hle ⌊x⌋
    rwa [Int.self_sub_floor, ← ht, abs_of_pos ht0] at this
  · have hsym := sub_half_add_sum_sin_one_sub M (1 - t)
    rw [sub_sub_cancel] at hsym
    rw [hsym, abs_neg]
    refine (abs_sub_half_add_sum_sin_le_of_le_half hM (by linarith) (by linarith)).trans
      (hfin (1 - t) ?_)
    have := hle (⌊x⌋ + 1)
    rwa [show x - ((⌊x⌋ + 1 : ℤ) : ℝ) = -(1 - t) by rw [ht, ← Int.self_sub_floor]; push_cast; ring,
      abs_neg, abs_of_pos (by linarith)] at this

/-- The symmetric punctured sum `∑_{0 < |m| ≤ N} h m` as a sum over the pairs `±(k + 1)`. -/
private lemma sum_Icc_neg_sdiff_zero_eq_sum_range {E : Type*} [AddCommMonoid E] (h : ℤ → E)
    (N : ℕ) :
    ∑ m ∈ Icc (-(N : ℤ)) (N : ℤ) \ {0}, h m =
      ∑ k ∈ range N, (h ((k : ℤ) + 1) + h (-((k : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hset : Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) \ {0} =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Icc (-(n : ℤ)) (n : ℤ) \ {0})) := by
      ext m; simp only [mem_sdiff, mem_Icc, mem_singleton, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_range_succ,
      add_comm _ (h _ + h _), add_assoc]

/-- **Fourier partial sums at the endpoint.** Let `f : ℝ → ℂ` be continuous on `[0, 1]`, with
derivative `f'` on `(0, 1)` satisfying `‖f'‖ ≤ K`. Then the symmetric partial sums of the
Fourier series of `f` on `[0, 1]`, evaluated at `0`, approach the average of the endpoint
values: for `M ≥ 2`,
`‖∑_{|m| ≤ M} f̂(m) - (f(0) + f(1)) / 2‖ ≤ 20 K log M / M`. -/
theorem norm_sum_fourierCoeffOn_sub_average_le {f f' : ℝ → ℂ} {K : ℝ} {M : ℕ}
    (hfc : ContinuousOn f (Set.Icc 0 1)) (hf : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hK : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ‖f' x‖ ≤ K) (hM : 2 ≤ M) :
    ‖∑ m ∈ Icc (-(M : ℤ)) (M : ℤ), fourierCoeffOn zero_lt_one f m - (f 0 + f 1) / 2‖ ≤
      20 * K * Real.log M / M := by
  have hfd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (deriv f x) x := fun x hx ↦
    (hf x hx).differentiableAt.hasDerivAt
  have hKd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ‖deriv f x‖ ≤ K := fun x hx ↦ (hf x hx).deriv ▸ hK x hx
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK (1 / 2) ⟨by norm_num, by norm_num⟩)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  -- The Fourier coefficients as integrals against `e(m x)`.
  have hcoef : ∑ m ∈ Icc (-(M : ℤ)) (M : ℤ), fourierCoeffOn zero_lt_one f m =
      ∑ m ∈ Icc (-(M : ℤ)) (M : ℤ),
        ∫ x in (0 : ℝ)..1, f x * Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ)) := by
    refine sum_nbij' (fun m ↦ -m) (fun m ↦ -m) (fun m hm ↦ ?_) (fun m hm ↦ ?_)
      (fun m _ ↦ neg_neg m) (fun m _ ↦ neg_neg m) (fun m _ ↦ ?_)
    · simp only [mem_Icc] at hm ⊢; omega
    · simp only [mem_Icc] at hm ⊢; omega
    · rw [fourierCoeffOn_eq_integral]
      simp only [sub_zero, div_one, one_smul, fourier_coe_apply, smul_eq_mul]
      refine intervalIntegral.integral_congr fun x _ ↦ ?_
      simp only [Complex.ofReal_one, div_one, Int.cast_neg]
      ring
  -- The real form `g` of the kernel `D`.
  set g : ℝ → ℝ := fun s ↦ s - 1 / 2 + ∑ k ∈ range M,
    Real.sin (2 * π * ((k : ℝ) + 1) * s) / (π * ((k : ℝ) + 1)) with hgdef
  set D : ℝ → ℂ := fun x ↦ ((x - 1 / 2 : ℝ) : ℂ) + ∑ m ∈ Icc (-(M : ℤ)) (M : ℤ) \ {0},
    Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ)) / (2 * π * Complex.I * (m : ℂ))
    with hDdef
  have hpair : ∀ (x : ℝ) (k : ℕ),
      Complex.exp (2 * π * Complex.I * (((k : ℤ) + 1 : ℤ) : ℂ) * (x : ℂ)) /
          (2 * π * Complex.I * (((k : ℤ) + 1 : ℤ) : ℂ)) +
        Complex.exp (2 * π * Complex.I * ((-((k : ℤ) + 1) : ℤ) : ℂ) * (x : ℂ)) /
          (2 * π * Complex.I * ((-((k : ℤ) + 1) : ℤ) : ℂ)) =
      ((Real.sin (2 * π * ((k : ℝ) + 1) * x) / (π * ((k : ℝ) + 1)) : ℝ) : ℂ) := by
    intro x k
    set θ : ℝ := 2 * π * ((k : ℝ) + 1) * x with hθ
    have e1 : Complex.exp (2 * π * Complex.I * (((k : ℤ) + 1 : ℤ) : ℂ) * (x : ℂ)) =
        (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
      rw [show 2 * π * Complex.I * (((k : ℤ) + 1 : ℤ) : ℂ) * (x : ℂ) = (θ : ℂ) * Complex.I by
        rw [hθ]; push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have e2 : Complex.exp (2 * π * Complex.I * ((-((k : ℤ) + 1) : ℤ) : ℂ) * (x : ℂ)) =
        (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
      rw [show 2 * π * Complex.I * ((-((k : ℤ) + 1) : ℤ) : ℂ) * (x : ℂ)
          = ((-θ : ℝ) : ℂ) * Complex.I by rw [hθ]; push_cast; ring, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [e1, e2]
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_pos.ne'
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast
    field_simp
    ring_nf
  have hDg : ∀ x, D x = (g x : ℂ) := by
    intro x
    simp only [hDdef, hgdef]
    rw [sum_Icc_neg_sdiff_zero_eq_sum_range (fun m : ℤ ↦
      Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ)) / (2 * π * Complex.I * (m : ℂ))) M]
    simp only [hpair]
    push_cast
    ring
  -- The derivative of `D` is the full exponential sum.
  have hD' : ∀ x : ℝ, HasDerivAt D (∑ m ∈ Icc (-(M : ℤ)) (M : ℤ),
      Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ))) x := by
    intro x
    rw [← add_sum_erase _ _ (by simp : (0 : ℤ) ∈ Icc (-(M : ℤ)) (M : ℤ)),
      ← sdiff_singleton_eq_erase]
    have h0 : Complex.exp (2 * π * Complex.I * ((0 : ℤ) : ℂ) * (x : ℂ)) = 1 := by simp
    rw [h0]
    apply HasDerivAt.add
    · simpa using ((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).ofReal_comp
    · apply HasDerivAt.fun_sum
      intro m hm
      have hm0 : (m : ℂ) ≠ 0 := by
        have : m ≠ 0 := by simpa using (mem_sdiff.1 hm).2
        exact_mod_cast this
      have hc : (2 * π * Complex.I * (m : ℂ)) ≠ 0 := by
        have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_pos.ne'
        simp [hpi, hm0, Complex.I_ne_zero]
      have h1 := (((hasDerivAt_id x).ofReal_comp).const_mul
        (2 * π * Complex.I * (m : ℂ))).cexp.div_const (2 * π * Complex.I * (m : ℂ))
      simp only [id, Complex.ofReal_one, mul_one] at h1
      rw [mul_div_assoc, div_self hc, mul_one] at h1
      exact h1
  -- Endpoint values.
  have hg0 : g 0 = -1 / 2 := by simp [hgdef]; norm_num
  have hg1 : g 1 = 1 / 2 := by
    simp only [hgdef]
    rw [sum_eq_zero, add_zero]
    · norm_num
    intro k _
    rw [show 2 * π * ((k : ℝ) + 1) * 1 = ((2 * (k + 1) : ℕ) : ℝ) * π by push_cast; ring,
      Real.sin_nat_mul_pi, zero_div]
  -- Integrability and integration by parts.
  have hintC : IntervalIntegrable (deriv f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    refine Measure.integrableOn_of_bounded (M := K) (by simp)
      (measurable_deriv f).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun x hx ↦ hKd x hx
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun x ↦ (hD' x).continuousAt
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := 0) (b := 1)
    (u := f) (u' := deriv f) (v := D)
    (v' := fun x ↦ ∑ m ∈ Icc (-(M : ℤ)) (M : ℤ),
      Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ)))
    (by rwa [hIcc]) hDc.continuousOn
    (fun x hx ↦ hfd x (by simpa using hx)) (fun x _ ↦ hD' x) hintC
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hsum : ∑ m ∈ Icc (-(M : ℤ)) (M : ℤ), ∫ x in (0 : ℝ)..1,
        f x * Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ)) =
      ∫ x in (0 : ℝ)..1, f x * ∑ m ∈ Icc (-(M : ℤ)) (M : ℤ),
        Complex.exp (2 * π * Complex.I * (m : ℂ) * (x : ℂ)) := by
    rw [← intervalIntegral.integral_finsetSum]
    · congr 1; ext x; rw [mul_sum]
    · intro m _
      exact ((hIcc ▸ hfc).mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable
  -- Pointwise bounds on `g`.
  have hsmallb : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → |g y| ≤ 1 / 2 + 2 * M * y := by
    intro y hy0 hy1
    simp only [hgdef]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_le]; constructor <;> linarith
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range M, |Real.sin (2 * π * ((k : ℝ) + 1) * y) / (π * ((k : ℝ) + 1))|
        ≤ ∑ k ∈ range M, 2 * y := by
          apply sum_le_sum
          intro k _
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < π * ((k : ℝ) + 1)),
            div_le_iff₀ (by positivity)]
          refine (Real.abs_sin_le_abs).trans (le_of_eq ?_)
          rw [abs_of_nonneg (by positivity)]; ring
      _ = 2 * M * y := by simp; ring
  have hlargeb : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → |g y| ≤ 1 / (M * y) := by
    intro y hy0 hy1
    refine (abs_sub_half_add_sum_sin_le_of_le_half (by omega) hy0 hy1).trans
      (one_div_le_one_div_of_le (by positivity) ?_)
    nlinarith [Real.two_le_pi, mul_pos hMpos hy0]
  have hhalf : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 → |g y| ≤ 5 / (1 + M * y) := by
    intro y hy0 hy1
    rcases le_or_gt ((M : ℝ) * y) 1 with hMy | hMy
    · refine (hsmallb y hy0 (by linarith)).trans ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hMpos.le hy0]
    · have hy : 0 < y := by
        by_contra hc; push Not at hc; nlinarith
      refine (hlargeb y hy hy1).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hsym : ∀ x, g (1 - x) = -g x := fun t ↦ sub_half_add_sum_sin_one_sub M t
  have hgB : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |g x| ≤ 5 * (1 / (1 + M * x) + 1 / (1 + M * (1 - x))) := by
    rintro x ⟨hx0, hx1⟩
    have ha : 0 < 1 + (M : ℝ) * x := by positivity
    have hb : 0 < 1 + (M : ℝ) * (1 - x) := by
      have : 0 ≤ (M : ℝ) * (1 - x) := mul_nonneg hMpos.le (by linarith)
      linarith
    rcases le_total x (1 / 2) with h | h
    · have := hhalf x hx0 h
      have : 0 ≤ 1 / (1 + (M : ℝ) * (1 - x)) := by positivity
      rw [mul_add, ← mul_div_assoc, mul_one]
      linarith
    · have e : g x = -g (1 - x) := by rw [hsym, neg_neg]
      have := hhalf (1 - x) (by linarith) (by linarith)
      have : 0 ≤ 5 / (1 + (M : ℝ) * x) := by positivity
      rw [e, abs_neg, mul_add, ← mul_div_assoc, mul_one, ← mul_div_assoc 5 1, mul_one]
      linarith
  -- The two logarithmic integrals.
  have hpos1 : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 + (M : ℝ) * x := fun x hx ↦ by
    have := (hIcc ▸ hx).1; positivity
  have hpos2 : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 + (M : ℝ) * (1 - x) := fun x hx ↦ by
    have : 0 ≤ (M : ℝ) * (1 - x) := mul_nonneg hMpos.le (by linarith [(hIcc ▸ hx).2])
    linarith
  have hint1 : IntervalIntegrable (fun x : ℝ ↦ 1 / (1 + M * x)) volume 0 1 :=
    (continuousOn_const.div (by fun_prop) fun x hx ↦ (hpos1 x hx).ne').intervalIntegrable
  have hint2 : IntervalIntegrable (fun x : ℝ ↦ 1 / (1 + M * (1 - x))) volume 0 1 :=
    (continuousOn_const.div (by fun_prop) fun x hx ↦ (hpos2 x hx).ne').intervalIntegrable
  have hI1 : ∫ x in (0 : ℝ)..1, 1 / (1 + M * x) = Real.log (1 + M) / M := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ ↦ Real.log (1 + M * x) / M) (f' := fun x : ℝ ↦ 1 / (1 + M * x))
      (a := 0) (b := 1) (fun x hx ↦ by
        have h1 := ((((hasDerivAt_id x).const_mul (M : ℝ)).const_add 1).log
          (hpos1 x hx).ne').div_const (M : ℝ)
        simp only [id] at h1
        refine h1.congr_deriv ?_
        field_simp) hint1
    rw [this]; simp
  have hI2 : ∫ x in (0 : ℝ)..1, 1 / (1 + M * (1 - x)) = Real.log (1 + M) / M := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ ↦ -(Real.log (1 + M * (1 - x)) / M))
      (f' := fun x : ℝ ↦ 1 / (1 + M * (1 - x)))
      (a := 0) (b := 1) (fun x hx ↦ by
        have h1 := (((((hasDerivAt_id x).const_sub 1).const_mul (M : ℝ)).const_add 1).log
          (hpos2 x hx).ne').div_const (M : ℝ) |>.neg
        simp only [id] at h1
        refine h1.congr_deriv ?_
        field_simp) hint2
    rw [this]; simp
  have hL : Real.log (1 + M) ≤ 2 * Real.log M := by
    have := Real.log_le_log (by positivity) (show 1 + (M : ℝ) ≤ (M : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  rw [hcoef, hsum, hIBP, hDg 0, hDg 1, hg0, hg1]
  have hbint : IntervalIntegrable
      (fun x : ℝ ↦ K * (5 * (1 / (1 + M * x) + 1 / (1 + M * (1 - x))))) volume 0 1 :=
    ((hint1.add hint2).const_mul 5).const_mul K
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0 : ℝ) 1 →
      ‖deriv f x * D x‖ ≤ K * (5 * (1 / (1 + M * x) + 1 / (1 + M * (1 - x)))) := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with x hx1 hx
    have hxo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 (by simpa using hx1)⟩
    rw [norm_mul, hDg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hKd x hxo) (hgB x (Set.Ioo_subset_Icc_self hxo)) (abs_nonneg _) hK0
  calc _ = ‖-(∫ x in (0 : ℝ)..1, deriv f x * D x)‖ := by
          congr 1; push_cast; ring
    _ = ‖∫ x in (0 : ℝ)..1, deriv f x * D x‖ := norm_neg _
    _ ≤ ∫ x in (0 : ℝ)..1, K * (5 * (1 / (1 + M * x) + 1 / (1 + M * (1 - x)))) :=
          intervalIntegral.norm_integral_le_of_norm_le zero_le_one hae hbint
    _ = K * (5 * (Real.log (1 + M) / M + Real.log (1 + M) / M)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hint1 hint2, hI1, hI2]
    _ ≤ 20 * K * Real.log M / M := by
          have := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 10 * K)) hMpos.le
          calc K * (5 * (Real.log (1 + M) / M + Real.log (1 + M) / M))
              = 10 * K * Real.log (1 + M) / M := by ring
            _ ≤ 10 * K * (2 * Real.log M) / M := this
            _ = 20 * K * Real.log M / M := by ring

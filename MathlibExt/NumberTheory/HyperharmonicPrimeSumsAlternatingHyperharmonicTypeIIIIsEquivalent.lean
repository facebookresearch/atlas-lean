/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AlternatingHyperharmonic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Asymptotics of type III alternating hyperharmonic numbers

This module proves the odd-order asymptotic, the even-order asymptotic at exponent one,
and the even-order asymptotics on both parity subsequences at integer exponents at least two.
Two alternating summations become one ordinary summation on each parity subsequence.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 16 (`jis-2024-24.4.1-lem-16`).
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset
open scoped Topology

namespace alternatingHyperharmonic_typeIII_isEquivalent

private theorem sum_Icc_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Icc 1 n, f i = ∑ i ∈ range n, f (i + 1) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [Nat.add_comm 1]

/-- Partial sums of equivalent sequences are equivalent when the comparison sequence is eventually
nonnegative with divergent partial sums. -/
private theorem sum_Icc_isEquivalent {u v : ℕ → ℝ} (huv : u ~[atTop] v)
    (hv : ∀ᶠ i in atTop, 0 ≤ v i) (hdiv : Tendsto (fun n => ∑ i ∈ Icc 1 n, v i) atTop atTop) :
    (fun n => ∑ i ∈ Icc 1 n, u i) ~[atTop] fun n => ∑ i ∈ Icc 1 n, v i := by
  simp_rw [sum_Icc_eq_sum_range] at hdiv ⊢
  set w : ℕ → ℝ := fun i => max (v (i + 1)) 0 with hw
  have hvw : (fun i => v (i + 1)) =ᶠ[atTop] w := by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hv] with i hi
    simp [hw, max_eq_left hi]
  have h1 : (fun i => u (i + 1) - v (i + 1)) =o[atTop] w :=
    (huv.isLittleO.comp_tendsto (tendsto_add_atTop_nat 1)).congr'
      (Eventually.of_forall fun _ => rfl) hvw
  have hwdiv : Tendsto (fun n => ∑ i ∈ range n, w i) atTop atTop :=
    tendsto_atTop_mono (fun n => sum_le_sum fun i _ => le_max_left _ _) hdiv
  have h2 := h1.sum_range (fun i => le_max_right _ _) hwdiv
  obtain ⟨N, hN⟩ := eventually_atTop.1 hvw
  have hC : ∀ n ≥ N, ∑ i ∈ range n, w i =
      ∑ i ∈ range n, v (i + 1) + ∑ i ∈ range N, (w i - v (i + 1)) := by
    intro n hn
    rw [← sum_range_add_sum_Ico _ hn, ← sum_range_add_sum_Ico (fun i => v (i + 1)) hn,
      sum_congr rfl fun i hi => (hN i (mem_Ico.1 hi).1).symm, sum_sub_distrib]
    ring
  have hconst : (fun _ : ℕ => ∑ i ∈ range N, (w i - v (i + 1))) =o[atTop]
      fun n => ∑ i ∈ range n, v (i + 1) :=
    isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hdiv))
  have h3 : (fun n => ∑ i ∈ range n, w i) =O[atTop] fun n => ∑ i ∈ range n, v (i + 1) := by
    refine ((isBigO_refl _ _).add hconst.isBigO).congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hC n hn).symm
  refine (h2.trans_isBigO h3).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards with n
  simp [sum_sub_distrib]

/-- A sequence equivalent to an eventually positive one is eventually positive. -/
private theorem eventually_pos_of_isEquivalent {u v : ℕ → ℝ} (huv : u ~[atTop] v)
    (hu : ∀ᶠ i in atTop, 0 < u i) : ∀ᶠ i in atTop, 0 < v i := by
  filter_upwards [huv.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num), hu] with i hi hui
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs] at hi
  by_contra hneg
  push Not at hneg
  rw [abs_of_nonpos hneg] at hi
  have := (abs_le.1 hi).2
  linarith

/-- Equivalence along the even and the odd indices gives equivalence. -/
private theorem isEquivalent_of_even_odd {u v : ℕ → ℝ}
    (h0 : (fun n => u (2 * n)) ~[atTop] fun n => v (2 * n))
    (h1 : (fun n => u (2 * n - 1)) ~[atTop] fun n => v (2 * n - 1)) : u ~[atTop] v := by
  unfold IsEquivalent at *
  rw [isLittleO_iff] at *
  intro c hc
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h0 hc)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 hc)
  refine eventually_atTop.2 ⟨2 * (N0 + N1), fun n hn => ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN0 m (by omega)
  · simpa [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] using hN1 (m + 1) (by omega)

/-! ### Summation of slowly varying weights -/

/-- The weight `s` changes by `o(1/l)` in relative size from `l - 1` to `l`. -/
private def SlowStep (s : ℕ → ℝ) : Prop :=
  Tendsto (fun l : ℕ => (l : ℝ) * (s (l - 1) / s l - 1)) atTop (𝓝 0)

private theorem SlowStep.tendsto_ratio {s : ℕ → ℝ} (hs : SlowStep s) :
    Tendsto (fun l : ℕ => s (l - 1) / s l) atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul hs
  rw [mul_zero] at h
  have h' : Tendsto (fun l : ℕ => s (l - 1) / s l - 1) atTop (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with l hl
    have : (l : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    field_simp
  simpa using h'.add_const 1

private theorem slowStep_one : SlowStep fun _ => 1 := by
  simp [SlowStep]

private theorem SlowStep.mul {s t : ℕ → ℝ} (hs : SlowStep s) (ht : SlowStep t) :
    SlowStep fun l => s l * t l := by
  unfold SlowStep
  have key : ∀ l : ℕ, (l : ℝ) * (s (l - 1) * t (l - 1) / (s l * t l) - 1) =
      (l : ℝ) * (s (l - 1) / s l - 1) * (t (l - 1) / t l) + (l : ℝ) * (t (l - 1) / t l - 1) := by
    intro l
    rw [mul_div_mul_comm]
    ring
  simp_rw [key]
  simpa using (Filter.Tendsto.mul hs ht.tendsto_ratio).add ht

private theorem SlowStep.pow {s : ℕ → ℝ} (hs : SlowStep s) (n : ℕ) :
    SlowStep fun l => s l ^ n := by
  induction n with
  | zero => simpa using slowStep_one
  | succ n ih => simpa [pow_succ] using ih.mul hs

private theorem natCast_sub_one {l : ℕ} (hl : 1 ≤ l) : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
  rw [Nat.cast_sub hl, Nat.cast_one]

private theorem slowStep_log : SlowStep fun l : ℕ => Real.log l := by
  unfold SlowStep
  have hlog : Tendsto (fun l : ℕ => Real.log l) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_
    (tendsto_const_nhds.div_atTop hlog : Tendsto (fun l : ℕ => (2 : ℝ) / Real.log l) atTop (𝓝 0))
  filter_upwards [eventually_ge_atTop 3] with l hl
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  rw [natCast_sub_one (by omega)]
  set x : ℝ := (l : ℝ) with hx
  have hx1 : 0 < x - 1 := by linarith
  have hb : 0 < Real.log x := Real.log_pos (by linarith)
  have hab : Real.log (x - 1) ≤ Real.log x := Real.log_le_log hx1 (by linarith)
  have hdiff : Real.log x - Real.log (x - 1) ≤ 1 / (x - 1) := by
    rw [← Real.log_div (by linarith) hx1.ne']
    calc Real.log (x / (x - 1)) ≤ x / (x - 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (x - 1) := by field_simp; ring
  calc ‖x * (Real.log (x - 1) / Real.log x - 1)‖
      = x * (Real.log x - Real.log (x - 1)) / Real.log x := by
        rw [show x * (Real.log (x - 1) / Real.log x - 1) =
            -(x * (Real.log x - Real.log (x - 1)) / Real.log x) by field_simp; ring,
          norm_neg, Real.norm_eq_abs, abs_of_nonneg]
        have := sub_nonneg.2 hab
        positivity
    _ ≤ x * (1 / (x - 1)) / Real.log x := by
        gcongr
    _ ≤ 2 / Real.log x := by
        gcongr
        rw [mul_one_div, div_le_iff₀ hx1]
        linarith

/-- **Summation of slowly varying weights.** If the weight `s` is eventually positive, changes by
`o(1/l)` in relative size per step, and `x ^ (a + 1) * s x → ∞`, then
`∑_{l ≤ x} l ^ a s l ~ x ^ (a + 1) s x / (a + 1)`. -/
private theorem sum_pow_mul_isEquivalent {a : ℕ} {s : ℕ → ℝ} (hs : SlowStep s)
    (hpos : ∀ᶠ l in atTop, 0 < s l)
    (hG : Tendsto (fun x : ℕ => (x : ℝ) ^ (a + 1) * s x) atTop atTop) :
    (fun x : ℕ => ∑ l ∈ Icc 1 x, (l : ℝ) ^ a * s l) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (a + 1) * s x / (a + 1) := by
  set G : ℕ → ℝ := fun x => (x : ℝ) ^ (a + 1) * s x / (a + 1) with hGdef
  have ha1 : (0 : ℝ) < a + 1 := by positivity
  have htel : ∀ x : ℕ, ∑ l ∈ Icc 1 x, (G l - G (l - 1)) = G x := by
    intro x
    rw [sum_Icc_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    rw [sum_range_sub]
    simp [hGdef]
  set t : ℕ → ℝ := fun l => ((l - 1 : ℕ) : ℝ) / l with ht
  have ht1 : Tendsto t atTop (𝓝 1) := by
    have : Tendsto (fun l : ℕ => 1 - (l : ℝ)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with l hl
    have : (l : ℝ) ≠ 0 := by positivity
    simp only [ht, natCast_sub_one hl]
    field_simp
  have hgeom : Tendsto (fun l => ∑ j ∈ range (a + 1), t l ^ j) atTop (𝓝 (a + 1)) := by
    have := tendsto_finsetSum (range (a + 1)) fun j _ => ht1.pow j
    simpa using this
  have hR : Tendsto (fun l : ℕ => (∑ j ∈ range (a + 1), t l ^ j -
      t l ^ (a + 1) * ((l : ℝ) * (s (l - 1) / s l - 1))) / (a + 1)) atTop (𝓝 1) := by
    have := (hgeom.sub ((ht1.pow (a + 1)).mul hs)).div_const (a + 1 : ℝ)
    rw [one_pow, mul_zero, sub_zero, div_self ha1.ne'] at this
    exact this
  have hΔ : (fun l : ℕ => G l - G (l - 1)) ~[atTop] fun l : ℕ => (l : ℝ) ^ a * s l := by
    have h1 := (isEquivalent_const_iff_tendsto one_ne_zero).2 hR
    have h2 := h1.mul (IsEquivalent.refl (u := fun l : ℕ => (l : ℝ) ^ a * s l))
    refine (h2.congr_left ?_).congr_right ?_
    · filter_upwards [eventually_ge_atTop 1, hpos] with l hl hsl
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      have htl : t l * l = ((l - 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hl0
      have hgs := geom_sum_mul (t l) (a + 1)
      have h' : (t l - 1) * l = -1 := by rw [sub_mul, htl, one_mul, natCast_sub_one hl]; ring
      have hsum : ∑ j ∈ range (a + 1), t l ^ j = l * (1 - t l ^ (a + 1)) := by
        calc ∑ j ∈ range (a + 1), t l ^ j
            = (∑ j ∈ range (a + 1), t l ^ j) * (-((t l - 1) * l)) := by rw [h']; ring
          _ = -((∑ j ∈ range (a + 1), t l ^ j) * (t l - 1)) * l := by ring
          _ = l * (1 - t l ^ (a + 1)) := by rw [hgs]; ring
      have hσ : s (l - 1) / s l * s l = s (l - 1) := div_mul_cancel₀ _ hsl.ne'
      simp only [Pi.mul_apply, hGdef, ← htl, hsum]
      rw [mul_pow, ← hσ]
      field_simp
      ring
    · filter_upwards with l
      simp
  have hpos' : ∀ᶠ l : ℕ in atTop, 0 < (l : ℝ) ^ a * s l := by
    filter_upwards [eventually_ge_atTop 1, hpos] with l hl hsl
    have : (0 : ℝ) < l := by exact_mod_cast hl
    positivity
  have hΔpos := eventually_pos_of_isEquivalent hΔ.symm hpos'
  have hdiv : Tendsto (fun x => ∑ l ∈ Icc 1 x, (G l - G (l - 1))) atTop atTop := by
    simp_rw [htel]
    exact hG.atTop_div_const ha1
  have := sum_Icc_isEquivalent hΔ.symm (hΔpos.mono fun _ h => h.le) hdiv
  simp_rw [htel] at this
  exact this

private theorem tendsto_pow_mul_log (a b : ℕ) :
    Tendsto (fun x : ℕ => (x : ℝ) ^ (a + 1) * Real.log x ^ b) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 1), eventually_ge_atTop 1] with x hxlog hx
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  calc (x : ℝ) ≤ (x : ℝ) ^ (a + 1) := by
        simpa using pow_le_pow_right₀ hx' (show 1 ≤ a + 1 by omega)
    _ ≤ (x : ℝ) ^ (a + 1) * Real.log x ^ b :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hxlog)

private theorem sum_pow_log_isEquivalent (a b : ℕ) :
    (fun x : ℕ => ∑ l ∈ Icc 1 x, (l : ℝ) ^ a * Real.log l ^ b) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (a + 1) * Real.log x ^ b / (a + 1) := by
  refine sum_pow_mul_isEquivalent (slowStep_log.pow b) ?_ (tendsto_pow_mul_log a b)
  filter_upwards [eventually_ge_atTop 2] with l hl
  have hlog : 0 < Real.log l := Real.log_pos (by exact_mod_cast hl)
  positivity

/-- If `c i ~ L (log i) ^ b` with `L > 0`, the `(d + 1)`-st iterated partial sum of `c` (constant
signs) is equivalent to `L n ^ d (log n) ^ b / d!`. -/
private theorem iter_isEquivalent {c : ℕ → ℝ} {L : ℝ} (hL : 0 < L) {b : ℕ}
    (hc : c ~[atTop] fun i : ℕ => L * Real.log i ^ b) (d : ℕ) :
    signedIteratedPartialSum false c (d + 1) ~[atTop]
      fun n : ℕ => L * (n : ℝ) ^ d * Real.log n ^ b / d.factorial := by
  induction d with
  | zero =>
    refine hc.congr_right ?_
    filter_upwards with n
    simp
  | succ d ih =>
    set v : ℕ → ℝ := fun n => L * (n : ℝ) ^ d * Real.log n ^ b / d.factorial with hv
    have hv_eq : ∀ x, ∑ l ∈ Icc 1 x, v l =
        L / d.factorial * ∑ l ∈ Icc 1 x, (l : ℝ) ^ d * Real.log l ^ b := by
      intro x
      rw [mul_sum]
      refine sum_congr rfl fun l _ => ?_
      simp only [hv]
      ring
    have hS : (fun x => ∑ l ∈ Icc 1 x, v l) ~[atTop]
        fun x : ℕ => L / d.factorial * ((x : ℝ) ^ (d + 1) * Real.log x ^ b / (d + 1)) := by
      simp_rw [hv_eq]
      exact (IsEquivalent.refl (u := fun _ : ℕ => L / d.factorial)).mul
        (sum_pow_log_isEquivalent d b)
    have hdiv : Tendsto (fun x => ∑ l ∈ Icc 1 x, v l) atTop atTop := by
      refine hS.symm.tendsto_atTop ?_
      have := tendsto_pow_mul_log d b
      exact (this.atTop_div_const (by positivity)).const_mul_atTop (by positivity)
    have hvpos : ∀ᶠ l in atTop, 0 ≤ v l := by
      filter_upwards [eventually_ge_atTop 1] with l hl
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl
      have := Real.log_nonneg this
      simp only [hv]
      positivity
    have h := sum_Icc_isEquivalent ih hvpos hdiv
    refine ((h.trans hS).congr_left ?_).congr_right ?_
    · filter_upwards with n
      rw [signedIteratedPartialSum_succ]
      simp
    · filter_upwards with n
      rw [Nat.factorial_succ]
      push_cast
      field_simp

private theorem alt_zero (b : ℕ → ℝ) (R : ℕ) :
    signedIteratedPartialSum true b (R + 2) 0 = 0 := by
  rw [signedIteratedPartialSum_succ]
  simp

private theorem alt_succ (b : ℕ → ℝ) (R m : ℕ) :
    signedIteratedPartialSum true b (R + 2) (m + 1) =
      signedIteratedPartialSum true b (R + 2) m +
        (-1) ^ m * signedIteratedPartialSum true b (R + 1) (m + 1) := by
  rw [signedIteratedPartialSum_succ, signedIteratedPartialSum_succ, sum_Icc_succ_top (by omega)]
  simp

/-- Two steps of alternating partial summation sum over indices of the same parity. -/
private theorem alt_two_step (b : ℕ → ℝ) (r n : ℕ) :
    signedIteratedPartialSum true b (r + 3) (n + 2) =
      signedIteratedPartialSum true b (r + 3) n +
        signedIteratedPartialSum true b (r + 1) (n + 2) := by
  have h1 : signedIteratedPartialSum true b (r + 3) (n + 2) =
      signedIteratedPartialSum true b (r + 3) (n + 1) +
        (-1) ^ (n + 1) * signedIteratedPartialSum true b (r + 2) (n + 2) :=
    alt_succ b (r + 1) (n + 1)
  have h2 : signedIteratedPartialSum true b (r + 3) (n + 1) =
      signedIteratedPartialSum true b (r + 3) n +
        (-1) ^ n * signedIteratedPartialSum true b (r + 2) (n + 1) := alt_succ b (r + 1) n
  have h3 : signedIteratedPartialSum true b (r + 2) (n + 2) =
      signedIteratedPartialSum true b (r + 2) (n + 1) +
        (-1) ^ (n + 1) * signedIteratedPartialSum true b (r + 1) (n + 2) := alt_succ b r (n + 1)
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [h1, h2, h3]
  linear_combination signedIteratedPartialSum true b (r + 1) (n + 2) * hsq

private theorem alt_one (b : ℕ → ℝ) (r : ℕ) :
    signedIteratedPartialSum true b (r + 3) 1 = signedIteratedPartialSum true b (r + 1) 1 := by
  have h1 : signedIteratedPartialSum true b (r + 3) 1 =
      signedIteratedPartialSum true b (r + 3) 0 +
        (-1) ^ 0 * signedIteratedPartialSum true b (r + 2) 1 := alt_succ b (r + 1) 0
  have h2 : signedIteratedPartialSum true b (r + 2) 1 =
      signedIteratedPartialSum true b (r + 2) 0 +
        (-1) ^ 0 * signedIteratedPartialSum true b (r + 1) 1 := alt_succ b r 0
  have h0 : signedIteratedPartialSum true b (r + 3) 0 = 0 := alt_zero b (r + 1)
  have h0' : signedIteratedPartialSum true b (r + 2) 0 = 0 := alt_zero b r
  rw [h1, h2, h0, h0']
  simp

/-- Along the even indices, adding `2 * j` to the order gives `j` ordinary partial summations. -/
private theorem alt_even (b : ℕ → ℝ) (r j : ℕ) :
    (fun n => signedIteratedPartialSum true b (r + 1 + 2 * j) (2 * n)) =
      signedIteratedPartialSum false (fun i => signedIteratedPartialSum true b (r + 1) (2 * i))
        (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext n
    rw [signedIteratedPartialSum_succ, ← ih]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have e1 : r + 1 + 2 * (j + 1) = r + 2 * j + 3 := by ring
    have e2 : r + 1 + 2 * j = r + 2 * j + 1 := by ring
    induction n with
    | zero =>
      rw [e1]
      simpa using alt_zero b (r + 2 * j + 1)
    | succ n ihn =>
      rw [sum_Icc_succ_top (by omega), ← ihn, e1, e2, show 2 * (n + 1) = 2 * n + 2 by ring,
        alt_two_step]

/-- Along the odd indices, adding `2 * j` to the order gives `j` ordinary partial summations. -/
private theorem alt_odd (b : ℕ → ℝ) (r j : ℕ) :
    (fun n => signedIteratedPartialSum true b (r + 1 + 2 * j) (2 * n - 1)) =
      signedIteratedPartialSum false
        (fun i => signedIteratedPartialSum true b (r + 1) (2 * i - 1)) (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext n
    rw [signedIteratedPartialSum_succ, ← ih]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have e1 : r + 1 + 2 * (j + 1) = r + 2 * j + 3 := by ring
    have e2 : r + 1 + 2 * j = r + 2 * j + 1 := by ring
    induction n with
    | zero =>
      rw [e1]
      simpa using alt_zero b (r + 2 * j + 1)
    | succ n ihn =>
      rw [sum_Icc_succ_top (by omega), ← ihn, e1, e2]
      rcases n with _ | n
      · have h0 : signedIteratedPartialSum true b (r + 2 * j + 3) 0 = 0 :=
          alt_zero b (r + 2 * j + 1)
        simpa [h0] using alt_one b (r + 2 * j)
      · rw [show 2 * (n + 1 + 1) - 1 = 2 * n + 1 + 2 by omega,
          show 2 * (n + 1) - 1 = 2 * n + 1 by omega, alt_two_step]

/-! ### Limits of the alternating harmonic numbers and of the second order -/

private theorem tendsto_two_mul : Tendsto (fun i : ℕ => 2 * i) atTop atTop :=
  tendsto_atTop_mono (fun i => by simp only [id]; omega) tendsto_id

private theorem tendsto_two_mul_sub_one : Tendsto (fun i : ℕ => 2 * i - 1) atTop atTop :=
  tendsto_atTop_mono (fun i => by omega) (tendsto_sub_atTop_nat 1)

private theorem altHarmonic_tendsto {p : ℕ} (hp : 1 ≤ p) :
    Tendsto (alternatingGeneralizedHarmonic p) atTop (𝓝 (alternatingZeta p)) := by
  have h := alternatingHyperharmonic_typeII_isEquivalent (r := 1) (p := p) le_rfl hp
  apply IsEquivalent.tendsto_const
  simpa [signedIteratedPartialSum_one, Function.const_def] using h

private theorem alternatingZeta_pos {p : ℕ} (hp : 1 ≤ p) : 0 < alternatingZeta p := by
  rcases eq_or_lt_of_le hp with h | h
  · subst p
    rw [alternatingZeta_one]
    exact Real.log_pos (by norm_num)
  simp only [alternatingZeta, h.ne', ↓reduceIte]
  apply mul_pos
  · apply sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_)
    exact sub_neg.mpr (by exact_mod_cast h)
  · exact (Real.summable_one_div_nat_pow.mpr h).tsum_pos (fun n => by positivity) 1 (by simp)

private theorem zeta_pos {q : ℕ} (hq : 2 ≤ q) : 0 < ∑' i : ℕ, 1 / (i : ℝ) ^ q :=
  (Real.summable_one_div_nat_pow.mpr (by omega)).tsum_pos (fun n => by positivity) 1 (by simp)

/-- `ζ(q) - ζ̄(q) = 2 · 2⁻ᵠ ζ(q)` for `q ≥ 2`. -/
private theorem zeta_sub_alternatingZeta {q : ℕ} (hq : 2 ≤ q) :
    (∑' i : ℕ, 1 / (i : ℝ) ^ q) - alternatingZeta q =
      2 * (((2 : ℝ) ^ q)⁻¹ * ∑' i : ℕ, 1 / (i : ℝ) ^ q) := by
  simp only [alternatingZeta, show q ≠ 1 by omega, ↓reduceIte]
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  field_simp
  ring

/-- The second-order type III numbers along even indices: `H_{2i}^{(s,2,3)} = ∑_{m ≤ i} (2m)⁻ˢ`. -/
private theorem alt_two_even (s : ℝ) (i : ℕ) :
    signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * i) =
      ∑ m ∈ Icc 1 i, (((2 * m : ℕ) : ℝ) ^ s)⁻¹ := by
  induction i with
  | zero => simp [signedIteratedPartialSum_succ]
  | succ i ih =>
    have h1 : signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * (i + 1)) =
        signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * i + 1) +
          (-1) ^ (2 * i + 1) * alternatingGeneralizedHarmonic s (2 * (i + 1)) :=
      alt_succ _ 0 (2 * i + 1)
    have h2 : signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * i + 1) =
        signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * i) +
          (-1) ^ (2 * i) * alternatingGeneralizedHarmonic s (2 * i + 1) :=
      alt_succ _ 0 (2 * i)
    have h3 : alternatingGeneralizedHarmonic s (2 * (i + 1)) =
        alternatingGeneralizedHarmonic s (2 * i + 1) +
          (-1) ^ (2 * i + 1) * (((2 * (i + 1) : ℕ) : ℝ) ^ s)⁻¹ := by
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, alternatingGeneralizedHarmonic,
        alternatingGeneralizedHarmonic, sum_Icc_succ_top (by omega)]
      simp
    rw [h1, h2, h3, ih, sum_Icc_succ_top (by omega)]
    simp [pow_succ, pow_mul]
    ring

private theorem alt_two_odd (s : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * i - 1) =
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * i) +
        alternatingGeneralizedHarmonic s (2 * i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h : signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * (j + 1)) =
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) 2 (2 * j + 1) +
        (-1) ^ (2 * j + 1) * alternatingGeneralizedHarmonic s (2 * (j + 1)) :=
    alt_succ _ 0 (2 * j + 1)
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, h]
  simp [pow_succ, pow_mul]

private theorem zeta_partial_tendsto {q : ℕ} (hq : 2 ≤ q) :
    Tendsto (fun i : ℕ => ∑ m ∈ Icc 1 i, 1 / (m : ℝ) ^ q) atTop
      (𝓝 (∑' m : ℕ, 1 / (m : ℝ) ^ q)) := by
  have hs : Summable fun m : ℕ => 1 / (m : ℝ) ^ q := Real.summable_one_div_nat_pow.mpr (by omega)
  refine ((hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).congr fun i => ?_
  simp only [Function.comp_apply]
  rw [sum_range_succ', sum_Icc_eq_sum_range]
  simp [show q ≠ 0 by omega]

private theorem two_mul_rpow_inv (q m : ℕ) :
    (((2 * m : ℕ) : ℝ) ^ (q : ℝ))⁻¹ = ((2 : ℝ) ^ q)⁻¹ * (1 / (m : ℝ) ^ q) := by
  rw [Real.rpow_natCast]
  push_cast
  rw [mul_pow, mul_inv, one_div]

private theorem alt_two_even_tendsto {q : ℕ} (hq : 2 ≤ q) :
    Tendsto (fun i : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic q) 2
      (2 * i)) atTop (𝓝 (((2 : ℝ) ^ q)⁻¹ * ∑' m : ℕ, 1 / (m : ℝ) ^ q)) := by
  simp_rw [alt_two_even, two_mul_rpow_inv, ← mul_sum]
  exact (zeta_partial_tendsto hq).const_mul _

private theorem alt_two_odd_tendsto {q : ℕ} (hq : 2 ≤ q) :
    Tendsto (fun i : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic q) 2
      (2 * i - 1)) atTop
      (𝓝 (((2 : ℝ) ^ q)⁻¹ * (∑' m : ℕ, 1 / (m : ℝ) ^ q) + alternatingZeta q)) := by
  refine ((alt_two_even_tendsto hq).add
    ((altHarmonic_tendsto (by omega)).comp tendsto_two_mul)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with i hi
  rw [alt_two_odd _ hi]
  rfl

private theorem harmonic_isEquivalent_log :
    (fun i : ℕ => (harmonic i : ℝ)) ~[atTop] fun i : ℕ => Real.log i := by
  have hb : (fun i : ℕ => (harmonic i : ℝ) - Real.log i) =O[atTop] fun _ => (1 : ℝ) := by
    refine isBigO_iff.2 ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with i hi
    have h1 := log_add_one_le_harmonic i
    have h2 := harmonic_le_one_add_log i
    have h3 : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hi) (by push_cast; linarith)
    rw [Real.norm_eq_abs, abs_le, norm_one, mul_one]
    constructor <;> linarith
  have hlog : Tendsto (fun i : ℕ => Real.log i) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hb.trans_isLittleO (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hlog)))

private theorem alt_two_even_one_isEquivalent :
    (fun i : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 2
      (2 * i)) ~[atTop] fun i : ℕ => 1 / 2 * Real.log i ^ 1 := by
  have h : ∀ i : ℕ, signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1)
      2 (2 * i) = 1 / 2 * (harmonic i : ℝ) := by
    intro i
    rw [alt_two_even, harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Real.rpow_one, mul_inv]
    ring
  simp_rw [h, pow_one]
  exact (IsEquivalent.refl (u := fun _ : ℕ => (1 / 2 : ℝ))).mul harmonic_isEquivalent_log

private theorem alt_two_odd_one_isEquivalent :
    (fun i : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 2
      (2 * i - 1)) ~[atTop] fun i : ℕ => 1 / 2 * Real.log i ^ 1 := by
  have hlog : Tendsto (fun i : ℕ => 1 / 2 * Real.log i ^ 1) atTop atTop := by
    simpa using (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlim : Tendsto (alternatingGeneralizedHarmonic 1) atTop (𝓝 (alternatingZeta 1)) := by
    simpa using altHarmonic_tendsto (p := 1) le_rfl
  have hbdd : (fun i : ℕ => alternatingGeneralizedHarmonic 1 (2 * i)) =o[atTop]
      fun i : ℕ => 1 / 2 * Real.log i ^ 1 :=
    (hlim.comp tendsto_two_mul).isBigO_one ℝ |>.trans_isLittleO
      (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hlog)))
  refine (alt_two_even_one_isEquivalent.add_isLittleO hbdd).congr_left ?_
  filter_upwards [eventually_ge_atTop 1] with i hi
  rw [alt_two_odd _ hi]
  rfl

private theorem two_mul_sub_one_isEquivalent :
    (fun n : ℕ => ((2 * n - 1 : ℕ) : ℝ)) ~[atTop] fun n : ℕ => 2 * (n : ℝ) := by
  have htend : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop two_pos
  have h : (fun n : ℕ => 2 * (n : ℝ)) - (fun _ => (1 : ℝ)) ~[atTop] fun n : ℕ => 2 * (n : ℝ) :=
    IsEquivalent.refl.sub_isLittleO
      (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp htend)))
  refine h.congr_left ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Pi.sub_apply]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

private theorem log_two_mul_isEquivalent :
    (fun n : ℕ => Real.log (2 * (n : ℝ))) ~[atTop] fun n : ℕ => Real.log n := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h : (fun n : ℕ => Real.log n) + (fun _ => Real.log 2) ~[atTop]
      fun n : ℕ => Real.log n :=
    IsEquivalent.refl.add_isLittleO
      (isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hlog)))
  refine h.congr_left ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Pi.add_apply]
  rw [Real.log_mul (by norm_num) this.ne']
  ring

/-- Type III numbers of odd order: `H_n^{(p,2y+1,3)} ~ n ^ y ζ̄(p) / (2 ^ y y!)`. -/
private theorem typeIII_odd_order {y p : ℕ} (hp : 1 ≤ p) :
    (fun n : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic p) (2 * y + 1) n)
      ~[atTop] fun n : ℕ => (n : ℝ) ^ y * alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ) := by
  set b := alternatingGeneralizedHarmonic (p : ℝ) with hb
  have hz := alternatingZeta_pos hp
  have hlim := altHarmonic_tendsto hp
  have hconst : ∀ {c : ℕ → ℝ}, Tendsto c atTop (𝓝 (alternatingZeta p)) →
      c ~[atTop] fun i : ℕ => alternatingZeta p * Real.log i ^ 0 := by
    intro c hc
    refine ((isEquivalent_const_iff_tendsto hz.ne').2 hc).congr_right ?_
    filter_upwards with i
    simp
  have he := iter_isEquivalent hz (hconst (hlim.comp tendsto_two_mul)) y
  have ho := iter_isEquivalent hz (hconst (hlim.comp tendsto_two_mul_sub_one)) y
  have heven : (fun n => signedIteratedPartialSum true b (2 * y + 1) (2 * n)) =
      signedIteratedPartialSum false (fun i => b (2 * i)) (y + 1) := by
    rw [show 2 * y + 1 = 0 + 1 + 2 * y by ring]
    exact alt_even b 0 y
  have hodd : (fun n => signedIteratedPartialSum true b (2 * y + 1) (2 * n - 1)) =
      signedIteratedPartialSum false (fun i => b (2 * i - 1)) (y + 1) := by
    rw [show 2 * y + 1 = 0 + 1 + 2 * y by ring]
    exact alt_odd b 0 y
  have hfac : (0 : ℝ) < y.factorial := by positivity
  have hE : (fun n => signedIteratedPartialSum true b (2 * y + 1) (2 * n)) ~[atTop]
      fun n => ((2 * n : ℕ) : ℝ) ^ y * alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ) := by
    rw [heven]
    refine he.congr_right ?_
    filter_upwards with n
    push_cast
    field_simp
    ring
  have hO : (fun n => signedIteratedPartialSum true b (2 * y + 1) (2 * n - 1)) ~[atTop]
      fun n => ((2 * n - 1 : ℕ) : ℝ) ^ y * alternatingZeta p /
        ((2 ^ y * y.factorial : ℕ) : ℝ) := by
    rw [hodd]
    refine ho.trans ?_
    have h2 := (two_mul_sub_one_isEquivalent.symm.pow y).mul
      (IsEquivalent.refl (u := fun _ : ℕ => alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ)))
    refine (h2.congr_left ?_).congr_right ?_
    · filter_upwards with n
      simp only [Pi.mul_apply, Pi.pow_apply]
      push_cast
      field_simp
      ring
    · filter_upwards with n
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
  exact isEquivalent_of_even_odd hE hO

/-- Type III numbers of even order at `p = 1`: `H_n^{(1,2y,3)} ~ n ^ (y-1) log n / (2^y (y-1)!)`. -/
private theorem typeIII_even_order_one {y : ℕ} (hy : 1 ≤ y) :
    (fun n : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) (2 * y) n)
      ~[atTop] fun n : ℕ => (n : ℝ) ^ (y - 1) * Real.log n /
        ((2 ^ y * (y - 1).factorial : ℕ) : ℝ) := by
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set b := alternatingGeneralizedHarmonic 1 with hb
  have hL : (0 : ℝ) < 1 / 2 := by norm_num
  have he := iter_isEquivalent hL alt_two_even_one_isEquivalent y
  have ho := iter_isEquivalent hL alt_two_odd_one_isEquivalent y
  have heven : (fun n => signedIteratedPartialSum true b (2 * (y + 1)) (2 * n)) =
      signedIteratedPartialSum false (fun i => signedIteratedPartialSum true b 2 (2 * i))
        (y + 1) := by
    rw [show 2 * (y + 1) = 1 + 1 + 2 * y by ring]
    exact alt_even b 1 y
  have hodd : (fun n => signedIteratedPartialSum true b (2 * (y + 1)) (2 * n - 1)) =
      signedIteratedPartialSum false (fun i => signedIteratedPartialSum true b 2 (2 * i - 1))
        (y + 1) := by
    rw [show 2 * (y + 1) = 1 + 1 + 2 * y by ring]
    exact alt_odd b 1 y
  have hfac : (0 : ℝ) < y.factorial := by positivity
  have hE : (fun n => signedIteratedPartialSum true b (2 * (y + 1)) (2 * n)) ~[atTop]
      fun n => ((2 * n : ℕ) : ℝ) ^ y * Real.log ((2 * n : ℕ) : ℝ) /
        ((2 ^ (y + 1) * y.factorial : ℕ) : ℝ) := by
    rw [heven]
    refine he.trans ?_
    have h2 := log_two_mul_isEquivalent.symm.mul
      (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ) ^ y / (2 * y.factorial)))
    refine (h2.congr_left ?_).congr_right ?_
    · filter_upwards with n
      simp only [Pi.mul_apply]
      field_simp
    · filter_upwards with n
      simp only [Pi.mul_apply]
      push_cast
      field_simp
      ring
  have hO : (fun n => signedIteratedPartialSum true b (2 * (y + 1)) (2 * n - 1)) ~[atTop]
      fun n => ((2 * n - 1 : ℕ) : ℝ) ^ y * Real.log ((2 * n - 1 : ℕ) : ℝ) /
        ((2 ^ (y + 1) * y.factorial : ℕ) : ℝ) := by
    rw [hodd]
    refine ho.trans ?_
    have hlog1 : (fun n : ℕ => Real.log ((2 * n - 1 : ℕ) : ℝ)) ~[atTop]
        fun n : ℕ => Real.log n :=
      (two_mul_sub_one_isEquivalent.log
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)).trans log_two_mul_isEquivalent
    have h2 := ((two_mul_sub_one_isEquivalent.pow y).mul hlog1).mul
      (IsEquivalent.refl (u := fun _ : ℕ => (1 : ℝ) / ((2 ^ (y + 1) * y.factorial : ℕ) : ℝ)))
    refine (h2.symm.congr_left ?_).congr_right ?_
    · filter_upwards with n
      simp only [Pi.mul_apply, Pi.pow_apply]
      push_cast
      field_simp
      ring
    · filter_upwards with n
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
  exact isEquivalent_of_even_odd hE hO

/-- Type III numbers of even order at odd indices:
`H_{2n-1}^{(q,2y,3)} ~ n ^ (y-1) (ζ(q) + ζ̄(q)) / (2 (y-1)!)` for `q ≥ 2`. -/
private theorem typeIII_even_order_odd_index {y q : ℕ} (hy : 1 ≤ y) (hq : 2 ≤ q) :
    (fun n : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic q) (2 * y)
      (2 * n - 1)) ~[atTop] fun n : ℕ => (n : ℝ) ^ (y - 1) *
        ((∑' i : ℕ, 1 / (i : ℝ) ^ q) + alternatingZeta q) /
          ((2 * (y - 1).factorial : ℕ) : ℝ) := by
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set b := alternatingGeneralizedHarmonic (q : ℝ) with hb
  have hz := zeta_pos hq
  have hz' := alternatingZeta_pos (show 1 ≤ q by omega)
  have hLo : 0 < ((2 : ℝ) ^ q)⁻¹ * (∑' i : ℕ, 1 / (i : ℝ) ^ q) + alternatingZeta q := by
    positivity
  have hco : (fun i => signedIteratedPartialSum true b 2 (2 * i - 1)) ~[atTop]
      fun i : ℕ => (((2 : ℝ) ^ q)⁻¹ * (∑' i : ℕ, 1 / (i : ℝ) ^ q) + alternatingZeta q) *
        Real.log i ^ 0 := by
    refine ((isEquivalent_const_iff_tendsto hLo.ne').2 (alt_two_odd_tendsto hq)).congr_right ?_
    filter_upwards with i
    simp
  have hodd : (fun n => signedIteratedPartialSum true b (2 * (y + 1)) (2 * n - 1)) =
      signedIteratedPartialSum false (fun i => signedIteratedPartialSum true b 2 (2 * i - 1))
        (y + 1) := by
    rw [show 2 * (y + 1) = 1 + 1 + 2 * y by ring]
    exact alt_odd b 1 y
  have hfac : (0 : ℝ) < y.factorial := by positivity
  have hrel := zeta_sub_alternatingZeta hq
  have h2 : (∑' i : ℕ, 1 / (i : ℝ) ^ q) + alternatingZeta q =
      2 * (((2 : ℝ) ^ q)⁻¹ * (∑' i : ℕ, 1 / (i : ℝ) ^ q) + alternatingZeta q) := by
    linear_combination hrel
  rw [hodd]
  refine (iter_isEquivalent hLo hco y).congr_right ?_
  filter_upwards with n
  rw [h2]
  push_cast
  field_simp

/-- Type III numbers of even order at even indices:
`H_{2n}^{(q,2y,3)} ~ n ^ (y-1) (ζ(q) - ζ̄(q)) / (2 (y-1)!)` for `q ≥ 2`. -/
private theorem typeIII_even_order_even_index {y q : ℕ} (hy : 1 ≤ y) (hq : 2 ≤ q) :
    (fun n : ℕ => signedIteratedPartialSum true (alternatingGeneralizedHarmonic q) (2 * y)
      (2 * n)) ~[atTop] fun n : ℕ => (n : ℝ) ^ (y - 1) *
        ((∑' i : ℕ, 1 / (i : ℝ) ^ q) - alternatingZeta q) /
          ((2 * (y - 1).factorial : ℕ) : ℝ) := by
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set b := alternatingGeneralizedHarmonic (q : ℝ) with hb
  have hz := zeta_pos hq
  have hLe : 0 < ((2 : ℝ) ^ q)⁻¹ * (∑' i : ℕ, 1 / (i : ℝ) ^ q) := by positivity
  have hce : (fun i => signedIteratedPartialSum true b 2 (2 * i)) ~[atTop]
      fun i : ℕ => (((2 : ℝ) ^ q)⁻¹ * (∑' i : ℕ, 1 / (i : ℝ) ^ q)) * Real.log i ^ 0 := by
    refine ((isEquivalent_const_iff_tendsto hLe.ne').2 (alt_two_even_tendsto hq)).congr_right ?_
    filter_upwards with i
    simp
  have heven : (fun n => signedIteratedPartialSum true b (2 * (y + 1)) (2 * n)) =
      signedIteratedPartialSum false (fun i => signedIteratedPartialSum true b 2 (2 * i))
        (y + 1) := by
    rw [show 2 * (y + 1) = 1 + 1 + 2 * y by ring]
    exact alt_even b 1 y
  have hfac : (0 : ℝ) < y.factorial := by positivity
  have hrel := zeta_sub_alternatingZeta hq
  rw [heven]
  refine (iter_isEquivalent hLe hce y).congr_right ?_
  filter_upwards with n
  push_cast
  rw [hrel]
  field_simp

end alternatingHyperharmonic_typeIII_isEquivalent

open alternatingHyperharmonic_typeIII_isEquivalent in
/-- **Asymptotics of type III alternating hyperharmonic numbers.** For real $s$ let
$\overline{H}_n^{(s)} = \sum_{i=1}^{n} (-1)^{i-1}/i^s$ be the alternating generalized harmonic
numbers, and let the type III generalized alternating hyperharmonic numbers be
$H_n^{(s,1,3)} = \overline{H}_n^{(s)}$ and
$H_n^{(s,r+1,3)} = \sum_{k=1}^{n} (-1)^{k-1} H_k^{(s,r,3)}$. Let $y \ge 1$ and $p \ge 1$ be natural
numbers and let $\bar\zeta(p)$ be the alternating zeta value at $p$. Then, as $n \to \infty$,
$H_n^{(p,2y+1,3)} \sim n^y \bar\zeta(p) / (2^y\, y!)$ and
$H_n^{(1,2y,3)} \sim n^{y-1} \log n / (2^y (y-1)!)$. If moreover $p \ge 2$, then, with
$\zeta(p) = \sum_{i \ge 1} 1/i^p$, as $n \to \infty$,
$H_{2n}^{(p,2y,3)} \sim n^{y-1} (\zeta(p) - \bar\zeta(p)) / (2\,(y-1)!)$ and
$H_{2n-1}^{(p,2y,3)} \sim n^{y-1} (\zeta(p) + \bar\zeta(p)) / (2\,(y-1)!)$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 16 (`jis-2024-24.4.1-lem-16`). -/
public theorem alternatingHyperharmonic_typeIII_isEquivalent {y p : ℕ} (hy : 1 ≤ y)
    (hp : 1 ≤ p) :
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    let ζp : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ p
    ((fun n : ℕ => HIII p (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HIII 1 (2 * y) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * Real.log n / ((2 ^ y * (y - 1).factorial : ℕ) : ℝ)) ∧
    (2 ≤ p → (fun n : ℕ => HIII p (2 * y) (2 * n)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp - alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ)) ∧
    (2 ≤ p → (fun n : ℕ => HIII p (2 * y) (2 * n - 1)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp + alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))
    := by
  exact ⟨typeIII_odd_order hp, typeIII_even_order_one hy,
    fun hp' => typeIII_even_order_even_index hy hp',
    fun hp' => typeIII_even_order_odd_index hy hp'⟩

end MetaMathlibExt

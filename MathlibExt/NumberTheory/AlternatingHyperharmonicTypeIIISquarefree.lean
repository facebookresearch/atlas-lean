/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AlternatingHyperharmonic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import MathlibExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptotic

/-!
# Type III alternating hyperharmonic power sums over squarefree numbers with `k` prime factors

This file proves the asymptotics, as `x → ∞`, of the sums `∑_{ℓ ≤ x} p_{ℓ,k} ^ α f(ℓ) ^ m` and
`∑_{ℓ ≤ x, p_{ℓ,k} ≤ x} p_{ℓ,k} ^ α f(ℓ) ^ m`, where `p_{ℓ,k}` is the `ℓ`-th squarefree number with
exactly `k` prime factors and `f` is one of four sequences of type III alternating hyperharmonic
numbers, following Rusen Li, *Sums over Primes II* (the main theorem's docstring gives the
reference).

## Main results

* `MetaMathlibExt.alternatingHyperharmonic_typeIII_isEquivalent`: the asymptotics of the type III
  numbers themselves, the odd-order one, the even-order one at exponent one, and the even-order ones
  along the even and the odd indices.
* `MetaMathlibExt.sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent`:
  the eight asymptotics.

## Proof outline

* Two steps of alternating partial summation sum over the indices of the same parity, so along
  the even and along the odd indices the type III numbers are plain iterated partial sums. This
  gives their asymptotics.
* The number of squarefree `n ≤ x` with `k` prime factors is asymptotic to Landau's
  `x (log log x) ^ (k - 1) / ((k - 1)! log x)`: the non-squarefree `n ≤ x` with `k` prime factors
  counted with multiplicity are at most `k - 1` times as many as the `n ≤ x` with `k - 1` prime
  factors. Inverting gives `p_{ℓ,k} ~ (k - 1)! ℓ log ℓ / (log log ℓ) ^ (k - 1)`.
* `∑_{ℓ ≤ x} ℓ ^ a (log ℓ) ^ b / (log log ℓ) ^ c ~ x ^ (a + 1) (log x) ^ b / ((a + 1)
  (log log x) ^ c)`, by comparing the terms with the differences of the right side.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset
open scoped Topology

namespace sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent

/-! ### Sums of equivalent sequences -/

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

private theorem SlowStep.inv {s : ℕ → ℝ} (hs : SlowStep s) : SlowStep fun l => (s l)⁻¹ := by
  unfold SlowStep
  have hr := hs.tendsto_ratio
  have hlim : Tendsto (fun l : ℕ => -((l : ℝ) * (s (l - 1) / s l - 1)) / (s (l - 1) / s l))
      atTop (𝓝 0) := by
    have := (Filter.Tendsto.neg hs).div hr one_ne_zero
    rw [neg_zero, zero_div] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [hr.eventually_ne one_ne_zero] with l hl
  rw [div_ne_zero_iff] at hl
  rw [inv_div_inv]
  field_simp [hl.1, hl.2]
  ring


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

private theorem slowStep_loglog : SlowStep fun l : ℕ => Real.log (Real.log l) := by
  unfold SlowStep
  have hloglog : Tendsto (fun l : ℕ => Real.log (Real.log l)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hloglog :
    Tendsto (fun l : ℕ => (2 : ℝ) / Real.log (Real.log l)) atTop (𝓝 0))
  filter_upwards [eventually_ge_atTop 4] with l hl
  have hl' : (4 : ℝ) ≤ l := by exact_mod_cast hl
  rw [natCast_sub_one (by omega)]
  set x : ℝ := (l : ℝ) with hx
  have hx1 : 0 < x - 1 := by linarith
  have he : Real.exp 1 ≤ x - 1 := by
    have := Real.exp_one_lt_three
    linarith
  have ha1 : 1 ≤ Real.log (x - 1) := (Real.le_log_iff_exp_le hx1).2 he
  have hab : Real.log (x - 1) < Real.log x := Real.log_lt_log hx1 (by linarith)
  have hb1 : 1 < Real.log x := lt_of_le_of_lt ha1 hab
  have hB : 0 < Real.log (Real.log x) := Real.log_pos hb1
  have hAB : Real.log (Real.log (x - 1)) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by linarith) hab.le
  have hdiff : Real.log x - Real.log (x - 1) ≤ 1 / (x - 1) := by
    rw [← Real.log_div (by linarith) hx1.ne']
    calc Real.log (x / (x - 1)) ≤ x / (x - 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (x - 1) := by field_simp; ring
  have hdiff2 : Real.log (Real.log x) - Real.log (Real.log (x - 1)) ≤ 1 / (x - 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    calc Real.log (Real.log x / Real.log (x - 1))
        ≤ Real.log x / Real.log (x - 1) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = (Real.log x - Real.log (x - 1)) / Real.log (x - 1) := by field_simp
      _ ≤ (Real.log x - Real.log (x - 1)) / 1 := by gcongr
      _ ≤ 1 / (x - 1) := by rw [div_one]; exact hdiff
  calc ‖x * (Real.log (Real.log (x - 1)) / Real.log (Real.log x) - 1)‖
      = x * (Real.log (Real.log x) - Real.log (Real.log (x - 1))) / Real.log (Real.log x) := by
        rw [show x * (Real.log (Real.log (x - 1)) / Real.log (Real.log x) - 1) =
            -(x * (Real.log (Real.log x) - Real.log (Real.log (x - 1))) /
              Real.log (Real.log x)) by field_simp; ring,
          norm_neg, Real.norm_eq_abs, abs_of_nonneg]
        have := sub_nonneg.2 hAB
        positivity
    _ ≤ x * (1 / (x - 1)) / Real.log (Real.log x) := by
        gcongr
    _ ≤ 2 / Real.log (Real.log x) := by
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


private theorem log_gt_one_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 < Real.log x := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_three
  linarith

private theorem weight_pos (b c : ℕ) :
    ∀ᶠ l : ℕ in atTop, 0 < Real.log l ^ b * (Real.log (Real.log l) ^ c)⁻¹ := by
  filter_upwards [eventually_ge_atTop 3] with l hl
  have h1 : 1 < Real.log l := log_gt_one_of_three_le (by exact_mod_cast hl)
  have h2 : 0 < Real.log (Real.log l) := Real.log_pos h1
  have h3 : 0 < Real.log l := by linarith
  positivity

private theorem tendsto_div_log_pow (c : ℕ) :
    Tendsto (fun x : ℕ => (x : ℝ) / Real.log x ^ c) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ c / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 c one_ne_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ c / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa using h0, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    have := Real.log_pos hx
    simp only [Set.mem_Ioi]
    positivity
  refine (h1.inv_tendsto_nhdsGT_zero.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards with x
  simp [inv_div]

private theorem tendsto_pow_mul_weight (a b c : ℕ) :
    Tendsto (fun x : ℕ => (x : ℝ) ^ (a + 1) *
      (Real.log x ^ b * (Real.log (Real.log x) ^ c)⁻¹)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_div_log_pow c)
  filter_upwards [eventually_ge_atTop 3] with x hx
  have hx' : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have h1 : 1 < Real.log x := log_gt_one_of_three_le hx'
  have h2 : 0 < Real.log (Real.log x) := Real.log_pos h1
  have h3 : Real.log (Real.log x) ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log x by linarith)
    linarith
  have hxa : (x : ℝ) ≤ (x : ℝ) ^ (a + 1) := by
    calc (x : ℝ) = (x : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (x : ℝ) ^ (a + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hb : 1 ≤ Real.log x ^ b := one_le_pow₀ h1.le
  have hc : Real.log (Real.log x) ^ c ≤ Real.log x ^ c := pow_le_pow_left₀ h2.le h3 c
  rw [div_eq_mul_inv]
  calc (x : ℝ) * (Real.log x ^ c)⁻¹ ≤ (x : ℝ) ^ (a + 1) * (1 * (Real.log (Real.log x) ^ c)⁻¹) := by
        rw [one_mul]
        gcongr
    _ ≤ _ := by gcongr

/-- `∑_{l ≤ x} l ^ a (log l) ^ b / (log log l) ^ c ~ x ^ (a + 1) (log x) ^ b / ((a + 1)
(log log x) ^ c)`. -/
private theorem sum_pow_log_loglog_isEquivalent (a b c : ℕ) :
    (fun x : ℕ => ∑ l ∈ Icc 1 x, (l : ℝ) ^ a *
      (Real.log l ^ b * (Real.log (Real.log l) ^ c)⁻¹)) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (a + 1) * (Real.log x ^ b * (Real.log (Real.log x) ^ c)⁻¹) /
        (a + 1) :=
  sum_pow_mul_isEquivalent ((slowStep_log.pow b).mul (slowStep_loglog.pow c).inv)
    (weight_pos b c) (tendsto_pow_mul_weight a b c)

private theorem sum_pow_log_isEquivalent (a b : ℕ) :
    (fun x : ℕ => ∑ l ∈ Icc 1 x, (l : ℝ) ^ a * Real.log l ^ b) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (a + 1) * Real.log x ^ b / (a + 1) := by
  simpa using sum_pow_log_loglog_isEquivalent a b 0

/-! ### Iterated partial sums -/

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
      have := tendsto_pow_mul_weight d b 0
      simp only [pow_zero, inv_one, mul_one] at this
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

/-! ### Type III alternating hyperharmonic numbers -/

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

/-- Along the even indices, alternating partial summation of order `2j` is plain iterated
summation of order `j`. -/
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

/-- Along the odd indices, alternating partial summation of order `2j` is plain iterated
summation of order `j`. -/
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

/-! ### Squarefree numbers with `k` prime factors -/

/-- There are infinitely many squarefree numbers with `k ≥ 1` prime factors. -/
private theorem sqfree_infinite {k : ℕ} (hk : 1 ≤ k) :
    (Set.ofPred (fun t : ℕ => Squarefree t ∧ t.primeFactors.card = k)).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  set s : Finset ℕ := (range k).image fun i => Nat.nth Nat.Prime (N + 1 + i) with hs
  have hprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := mem_image.mp hp
    exact Nat.prime_nth_prime _
  have hinj : Function.Injective fun i => Nat.nth Nat.Prime (N + 1 + i) := fun i j hij =>
    by simpa using (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
  refine ⟨∏ p ∈ s, p, ⟨?_, ?_⟩, ?_⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      fun p hp => (hprime p hp).prime.squarefree
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  · rw [Nat.primeFactors_prod hprime, hs, card_image_of_injective _ hinj, card_range]
  · have hmem : Nat.nth Nat.Prime (N + 1 + 0) ∈ s :=
      mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩
    have hle : Nat.nth Nat.Prime (N + 1 + 0) ≤ ∏ p ∈ s, p :=
      Finset.single_le_prod (fun p hp => (hprime p hp).one_lt.le) hmem
    have hge : N + 1 ≤ Nat.nth Nat.Prime (N + 1 + 0) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le _
    change N < ∏ p ∈ s, p
    omega

/-- A squarefree number with `k` distinct prime factors has `k` prime factors with
multiplicity. -/
private theorem isAlmostPrime_of_sqfree {k t : ℕ} (h : Squarefree t ∧ t.primeFactors.card = k) :
    Nat.IsAlmostPrime k t := by
  refine ⟨h.1.ne_zero, ?_⟩
  rw [← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree h.1.ne_zero).mpr
    h.1, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, h.2]

private theorem count_eq_card_Icc {k : ℕ} (x : ℕ) :
    Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) =
      #{t ∈ Icc 1 x | Squarefree t ∧ t.primeFactors.card = k} := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext t
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨⟨Nat.pos_of_ne_zero h.1.ne_zero, by omega⟩, h⟩
  · rintro ⟨ht, h⟩
    exact ⟨by omega, h⟩

private theorem count_le_almostPrimeCounting {k : ℕ} (x : ℕ) :
    Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) ≤
      almostPrimeCounting k x := by
  rw [count_eq_card_Icc, almostPrimeCounting_eq_card_filter,
    ← show Icc 1 x = Ioc 0 x from Icc_succ_left_eq_Ioc 0 x]
  refine card_le_card fun t ht => ?_
  simp only [mem_filter] at ht ⊢
  exact ⟨ht.1, isAlmostPrime_of_sqfree ht.2⟩

/-- The non-squarefree numbers with `k` prime factors are few. -/
private theorem card_nonsqfree_le (k x : ℕ) :
    #{n ∈ Icc 1 x | Nat.IsAlmostPrime k n ∧ ¬Squarefree n} ≤
      (k - 1) * almostPrimeCounting (k - 1) x := by
  classical
  set B := {m ∈ Icc 1 x | Nat.IsAlmostPrime (k - 1) m} with hB
  have hsub : {n ∈ Icc 1 x | Nat.IsAlmostPrime k n ∧ ¬Squarefree n} ⊆
      (B.sigma fun m => m.primeFactors).image fun q => q.1 * q.2 := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, ⟨hn0, hΩ⟩, hsq⟩ := hn
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpp⟩ := hsq
    have hpn : p ∣ n := (Dvd.intro p rfl).trans hpp
    obtain ⟨m, rfl⟩ := hpn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
    have hpm : p ∣ m := Nat.dvd_of_mul_dvd_mul_left hp.pos hpp
    have hΩm : ArithmeticFunction.cardFactors m = k - 1 := by
      rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hm0,
        ArithmeticFunction.cardFactors_apply_prime hp] at hΩ
      omega
    refine mem_image.mpr ⟨⟨m, p⟩, ?_, by simp [mul_comm]⟩
    rw [mem_sigma]
    refine ⟨?_, Nat.mem_primeFactors.mpr ⟨hp, hpm, hm0⟩⟩
    simp only [hB, mem_filter, mem_Icc]
    refine ⟨⟨Nat.pos_of_ne_zero hm0, ?_⟩, hm0, hΩm⟩
    calc m ≤ p * m := Nat.le_mul_of_pos_left m hp.pos
      _ ≤ x := hnx
  calc #{n ∈ Icc 1 x | Nat.IsAlmostPrime k n ∧ ¬Squarefree n}
      ≤ #((B.sigma fun m => m.primeFactors).image fun q => q.1 * q.2) := card_le_card hsub
    _ ≤ #(B.sigma fun m => m.primeFactors) := card_image_le
    _ = ∑ m ∈ B, #m.primeFactors := card_sigma _ _
    _ ≤ ∑ _m ∈ B, (k - 1) := by
      refine sum_le_sum fun m hm => ?_
      simp only [hB, mem_filter] at hm
      rw [← hm.2.2, ArithmeticFunction.cardFactors_apply]
      exact List.toFinset_card_le _
    _ = (k - 1) * almostPrimeCounting (k - 1) x := by
      rw [sum_const, smul_eq_mul, mul_comm, almostPrimeCounting_eq_card_filter,
        ← show Icc 1 x = Ioc 0 x from Icc_succ_left_eq_Ioc 0 x, hB]

private theorem almostPrimeCounting_le {k : ℕ} (x : ℕ) :
    almostPrimeCounting k x ≤
      Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) +
        (k - 1) * almostPrimeCounting (k - 1) x := by
  classical
  rw [count_eq_card_Icc]
  refine le_trans ?_ (add_le_add_right (card_nonsqfree_le k x) _)
  rw [almostPrimeCounting_eq_card_filter, ← show Icc 1 x = Ioc 0 x from Icc_succ_left_eq_Ioc 0 x]
  rw [← card_filter_add_card_filter_not (s := {n ∈ Icc 1 x | Nat.IsAlmostPrime k n})
    (p := Squarefree)]
  refine add_le_add (card_le_card fun t ht => ?_) (card_le_card fun t ht => ?_)
  · simp only [mem_filter] at ht ⊢
    refine ⟨ht.1.1, ht.2, ?_⟩
    rw [← ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
      (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree ht.1.2.1).mpr ht.2,
      ht.1.2.2]
  · simp only [mem_filter] at ht ⊢
    exact ⟨ht.1.1, ht.1.2, ht.2⟩


/-- For `k ≥ 1`, the correction `(k - 1) π_{k-1}(x)` is negligible against Landau's main term. -/
private theorem correction_isLittleO {k : ℕ} (hk : 1 ≤ k) :
    (fun x : ℕ => ((k - 1 : ℕ) : ℝ) * (almostPrimeCounting (k - 1) x : ℝ)) =o[atTop]
      fun x : ℕ => (x : ℝ) * Real.log (Real.log x) ^ (k - 1) /
        (((k - 1).factorial : ℝ) * Real.log x) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | j
  · simp
  simp only [Nat.add_sub_cancel]
  have hL : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun x : ℕ => ((j : ℝ) + 1) / Real.log (Real.log x)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hL
  have hsmall := ((isLittleO_one_iff ℝ).mpr h0).mul_isBigO
    (isBigO_refl (fun x : ℕ => (x : ℝ) * Real.log (Real.log x) ^ (j + 1) /
      (((j + 1).factorial : ℝ) * Real.log x)) atTop)
  have hT : (fun x : ℕ => (x : ℝ) * Real.log (Real.log x) ^ j /
      ((j.factorial : ℝ) * Real.log x)) =o[atTop]
      fun x : ℕ => (x : ℝ) * Real.log (Real.log x) ^ (j + 1) /
        (((j + 1).factorial : ℝ) * Real.log x) := by
    refine hsmall.congr' ?_ (Eventually.of_forall fun x => by simp)
    filter_upwards [hL.eventually_gt_atTop 0] with x hx
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hπ := (landau_almostPrimeCounting_isEquivalent (j + 1) (by omega)).isBigO
  simp only [Nat.add_sub_cancel] at hπ
  exact (hπ.trans_isLittleO hT).const_mul_left _

/-- Landau's asymptotic for the number of squarefree `n ≤ x` with `k` prime factors. -/
private theorem sqfree_count_isEquivalent {k : ℕ} (hk : 1 ≤ k) :
    (fun x : ℕ => (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) : ℝ))
      ~[atTop] fun x : ℕ => (x : ℝ) * Real.log (Real.log x) ^ (k - 1) /
        (((k - 1).factorial : ℝ) * Real.log x) := by
  have hmain := landau_almostPrimeCounting_isEquivalent k hk
  have hdiff : (fun x : ℕ =>
      (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) : ℝ) -
        (almostPrimeCounting k x : ℝ)) =o[atTop]
      fun x : ℕ => (x : ℝ) * Real.log (Real.log x) ^ (k - 1) /
        (((k - 1).factorial : ℝ) * Real.log x) := by
    refine IsBigO.trans_isLittleO ?_ (correction_isLittleO hk)
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    have h1 := count_le_almostPrimeCounting (k := k) x
    have h2 := almostPrimeCounting_le (k := k) x
    have h1' : (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) : ℝ) ≤
        almostPrimeCounting k x := by exact_mod_cast h1
    have h2' : (almostPrimeCounting k x : ℝ) ≤
        Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) +
          ((k - 1 : ℕ) : ℝ) * almostPrimeCounting (k - 1) x := by exact_mod_cast h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonpos (by linarith),
      abs_of_nonneg (by positivity)]
    linarith
  exact (hmain.add_isLittleO hdiff).congr_left (Eventually.of_forall fun x => by simp)

private theorem sqfree_count_tendsto {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun x : ℕ => Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1))
      atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ⟨Nat.nth (fun t => Squarefree t ∧
    t.primeFactors.card = k) b, fun a ha => ?_⟩
  calc b ≤ b + 1 := Nat.le_succ b
    _ = Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k)
        (Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) b + 1) :=
      (Nat.count_nth_succ_of_infinite (sqfree_infinite hk) b).symm
    _ ≤ _ := Nat.count_monotone _ (by omega)

/-- The logarithm of Landau's main term is asymptotic to the logarithm. -/
private theorem log_phi_isEquivalent (k : ℕ) :
    (fun t : ℝ => Real.log (t * Real.log (Real.log t) ^ (k - 1) /
      (((k - 1).factorial : ℝ) * Real.log t))) ~[atTop] Real.log := by
  have h1 : (fun t => Real.log (Real.log t)) =o[atTop] Real.log :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have h2 : (fun t => Real.log (Real.log (Real.log t))) =o[atTop] Real.log :=
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).trans h1
  have h3 : (fun _ : ℝ => Real.log ((k - 1).factorial : ℝ)) =o[atTop] Real.log :=
    Real.isLittleO_const_log_atTop
  have hE := ((h2.const_mul_left ((k - 1 : ℕ) : ℝ)).sub h3).sub h1
  refine (IsEquivalent.refl.add_isLittleO hE).congr_left ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with t ht hlt
  have hlog0 : 0 < Real.log t := by linarith
  have hll : 0 < Real.log (Real.log t) := Real.log_pos hlt
  have hK : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  simp only [Pi.add_apply]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul ht.ne' (by positivity),
    Real.log_mul hK.ne' hlog0.ne', Real.log_pow]
  ring

private theorem log_sqfree_count_isEquivalent {k : ℕ} (hk : 1 ≤ k) :
    (fun x : ℕ => Real.log
        (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) : ℝ))
      ~[atTop] fun x : ℕ => Real.log x := by
  have hC : Tendsto (fun x : ℕ =>
      (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (sqfree_count_tendsto hk)
  have hlog := ((sqfree_count_isEquivalent hk).symm.log hC).symm
  exact hlog.trans ((log_phi_isEquivalent k).comp_tendsto tendsto_natCast_atTop_atTop)

private theorem loglog_sqfree_count_isEquivalent {k : ℕ} (hk : 1 ≤ k) :
    (fun x : ℕ => Real.log (Real.log
        (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) : ℝ)))
      ~[atTop] fun x : ℕ => Real.log (Real.log x) :=
  (log_sqfree_count_isEquivalent hk).log
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The indices `l ≤ x` with `p_{l,k} ≤ x` are those with `l ≤ π*_k(x)`. -/
private theorem filter_pk_le_eq {k : ℕ} (hk : 1 ≤ k) (x : ℕ) :
    (Icc 1 x).filter
        (fun l => Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1) ≤ x) =
      Icc 1 (Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1)) := by
  have hle : Nat.count (fun t => Squarefree t ∧ t.primeFactors.card = k) (x + 1) ≤ x := by
    rw [Nat.count_succ', ite_eq_right (by simp), add_zero]
    exact Nat.count_le _
  ext l
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hl1, -⟩, hl⟩
    refine ⟨hl1, ?_⟩
    have := (Nat.lt_nth_iff_count_lt (sqfree_infinite hk) (a := l - 1) (b := x + 1)).mpr
      (by omega)
    omega
  · rintro ⟨hl1, hl⟩
    refine ⟨⟨hl1, hl.trans hle⟩, ?_⟩
    have := (Nat.lt_nth_iff_count_lt (sqfree_infinite hk) (a := l - 1) (b := x + 1)).mp
      (by omega)
    omega

/-- `p_{l,k} ~ (k - 1)! l log l / (log log l) ^ (k - 1)`. -/
private theorem pk_isEquivalent {k : ℕ} (hk : 1 ≤ k) :
    (fun l : ℕ => (Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1) : ℝ))
      ~[atTop] fun l : ℕ => ((k - 1).factorial : ℝ) * l * Real.log l /
        Real.log (Real.log l) ^ (k - 1) := by
  set P : ℕ → Prop := fun t => Squarefree t ∧ t.primeFactors.card = k with hP
  have hinf : (Set.ofPred P).Infinite := sqfree_infinite hk
  set pk : ℕ → ℕ := fun l => Nat.nth P (l - 1) with hpk
  have hpk_tendsto : Tendsto pk atTop atTop :=
    (Nat.nth_strictMono hinf).tendsto_atTop.comp (tendsto_sub_atTop_nat 1)
  have hpkR : Tendsto (fun l => (pk l : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpk_tendsto
  -- `l ~ φ (pk l)`, from the counting asymptotic and `count (pk l + 1) = l`.
  have hcount : ∀ l, 1 ≤ l → Nat.count P (pk l + 1) = l := fun l hl => by
    rw [hpk]
    simp only
    rw [Nat.count_nth_succ_of_infinite hinf]
    omega
  have hl : (fun l : ℕ => (l : ℝ)) ~[atTop] fun l => (pk l : ℝ) *
      Real.log (Real.log (pk l)) ^ (k - 1) / (((k - 1).factorial : ℝ) * Real.log (pk l)) := by
    refine ((sqfree_count_isEquivalent hk).comp_tendsto hpk_tendsto).congr_left ?_
    filter_upwards [eventually_ge_atTop 1] with l hl1
    simp only [Function.comp_apply]
    rw [hcount l hl1]
  have hlog : (fun l : ℕ => Real.log (pk l)) ~[atTop] fun l => Real.log l := by
    have h1 := (hl.symm.log (tendsto_natCast_atTop_atTop)).symm
    exact (((log_phi_isEquivalent k).comp_tendsto hpkR).symm.trans h1.symm)
  have hloglog : (fun l : ℕ => Real.log (Real.log (pk l))) ~[atTop]
      fun l => Real.log (Real.log l) :=
    hlog.log (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hprod := ((hl.symm.mul (IsEquivalent.refl (u := fun _ : ℕ =>
    ((k - 1).factorial : ℝ)))).mul hlog).div (hloglog.pow (k - 1))
  refine (hprod.congr_left ?_).congr_right ?_
  · filter_upwards [hpkR.eventually_gt_atTop 0,
      (Real.tendsto_log_atTop.comp hpkR).eventually_gt_atTop 1] with l h0 h1
    have hlog0 : 0 < Real.log (pk l : ℝ) := by
      simp only [Function.comp_apply] at h1
      linarith
    have hll : 0 < Real.log (Real.log (pk l : ℝ)) := Real.log_pos (by simpa using h1)
    have hK : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    field_simp
    rfl
  · filter_upwards with l
    simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    ring


/-! ### Weighted power sums over squarefree numbers with `k` prime factors -/

/-- The algebra behind the asymptotic of `T_x`. -/
private theorem alg_T (K c X L LL A : ℝ) (hK : K ≠ 0) (hL : L ≠ 0) (hLL : LL ≠ 0) (hA : A ≠ 0)
    (α m e d j : ℕ) :
    K ^ α * c ^ m * (X * LL ^ j / (K * L)) ^ (α + m * e + 1) * L ^ (α + m * d) /
        (A * LL ^ (α * j)) =
      c ^ m * X ^ (α + m * e + 1) * LL ^ ((m * e + 1) * j) * L ^ (m * d) /
        (K ^ (m * e + 1) * A * L ^ (m * e + 1)) := by
  rw [div_pow, mul_pow, mul_pow, ← pow_mul, mul_div_assoc', div_mul_eq_mul_div,
    div_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Master asymptotic.** If `f l ~ c l ^ e (log l) ^ d` with `c > 0`, then the sums `S_x(f)` and
`T_x(f)` weighted by the `α`-th powers of the squarefree numbers with `k` prime factors have the
asymptotics of Li's theorems. -/
private theorem master {α m k e d : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) {f : ℕ → ℝ}
    (hf : f ~[atTop] fun l : ℕ => c * (l : ℝ) ^ e * Real.log l ^ d) :
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1) : ℝ) ^ α * f l ^ m)
      ~[atTop] fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * c ^ m * (x : ℝ) ^ (α + m * e + 1) *
        Real.log x ^ (α + m * d) /
          (((α + m * e + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter
        (fun l => Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1) ≤ x),
        (Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1) : ℝ) ^ α * f l ^ m)
      ~[atTop] fun x : ℕ => c ^ m * (x : ℝ) ^ (α + m * e + 1) *
        Real.log (Real.log x) ^ ((m * e + 1) * (k - 1)) * Real.log x ^ (m * d) /
          (((k - 1).factorial : ℝ) ^ (m * e + 1) * ((α + m * e + 1 : ℕ) : ℝ) *
            Real.log x ^ (m * e + 1))) := by
  set P : ℕ → Prop := fun t => Squarefree t ∧ t.primeFactors.card = k with hP
  set K : ℝ := ((k - 1).factorial : ℝ) with hK
  have hK0 : 0 < K := by positivity
  set F : ℕ → ℝ := fun l => (Nat.nth P (l - 1) : ℝ) ^ α * f l ^ m with hF
  set w : ℕ → ℝ := fun l =>
    Real.log l ^ (α + m * d) * (Real.log (Real.log l) ^ (α * (k - 1)))⁻¹ with hw
  -- the summand is equivalent to `K ^ α c ^ m l ^ (α + m e) w l`
  have hterm : F ~[atTop] fun l : ℕ => K ^ α * c ^ m * ((l : ℝ) ^ (α + m * e) * w l) := by
    refine (((pk_isEquivalent hk).pow α).mul (hf.pow m)).congr_right ?_
    filter_upwards with l
    simp only [Pi.mul_apply, Pi.pow_apply, hw]
    ring
  have hsumw := sum_pow_log_loglog_isEquivalent (α + m * e) (α + m * d) (α * (k - 1))
  have hS : (fun x : ℕ => ∑ l ∈ Icc 1 x, K ^ α * c ^ m * ((l : ℝ) ^ (α + m * e) * w l))
      ~[atTop] fun x : ℕ => K ^ α * c ^ m *
        ((x : ℝ) ^ (α + m * e + 1) * w x / ((α + m * e : ℕ) + 1)) := by
    simp_rw [← mul_sum]
    exact (IsEquivalent.refl (u := fun _ : ℕ => K ^ α * c ^ m)).mul hsumw
  have hdiv : Tendsto (fun x : ℕ => ∑ l ∈ Icc 1 x, K ^ α * c ^ m * ((l : ℝ) ^ (α + m * e) * w l))
      atTop atTop := by
    refine hS.symm.tendsto_atTop ?_
    exact ((tendsto_pow_mul_weight (α + m * e) (α + m * d) (α * (k - 1))).atTop_div_const
      (by positivity)).const_mul_atTop (by positivity)
  have hvpos : ∀ᶠ l : ℕ in atTop, 0 ≤ K ^ α * c ^ m * ((l : ℝ) ^ (α + m * e) * w l) := by
    filter_upwards [weight_pos (α + m * d) (α * (k - 1))] with l hl
    have := hl.le
    positivity
  have hSx := (sum_Icc_isEquivalent hterm hvpos hdiv).trans hS
  -- the sum over `l ≤ x`
  have hS' : (fun x : ℕ => ∑ l ∈ Icc 1 x, F l) ~[atTop] fun x : ℕ => K ^ α * c ^ m *
      (x : ℝ) ^ (α + m * e + 1) * Real.log x ^ (α + m * d) /
        (((α + m * e + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1))) := by
    refine hSx.congr_right ?_
    filter_upwards with x
    simp only [hw]
    push_cast
    simp only [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨hS', ?_⟩
  -- the sum over `p_{l,k} ≤ x` is the sum over `l ≤ π*(x)`
  set N : ℕ → ℕ := fun x => Nat.count P (x + 1) with hN
  have hT : (fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => Nat.nth P (l - 1) ≤ x), F l) =
      fun x => ∑ l ∈ Icc 1 (N x), F l := by
    funext x
    rw [filter_pk_le_eq hk x]
  rw [hT]
  have hcomp := hS'.comp_tendsto (sqfree_count_tendsto hk)
  have hNx := sqfree_count_isEquivalent hk
  have hlogN := log_sqfree_count_isEquivalent hk
  have hloglogN := loglog_sqfree_count_isEquivalent hk
  have hG := (((IsEquivalent.refl (u := fun _ : ℕ => K ^ α * c ^ m)).mul
    (hNx.pow (α + m * e + 1))).mul (hlogN.pow (α + m * d))).div
    ((IsEquivalent.refl (u := fun _ : ℕ => ((α + m * e + 1 : ℕ) : ℝ))).mul
      (hloglogN.pow (α * (k - 1))))
  refine (hcomp.trans (hG.congr_left ?_)).congr_right ?_
  · filter_upwards with x
    simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  · have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually_gt_atTop 0,
      (Real.tendsto_log_atTop.comp hlog).eventually_gt_atTop 0] with x hx1 hx2
    simp only [Function.comp_apply] at hx2
    simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, hK]
    have hA : (0 : ℝ) < ((α + m * e + 1 : ℕ) : ℝ) := by positivity
    have hK1 : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
    exact alg_T _ _ _ _ _ _ hK1 hx1.ne' hx2.ne' hA.ne' α m e d (k - 1)

end sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent

open sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent in
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

-- `hα` and `hm` are hypotheses of the source theorem that the proof does not use; they keep their
-- names so that callers can supply them by name.
set_option linter.unusedVariables false in
open sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent in
/-- **Type III alternating hyperharmonic power sums weighted by squarefree $k$-prime numbers.**
Let $\alpha, m, k, p, y \ge 1$ and $q \ge 2$ be integers. Let $p_{\ell,k}$ be the $\ell$-th
squarefree number with exactly $k$ prime factors, let $H_n^{(s,r,3)}$ be the signed iterated
partial sum of order $r$, with alternating signs, of the alternating generalized harmonic numbers
$\bar H_n^{(s)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-s}$, let $\zeta(q) = \sum_{n \ge 1} n^{-q}$, and
let $\bar\zeta$ be the alternating zeta function ($\bar\zeta(1) = \log 2$). For a real sequence
$f$ write
$$S_x(f) = \sum_{\ell=1}^{x} p_{\ell,k}^\alpha f(\ell)^m, \qquad
T_x(f) = \sum_{\substack{1 \le \ell \le x \\ p_{\ell,k} \le x}} p_{\ell,k}^\alpha f(\ell)^m,$$
put $K = (k-1)!$, $E = my + 1$, $F = m(y-1) + 1$, $A = \alpha + E$ and $B = \alpha + F$, and let
$f_1(\ell) = H_\ell^{(p,2y+1,3)}$, $f_2(\ell) = H_\ell^{(1,2y,3)}$,
$f_3(\ell) = H_{2\ell-1}^{(q,2y,3)}$ and $f_4(\ell) = H_{2\ell}^{(q,2y,3)}$. Then, as the natural
number $x$ tends to infinity,
$$S_x(f_1) \sim
\frac{K^\alpha \bar\zeta(p)^m x^A (\log x)^\alpha}{(2^y y!)^m A (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_1) \sim
\frac{\bar\zeta(p)^m x^A (\log \log x)^{E(k-1)}}{(2^y y!)^m K^E A (\log x)^E},$$
$$S_x(f_2) \sim
\frac{K^\alpha x^B (\log x)^{\alpha+m}}{(2^y (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_2) \sim
\frac{x^B (\log \log x)^{F(k-1)}}{(2^y (y-1)!)^m K^F B (\log x)^{m(y-2)+1}},$$
$$S_x(f_3) \sim \frac{K^\alpha (\zeta(q) + \bar\zeta(q))^m x^B (\log x)^\alpha}
{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_3) \sim \frac{(\zeta(q) + \bar\zeta(q))^m x^B (\log \log x)^{F(k-1)}}
{(2 (y-1)!)^m K^F B (\log x)^F},$$
$$S_x(f_4) \sim \frac{K^\alpha (\zeta(q) - \bar\zeta(q))^m x^B (\log x)^\alpha}
{(2 (y-1)!)^m B (\log \log x)^{\alpha(k-1)}},
\qquad T_x(f_4) \sim \frac{(\zeta(q) - \bar\zeta(q))^m x^B (\log \log x)^{F(k-1)}}
{(2 (y-1)!)^m K^F B (\log x)^F}.$$

The exponent $m(y-2)+1$ of $\log x$ may be negative; the power is then an integer power.

The paper prints the first two items with the type I numbers $H_\ell^{(p,2y+1,1)}$, but their
asymptotics carry $\bar\zeta(p)$, the section treats type III, and the proof sums
$H_\ell^{(p,2y+1,3)}$; they are read here with type III.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 18 (`jis-2024-24.4.1-thm-18`). -/
public theorem sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    {α m k p q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hk : 1 ≤ k) (hp : 1 ≤ p) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * alternatingZeta p ^ m *
        (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) *
        Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
            ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) := by
  intro pk ζq HIII
  have hz := zeta_pos hq
  have hzp := alternatingZeta_pos hp
  have hzq := alternatingZeta_pos (show 1 ≤ q by omega)
  have hrel := zeta_sub_alternatingZeta hq
  -- the four sequences and their asymptotics `c l ^ e (log l) ^ d`
  have hf₁ : (fun l : ℕ => HIII p (2 * y + 1) l) ~[atTop] fun l : ℕ =>
      alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ) * (l : ℝ) ^ y * Real.log l ^ 0 := by
    refine (typeIII_odd_order hp).congr_right ?_
    filter_upwards with l
    rw [pow_zero, mul_one]
    ring
  have hf₂ : (fun l : ℕ => HIII 1 (2 * y) l) ~[atTop] fun l : ℕ =>
      1 / ((2 ^ y * (y - 1).factorial : ℕ) : ℝ) * (l : ℝ) ^ (y - 1) * Real.log l ^ 1 := by
    refine (typeIII_even_order_one hy).congr_right ?_
    filter_upwards with l
    rw [pow_one]
    ring
  have hf₃ : (fun l : ℕ => HIII q (2 * y) (2 * l - 1)) ~[atTop] fun l : ℕ =>
      (ζq + alternatingZeta q) / ((2 * (y - 1).factorial : ℕ) : ℝ) * (l : ℝ) ^ (y - 1) *
        Real.log l ^ 0 := by
    refine (typeIII_even_order_odd_index hy hq).congr_right ?_
    filter_upwards with l
    rw [pow_zero, mul_one]
    ring
  have hf₄ : (fun l : ℕ => HIII q (2 * y) (2 * l)) ~[atTop] fun l : ℕ =>
      (ζq - alternatingZeta q) / ((2 * (y - 1).factorial : ℕ) : ℝ) * (l : ℝ) ^ (y - 1) *
        Real.log l ^ 0 := by
    refine (typeIII_even_order_even_index hy hq).congr_right ?_
    filter_upwards with l
    rw [pow_zero, mul_one]
    ring
  have hc₁ : 0 < alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ) := by positivity
  have hc₂ : 0 < 1 / ((2 ^ y * (y - 1).factorial : ℕ) : ℝ) := by positivity
  have hc₃ : 0 < (ζq + alternatingZeta q) / ((2 * (y - 1).factorial : ℕ) : ℝ) := by
    have : 0 < ζq + alternatingZeta q := by positivity
    positivity
  have hc₄ : 0 < (ζq - alternatingZeta q) / ((2 * (y - 1).factorial : ℕ) : ℝ) := by
    have : 0 < ζq - alternatingZeta q := by
      change 0 < (∑' i : ℕ, 1 / (i : ℝ) ^ q) - alternatingZeta q
      rw [hrel]
      positivity
    positivity
  obtain ⟨h₁S, h₁T⟩ := master (α := α) (m := m) hk hc₁ hf₁
  obtain ⟨h₂S, h₂T⟩ := master (α := α) (m := m) hk hc₂ hf₂
  obtain ⟨h₃S, h₃T⟩ := master (α := α) (m := m) hk hc₃ hf₃
  obtain ⟨h₄S, h₄T⟩ := master (α := α) (m := m) hk hc₄ hf₄
  have hlog : ∀ᶠ x : ℕ in atTop, Real.log x ≠ 0 :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ne_atTop 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine h₁S.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, add_zero, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring
  · refine h₁T.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, pow_zero, mul_one, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring
  · refine h₂S.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_one, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring
  · refine h₂T.congr_right ?_
    filter_upwards [hlog] with x hx
    have hz : (m : ℤ) * ((y : ℤ) - 2) + 1 = ((m * (y - 1) + 1 : ℕ) : ℤ) - (m : ℤ) := by
      push_cast [Nat.cast_sub hy]
      ring
    rw [hz, zpow_sub₀ hx, zpow_natCast, zpow_natCast]
    simp only [mul_one, div_eq_mul_inv, mul_inv, mul_pow, inv_pow, inv_inv]
    ring
  · refine h₃S.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, add_zero, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring
  · refine h₃T.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, pow_zero, mul_one, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring
  · refine h₄S.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, add_zero, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring
  · refine h₄T.congr_right (Eventually.of_forall fun x => ?_)
    simp only [mul_zero, pow_zero, mul_one, div_eq_mul_inv, mul_inv, mul_pow, inv_pow]
    ring

end MetaMathlibExt

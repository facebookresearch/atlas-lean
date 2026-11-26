/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import MathlibExt.Probability.ConvexDistanceInequality
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Find
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Talagrand's concentration inequality around the mean

Concentration of bounded independent real variables under a convex Euclidean
`1`-Lipschitz function, around the expectation.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Theorem 2.1.13, inequalities `(2.18)` (median) and `(2.19)` (mean).
* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205.
-/

@[expose] public section

namespace MathlibExt.Probability.TalagrandConcentrationWanted

open MeasureTheory ProbabilityTheory Real
open MathlibExt.Probability.ConvexDistance

private theorem sublevel_separation {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hX : ∀ i ω, |X i ω| ≤ K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hL : LipschitzWith 1 F) (a : ℝ)
    (hA : {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a}.Nonempty)
    (x : Fin n → Ω) :
    F (WithLp.toLp 2 fun i => X i (x i)) - a ≤
      2 * K * convexDistance {y : Fin n → Ω |
        F (WithLp.toLp 2 fun i => X i (y i)) ≤ a} x := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => X i (x i)
  let A := {y : Fin n → Ω | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a}
  let D : Set (EuclideanSpace ℝ (Fin n)) := {s | ∃ z : EuclideanSpace ℝ (Fin n),
    F z ≤ a ∧ ∀ i, |v i - z i| ≤ 2 * K * s i}
  have hSD : convexSupport A x ⊆ D := by
    rintro s ⟨y, hy, hs, heq⟩
    refine ⟨WithLp.toLp 2 fun i => X i (y i), hy, fun i => ?_⟩
    rcases hs i with h | h
    · change |X i (x i) - X i (y i)| ≤ 2 * K * s i
      rw [heq i h, sub_self, abs_zero, h, mul_zero]
    · change |X i (x i) - X i (y i)| ≤ 2 * K * s i
      rw [h, mul_one]
      calc |X i (x i) - X i (y i)| ≤ |X i (x i)| + |X i (y i)| := abs_sub _ _
        _ ≤ K + K := add_le_add (hX i (x i)) (hX i (y i))
        _ = 2 * K := by ring
  have hD : Convex ℝ D := by
    rintro s ⟨z, hz, hzs⟩ t ⟨w, hw, hwt⟩ b c hb hc hbc
    refine ⟨b • z + c • w, ?_, fun i => ?_⟩
    · calc F (b • z + c • w) ≤ b * F z + c * F w :=
            hF.2 (Set.mem_univ _) (Set.mem_univ _) hb hc hbc
        _ ≤ b * a + c * a := add_le_add (mul_le_mul_of_nonneg_left hz hb)
            (mul_le_mul_of_nonneg_left hw hc)
        _ = a := by rw [← add_mul, hbc, one_mul]
    · have he : v i - (b • z + c • w) i =
          b * (v i - z i) + c * (v i - w i) := by
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        calc v i - (b * z i + c * w i) = (b + c) * v i - (b * z i + c * w i) := by
              rw [hbc, one_mul]
          _ = b * (v i - z i) + c * (v i - w i) := by ring
      rw [he]
      calc |b * (v i - z i) + c * (v i - w i)| ≤
            |b * (v i - z i)| + |c * (v i - w i)| := abs_add_le _ _
        _ = b * |v i - z i| + c * |v i - w i| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
        _ ≤ b * (2 * K * s i) + c * (2 * K * t i) :=
            add_le_add (mul_le_mul_of_nonneg_left (hzs i) hb)
              (mul_le_mul_of_nonneg_left (hwt i) hc)
        _ = 2 * K * (b • s + c • t) i := by
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            ring
  obtain ⟨s, hs, hsn⟩ := exists_mem_convexHull_norm_eq hA x
  obtain ⟨z, hz, hzs⟩ := convexHull_min hSD hD hs
  have hnorm : ‖v - z‖ ≤ 2 * K * ‖s‖ := by
    have hsum : ‖v - z‖ ^ 2 ≤ (2 * K * ‖s‖) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hi := pow_le_pow_left₀ (abs_nonneg (v i - z i)) (hzs i) 2
      simpa only [PiLp.sub_apply, sq_abs, mul_pow] using hi
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hK)
      (norm_nonneg _))).mp hsum
  have hdist : |F v - F z| ≤ ‖v - z‖ := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
      using hL.dist_le_mul v z
  calc F v - a ≤ F v - F z := sub_le_sub_left hz _
    _ ≤ |F v - F z| := le_abs_self _
    _ ≤ ‖v - z‖ := hdist
    _ ≤ 2 * K * ‖s‖ := hnorm
    _ = 2 * K * convexDistance A x := by rw [hsn]

private theorem product_sublevel_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (K : ℝ) (hK : 0 < K)
    (hX : ∀ i ω, |X i ω| ≤ K) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (hL : LipschitzWith 1 F) (a t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {y | F (WithLp.toLp 2 fun i => X i (y i)) ≤ a} *
      (Measure.pi (fun _ : Fin n => μ)).real
        {y | a + t * K ≤ F (WithLp.toLp 2 fun i => X i (y i))} ≤ exp (-t ^ 2 / 16) := by
  let Q := Measure.pi (fun _ : Fin n => μ)
  let f : (Fin n → Ω) → ℝ := fun y => F (WithLp.toLp 2 fun i => X i (y i))
  let A := {y | f y ≤ a}
  let B := {y | a + t * K ≤ f y}
  change Q.real A * Q.real B ≤ exp (-t ^ 2 / 16)
  have hfm : Measurable f := hL.continuous.measurable.comp
    ((WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i => (hXm i).comp (measurable_pi_apply i)))
  have hAm : MeasurableSet A := measurableSet_le hfm measurable_const
  by_cases hA : Q A = 0
  · simp only [show Q.real A = 0 from by simp [measureReal_def, hA], zero_mul]
    exact (exp_pos _).le
  have hAn : A.Nonempty := nonempty_of_measure_ne_zero hA
  have hsub : B ⊆ {x | t / 2 ≤ convexDistance A x} := by
    intro x hx
    have hg := sublevel_separation n X K hK.le hX F hF hL a hAn x
    change a + t * K ≤ f x at hx
    change f x - a ≤ 2 * K * convexDistance A x at hg
    apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * K by positivity)).mp
    calc 2 * K * (t / 2) = t * K := by ring
      _ ≤ f x - a := by linarith
      _ ≤ 2 * K * convexDistance A x := hg
  have htail := MathlibExt.Probability.ConvexDistanceWanted.measure_le_convexDistance_le
    μ n hAm (show 0 ≤ t / 2 by positivity)
  have he : -(t / 2) ^ 2 / 4 = -t ^ 2 / 16 := by ring
  rw [he] at htail
  have hB : Q B ≤ ENNReal.ofReal (exp (-t ^ 2 / 16)) * (Q A)⁻¹ :=
    (measure_mono hsub).trans htail
  have hprod : Q A * Q B ≤ ENNReal.ofReal (exp (-t ^ 2 / 16)) := by
    calc Q A * Q B ≤ Q A * (ENNReal.ofReal (exp (-t ^ 2 / 16)) * (Q A)⁻¹) :=
          mul_le_mul' le_rfl hB
      _ = ENNReal.ofReal (exp (-t ^ 2 / 16)) := by
          rw [mul_left_comm, ENNReal.mul_inv_cancel hA (measure_ne_top _ _), mul_one]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprod
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (exp_pos _).le] using hr

private theorem independent_sublevel_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (K : ℝ) (hK : 0 < K) (hX : ∀ i ω, |X i ω| ≤ K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (hL : LipschitzWith 1 F) (a t : ℝ) (ht : 0 < t) :
    P.real {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ a} *
      P.real {ω | a + t * K ≤ F (WithLp.toLp 2 fun i => X i ω)} ≤ exp (-t ^ 2 / 16) := by
  let Q := Measure.pi (fun _ : Fin n => P)
  let g : (Fin n → ℝ) → ℝ := fun y => F (WithLp.toLp 2 y)
  have hgm : Measurable g := hL.continuous.measurable.comp (WithLp.measurable_toLp 2 _)
  have hj : P.map (fun ω i => X i ω) = Q.map (fun y i => X i (y i)) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i => (hXm i).aemeasurable) hXi,
      Measure.pi_map_pi (fun i => (hXm i).aemeasurable)]
  have hm : Measurable (fun ω i => X i ω) := measurable_pi_iff.mpr hXm
  have hmq : Measurable (fun (y : Fin n → Ω) i => X i (y i)) :=
    measurable_pi_iff.mpr fun i => (hXm i).comp (measurable_pi_apply i)
  have hlo : P.real {ω | g (fun i => X i ω) ≤ a} =
      Q.real {y | g (fun i => X i (y i)) ≤ a} := by
    calc P.real {ω | g (fun i => X i ω) ≤ a} =
          (P.map (fun ω i => X i ω)).real {z | g z ≤ a} :=
            (map_measureReal_apply hm (measurableSet_le hgm measurable_const)).symm
      _ = (Q.map (fun y i => X i (y i))).real {z | g z ≤ a} := by rw [hj]
      _ = Q.real {y | g (fun i => X i (y i)) ≤ a} :=
            map_measureReal_apply hmq (measurableSet_le hgm measurable_const)
  have hhi : P.real {ω | a + t * K ≤ g (fun i => X i ω)} =
      Q.real {y | a + t * K ≤ g (fun i => X i (y i))} := by
    calc P.real {ω | a + t * K ≤ g (fun i => X i ω)} =
          (P.map (fun ω i => X i ω)).real {z | a + t * K ≤ g z} :=
            (map_measureReal_apply hm (measurableSet_le measurable_const hgm)).symm
      _ = (Q.map (fun y i => X i (y i))).real {z | a + t * K ≤ g z} := by rw [hj]
      _ = Q.real {y | a + t * K ≤ g (fun i => X i (y i))} :=
            map_measureReal_apply hmq (measurableSet_le measurable_const hgm)
  change P.real {ω | g (fun i => X i ω) ≤ a} *
    P.real {ω | a + t * K ≤ g (fun i => X i ω)} ≤ exp (-t ^ 2 / 16)
  rw [hlo, hhi]
  exact product_sublevel_tail P n X hXm K hK hX F hF hL a t ht

private theorem bounded_values {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ)
    (K : ℝ) (hX : ∀ i ω, |X i ω| ≤ K) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : LipschitzWith 1 F) :
    ∃ R : ℝ, ∀ ω, |F (WithLp.toLp 2 fun i => X i ω)| ≤ R := by
  refine ⟨|F 0| + sqrt (∑ _ : Fin n, K ^ 2), fun ω => ?_⟩
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => X i ω
  have hn : ‖v‖ ≤ sqrt (∑ _ : Fin n, K ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    apply sqrt_le_sqrt
    exact Finset.sum_le_sum fun i _ =>
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hX i ω))).mpr (hX i ω)
  have hd : |F v - F 0| ≤ ‖v‖ := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_zero_right]
      using hL.dist_le_mul v 0
  calc |F v| ≤ |F v - F 0| + |F 0| := by
        simpa only [sub_add_cancel] using abs_add_le (F v - F 0) (F 0)
    _ ≤ sqrt (∑ _ : Fin n, K ^ 2) + |F 0| := add_le_add (hd.trans hn) le_rfl
    _ = |F 0| + sqrt (∑ _ : Fin n, K ^ 2) := add_comm _ _

open scoped Classical in
private theorem exists_approximate_median {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (R : ℝ) (hf : ∀ ω, |f ω| ≤ R) (K : ℝ) (hK : 0 < K) :
    ∃ a : ℝ, 1 / 2 ≤ P.real {ω | f ω ≤ a} ∧
      1 / 2 ≤ P.real {ω | a - K ≤ f ω} := by
  classical
  let b := -R - K
  have hex : ∃ n : ℕ, 1 / 2 ≤ P.real {ω | f ω ≤ b + (n : ℝ) * K} := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((R - b) / K)
    have hbound : R < b + (n : ℝ) * K := by
      have := (div_lt_iff₀ hK).mp hn
      linarith
    have hset : {ω | f ω ≤ b + (n : ℝ) * K} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ((le_abs_self _).trans (hf ω)).trans hbound.le
    exact ⟨n, by rw [hset, probReal_univ]; norm_num⟩
  have hzero : ¬(1 / 2 ≤ P.real {ω | f ω ≤ b + (0 : ℝ) * K}) := by
    have hset : {ω | f ω ≤ b + (0 : ℝ) * K} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have := (abs_le.mp (hf ω)).1
      dsimp [b] at h
      linarith
    rw [hset, measureReal_empty]
    norm_num
  have hn : Nat.find hex ≠ 0 := by
    intro h
    apply hzero
    simpa only [Nat.cast_zero] using (Nat.find_eq_zero hex).mp h
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨b + ((k + 1 : ℕ) : ℝ) * K, ?_, ?_⟩
  · simpa only [hk] using Nat.find_spec hex
  · have hprev : P.real {ω | f ω ≤ b + (k : ℝ) * K} < 1 / 2 :=
      not_le.mp (Nat.find_min hex (by omega))
    have hc := measureReal_add_measureReal_compl (μ := P)
      (measurableSet_le hfm (measurable_const (a := b + (k : ℝ) * K)))
    rw [probReal_univ] at hc
    have hm : {ω | f ω ≤ b + (k : ℝ) * K}ᶜ ⊆
        {ω | b + ((k + 1 : ℕ) : ℝ) * K - K ≤ f ω} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      change b + ((k + 1 : ℕ) : ℝ) * K - K ≤ f ω
      push_cast
      linarith
    have := measureReal_mono (μ := P) hm
    linarith

private theorem approximate_median_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (K : ℝ) (hK : 0 < K)
    (hsep : ∀ a t : ℝ, 0 < t → P.real {ω | f ω ≤ a} *
      P.real {ω | a + t * K ≤ f ω} ≤ exp (-t ^ 2 / 16))
    (a : ℝ) (ha : 1 / 2 ≤ P.real {ω | f ω ≤ a})
    (ha' : 1 / 2 ≤ P.real {ω | a - K ≤ f ω}) (t : ℝ) (ht : 1 < t) :
    P.real {ω | t ≤ |(f ω - a) / K|} ≤ 4 * exp (-(t - 1) ^ 2 / 16) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hu : P.real {ω | a + t * K ≤ f ω} ≤ 2 * exp (-(t - 1) ^ 2 / 16) := by
    have hh := hsep a t ht0
    have hp := mul_le_mul_of_nonneg_right ha
      (measureReal_nonneg (μ := P) (s := {ω | a + t * K ≤ f ω}))
    have he : exp (-t ^ 2 / 16) ≤ exp (-(t - 1) ^ 2 / 16) :=
      exp_le_exp.mpr (by nlinarith)
    linarith
  have hl : P.real {ω | f ω ≤ a - t * K} ≤ 2 * exp (-(t - 1) ^ 2 / 16) := by
    have hh := hsep (a - t * K) (t - 1) (sub_pos.mpr ht)
    have he : a - t * K + (t - 1) * K = a - K := by ring
    rw [he] at hh
    have hp := mul_le_mul_of_nonneg_left ha'
      (measureReal_nonneg (μ := P) (s := {ω | f ω ≤ a - t * K}))
    linarith
  have hsub : {ω | t ≤ |(f ω - a) / K|} ⊆
      {ω | a + t * K ≤ f ω} ∪ {ω | f ω ≤ a - t * K} := by
    intro ω hω
    change t ≤ |(f ω - a) / K| at hω
    rw [abs_div, abs_of_pos hK] at hω
    have hh := (le_div_iff₀ hK).mp hω
    by_cases h : 0 ≤ f ω - a
    · rw [abs_of_nonneg h] at hh
      left
      change a + t * K ≤ f ω
      linarith
    · rw [abs_of_neg (not_le.mp h)] at hh
      right
      change f ω ≤ a - t * K
      linarith
  calc P.real {ω | t ≤ |(f ω - a) / K|} ≤
        P.real ({ω | a + t * K ≤ f ω} ∪ {ω | f ω ≤ a - t * K}) := measureReal_mono hsub
    _ ≤ P.real {ω | a + t * K ≤ f ω} + P.real {ω | f ω ≤ a - t * K} :=
        measureReal_union_le _ _
    _ ≤ 4 * exp (-(t - 1) ^ 2 / 16) := by linarith

private theorem mean_shift_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Integrable f P)
    (K : ℝ) (hK : 0 < K) (a : ℝ)
    (htail : ∀ t : ℝ, 1 < t → P.real {ω | t ≤ |(f ω - a) / K|} ≤
      4 * exp (-(t - 1) ^ 2 / 16)) :
    |(∫ ω, f ω ∂P) - a| ≤ (128 * exp 1) * K := by
  let Y : Ω → ℝ := fun ω => (f ω - a) / K
  have hYi : Integrable Y P := (hf.sub (integrable_const a)).div_const K
  have hb : ∀ t : ℝ, 0 < t → P.real {ω | t ≤ |Y ω|} ≤
      (4 * exp 1) * exp ((-1 / 32) * t) := by
    intro t ht
    by_cases ht1 : 1 < t
    · have hh := htail t ht1
      have he : exp (-(t - 1) ^ 2 / 16) ≤ exp 1 * exp ((-1 / 32) * t) := by
        rw [← exp_add]
        apply exp_le_exp.mpr
        nlinarith [sq_nonneg (t - 5 / 4)]
      exact hh.trans (by nlinarith)
    · have he : 1 ≤ exp (1 + (-1 / 32) * t) :=
        one_le_exp_iff.mpr (by linarith)
      have hh : P.real {ω | t ≤ |Y ω|} ≤ 1 := measureReal_le_one
      rw [mul_assoc, ← exp_add]
      linarith
  have hbound : (∫ ω, |Y ω| ∂P) ≤ 128 * exp 1 := by
    rw [hYi.abs.integral_eq_integral_meas_le (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
    calc (∫ t in Set.Ioi 0, P.real {ω | t ≤ |Y ω|}) ≤
          ∫ t in Set.Ioi 0, (4 * exp 1) * exp ((-1 / 32) * t) := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun t => measureReal_nonneg
            · exact (integrableOn_exp_mul_Ioi (a := (-1 / 32 : ℝ)) (by norm_num) 0).const_mul _
            · exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => hb t ht
      _ = 128 * exp 1 := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num), mul_zero, exp_zero]
          ring
  have hmean : |(∫ ω, Y ω ∂P)| ≤ ∫ ω, |Y ω| ∂P := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm Y
  have he : (∫ ω, Y ω ∂P) = ((∫ ω, f ω ∂P) - a) / K := by
    rw [integral_div, integral_sub hf (integrable_const a), integral_const, probReal_univ,
      one_smul]
  rw [he, abs_div, abs_of_pos hK] at hmean
  exact (div_le_iff₀ hK).mp (hmean.trans hbound)

/-- **Talagrand's concentration inequality around the mean** (Tao, *Topics in Random Matrix
Theory*, Theorem 2.1.13, `(2.19)`, real case). Under the hypotheses of
`talagrand_concentration_median`, `P(|F(X) - 𝔼 F(X)| ≥ λK) ≤ C exp(-cλ²)` for every `λ > 0`.
(`F(X)` is bounded and measurable, so its expectation is a genuine integral.) -/
public theorem talagrand_concentration_mean :
    ∃ C > 0, ∃ c > 0, ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (K : ℝ), 0 < K →
      (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i ω, |X i ω| ≤ K) →
      ∀ F : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ Set.univ F → LipschitzWith 1 F →
      ∀ t : ℝ, 0 < t →
        P.real {ω | t * K ≤ |F (WithLp.toLp 2 fun i => X i ω) -
          ∫ ω', F (WithLp.toLp 2 fun i => X i ω') ∂P|} ≤ C * exp (-c * t ^ 2)
    := by
  let A : ℝ := 128 * exp 1
  let B : ℝ := A + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨4 * exp (B ^ 2 / 16), by positivity, 1 / 64, by norm_num, ?_⟩
  intro Ω mΩ P hP n X K hK hXm hXi hX F hF hL t ht
  let : IsProbabilityMeasure P := hP
  let f : Ω → ℝ := fun ω => F (WithLp.toLp 2 fun i => X i ω)
  have hfm : Measurable f := hL.continuous.measurable.comp
    ((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hXm))
  obtain ⟨R, hR⟩ := bounded_values n X K hX F hL
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable R
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hR ω)
  have hsep : ∀ a s : ℝ, 0 < s → P.real {ω | f ω ≤ a} *
      P.real {ω | a + s * K ≤ f ω} ≤ exp (-s ^ 2 / 16) :=
    independent_sublevel_tail P n X hXm hXi K hK hX F hF hL
  obtain ⟨a, ha, ha'⟩ := exists_approximate_median P f hfm R hR K hK
  have hpiv := approximate_median_tail P f K hK hsep a ha ha'
  have hmean : |(∫ ω, f ω ∂P) - a| ≤ A * K := mean_shift_of_tail P f hfi K hK a hpiv
  change P.real {ω | t * K ≤ |f ω - ∫ ω', f ω' ∂P|} ≤
    (4 * exp (B ^ 2 / 16)) * exp (-(1 / 64) * t ^ 2)
  have he : -(1 / 64 : ℝ) * t ^ 2 = -t ^ 2 / 64 := by ring
  rw [he]
  by_cases hlarge : 2 * B < t
  · have hs : 1 < t - A := by dsimp [B] at hlarge; linarith
    have hsub : {ω | t * K ≤ |f ω - ∫ ω', f ω' ∂P|} ⊆
        {ω | t - A ≤ |(f ω - a) / K|} := by
      intro ω hω
      change t * K ≤ |f ω - ∫ ω', f ω' ∂P| at hω
      change t - A ≤ |(f ω - a) / K|
      rw [abs_div, abs_of_pos hK, le_div_iff₀ hK]
      have htri : |f ω - ∫ ω', f ω' ∂P| ≤ |f ω - a| + |(∫ ω', f ω' ∂P) - a| := by
        simpa only [sub_add_sub_cancel, abs_sub_comm] using
          abs_add_le (f ω - a) (a - ∫ ω', f ω' ∂P)
      nlinarith
    have hexp : exp (-((t - A) - 1) ^ 2 / 16) ≤ exp (-t ^ 2 / 64) := by
      apply exp_le_exp.mpr
      have hs' : t / 2 ≤ (t - A) - 1 := by dsimp [B] at hlarge; linarith
      have hh := pow_le_pow_left₀ (by linarith : 0 ≤ t / 2) hs' 2
      nlinarith
    have hC : 4 ≤ 4 * exp (B ^ 2 / 16) := by
      have := one_le_exp_iff.mpr (show 0 ≤ B ^ 2 / 16 by positivity)
      linarith
    calc P.real {ω | t * K ≤ |f ω - ∫ ω', f ω' ∂P|} ≤
          P.real {ω | t - A ≤ |(f ω - a) / K|} := measureReal_mono hsub
      _ ≤ 4 * exp (-((t - A) - 1) ^ 2 / 16) := hpiv (t - A) hs
      _ ≤ 4 * exp (-t ^ 2 / 64) := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ (4 * exp (B ^ 2 / 16)) * exp (-t ^ 2 / 64) :=
          mul_le_mul_of_nonneg_right hC (exp_pos _).le
  · have htB : t ≤ 2 * B := not_lt.mp hlarge
    have hs := pow_le_pow_left₀ ht.le htB 2
    have hexp : 1 ≤ exp (B ^ 2 / 16 + -t ^ 2 / 64) :=
      one_le_exp_iff.mpr (by nlinarith)
    calc P.real {ω | t * K ≤ |f ω - ∫ ω', f ω' ∂P|} ≤ 1 := measureReal_le_one
      _ ≤ 4 * exp (B ^ 2 / 16 + -t ^ 2 / 64) := by linarith
      _ = (4 * exp (B ^ 2 / 16)) * exp (-t ^ 2 / 64) := by rw [exp_add]; ring


end MathlibExt.Probability.TalagrandConcentrationWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators
open scoped MeasureTheory

namespace MetaMathlibExt

section

/-- Finite intersection of a.e. statements. -/
private theorem kh_ae_all_of_finset {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {ι : Type*} {s : Finset ι} {p : ι → Ω → Prop}
    (h : ∀ i ∈ s, ∀ᵐ ω ∂μ, p i ω) : ∀ᵐ ω ∂μ, ∀ i ∈ s, p i ω := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact Filter.Eventually.of_forall fun ω i hi => absurd hi (Finset.notMem_empty i)
  | @insert j s' hj ih =>
    have h1 := h j (Finset.mem_insert_self j s')
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    filter_upwards [h1, h2] with ω h1 h2 i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h1
    · exact h2 i hi

/-- Even moments of a Rademacher variable equal 1. -/
private theorem kh_integral_rademacher_pow_even {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hae : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1) {n : ℕ} (hev : Even n) :
    MeasureTheory.integral μ (fun ω => (X ω) ^ n) = 1 := by
  have h1 : (fun ω => (X ω) ^ n) =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [hae] with ω hω
    rcases hω with h | h
    · rw [h, one_pow]
    · rw [h]; exact hev.neg_one_pow
  rw [MeasureTheory.integral_congr_ae h1]
  simp

/-- Odd moments of a mean-zero Rademacher variable vanish. -/
private theorem kh_integral_rademacher_pow_odd {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (X : Ω → ℝ) (hae : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1)
    (hmean : MeasureTheory.integral μ X = 0) {n : ℕ} (hodd : Odd n) :
    MeasureTheory.integral μ (fun ω => (X ω) ^ n) = 0 := by
  have h1 : (fun ω => (X ω) ^ n) =ᵐ[μ] X := by
    filter_upwards [hae] with ω hω
    rcases hω with h | h
    · rw [h, one_pow]
    · rw [h]; exact hodd.neg_one_pow
  rw [MeasureTheory.integral_congr_ae h1]
  exact hmean

/-- Powers of a Rademacher variable are integrable. -/
private theorem kh_integrable_rademacher_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hae : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1) (n : ℕ) :
    MeasureTheory.Integrable (fun ω => (X ω) ^ n) μ := by
  apply MeasureTheory.Integrable.of_bound (hX.pow_const n).aestronglyMeasurable 1
  filter_upwards [hae] with ω hω
  have hnorm : ‖(X ω) ^ n‖ = 1 := by
    rcases hω with h | h
    · rw [h, one_pow, norm_one]
    · rw [h]
      rcases Nat.even_or_odd n with hev | hodd
      · rw [hev.neg_one_pow, norm_one]
      · rw [hodd.neg_one_pow, norm_neg, norm_one]
  rw [hnorm]


/-- Second moment of a Rademacher sum equals the sum of squared coefficients. -/
private theorem kh_second_moment (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i))
    (hae : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1)
    (hmean : ∀ i, MeasureTheory.integral μ (ε i) = 0)
    (hindep : ProbabilityTheory.iIndepFun ε μ) :
    MeasureTheory.integral μ (fun ω => ((∑ i, a i * ε i ω) ^ 2)) = ∑ i, (a i) ^ 2 := by
  have hinter : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ j ∈ Finset.univ,
      MeasureTheory.Integrable (fun ω => (a i * a j) * (ε i ω * ε j ω)) μ := by
    intro i _ j _
    have hmeas' : MeasureTheory.AEStronglyMeasurable (fun ω => (a i * a j) * (ε i ω * ε j ω)) μ :=
      (((hmeas i).mul (hmeas j)).const_mul _).aestronglyMeasurable
    apply MeasureTheory.Integrable.of_bound hmeas' |a i * a j|
    filter_upwards [hae i, hae j] with ω hi hj
    have e1 : |ε i ω| = 1 := by
      rcases hi with h | h <;> simp [h]
    have e2 : |ε j ω| = 1 := by
      rcases hj with h | h <;> simp [h]
    have e12 : |ε i ω * ε j ω| = 1 := by rw [abs_mul, e1, e2, mul_one]
    rw [Real.norm_eq_abs, abs_mul, e12, mul_one]
  have hInt1 : ∀ i, MeasureTheory.Integrable (ε i) μ := by
    intro i
    have h := kh_integrable_rademacher_pow μ (ε i) (hmeas i) (hae i) 1
    simpa using h
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ j ∈ Finset.univ,
      MeasureTheory.integral μ (fun ω => (a i * a j) * (ε i ω * ε j ω))
        = (a i * a j) * (if i = j then 1 else 0) := by
    intro i _ j _
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, mul_one]
      have heq : (fun ω => (a i * a i) * (ε i ω * ε i ω))
          = fun ω => (a i * a i) * ((ε i ω) ^ 2) := by
        funext ω; ring
      rw [heq, MeasureTheory.integral_const_mul,
        kh_integral_rademacher_pow_even μ (ε i) (hae i) even_two, mul_one]
    · simp only [hij, ite_false, mul_zero]
      have h0 : MeasureTheory.integral μ (fun ω => ε i ω * ε j ω) = 0 := by
        have hindepij : ProbabilityTheory.IndepFun (ε i) (ε j) μ := hindep.indepFun hij
        rw [hindepij.integral_fun_mul_eq_mul_integral
          (hInt1 i).aestronglyMeasurable (hInt1 j).aestronglyMeasurable,
          hmean i, hmean j, mul_zero]
      rw [MeasureTheory.integral_const_mul, h0, mul_zero]
  have hexpand : ∀ ω, (∑ i, a i * ε i ω) ^ 2
      = ∑ i, ∑ j, ((a i * a j) * (ε i ω * ε j ω)) := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum : MeasureTheory.integral μ (fun ω => ((∑ i, a i * ε i ω) ^ 2))
      = ∑ i, ∑ j, MeasureTheory.integral μ (fun ω => (a i * a j) * (ε i ω * ε j ω)) := by
    have heq : (fun ω => ((∑ i, a i * ε i ω) ^ 2))
        = fun ω => ∑ i, ∑ j, ((a i * a j) * (ε i ω * ε j ω)) := funext hexpand
    rw [heq, MeasureTheory.integral_finsetSum _ (fun i _ =>
      MeasureTheory.integrable_finsetSum _ (fun j _ =>
        hinter i (Finset.mem_univ i) j (Finset.mem_univ j)))]
    apply Finset.sum_congr rfl
    intro i _
    exact MeasureTheory.integral_finsetSum _ (fun j _ =>
      hinter i (Finset.mem_univ i) j (Finset.mem_univ j))
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  have hterm' : ∀ j : Fin N, (a i * a j) * (if i = j then (1 : ℝ) else 0)
      = (if j = i then (a i * a j) else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp
    · simp only [hij, ite_false, mul_zero]
      rw [ite_eq_right (fun h => hij h.symm)]
  calc (∑ j, MeasureTheory.integral μ (fun ω => (a i * a j) * (ε i ω * ε j ω)))
      = ∑ j, (if j = i then (a i * a j) else 0) :=
        Finset.sum_congr rfl (fun j _ => by
          rw [hterm i (Finset.mem_univ i) j (Finset.mem_univ j)]; exact hterm' j)
    _ = (a i) ^ 2 := by
        rw [Finset.sum_ite_eq' Finset.univ i (fun j => a i * a j)]
        simp [pow_two]

/-- Even moments of a Rademacher sum: `E[S_s^{2k}] ≤ (2k)! (∑_{s} aᵢ²)^k`. -/
private theorem kh_even_moment (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i))
    (hae : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1)
    (hmean : ∀ i, MeasureTheory.integral μ (ε i) = 0)
    (hindep : ProbabilityTheory.iIndepFun ε μ)
    (s : Finset (Fin N)) :
    ∀ k : ℕ, MeasureTheory.integral μ (fun ω => ((∑ i ∈ s, a i * ε i ω) ^ (2 * k)))
      ≤ (Nat.factorial (2 * k) : ℝ) * ((∑ i ∈ s, (a i) ^ 2) ^ k) := by
  induction s using Finset.induction with
  | empty =>
    intro k
    simp only [Finset.sum_empty]
    by_cases hk : k = 0
    · subst hk
      simp
    · have h2k : 2 * k ≠ 0 := by omega
      have hLHS : MeasureTheory.integral μ (fun ω => (0 : ℝ) ^ (2 * k)) = 0 := by
        rw [show (fun ω => (0 : ℝ) ^ (2 * k)) = fun _ => (0 : ℝ) from
          funext fun ω => zero_pow h2k]
        simp
      rw [hLHS]
      positivity
  | @insert j s' hj ih =>
    intro k
    have hindepW : ProbabilityTheory.iIndepFun (fun i => fun ω => a i * ε i ω) μ := by
      have h := hindep.comp (fun i => (fun x => a i * x))
        (fun i => measurable_const_mul (a i))
      simpa only [Function.comp_def] using h
    have hXY : ProbabilityTheory.IndepFun (fun ω => ∑ i ∈ s', a i * ε i ω)
        (fun ω => a j * ε j ω) μ := by
      have h := hindepW.indepFun_finsetSum_of_notMem (s := s') (i := j)
        (fun i => (hmeas i).const_mul (a i)) hj
      have hfun : (∑ i ∈ s', fun ω => a i * ε i ω)
          = (fun ω => ∑ i ∈ s', a i * ε i ω) :=
        funext (fun ω => Finset.sum_apply _ _ _)
      rw [hfun] at h
      exact h
    have hYmeas : Measurable (fun ω => a j * ε j ω) := (hmeas j).const_mul _
    have hXmeas : Measurable (fun ω => ∑ i ∈ s', a i * ε i ω) :=
      Finset.measurable_sum _ (fun i _ => (hmeas i).const_mul _)
    have hYb : ∀ᵐ ω ∂μ, ‖(a j * ε j ω)‖ ≤ |a j| := by
      filter_upwards [hae j] with ω hω
      have e : |ε j ω| = 1 := by rcases hω with h | h <;> simp [h]
      rw [Real.norm_eq_abs, abs_mul, e, mul_one]
    have hXb : ∀ᵐ ω ∂μ, ‖(∑ i ∈ s', a i * ε i ω)‖ ≤ ∑ i ∈ s', |a i| := by
      have hall := kh_ae_all_of_finset (s := s') (fun i hi => hae i)
      filter_upwards [hall] with ω hall
      calc ‖(∑ i ∈ s', a i * ε i ω)‖ ≤ ∑ i ∈ s', ‖(a i * ε i ω)‖ :=
            norm_sum_le _ _
        _ = ∑ i ∈ s', |a i| := by
            apply Finset.sum_congr rfl
            intro i hi
            have e : |ε i ω| = 1 := by
              have hi2 := hall i hi
              rcases hi2 with h | h <;> simp [h]
            rw [Real.norm_eq_abs, abs_mul, e, mul_one]
    have hterm_int : ∀ m ∈ Finset.range (2 * k + 1),
        MeasureTheory.Integrable
          (fun ω => (a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)
            * ((2 * k).choose m : ℝ)) μ := by
      intro m _
      have hae' : MeasureTheory.AEStronglyMeasurable
          (fun ω => (a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)
            * ((2 * k).choose m : ℝ)) μ :=
        ((((hYmeas.pow_const m).mul (hXmeas.pow_const _)).mul_const _)).aestronglyMeasurable
      refine MeasureTheory.Integrable.of_bound hae'
        (|a j| ^ m * (∑ i ∈ s', |a i|) ^ (2 * k - m) * ‖((2 * k).choose m : ℝ)‖) ?_
      filter_upwards [hYb, hXb] with ω hY hX
      calc ‖(a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)
              * ((2 * k).choose m : ℝ)‖
          ≤ ‖(a j * ε j ω)‖ ^ m * ‖(∑ i ∈ s', a i * ε i ω)‖ ^ (2 * k - m)
              * ‖((2 * k).choose m : ℝ)‖ := by
            rw [norm_mul, norm_mul, norm_pow, norm_pow]
        _ ≤ |a j| ^ m * (∑ i ∈ s', |a i|) ^ (2 * k - m)
              * ‖((2 * k).choose m : ℝ)‖ := by
            gcongr
    have hYm : ∀ m : ℕ, MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m)
        = (a j) ^ m * (MeasureTheory.integral μ (fun ω => (ε j ω) ^ m)) := by
      intro m
      have heq : (fun ω => (a j * ε j ω) ^ m)
          = fun ω => (a j) ^ m * ((ε j ω) ^ m) := by
        funext ω; rw [mul_pow]
      rw [heq, MeasureTheory.integral_const_mul]
    have hYpow_even : ∀ m : ℕ, Even m →
        MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m) = (a j) ^ m := by
      intro m hev
      rw [hYm, kh_integral_rademacher_pow_even μ (ε j) (hae j) hev, mul_one]
    have hYpow_odd : ∀ m : ℕ, Odd m →
        MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m) = 0 := by
      intro m hodd
      rw [hYm, kh_integral_rademacher_pow_odd μ (ε j) (hae j) (hmean j) hodd,
        mul_zero]
    have hprod : ∀ m l : ℕ,
        MeasureTheory.integral μ
          (fun ω => (a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ l)
        = (MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
          * (MeasureTheory.integral μ (fun ω => (∑ i ∈ s', a i * ε i ω) ^ l)) := by
      intro m l
      have hcomp := hXY.symm.comp (measurable_id.pow_const m)
        (measurable_id.pow_const l)
      have h2 := hcomp.integral_fun_mul_eq_mul_integral
        ((measurable_id.pow_const m).comp hYmeas).aestronglyMeasurable
        ((measurable_id.pow_const l).comp hXmeas).aestronglyMeasurable
      exact h2
    have hInt_eq : MeasureTheory.integral μ
          (fun ω => ((∑ i ∈ insert j s', a i * ε i ω) ^ (2 * k)))
        = ∑ m ∈ Finset.range (2 * k + 1),
          (((2 * k).choose m : ℝ)
            * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m))))) := by
      have heq : (fun ω => ((∑ i ∈ insert j s', a i * ε i ω) ^ (2 * k)))
          = fun ω => ∑ m ∈ Finset.range (2 * k + 1),
            ((a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)
              * ((2 * k).choose m : ℝ)) := by
        funext ω
        have hω : (∑ i ∈ insert j s', a i * ε i ω)
            = (a j * ε j ω) + (∑ i ∈ s', a i * ε i ω) := Finset.sum_insert hj
        rw [hω]
        exact add_pow _ _ _
      have reassoc : ∀ m ∈ Finset.range (2 * k + 1),
          (fun ω => (a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)
            * ((2 * k).choose m : ℝ))
          = fun ω => ((2 * k).choose m : ℝ)
            * ((a j * ε j ω) ^ m * (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)) := by
        intro m _
        funext ω; ring
      rw [heq, MeasureTheory.integral_finsetSum _ (fun m hm => hterm_int m hm)]
      apply Finset.sum_congr rfl
      intro m hm
      rw [reassoc m hm, MeasureTheory.integral_const_mul, hprod m (2 * k - m)]
    have hodd_zero : ∀ m ∈ Finset.range (2 * k + 1), Odd m →
        (((2 * k).choose m : ℝ)
          * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
            * (MeasureTheory.integral μ
              (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m))))) = 0 := by
      intro m _ hodd
      rw [hYpow_odd m hodd, zero_mul, mul_zero]
    have hfact_le : ∀ t : ℕ, t ≤ k →
        (Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ) ≤
          (Nat.factorial (2 * t) : ℝ) * (Nat.factorial k : ℝ) := by
      intro t ht
      have h1 : (Nat.factorial t : ℝ) ≤ (Nat.factorial (2 * t) : ℝ) := by
        apply Nat.cast_le.mpr
        apply Nat.factorial_le
        omega
      have h2 : (Nat.factorial (k - t) : ℝ) ≤ (Nat.factorial k : ℝ) := by
        apply Nat.cast_le.mpr
        apply Nat.factorial_le
        omega
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have heven_le : ∀ t ∈ Finset.range (k + 1),
        (((2 * k).choose (2 * t) : ℝ)
          * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ (2 * t)))
            * (MeasureTheory.integral μ
              (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - 2 * t)))))
        ≤ (Nat.factorial (2 * k) : ℝ)
          * (((k).choose t : ℝ)
            * (((∑ i ∈ s', (a i) ^ 2) ^ (k - t)) * (((a j) ^ 2) ^ t))) := by
      intro t ht
      have htk : t ≤ k := by
        have := Finset.mem_range.mp ht
        omega
      have hexp_eq : 2 * k - 2 * t = 2 * (k - t) := by omega
      have hEX : MeasureTheory.integral μ
            (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - 2 * t))
          ≤ (Nat.factorial (2 * (k - t)) : ℝ) * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t)) := by
        rw [hexp_eq]
        exact ih (k - t)
      have hEY : MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ (2 * t))
          = (a j) ^ (2 * t) := hYpow_even (2 * t) ⟨t, by ring⟩
      have hC1F1 : ((2 * k).choose (2 * t) : ℝ) * (Nat.factorial (2 * (k - t)) : ℝ)
          = (Nat.factorial (2 * k) : ℝ) / (Nat.factorial (2 * t) : ℝ) := by
        have hnat : (2 * k).choose (2 * t) * Nat.factorial (2 * t) *
            Nat.factorial (2 * k - 2 * t) = Nat.factorial (2 * k) :=
          Nat.choose_mul_factorial_mul_factorial (by omega)
        rw [hexp_eq] at hnat
        have hcast : ((2 * k).choose (2 * t) : ℝ) * (Nat.factorial (2 * t) : ℝ)
            * (Nat.factorial (2 * (k - t)) : ℝ) = (Nat.factorial (2 * k) : ℝ) := by
          exact_mod_cast hnat
        have hF2pos : (0 : ℝ) < (Nat.factorial (2 * t) : ℝ) := by positivity
        rw [eq_div_iff (ne_of_gt hF2pos)]
        linarith [hcast]
      have hK1 : ((k).choose t : ℝ) * (Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ) =
          (Nat.factorial k : ℝ) := by
        have hnat : (k).choose t * Nat.factorial t * Nat.factorial (k - t) = Nat.factorial k :=
          Nat.choose_mul_factorial_mul_factorial htk
        exact_mod_cast hnat
      have hpow_a : (a j) ^ (2 * t) = (((a j) ^ 2)) ^ t := by rw [← pow_mul]
      have hnonneg1 : (0 : ℝ) ≤ ((2 * k).choose (2 * t) : ℝ) := by positivity
      have hnonneg2 : (0 : ℝ) ≤ (a j) ^ (2 * t) := Even.pow_nonneg ⟨t, by ring⟩ _
      have htau_nonneg : (0 : ℝ) ≤ (∑ i ∈ s', (a i) ^ 2) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      rw [hEY]
      calc ((2 * k).choose (2 * t) : ℝ) * ((a j) ^ (2 * t)
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - 2 * t))))
          ≤ ((2 * k).choose (2 * t) : ℝ) * ((a j) ^ (2 * t)
              * ((Nat.factorial (2 * (k - t)) : ℝ) * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t)))) := by
            apply mul_le_mul_of_nonneg_left _ hnonneg1
            apply mul_le_mul_of_nonneg_left hEX hnonneg2
        _ = ((((2 * k).choose (2 * t) : ℝ) * (Nat.factorial (2 * (k - t)) : ℝ))
              * (((((a j) ^ 2)) ^ t) * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t)))) := by
            rw [hpow_a]; ring
        _ = ((Nat.factorial (2 * k) : ℝ) / (Nat.factorial (2 * t) : ℝ))
              * (((((a j) ^ 2)) ^ t) * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t))) := by
            rw [hC1F1]
        _ ≤ (Nat.factorial (2 * k) : ℝ)
              * (((k).choose t : ℝ)
                * (((∑ i ∈ s', (a i) ^ 2) ^ (k - t)) * (((a j) ^ 2) ^ t))) := by
            have hW_nonneg : (0 : ℝ) ≤ ((((a j) ^ 2)) ^ t)
                * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t)) := by positivity
            have h1le : (1 : ℝ) ≤ ((k).choose t : ℝ) * (Nat.factorial (2 * t) : ℝ) := by
              have hKF : (((k).choose t : ℝ) * (Nat.factorial (2 * t) : ℝ))
                  * ((Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ))
                  = (Nat.factorial k : ℝ) * (Nat.factorial (2 * t) : ℝ) := by
                calc (((k).choose t : ℝ) * (Nat.factorial (2 * t) : ℝ))
                      * ((Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ))
                    = ((((k).choose t : ℝ) * (Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ)))
                      * (Nat.factorial (2 * t) : ℝ) := by ring
                  _ = (Nat.factorial k : ℝ) * (Nat.factorial (2 * t) : ℝ) := by rw [hK1]
              have hpos : (0 : ℝ) < (Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ) := by
                positivity
              have hle : (1 : ℝ) * ((Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ))
                  ≤ ((((k).choose t : ℝ) * (Nat.factorial (2 * t) : ℝ)))
                    * ((Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ)) := by
                rw [one_mul, hKF]
                calc (Nat.factorial t : ℝ) * (Nat.factorial (k - t) : ℝ)
                    ≤ (Nat.factorial (2 * t) : ℝ) * (Nat.factorial k : ℝ) := hfact_le t htk
                  _ = (Nat.factorial k : ℝ) * (Nat.factorial (2 * t) : ℝ) := by ring
              exact le_of_mul_le_mul_right hle hpos
            have hF2pos : (0 : ℝ) < (Nat.factorial (2 * t) : ℝ) := by positivity
            have hstep : (Nat.factorial (2 * k) : ℝ) / (Nat.factorial (2 * t) : ℝ)
                ≤ (Nat.factorial (2 * k) : ℝ) * (((k).choose t : ℝ)) := by
              rw [div_le_iff₀ hF2pos]
              calc (Nat.factorial (2 * k) : ℝ) = (Nat.factorial (2 * k) : ℝ) * 1 := by ring
                _ ≤ (Nat.factorial (2 * k) : ℝ) *
                    ((((k).choose t : ℝ) * (Nat.factorial (2 * t) : ℝ))) := by
                    apply mul_le_mul_of_nonneg_left h1le (by positivity)
                _ = (Nat.factorial (2 * k) : ℝ) * (((k).choose t : ℝ)) *
                    (Nat.factorial (2 * t) : ℝ) := by
                    ring
            calc ((Nat.factorial (2 * k) : ℝ) / (Nat.factorial (2 * t) : ℝ))
                  * (((((a j) ^ 2)) ^ t) * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t)))
                ≤ ((Nat.factorial (2 * k) : ℝ) * (((k).choose t : ℝ)))
                  * (((((a j) ^ 2)) ^ t) * (((∑ i ∈ s', (a i) ^ 2)) ^ (k - t))) := by
                    apply mul_le_mul_of_nonneg_right hstep hW_nonneg
              _ = (Nat.factorial (2 * k) : ℝ)
                  * (((k).choose t : ℝ)
                    * (((∑ i ∈ s', (a i) ^ 2) ^ (k - t)) * (((a j) ^ 2) ^ t))) := by
                    ring
    have himage : Finset.image (fun t => 2 * t) (Finset.range (k + 1))
        = (Finset.range (2 * k + 1)).filter Even := by
      ext m
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨t, ht, htm⟩
        have htm2 : 2 * t = m := htm
        subst htm2
        refine ⟨by omega, ?_⟩
        exact ⟨t, by ring⟩
      · rintro ⟨hm, hev⟩
        obtain ⟨t, ht⟩ := hev
        refine ⟨t, by omega, ?_⟩
        show 2 * t = m
        omega
    have hsum_odd_zero :
        ∑ m ∈ (Finset.range (2 * k + 1)).filter (fun m => ¬ Even m),
          (((2 * k).choose m : ℝ)
            * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m))))) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hm' : m ∈ Finset.range (2 * k + 1) := (Finset.mem_filter.mp hm).1
      have hno : ¬ Even m := (Finset.mem_filter.mp hm).2
      exact hodd_zero m hm' (Nat.not_even_iff_odd.mp hno)
    have himg_sum :
        ∑ m ∈ Finset.image (fun t => 2 * t) (Finset.range (k + 1)),
          (((2 * k).choose m : ℝ)
            * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)))))
        = ∑ t ∈ Finset.range (k + 1),
          (((2 * k).choose (2 * t) : ℝ)
            * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ (2 * t)))
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - 2 * t))))) := by
      apply Finset.sum_image
      intro x _ y _ h
      have h2 : 2 * x = 2 * y := h
      omega
    have hsplit_sum :
        ∑ m ∈ Finset.range (2 * k + 1),
          (((2 * k).choose m : ℝ)
            * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)))))
        = ∑ t ∈ Finset.range (k + 1),
          (((2 * k).choose (2 * t) : ℝ)
            * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ (2 * t)))
              * (MeasureTheory.integral μ
                (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - 2 * t))))) := by
      have h1 := Finset.sum_filter_add_sum_filter_not
        (Finset.range (2 * k + 1)) Even
        (fun m => ((2 * k).choose m : ℝ)
          * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
            * (MeasureTheory.integral μ
              (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m)))))
      rw [← h1, hsum_odd_zero, add_zero, ← himage]
      exact himg_sum
    calc MeasureTheory.integral μ
            (fun ω => ((∑ i ∈ insert j s', a i * ε i ω) ^ (2 * k)))
        = ∑ m ∈ Finset.range (2 * k + 1),
            (((2 * k).choose m : ℝ)
              * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ m))
                * (MeasureTheory.integral μ
                  (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - m))))) := hInt_eq
      _ = ∑ t ∈ Finset.range (k + 1),
            (((2 * k).choose (2 * t) : ℝ)
              * ((MeasureTheory.integral μ (fun ω => (a j * ε j ω) ^ (2 * t)))
                * (MeasureTheory.integral μ
                  (fun ω => (∑ i ∈ s', a i * ε i ω) ^ (2 * k - 2 * t))))) :=
            hsplit_sum
      _ ≤ ∑ t ∈ Finset.range (k + 1),
            ((Nat.factorial (2 * k) : ℝ)
              * (((k).choose t : ℝ)
                * (((∑ i ∈ s', (a i) ^ 2) ^ (k - t)) * (((a j) ^ 2) ^ t)))) :=
            Finset.sum_le_sum (fun t ht => heven_le t ht)
      _ = (Nat.factorial (2 * k) : ℝ) * ((((a j) ^ 2) + (∑ i ∈ s', (a i) ^ 2)) ^ k) := by
            rw [← Finset.mul_sum]
            congr 1
            have hadd := add_pow ((a j) ^ 2) (∑ i ∈ s', (a i) ^ 2) k
            rw [hadd]
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ = (Nat.factorial (2 * k) : ℝ) * ((∑ i ∈ insert j s', (a i) ^ 2) ^ k) := by
            rw [Finset.sum_insert hj]
/-- Measurability of a Rademacher sum. -/
private theorem kh_S_meas (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (ε : Fin N → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i)) :
    Measurable (fun ω => ∑ i, a i * ε i ω) :=
  Finset.measurable_sum _ (fun i _ => (hmeas i).const_mul _)

/-- A Rademacher sum is a.e. bounded by the sum of absolute coefficients. -/
private theorem kh_S_bound (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (ε : Fin N → Ω → ℝ) (hae : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1) :
    ∀ᵐ ω ∂μ, ‖(∑ i, a i * ε i ω)‖ ≤ ∑ i, |a i| := by
  have hall := kh_ae_all_of_finset (s := (Finset.univ : Finset (Fin N)))
    (fun i _ => hae i)
  filter_upwards [hall] with ω hall
  calc ‖(∑ i, a i * ε i ω)‖ ≤ ∑ i, ‖(a i * ε i ω)‖ := norm_sum_le _ _
    _ = ∑ i, |a i| := by
        apply Finset.sum_congr rfl
        intro i _
        have e : |ε i ω| = 1 := by
          have hi2 := hall i (Finset.mem_univ i)
          rcases hi2 with h | h <;> simp [h]
        rw [Real.norm_eq_abs, abs_mul, e, mul_one]

/-- A Rademacher sum is in every `MemLp` space. -/
private theorem kh_S_memlp (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Fin N → Ω → ℝ) (hmeas : ∀ i, Measurable (ε i))
    (hae : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1) (p : ENNReal) :
    MeasureTheory.MemLp (fun ω => ∑ i, a i * ε i ω) p μ :=
  MeasureTheory.MemLp.of_bound (kh_S_meas N a Ω ε hmeas).aestronglyMeasurable _
    (kh_S_bound N a Ω μ ε hae)

/-- The `eLpNorm` of a Rademacher sum equals the `rpow` moment in the goal. -/
private theorem kh_ebridge (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (ε : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i))
    {p : ℝ} (hp : 0 < p) :
    (MeasureTheory.eLpNorm (fun ω => ∑ i, a i * ε i ω) (ENNReal.ofReal p) μ).toReal
      = (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p) := by
  have hS := kh_S_meas N a Ω ε hmeas
  have hSint : MeasureTheory.AEStronglyMeasurable
      (fun ω => |∑ i, a i * ε i ω| ^ p) μ :=
    ((continuous_abs.rpow_const (fun _ => Or.inr hp.le)).measurable.comp
      hS).aestronglyMeasurable
  have hpos : 0 ≤ᵐ[μ] (fun ω => |∑ i, a i * ε i ω| ^ p) :=
    Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (abs_nonneg _) p)
  have hep0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have heptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hep0 heptop
    hS.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  have hcongr : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ p ∂μ)
      = ∫⁻ ω, ENNReal.ofReal (|∑ i, a i * ε i ω| ^ p) ∂μ := by
    apply MeasureTheory.lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  rw [hcongr, ← ENNReal.toReal_rpow,
    ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae hpos hSint]

/-- Lyapunov comparison of `rpow` moments on a probability space. -/
private theorem kh_lyapunov (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i))
    (hae : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p)
      ≤ (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ q)) ^ (1 / q) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hfin : MeasureTheory.eLpNorm (fun ω => ∑ i, a i * ε i ω)
      (ENNReal.ofReal q) μ ≠ ⊤ :=
    (kh_S_memlp N a Ω μ ε hmeas hae _).eLpNorm_lt_top.ne
  have hle : MeasureTheory.eLpNorm (fun ω => ∑ i, a i * ε i ω) (ENNReal.ofReal p) μ
      ≤ MeasureTheory.eLpNorm (fun ω => ∑ i, a i * ε i ω) (ENNReal.ofReal q) μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)
  rw [← kh_ebridge N a Ω μ ε hmeas hp, ← kh_ebridge N a Ω μ ε hmeas hq]
  exact ENNReal.toReal_mono hfin hle

/-- The second `rpow` moment equals the root sum of squares. -/
private theorem kh_mom_two (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ε i))
    (hae : ∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1)
    (hmean : ∀ i, MeasureTheory.integral μ (ε i) = 0)
    (hindep : ProbabilityTheory.iIndepFun ε μ) :
    (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ (2 : ℝ))) ^ (1 / 2 : ℝ)
      = Real.sqrt (∑ i, (a i) ^ 2) := by
  have h2 : (fun ω => |∑ i, a i * ε i ω| ^ (2 : ℝ))
      = fun ω => ((∑ i, a i * ε i ω) ^ 2) := by
    funext ω
    rw [Real.rpow_two, Even.pow_abs even_two]
  rw [h2, kh_second_moment N a Ω μ ε hmeas hae hmean hindep, ← Real.sqrt_eq_rpow]

/-- An even `rpow` moment equals the corresponding `Monoid.pow` moment. -/
private theorem kh_rpowint_eq_powint (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (ε : Fin N → Ω → ℝ) (k : ℕ) :
    MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ ((2 * k : ℕ) : ℝ))
      = MeasureTheory.integral μ (fun ω => (∑ i, a i * ε i ω) ^ (2 * k)) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with ω
  rw [Real.rpow_natCast, Even.pow_abs ⟨k, by ring⟩]
/-- Split an `ENNReal` product of `rpow`s (for positive exponents). -/
private theorem kh_ennreal_split (e : ENNReal) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (he : e ≠ ⊤) : e ^ u * e ^ v = e ^ (u + v) := by
  by_cases h0 : e = 0
  · subst h0
    rw [ENNReal.zero_rpow_of_pos hu, ENNReal.zero_rpow_of_pos hv, zero_mul,
      ENNReal.zero_rpow_of_pos (add_pos hu hv)]
  · exact (ENNReal.rpow_add _ _ h0 he).symm

/-- **Khintchine inequality.** For every real $p > 0$ there are constants $A_p > 0$ and $B_p > 0$
such that the following holds for every $N \in \mathbb{N}$, all real numbers $a_1, \dots, a_N$
and every probability space. Let $\varepsilon_1, \dots, \varepsilon_N$ be independent measurable
random variables, each almost surely equal to $1$ or $-1$ and each with mean $0$, and let
$S = \sum_{i=1}^N a_i \varepsilon_i$ and $\|a\|_2 = \big(\sum_{i=1}^N a_i^2\big)^{1/2}$. Then
$$A_p \|a\|_2 \le \big(\mathbb{E}\,|S|^p\big)^{1/p} \le B_p \|a\|_2.$$

Proves `Wanted` entry `khintchine_inequality`.

Source: statement `khintchine-s1`.

Source: https://en.wikipedia.org/wiki/Khintchine_inequality
-/
theorem khintchine_inequality :
    ∀ (p : ℝ), 0 < p →
      ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
        ∀ (N : ℕ) (a : Fin N → ℝ) (Ω : Type*) [MeasurableSpace Ω]
          (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
          (ε : Fin N → Ω → ℝ),
          (∀ i, Measurable (ε i)) →
          (∀ i, ∀ᵐ ω ∂μ, ε i ω = 1 ∨ ε i ω = -1) →
          (∀ i, MeasureTheory.integral μ (ε i) = 0) →
          ProbabilityTheory.iIndepFun ε μ →
          A * Real.sqrt (∑ i, (a i) ^ 2) ≤
            Real.rpow
              (MeasureTheory.integral μ (fun ω => Real.rpow |∑ i, a i * ε i ω| p))
              (1 / p) ∧
          Real.rpow
            (MeasureTheory.integral μ (fun ω => Real.rpow |∑ i, a i * ε i ω| p))
            (1 / p) ≤
            B * Real.sqrt (∑ i, (a i) ^ 2) := by
  intro p hp
  have hpne : p ≠ 0 := hp.ne'
  refine ⟨min (1:ℝ) (24 ^ (-((2 - p) / p))),
    max (1:ℝ) ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
      ^ (1 / ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ))), ?_, ?_, ?_⟩
  · exact lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)
  · exact zero_lt_one.trans_le (le_max_left _ _)
  · intro N a Ω _ μ _ ε hmeas hae hmean hindep
    change min (1:ℝ) (24 ^ (-((2 - p) / p))) * Real.sqrt (∑ i, (a i) ^ 2) ≤
        (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p) ∧
      (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p) ≤
        max (1:ℝ) ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
          ^ (1 / ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ))) * Real.sqrt (∑ i, (a i) ^ 2)
    have hσnn : (0 : ℝ) ≤ ∑ i, (a i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt (∑ i, (a i) ^ 2) :=
      Real.sqrt_nonneg _
    have hA_le1 : min (1:ℝ) (24 ^ (-((2 - p) / p))) ≤ 1 := min_le_left _ _
    have hB_ge1 : (1 : ℝ) ≤ max (1:ℝ) ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
        ^ (1 / ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ))) := le_max_left _ _
    have hMp_nonneg : (0 : ℝ) ≤
        MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p) :=
      MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall
        (fun ω => Real.rpow_nonneg (abs_nonneg _) p))
    by_cases hσ : ∑ i, (a i) ^ 2 = 0
    · have ha0 : ∀ i, a i = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (fun i _ => by positivity : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ (a i) ^ 2)).mp
          hσ
        intro i
        have hi := h i (Finset.mem_univ i)
        exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hi
      have hM0 : MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p)
          = 0 := by
        have heq : (fun ω => |∑ i, a i * ε i ω| ^ p) = fun _ => (0 : ℝ) := by
          funext ω
          have hSi : (∑ i, a i * ε i ω) = 0 := by simp [ha0]
          rw [hSi, abs_zero, Real.zero_rpow hp.ne']
        rw [heq]
        simp
      have hN0 : (MeasureTheory.integral μ
          (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p) = 0 := by
        rw [hM0, Real.zero_rpow (one_div_ne_zero hp.ne')]
      rw [hσ, Real.sqrt_zero, hN0]
      exact ⟨by simp, by simp⟩
    · have hσpos : (0 : ℝ) < ∑ i, (a i) ^ 2 :=
        lt_of_le_of_ne hσnn (Ne.symm hσ)
      have hN2 := kh_mom_two N a Ω μ ε hmeas hae hmean hindep
      have hlower : min (1:ℝ) (24 ^ (-((2 - p) / p)))
          * Real.sqrt (∑ i, (a i) ^ 2)
          ≤ (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p))
            ^ (1 / p) := by
        by_cases hp2 : 2 ≤ p
        · calc min (1:ℝ) (24 ^ (-((2 - p) / p))) * Real.sqrt (∑ i, (a i) ^ 2)
                ≤ 1 * Real.sqrt (∑ i, (a i) ^ 2) :=
                mul_le_mul_of_nonneg_right hA_le1 hsqrt_nonneg
            _ = Real.sqrt (∑ i, (a i) ^ 2) := one_mul _
            _ = (MeasureTheory.integral μ
                  (fun ω => |∑ i, a i * ε i ω| ^ (2 : ℝ))) ^ (1 / 2 : ℝ) :=
                hN2.symm
            _ ≤ (MeasureTheory.integral μ
                  (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p) :=
                kh_lyapunov N a Ω μ ε hmeas hae (by norm_num) hp2
        · have hAle : min (1:ℝ) (24 ^ (-((2 - p) / p)))
              ≤ 24 ^ (-((2 - p) / p)) := min_le_right _ _
          apply le_trans (mul_le_mul_of_nonneg_right hAle hsqrt_nonneg)
          have h4ppos : (0 : ℝ) < 4 - p := by linarith
          have h4pne : (4 : ℝ) - p ≠ 0 := ne_of_gt h4ppos
          have hp'pos : (0 : ℝ) < 2 / (4 - p) := div_pos (by norm_num) h4ppos
          have hq'pos : (0 : ℝ) < (2 - p) / (4 - p) :=
            div_pos (by linarith) h4ppos
          have hexp : p * (2 / (4 - p)) + 4 * ((2 - p) / (4 - p)) = 2 := by
            field_simp
            ring
          have hpq1 : 2 / (4 - p) + (2 - p) / (4 - p) = 1 := by
            rw [← add_div, show (2 : ℝ) + (2 - p) = 4 - p by ring,
              div_self h4pne]
          have hSaem : AEMeasurable (fun ω => ‖(∑ i, a i * ε i ω)‖ₑ) μ :=
            (kh_S_meas N a Ω ε hmeas).aemeasurable.enorm
          have hetop : ∀ ω, ‖(∑ i, a i * ε i ω)‖ₑ ≠ ⊤ := by
            intro ω
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_ne_top
          have hHoelder := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
            (f := fun ω => ‖(∑ i, a i * ε i ω)‖ₑ ^ p)
            (g := fun ω => ‖(∑ i, a i * ε i ω)‖ₑ ^ (4 : ℝ))
            (p := 2 / (4 - p)) (q := (2 - p) / (4 - p))
            (hSaem.pow_const p) (hSaem.pow_const 4)
            (div_nonneg (by norm_num) h4ppos.le)
            (div_nonneg (by linarith) h4ppos.le) hpq1
          have hLHS : (∫⁻ ω, (‖(∑ i, a i * ε i ω)‖ₑ ^ p) ^ (2 / (4 - p))
              * (‖(∑ i, a i * ε i ω)‖ₑ ^ (4 : ℝ)) ^ ((2 - p) / (4 - p)) ∂μ)
              = ∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ (2 : ℝ) ∂μ := by
            apply MeasureTheory.lintegral_congr
            intro ω
            rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
              kh_ennreal_split _ (mul_pos hp hp'pos)
                (mul_pos (by norm_num : (0 : ℝ) < 4) hq'pos) (hetop ω), hexp]
          have hposp : 0 ≤ᵐ[μ] (fun ω => |∑ i, a i * ε i ω| ^ p) :=
            Filter.Eventually.of_forall
              (fun ω => Real.rpow_nonneg (abs_nonneg _) p)
          have haesp : MeasureTheory.AEStronglyMeasurable
              (fun ω => |∑ i, a i * ε i ω| ^ p) μ :=
            (((continuous_abs.rpow_const (fun _ => Or.inr hp.le)).measurable.comp
              (kh_S_meas N a Ω ε hmeas))).aestronglyMeasurable
          have hIntp : MeasureTheory.Integrable
              (fun ω => |∑ i, a i * ε i ω| ^ p) μ := by
            refine MeasureTheory.Integrable.of_bound haesp
              ((∑ i, |a i|) ^ p) ?_
            filter_upwards [kh_S_bound N a Ω μ ε hae] with ω hω
            have h1 : |∑ i, a i * ε i ω| ≤ ∑ i, |a i| := by
              rw [← Real.norm_eq_abs]
              exact hω
            rw [Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
            exact Real.rpow_le_rpow (abs_nonneg _) h1 hp.le
          have hE1of : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ p ∂μ)
              = ENNReal.ofReal (MeasureTheory.integral μ
                (fun ω => |∑ i, a i * ε i ω| ^ p)) := by
            have hc1 : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ p ∂μ)
                = ∫⁻ ω, ENNReal.ofReal (|∑ i, a i * ε i ω| ^ p) ∂μ := by
              apply MeasureTheory.lintegral_congr
              intro ω
              rw [Real.enorm_eq_ofReal_abs,
                ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
            rw [hc1,
              ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntp hposp]
          have hpos4 : (0 : ℝ) < 4 := by norm_num
          have hae4 : MeasureTheory.AEStronglyMeasurable
              (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ)) μ :=
            ((((continuous_abs.rpow_const
                (fun _ => Or.inr hpos4.le)).measurable.comp
                (kh_S_meas N a Ω ε hmeas))).aestronglyMeasurable)
          have hInt4 : MeasureTheory.Integrable
              (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ)) μ := by
            refine MeasureTheory.Integrable.of_bound hae4
              ((∑ i, |a i|) ^ (4 : ℝ)) ?_
            filter_upwards [kh_S_bound N a Ω μ ε hae] with ω hω
            have h1 : |∑ i, a i * ε i ω| ≤ ∑ i, |a i| := by
              rw [← Real.norm_eq_abs]
              exact hω
            rw [Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) 4)]
            exact Real.rpow_le_rpow (abs_nonneg _) h1 hpos4.le
          have hE2of : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ (4 : ℝ) ∂μ)
              = ENNReal.ofReal (MeasureTheory.integral μ
                (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ))) := by
            have hc2 : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ (4 : ℝ) ∂μ)
                = ∫⁻ ω, ENNReal.ofReal (|∑ i, a i * ε i ω| ^ (4 : ℝ)) ∂μ := by
              apply MeasureTheory.lintegral_congr
              intro ω
              rw [Real.enorm_eq_ofReal_abs,
                ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpos4.le]
            rw [hc2,
              ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt4
                (Filter.Eventually.of_forall
                  (fun ω => Real.rpow_nonneg (abs_nonneg _) 4))]
          have hM4_nonneg : (0 : ℝ) ≤ MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ)) :=
            MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall
              (fun ω => Real.rpow_nonneg (abs_nonneg _) 4))
          have hM4 : MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ))
              ≤ 24 * ((∑ i, (a i) ^ 2) ^ 2) := by
            have hconv : MeasureTheory.integral μ
                  (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ))
                = MeasureTheory.integral μ
                  (fun ω => (∑ i, a i * ε i ω) ^ (2 * 2)) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with ω
              rw [show (4 : ℝ) = (((2 * 2 : ℕ)) : ℝ) by norm_num,
                Real.rpow_natCast, Even.pow_abs ⟨2, by ring⟩]
            rw [hconv]
            have h := kh_even_moment N a Ω μ ε hmeas hae hmean hindep
              Finset.univ 2
            norm_num at h ⊢
            exact h
          have hae2 : MeasureTheory.AEStronglyMeasurable
              (fun ω => (∑ i, a i * ε i ω) ^ 2) μ :=
            ((kh_S_meas N a Ω ε hmeas).pow_const 2).aestronglyMeasurable
          have hInt2 : MeasureTheory.Integrable
              (fun ω => (∑ i, a i * ε i ω) ^ 2) μ := by
            refine MeasureTheory.Integrable.of_bound hae2 ((∑ i, |a i|) ^ 2) ?_
            filter_upwards [kh_S_bound N a Ω μ ε hae] with ω hω
            have h1 : ‖(∑ i, a i * ε i ω) ^ 2‖ = ‖∑ i, a i * ε i ω‖ ^ 2 :=
              norm_pow _ _
            rw [h1]
            exact pow_le_pow_left₀ (norm_nonneg _) hω 2
          have hSec : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ (2 : ℝ) ∂μ)
              = ENNReal.ofReal (∑ i, (a i) ^ 2) := by
            have hc1 : (∫⁻ ω, ‖(∑ i, a i * ε i ω)‖ₑ ^ (2 : ℝ) ∂μ)
                = ∫⁻ ω, ENNReal.ofReal ((∑ i, a i * ε i ω) ^ 2) ∂μ := by
              apply MeasureTheory.lintegral_congr
              intro ω
              rw [Real.enorm_eq_ofReal_abs,
                ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
                Real.rpow_two, sq_abs]
            rw [hc1,
              ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2
                (Filter.Eventually.of_forall
                  (fun ω => Even.pow_nonneg even_two _)),
              kh_second_moment N a Ω μ ε hmeas hae hmean hindep]
          have hr1 : (0 : ℝ) ≤ 2 / (4 - p) :=
            div_nonneg (by norm_num) h4ppos.le
          have hr2 : (0 : ℝ) ≤ (2 - p) / (4 - p) :=
            div_nonneg (by linarith) h4ppos.le
          have hMr1 : (0 : ℝ) ≤ (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (2 / (4 - p)) :=
            Real.rpow_nonneg hMp_nonneg _
          rw [hLHS, hSec] at hHoelder
          rw [hE1of, hE2of,
            ENNReal.ofReal_rpow_of_nonneg hMp_nonneg hr1,
            ENNReal.ofReal_rpow_of_nonneg hM4_nonneg hr2,
            ← ENNReal.ofReal_mul hMr1] at hHoelder
          have hreal : (∑ i, (a i) ^ 2)
              ≤ (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p))
                ^ (2 / (4 - p))
                * (MeasureTheory.integral μ
                  (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ)))
                ^ ((2 - p) / (4 - p)) := by
            have hfin2 : (ENNReal.ofReal
                ((MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p))
                  ^ (2 / (4 - p))
                  * (MeasureTheory.integral μ
                    (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ)))
                  ^ ((2 - p) / (4 - p)))) ≠ ⊤ := ENNReal.ofReal_ne_top
            have h1 := ENNReal.toReal_mono hfin2 hHoelder
            rwa [ENNReal.toReal_ofReal hσnn,
              ENNReal.toReal_ofReal (mul_nonneg
                (Real.rpow_nonneg hMp_nonneg _)
                (Real.rpow_nonneg hM4_nonneg _))] at h1
          have hM4rpow : (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ (4 : ℝ))) ^ ((2 - p) / (4 - p))
              ≤ 24 ^ ((2 - p) / (4 - p))
                * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))) := by
            have hle := Real.rpow_le_rpow hM4_nonneg hM4 hr2
            have e1 : (((∑ i, (a i) ^ 2) ^ 2 : ℝ)) ^ (((2 - p) / (4 - p)) : ℝ)
                = (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hσnn, Nat.cast_ofNat]
            rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 24)
              (pow_nonneg hσnn 2), e1] at hle
          have hkey : (∑ i, (a i) ^ 2)
              ≤ (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p))
                ^ (2 / (4 - p))
                * (24 ^ ((2 - p) / (4 - p))
                  * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p)))) :=
            le_trans hreal (mul_le_mul_of_nonneg_left hM4rpow
              (Real.rpow_nonneg hMp_nonneg _))
          have hKpos : (0 : ℝ) < 24 ^ ((2 - p) / (4 - p))
              * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))) :=
            mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
              (Real.rpow_pos_of_pos hσpos _)
          have hApart : (∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
              * 24 ^ (-((2 - p) / (4 - p)))
              * (24 ^ ((2 - p) / (4 - p))
                * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))))
              = (∑ i, (a i) ^ 2) := by
            have e1 : ((1 : ℝ) - 2 * ((2 - p) / (4 - p)))
                + (2 * ((2 - p) / (4 - p))) = 1 := by ring
            have e2 : ((-((2 - p) / (4 - p)) : ℝ)) + ((2 - p) / (4 - p))
                = 0 := by ring
            calc (∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
                  * 24 ^ (-((2 - p) / (4 - p)))
                  * (24 ^ ((2 - p) / (4 - p))
                    * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))))
                = ((∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
                    * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))))
                  * (24 ^ (-((2 - p) / (4 - p)))
                    * 24 ^ ((2 - p) / (4 - p))) := by ring
              _ = (∑ i, (a i) ^ 2) := by
                  rw [← Real.rpow_add hσpos,
                    ← Real.rpow_add (by norm_num : (0 : ℝ) < 24), e1, e2,
                    Real.rpow_one, Real.rpow_zero, mul_one]
          have hA_le : (∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
              * 24 ^ (-((2 - p) / (4 - p)))
              ≤ (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p))
                ^ (2 / (4 - p)) := by
            have h2 : ((∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
                * 24 ^ (-((2 - p) / (4 - p))))
                * (24 ^ ((2 - p) / (4 - p))
                  * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p))))
                ≤ (MeasureTheory.integral μ
                    (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (2 / (4 - p))
                  * (24 ^ ((2 - p) / (4 - p))
                    * (∑ i, (a i) ^ 2) ^ (2 * ((2 - p) / (4 - p)))) := by
              rw [hApart]
              exact hkey
            exact le_of_mul_le_mul_right h2 hKpos
          have hMp_eq : ((MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p))
              ^ (p * (2 / (4 - p)))
              = (MeasureTheory.integral μ (fun ω => |∑ i, a i * ε i ω| ^ p))
                ^ (2 / (4 - p)) := by
            rw [← Real.rpow_mul hMp_nonneg]
            congr 1
            field_simp
          have hRHS : (24 ^ (-((2 - p) / p))
              * Real.sqrt (∑ i, (a i) ^ 2)) ^ (p * (2 / (4 - p)))
              = 24 ^ (-((2 - p) / p) * (p * (2 / (4 - p))))
                * (∑ i, (a i) ^ 2) ^ ((p * (2 / (4 - p))) / 2) := by
            rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _)
              (Real.sqrt_nonneg _)]
            congr 1
            · rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 24)]
            · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hσnn]
              congr 1
              ring
          have hE1 : (p * (2 / (4 - p))) / 2 = 1 - 2 * ((2 - p) / (4 - p)) := by
            field_simp
            ring
          have hE2 : -((2 - p) / p) * (p * (2 / (4 - p)))
              = -2 * ((2 - p) / (4 - p)) := by
            field_simp
          have hEpos : (0 : ℝ) < p * (2 / (4 - p)) := mul_pos hp hp'pos
          have hfin_step : (24 ^ (-((2 - p) / p))
              * Real.sqrt (∑ i, (a i) ^ 2)) ^ (p * (2 / (4 - p)))
              ≤ ((MeasureTheory.integral μ
                (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p))
                ^ (p * (2 / (4 - p))) := by
            rw [hRHS, hE1, hE2, hMp_eq]
            calc 24 ^ (-2 * ((2 - p) / (4 - p)))
                  * (∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
                ≤ 24 ^ (-((2 - p) / (4 - p)))
                  * (∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p))) := by
                  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hσnn _)
                  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                  linarith [hq'pos]
                _ = (∑ i, (a i) ^ 2) ^ (1 - 2 * ((2 - p) / (4 - p)))
                  * 24 ^ (-((2 - p) / (4 - p))) := by ring
                _ ≤ (MeasureTheory.integral μ
                    (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (2 / (4 - p)) :=
                  hA_le
          by_contra hlt
          have hlt' : (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p)
              < 24 ^ (-((2 - p) / p)) * Real.sqrt (∑ i, (a i) ^ 2) :=
            lt_of_not_ge hlt
          have hlt'' := Real.rpow_lt_rpow
            (Real.rpow_nonneg hMp_nonneg _) hlt' hEpos
          rw [hMp_eq] at hlt''
          linarith [hfin_step]
      have hupper : (MeasureTheory.integral μ
          (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p)
          ≤ max (1:ℝ) ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
            ^ (1 / ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ)))
            * Real.sqrt (∑ i, (a i) ^ 2) := by
        by_cases hp2 : p ≤ 2
        · calc (MeasureTheory.integral μ
                (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p)
              ≤ (MeasureTheory.integral μ
                  (fun ω => |∑ i, a i * ε i ω| ^ (2 : ℝ))) ^ (1 / 2 : ℝ) :=
                kh_lyapunov N a Ω μ ε hmeas hae hp hp2
            _ = Real.sqrt (∑ i, (a i) ^ 2) := hN2
            _ ≤ max (1:ℝ) ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
                ^ (1 / ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ)))
                * Real.sqrt (∑ i, (a i) ^ 2) :=
                le_mul_of_one_le_left hsqrt_nonneg hB_ge1
        · have hkR : (1 : ℝ) ≤ (⌈p / 2⌉₊ : ℝ) := by
            have h1 : (1 : ℝ) < p / 2 := by linarith
            have h2 : p / 2 ≤ (⌈p / 2⌉₊ : ℝ) := Nat.le_ceil _
            linarith
          have hk1 : 1 ≤ ⌈p / 2⌉₊ := by exact_mod_cast hkR
          have hkne : (⌈p / 2⌉₊ : ℝ) ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le (by norm_num) hkR)
          have hcast2 : ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ)
              = 2 * (⌈p / 2⌉₊ : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_ofNat]
          have h2k : p ≤ ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ) := by
            have h2 : p / 2 ≤ (⌈p / 2⌉₊ : ℝ) := Nat.le_ceil _
            have h3 : p ≤ 2 * (⌈p / 2⌉₊ : ℝ) := by linarith
            rwa [← hcast2] at h3
          have hqpos : (0 : ℝ) < ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ) :=
            Nat.cast_pos.mpr (by omega)
          have hexp_id : (⌈p / 2⌉₊ : ℝ)
              * (1 / ((2 * ⌈p / 2⌉₊ : ℕ) : ℝ)) = 1 / 2 := by
            rw [hcast2]
            field_simp
          have hMp_le : (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p)
              ≤ (MeasureTheory.integral μ
                (fun ω => |∑ i, a i * ε i ω|
                  ^ (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
                ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)) :=
            kh_lyapunov N a Ω μ ε hmeas hae hp h2k
          have hMbound : (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω| ^ (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
              ≤ (Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
                * ((∑ i, (a i) ^ 2) ^ ⌈p / 2⌉₊) := by
            rw [kh_rpowint_eq_powint N a Ω μ ε ⌈p / 2⌉₊]
            exact kh_even_moment N a Ω μ ε hmeas hae hmean hindep
              Finset.univ _
          have hMqnn : (0 : ℝ) ≤ (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω|
                ^ (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ))) :=
            MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall
              (fun ω => Real.rpow_nonneg (abs_nonneg _) _))
          have hsqrt_id : (((∑ i, (a i) ^ 2) ^ ⌈p / 2⌉₊) : ℝ)
              ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ))
              = Real.sqrt (∑ i, (a i) ^ 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hσnn, hexp_id,
              ← Real.sqrt_eq_rpow]
          have hbd2 : (MeasureTheory.integral μ
              (fun ω => |∑ i, a i * ε i ω|
                ^ (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
              ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ))
              ≤ ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
                ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
                * Real.sqrt (∑ i, (a i) ^ 2) := by
            have hle := Real.rpow_le_rpow hMqnn hMbound
              (le_of_lt (one_div_pos.mpr hqpos))
            rwa [Real.mul_rpow (by positivity : (0 : ℝ)
                ≤ (Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ))
              (pow_nonneg hσnn _), hsqrt_id] at hle
          calc (MeasureTheory.integral μ
                (fun ω => |∑ i, a i * ε i ω| ^ p)) ^ (1 / p)
              ≤ (MeasureTheory.integral μ
                  (fun ω => |∑ i, a i * ε i ω|
                    ^ (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
                  ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)) := hMp_le
            _ ≤ ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
                ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
                * Real.sqrt (∑ i, (a i) ^ 2) := hbd2
            _ ≤ max (1:ℝ) ((Nat.factorial (2 * ⌈p / 2⌉₊) : ℝ)
                ^ (1 / (((2 * ⌈p / 2⌉₊ : ℕ)) : ℝ)))
                * Real.sqrt (∑ i, (a i) ^ 2) := by
                apply mul_le_mul_of_nonneg_right _ hsqrt_nonneg
                exact le_max_right _ _
      exact ⟨hlower, hupper⟩
end

end MetaMathlibExt

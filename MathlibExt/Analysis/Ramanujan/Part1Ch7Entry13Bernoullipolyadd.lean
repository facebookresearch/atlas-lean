/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 13

Generalized Stieltjes constants exist uniquely; γ₀ is Euler-Mascheroni.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry13Bernoullipolyadd

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7StieltjesApprox (k m : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / j) -
    Real.log (m : ℝ) ^ (k + 1) / (k + 1)

private noncomputable def chapter7StieltjesFun (k : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ k / x

private noncomputable def chapter7StieltjesInt (k : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ (k + 1) / ((k : ℝ) + 1)

private lemma stieltjesFun_nonneg (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ chapter7StieltjesFun k x := by
  refine div_nonneg (pow_nonneg (Real.log_nonneg hx) k) ?_
  linarith

private lemma tendsto_stieltjesFun (k : ℕ) :
    Tendsto (fun n : ℕ => chapter7StieltjesFun k (n : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr (fun n => ?_) h
  simp [chapter7StieltjesFun]

private lemma sum_Icc_stieltjesFun (k m : ℕ) :
    (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / (j : ℝ)) =
      ∑ i ∈ range m, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ) := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ 1 ≤ (0 : ℕ))]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ,
      show Real.log ((n + 1 : ℕ) : ℝ) ^ k / ((n + 1 : ℕ) : ℝ) =
        chapter7StieltjesFun k ((n + 1 : ℕ) : ℝ) from rfl]

private lemma hasDerivAt_stieltjesInt (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (chapter7StieltjesInt k) (chapter7StieltjesFun k x) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  have hpow : HasDerivAt (Real.log ^ (k + 1))
      (((k : ℝ) + 1) * Real.log x ^ ((k + 1) - 1) * x⁻¹) x := by
    have h := hlog.pow (k + 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hdiv := hpow.div_const ((k : ℝ) + 1)
  rw [Nat.add_sub_cancel] at hdiv
  have hkk : ((k : ℝ) + 1) ≠ 0 := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfun : chapter7StieltjesInt k =
      (fun y => (Real.log ^ (k + 1)) y / ((k : ℝ) + 1)) := by
    ext y
    simp [chapter7StieltjesInt, Pi.pow_apply]
  have hval : chapter7StieltjesFun k x =
      ((((k : ℝ) + 1) * Real.log x ^ k * x⁻¹) / ((k : ℝ) + 1)) := by
    unfold chapter7StieltjesFun
    field_simp
  rw [hfun, hval]
  exact hdiv

private lemma integral_stieltjesFun (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, chapter7StieltjesFun k x =
      chapter7StieltjesInt k b - chapter7StieltjesInt k a := by
  have hpos : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    have hx1 : a ≤ x := by
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · linarith
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by linarith) hx1
    exact ne_of_gt hx0
  have hderiv : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ (chapter7StieltjesInt k) x :=
    fun x hx => (hasDerivAt_stieltjesInt k (hpos x hx)).differentiableAt
  have hdeq : ∀ x ∈ Set.uIcc a b,
      deriv (chapter7StieltjesInt k) x = chapter7StieltjesFun k x :=
    fun x hx => (hasDerivAt_stieltjesInt k (hpos x hx)).deriv
  have hcont : ContinuousOn (chapter7StieltjesFun k) (Set.uIcc a b) := by
    unfold chapter7StieltjesFun
    refine ContinuousOn.div ?_ continuousOn_id (fun x hx => hpos x hx)
    exact (Real.continuousOn_log.mono (fun x hx => by simpa using hpos x hx)).pow k
  have hint : IntervalIntegrable (chapter7StieltjesFun k) volume a b :=
    hcont.intervalIntegrable
  have hderiv_int : IntervalIntegrable (deriv (chapter7StieltjesInt k)) volume a b :=
    hint.congr (fun x hx => (hdeq x (Set.uIoc_subset_uIcc hx)).symm)
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hderiv_int
  rw [← hftc]
  exact intervalIntegral.integral_congr (fun x hx => (hdeq x hx).symm)

private lemma continuousOn_stieltjesFun (k : ℕ) {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (chapter7StieltjesFun k) s := by
  unfold chapter7StieltjesFun
  refine ContinuousOn.div ?_ continuousOn_id (fun x hx => hs x hx)
  exact (Real.continuousOn_log.mono (fun x hx => by simpa using hs x hx)).pow k

private lemma antitoneOn_stieltjesFun (k : ℕ) :
    AntitoneOn (chapter7StieltjesFun k) (Set.Ici (Real.exp (k : ℝ))) := by
  have hexp1 : (1 : ℝ) ≤ Real.exp (k : ℝ) := Real.one_le_exp (Nat.cast_nonneg k)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have heq : chapter7StieltjesFun 0 = fun x : ℝ => x⁻¹ := by
      ext x
      unfold chapter7StieltjesFun
      simp
    rw [heq]
    have h : AntitoneOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) := by
      intro a ha b hb hab
      simp only [Set.mem_Ioi] at ha hb
      exact (inv_le_inv₀ hb ha).mpr hab
    apply h.mono
    intro x hx
    simp only [Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hexp1, hx]
  · refine antitoneOn_of_deriv_nonpos (convex_Ici _) ?_ ?_ ?_
    · apply continuousOn_stieltjesFun k
      intro x hx
      simp only [Set.mem_Ici] at hx
      exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) hx)
    · rw [interior_Ici]
      intro x hx
      simp only [Set.mem_Ioi] at hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_trans (Real.exp_pos _) hx)
      unfold chapter7StieltjesFun
      have hhad := ((Real.hasDerivAt_log hx0).fun_pow k).div (hasDerivAt_id x) hx0
      exact hhad.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      simp only [Set.mem_Ioi] at hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_trans (Real.exp_pos _) hx)
      have hLk : (k : ℝ) < Real.log x := by
        have h := Real.log_lt_log (Real.exp_pos _) hx
        rwa [Real.log_exp] at h
      have hLpos : (0 : ℝ) < Real.log x := lt_trans (Nat.cast_pos.mpr hkpos) hLk
      have hhad := ((Real.hasDerivAt_log hx0).fun_pow k).div (hasDerivAt_id x) hx0
      have hde : deriv (chapter7StieltjesFun k) x =
          (((k : ℝ) * Real.log x ^ (k - 1) * x⁻¹ * x - Real.log x ^ k * 1) / x ^ 2) :=
        hhad.deriv
      rw [hde]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_one] at hLk ⊢
      rw [pow_succ]
      have hxinv : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0
      have hE : ((j : ℝ) + 1) * Real.log x ^ j * x⁻¹ * x - Real.log x ^ j * Real.log x * 1 ≤ 0 := by
        have h1 : ((j : ℝ) + 1) * Real.log x ^ j * x⁻¹ * x - Real.log x ^ j * Real.log x * 1
            = Real.log x ^ j * ((((j : ℝ) + 1) * (x⁻¹ * x)) - Real.log x) := by ring
        rw [h1]
        apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hLpos.le _)
        rw [hxinv, mul_one]
        linarith [hLk]
      exact div_nonpos_of_nonpos_of_nonneg hE (by positivity)

private lemma approx_eq_sum_sub_int (k m : ℕ) :
    chapter7StieltjesApprox k m =
      (∑ i ∈ range m, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
        chapter7StieltjesInt k (m : ℝ) := by
  unfold chapter7StieltjesApprox chapter7StieltjesInt
  rw [sum_Icc_stieltjesFun k m]

private lemma cauchySeq_stieltjesApprox (k : ℕ) : CauchySeq (chapter7StieltjesApprox k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_ge (Real.exp (k : ℝ))
  have hlim := tendsto_stieltjesFun k
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N1, hN1⟩ := hlim ε hε
  refine ⟨max (max N0 N1) 1, fun m1 hm1 m2 hm2 => ?_⟩
  have main : ∀ a b : ℕ, a ≥ max (max N0 N1) 1 → b ≥ max (max N0 N1) 1 → a ≤ b →
      dist (chapter7StieltjesApprox k a) (chapter7StieltjesApprox k b) < ε := by
    intro m1 m2 hm1 hm2 hle
    have hm1N0 : N0 ≤ m1 :=
      le_trans (le_trans (le_max_left N0 N1) (le_max_left _ 1)) hm1
    have hm1N1 : N1 ≤ m1 :=
      le_trans (le_trans (le_max_right N0 N1) (le_max_left _ 1)) hm1
    have hm11 : 1 ≤ m1 := le_trans (le_max_right _ 1) hm1
    have hm12 : 1 ≤ m2 := le_trans (le_max_right _ 1) hm2
    have hFsums : (∑ i ∈ range m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
        (∑ i ∈ range m1, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) =
        ∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ) :=
      (Finset.sum_Ico_eq_sub _ hle).symm
    have hInt : ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x =
        chapter7StieltjesInt k (m2 : ℝ) - chapter7StieltjesInt k (m1 : ℝ) :=
      integral_stieltjesFun k (by exact_mod_cast hm11) (by exact_mod_cast hle)
    have hdiff : chapter7StieltjesApprox k m2 - chapter7StieltjesApprox k m1 =
        (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
          ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x := by
      rw [approx_eq_sum_sub_int, approx_eq_sum_sub_int]
      linear_combination hFsums + hInt
    have hanti : AntitoneOn (chapter7StieltjesFun k) (Set.Icc (m1 : ℝ) (m2 : ℝ)) := by
      apply (antitoneOn_stieltjesFun k).mono
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ici]
      calc Real.exp (k : ℝ) ≤ (N0 : ℝ) := hN0
        _ ≤ (m1 : ℝ) := by exact_mod_cast hm1N0
        _ ≤ x := hx.1
    have hlow : (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) ≤
        ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x :=
      AntitoneOn.sum_le_integral_Ico (by exact_mod_cast hle) hanti
    have hhigh : ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x ≤
        ∑ i ∈ Ico m1 m2, chapter7StieltjesFun k (i : ℝ) :=
      AntitoneOn.integral_le_sum_Ico (by exact_mod_cast hle) hanti
    have htele : (∑ i ∈ Ico m1 m2, (chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ) -
        chapter7StieltjesFun k (i : ℝ))) =
        chapter7StieltjesFun k (m2 : ℝ) - chapter7StieltjesFun k (m1 : ℝ) := by
      have h2 : ∀ n : ℕ, (∑ i ∈ range n, (chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ) -
          chapter7StieltjesFun k (i : ℝ))) =
          chapter7StieltjesFun k (n : ℝ) - chapter7StieltjesFun k ((0 : ℕ) : ℝ) :=
        fun n => Finset.sum_range_sub (fun i => chapter7StieltjesFun k (i : ℝ)) n
      rw [Finset.sum_Ico_eq_sub _ hle, h2, h2]
      ring
    have hnn1 : 0 ≤ chapter7StieltjesFun k (m1 : ℝ) :=
      stieltjesFun_nonneg k (by exact_mod_cast hm11)
    have hnn2 : 0 ≤ chapter7StieltjesFun k (m2 : ℝ) :=
      stieltjesFun_nonneg k (by exact_mod_cast hm12)
    have hsmall : chapter7StieltjesFun k (m1 : ℝ) < ε := by
      have hdist : dist (chapter7StieltjesFun k (m1 : ℝ)) 0 < ε := hN1 m1 hm1N1
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn1] at hdist
      exact hdist
    have hbound : |((∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
        ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x)| ≤
        chapter7StieltjesFun k (m1 : ℝ) := by
      have hSS' : (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k (i : ℝ)) -
          (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) =
          chapter7StieltjesFun k (m1 : ℝ) - chapter7StieltjesFun k (m2 : ℝ) := by
        have h3 : (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k (i : ℝ)) -
            (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) =
            -((∑ i ∈ Ico m1 m2, (chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ) -
              chapter7StieltjesFun k (i : ℝ)))) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [h3, htele]
        ring
      rw [abs_le]
      constructor
      · have hle1 : (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
            ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x ≥
            (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
            (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k (i : ℝ)) := by
          linarith [hhigh]
        have heq2 : (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
            (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k (i : ℝ)) =
            -((∑ i ∈ Ico m1 m2, chapter7StieltjesFun k (i : ℝ)) -
            (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ))) := by ring
        rw [heq2, hSS'] at hle1
        linarith [hnn2]
      · have hle2 : (∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
            ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x ≤ 0 := by
          linarith [hlow]
        linarith [hnn1]
    calc dist (chapter7StieltjesApprox k m1) (chapter7StieltjesApprox k m2)
        = |chapter7StieltjesApprox k m1 - chapter7StieltjesApprox k m2| :=
          Real.dist_eq _ _
      _ = |chapter7StieltjesApprox k m2 - chapter7StieltjesApprox k m1| :=
          abs_sub_comm _ _
      _ = |(∑ i ∈ Ico m1 m2, chapter7StieltjesFun k ((i + 1 : ℕ) : ℝ)) -
            ∫ x in (m1 : ℝ)..(m2 : ℝ), chapter7StieltjesFun k x| := by rw [hdiff]
      _ ≤ chapter7StieltjesFun k (m1 : ℝ) := hbound
      _ < ε := hsmall
  rcases le_total m1 m2 with hle | hle
  · exact main m1 m2 hm1 hm2 hle
  · rw [dist_comm]
    exact main m2 m1 hm2 hm1 hle

/-- **Stieltjes constants exist, and the zeroth is Euler's constant.** There is exactly one sequence
of real numbers $(c_k)_{k \ge 0}$ such that, for every $k \ge 0$,
$$\sum_{j=1}^{m} \frac{(\log j)^k}{j} - \frac{(\log m)^{k+1}}{k+1} \longrightarrow c_k
  \quad (m \to \infty),$$
and $c_0 = \gamma$, where $\gamma$ is Euler's constant.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 13.
Proves `Wanted` entry `ramanujan_part1_ch7_entry13_bernoullipolyadd`.
-/
theorem ramanujan_part1_ch7_entry13_bernoullipolyadd :
    ∃! c : ℕ → ℝ,
      (∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) ∧
        c 0 = Real.eulerMascheroniConstant := by
  refine ⟨fun k => Filter.atTop.limUnder (chapter7StieltjesApprox k), ⟨?_, ?_⟩, ?_⟩
  · intro k
    exact (cauchySeq_stieltjesApprox k).tendsto_limUnder
  · have h0 : chapter7StieltjesApprox 0 =
        fun n : ℕ => ((harmonic n : ℚ) : ℝ) - Real.log (n : ℝ) := by
      ext m
      show chapter7StieltjesApprox 0 m = ((harmonic m : ℚ) : ℝ) - Real.log (m : ℝ)
      have hA : chapter7StieltjesApprox 0 m =
          (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ 0 / (j : ℝ)) -
            Real.log (m : ℝ) ^ (0 + 1) / (((0 : ℕ) : ℝ) + 1) := rfl
      have e2 : ((harmonic m : ℚ) : ℝ) =
          ∑ i ∈ range m, chapter7StieltjesFun 0 ((i + 1 : ℕ) : ℝ) := by
        unfold harmonic
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        unfold chapter7StieltjesFun
        simp
      rw [hA, sum_Icc_stieltjesFun 0 m, e2,
        show Real.log (m : ℝ) ^ (0 + 1) / (((0 : ℕ) : ℝ) + 1) =
          Real.log (m : ℝ) from by simp]
    have hlim0 : Tendsto (fun n : ℕ => ((harmonic n : ℚ) : ℝ) - Real.log (n : ℝ)) atTop
        (𝓝 (Filter.atTop.limUnder (chapter7StieltjesApprox 0))) :=
      Filter.Tendsto.congr (fun n => congrFun h0 n)
        (cauchySeq_stieltjesApprox 0).tendsto_limUnder
    have huniq := tendsto_nhds_unique hlim0 Real.tendsto_harmonic_sub_log
    have hbeta : (fun k => Filter.atTop.limUnder (chapter7StieltjesApprox k)) 0 =
        Filter.atTop.limUnder (chapter7StieltjesApprox 0) := rfl
    rw [hbeta]
    exact huniq
  · intro c' hc'
    obtain ⟨hlim', h0'⟩ := hc'
    funext k
    exact (tendsto_nhds_unique (cauchySeq_stieltjesApprox k).tendsto_limUnder
      (hlim' k)).symm

end

end Entry13Bernoullipolyadd

end MathlibExt.Analysis.Ramanujan.Part1Ch7

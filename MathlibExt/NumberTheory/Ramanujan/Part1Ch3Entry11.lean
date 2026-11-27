/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 11

Recurrence for coefficients of exp(f(x)) in terms of f's power series.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry11

private lemma aux_summable_bounded (h : ℕ → ℝ) (hs : Summable h) :
    ∃ C : ℝ, ∀ n, ‖h n‖ ≤ C := by
  have ht : Filter.Tendsto h Filter.atTop (nhds 0) := hs.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht 1 one_pos
  set S := Finset.image (fun n => ‖h n‖) (Finset.range (N + 1)) with hS
  have hSne : S.Nonempty := by
    rw [hS]
    exact Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N))
  refine ⟨max 1 (S.max' hSne), fun n => ?_⟩
  by_cases hn : n < N + 1
  · have hmem : ‖h n‖ ∈ S := Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩
    exact le_trans (Finset.le_max' S _ hmem) (le_max_right _ _)
  · have hn' : N ≤ n := by omega
    have h1 := hN n hn'
    rw [dist_zero_right] at h1
    exact le_trans h1.le (le_max_left _ _)

private lemma aux_eball_abs (R : ℝ) (hR : 0 < R) (y : ℝ) (rNN : NNReal) (hr : (rNN : ℝ) = R / 2)
    (hy : y ∈ Metric.eball 0 ((rNN : NNReal) : ENNReal)) :
    |y| < R := by
  rw [Metric.mem_eball, edist_lt_coe, nndist_zero_right] at hy
  have h4 : ((‖y‖₊ : NNReal) : ℝ) < (rNN : ℝ) := by exact_mod_cast hy
  rw [hr] at h4
  have h5 : ‖y‖ < R / 2 := h4
  rw [Real.norm_eq_abs] at h5
  linarith

private lemma aux_ball_subset (R : ℝ) (rNN : NNReal) (hr : (rNN : ℝ) = R / 2) :
    Metric.ball (0:ℝ) (R / 2) ⊆ Metric.eball 0 ((rNN : NNReal) : ENNReal) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [Metric.mem_eball, edist_lt_coe, nndist_zero_right]
  have h5 : ((‖x‖₊ : NNReal):ℝ) < (rNN:ℝ) := by rw [hr]; exact hx
  exact_mod_cast h5

private lemma aux_hasSum_shift (A : ℕ → ℝ) (y fval : ℝ)
    (h : HasSum (fun n : ℕ => A (n + 1) * y ^ (n + 1) / (↑(n + 1) : ℝ)) fval) :
    HasSum (fun m : ℕ => (if m = 0 then 0 else A m / (m : ℝ)) * y ^ m) fval := by
  set F : ℕ → ℝ := fun m => (if m = 0 then 0 else A m / (m : ℝ)) * y ^ m with hF
  have hF0 : F 0 = 0 := by simp [hF]
  have hshift : (fun n : ℕ => A (n + 1) * y ^ (n + 1) / (↑(n + 1) : ℝ)) =
      (fun n => F (n + 1)) := by
    funext n
    have hne : n + 1 ≠ 0 := by omega
    simp only [hF, hne, ↓reduceIte]
    ring
  rw [hshift] at h
  have h2 := (hasSum_nat_add_iff 1).mp h
  rw [Finset.sum_range_one] at h2
  rw [hF0, add_zero] at h2
  exact h2

private lemma aux_hasFPowerSeries_p (p : ℕ → ℝ) (R : ℝ) (g : ℝ → ℝ) (hR : 0 < R)
    (hg : ∀ x : ℝ, |x| < R → HasSum (fun n : ℕ => p n * x ^ n) (g x))
    (rNN : NNReal) (hr : (rNN : ℝ) = R / 2) :
    HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℝ p) 0
      ((rNN : NNReal) : ENNReal) := by
  have hpos2 : (0:ℝ) < R / 2 := by linarith
  have hy0 : |R / 2| < R := by
    rw [abs_of_pos hpos2]; linarith
  have hsum := (hg (R / 2) hy0).summable
  obtain ⟨C, hC⟩ := aux_summable_bounded _ hsum
  have hrNNle : (rNN : NNReal) ≤ (FormalMultilinearSeries.ofScalars ℝ p).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ (max C 0)
    intro n
    rw [FormalMultilinearSeries.ofScalars_norm]
    have hnorm : ‖(R / 2 : ℝ)‖ = R / 2 := by
      rw [Real.norm_eq_abs, abs_of_pos hpos2]
    calc ‖p n‖ * (rNN : ℝ) ^ n
        = ‖p n‖ * (R / 2) ^ n := by rw [hr]
      _ = ‖p n * (R / 2) ^ n‖ := by rw [norm_mul, norm_pow, hnorm]
      _ ≤ C := hC n
      _ ≤ max C 0 := le_max_left _ _
  apply HasFPowerSeriesOnBall.mk hrNNle _ _
  · rw [ENNReal.coe_pos]
    have hposNN : (0:ℝ) < (rNN : ℝ) := by rw [hr]; linarith
    exact_mod_cast hposNN
  · intro y hy
    have hyR : |y| < R := aux_eball_abs R hR y rNN hr hy
    have hgy := hg y hyR
    rw [zero_add]
    refine hgy.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

private lemma aux_hasFPowerSeries_f (A : ℕ → ℝ) (R : ℝ) (f : ℝ → ℝ) (hR : 0 < R)
    (hf : ∀ x : ℝ, |x| < R → HasSum (fun n : ℕ => A (n + 1) * x ^ (n + 1) / (↑(n + 1) : ℝ)) (f x))
    (rNN : NNReal) (hr : (rNN : ℝ) = R / 2) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℝ
      (fun m => if m = 0 then 0 else A m / (m : ℝ))) 0 ((rNN : NNReal) : ENNReal) := by
  have hpos2 : (0:ℝ) < R / 2 := by linarith
  have hy0 : |R / 2| < R := by
    rw [abs_of_pos hpos2]; linarith
  have hsum := (hf (R / 2) hy0).summable
  obtain ⟨C, hC⟩ := aux_summable_bounded _ hsum
  have hnorm : ‖(R / 2 : ℝ)‖ = R / 2 := by
    rw [Real.norm_eq_abs, abs_of_pos hpos2]
  have hrNNle : (rNN : NNReal) ≤ (FormalMultilinearSeries.ofScalars ℝ
      (fun m => if m = 0 then 0 else A m / (m : ℝ))).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ (max C 0)
    intro m
    rw [FormalMultilinearSeries.ofScalars_norm]
    by_cases hm : m = 0
    · subst hm
      simp only [ite_true, norm_zero, zero_mul]
      exact le_max_right _ _
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      have hne : n + 1 ≠ 0 := by omega
      have hif : (if n + 1 = 0 then (0:ℝ) else A (n + 1) / ((n + 1 : ℕ):ℝ)) =
          A (n + 1) / ((n + 1 : ℕ):ℝ) := by
        simp only [hne, ↓reduceIte]
      have hN : ‖(((n + 1 : ℕ)):ℝ)‖ = ((n + 1 : ℕ):ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      rw [hif, hr]
      have e : ‖A (n + 1) / ((n + 1 : ℕ):ℝ)‖ * (R / 2) ^ (n + 1) =
          ‖A (n + 1) * (R / 2) ^ (n + 1) / ((n + 1 : ℕ):ℝ)‖ := by
        simp only [norm_div, norm_mul, norm_pow, hnorm, hN]
        ring
      rw [e]
      exact le_trans (hC n) (le_max_left _ _)
  apply HasFPowerSeriesOnBall.mk hrNNle _ _
  · rw [ENNReal.coe_pos]
    have hposNN : (0:ℝ) < (rNN : ℝ) := by rw [hr]; linarith
    exact_mod_cast hposNN
  · intro y hy
    have hyR : |y| < R := aux_eball_abs R hR y rNN hr hy
    have hfy := aux_hasSum_shift A y (f y) (hf y hyR)
    rw [zero_add]
    refine hfy.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

private lemma aux_coeff (c : ℕ → ℝ) (F : ℝ → ℝ) (rNN : NNReal)
    (hP : HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℝ c) 0
      ((rNN : NNReal) : ENNReal))
    (n : ℕ) : iteratedDeriv n F 0 = (n.factorial : ℝ) * c n := by
  have h1 := hP.factorial_smul (1 : ℝ) n
  rw [FormalMultilinearSeries.ofScalars_apply_eq] at h1
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [← h1]
  simp only [nsmul_eq_mul, smul_eq_mul, one_pow, mul_one]

private lemma aux_deriv_coeff (A : ℕ → ℝ) (f : ℝ → ℝ) (rNN : NNReal)
    (hfP : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℝ
      (fun m => if m = 0 then 0 else A m / (m : ℝ))) 0 ((rNN : NNReal) : ENNReal))
    (k : ℕ) : iteratedDeriv k (deriv f) 0 = (k.factorial : ℝ) * A (k + 1) := by
  have h2 := aux_coeff (fun m => if m = 0 then 0 else A m / (m : ℝ)) f rNN hfP (k + 1)
  rw [← iteratedDeriv_succ', h2]
  have hne : k + 1 ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  have hfact : ((k + 1).factorial : ℝ) = (((k + 1 : ℕ)) : ℝ) * (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ k
  rw [hfact]
  have hk1 : (((k + 1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  field_simp

/-- **Recurrence for the coefficients of $e^{f(x)}$.** Let $(A_k)_{k \ge 1}$ and $(p_n)_{n \ge 0}$
be sequences of real numbers, let $R > 0$, and let $f : \mathbb{R} \to \mathbb{R}$. Suppose that
for every real $x$ with $|x| < R$ the series $\sum_{k \ge 1} A_k x^k / k$ is summable with sum
$f(x)$ and the series $\sum_{n \ge 0} p_n x^n$ is summable with sum $e^{f(x)}$. Then for every
integer $n \ge 1$,
$$n p_n = \sum_{k=1}^{n} A_k p_{n-k}.$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 11, printed p. 66 / PDF p.
    76.
Proves `Wanted` entry `ramanujan_part1_ch3_entry11`.
-/
theorem ramanujan_part1_ch3_entry11 (A p : ℕ → ℝ) (R : ℝ) (f : ℝ → ℝ) (hR : 0 < R)
    (hf : ∀ x : ℝ, |x| < R → HasSum (fun n : ℕ => A (n + 1) * x ^ (n + 1) / (↑(n + 1) : ℝ)) (f x))
    (hg : ∀ x : ℝ, |x| < R → HasSum (fun n : ℕ => p n * x ^ n) (Real.exp (f x))) :
    ∀ n : ℕ, 0 < n → (↑n : ℝ) * p n = ∑ k ∈ Finset.Icc 1 n, A k * p (n - k) := by
  have hrNN : (0:ℝ) ≤ R / 2 := by linarith
  let rNN : NNReal := ⟨R / 2, hrNN⟩
  have hr : (rNN : ℝ) = R / 2 := rfl
  have hfP := aux_hasFPowerSeries_f A R f hR hf rNN hr
  have hgP := aux_hasFPowerSeries_p p R (fun x => Real.exp (f x)) hR hg rNN hr
  have hfA : AnalyticAt ℝ f 0 := hfP.analyticAt
  have hgA : AnalyticAt ℝ (fun x => Real.exp (f x)) 0 := hgP.analyticAt
  have hfDA : AnalyticAt ℝ (deriv f) 0 := hfA.deriv
  have hball : Metric.ball (0:ℝ) (R / 2) ∈ nhds (0:ℝ) :=
    Metric.ball_mem_nhds 0 (by linarith)
  have hderiv_pt : ∀ x ∈ Metric.ball (0:ℝ) (R / 2),
      deriv (fun x => Real.exp (f x)) x =
        (fun x => Real.exp (f x)) x * deriv f x := by
    intro x hx
    have hxe : x ∈ Metric.eball (0:ℝ) ((rNN : NNReal) : ENNReal) :=
      aux_ball_subset R rNN hr hx
    have hNN : (‖x‖₊ : NNReal) < rNN := by
      have h := Metric.mem_eball.mp hxe
      rw [edist_lt_coe, nndist_zero_right] at h
      exact h
    have hmem : ((‖x‖₊ : NNReal) : ENNReal) < ((rNN : NNReal) : ENNReal) :=
      ENNReal.coe_lt_coe.mpr hNN
    have hfd := hfP.hasFDerivAt hmem
    rw [zero_add] at hfd
    have h2 := hfd.hasDerivAt
    have h3 := h2.exp
    have h4 := h3.deriv
    have h5 := h2.deriv
    rw [← h5] at h4
    exact h4
  have hEq : (deriv fun x => Real.exp (f x)) =ᶠ[nhds (0:ℝ)]
      ((fun x => Real.exp (f x)) * deriv f) := by
    filter_upwards [hball] with x hx
    rw [Pi.mul_apply]
    exact hderiv_pt x hx
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Nat.succ_eq_add_one]
  have hCg : ContDiffAt ℝ (↑m) (fun x => Real.exp (f x)) 0 := hgA.contDiffAt
  have hCf : ContDiffAt ℝ (↑m) (deriv f) 0 := hfDA.contDiffAt
  have hLeib := iteratedDeriv_mul hCg hCf
  have hLHS : iteratedDeriv m (deriv fun x => Real.exp (f x)) 0 =
      iteratedDeriv m ((fun x => Real.exp (f x)) * deriv f) 0 :=
    hEq.iteratedDeriv_eq m
  have hLHS2 : iteratedDeriv m (deriv fun x => Real.exp (f x)) 0 =
      ((m + 1).factorial : ℝ) * p (m + 1) := by
    rw [← iteratedDeriv_succ']
    exact aux_coeff p _ rNN hgP (m + 1)
  have key : ((m + 1).factorial : ℝ) * p (m + 1) =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (iteratedDeriv i (fun x => Real.exp (f x)) 0) *
        (iteratedDeriv (m - i) (deriv f) 0) := by
    rw [← hLHS2, hLHS, hLeib]
  have hterm : ∀ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * (iteratedDeriv i (fun x => Real.exp (f x)) 0) *
        (iteratedDeriv (m - i) (deriv f) 0) =
      (m.factorial : ℝ) * (p i * A (m + 1 - i)) := by
    intro i hi
    have hi_le : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have e1 := aux_coeff p _ rNN hgP i
    have e2 := aux_deriv_coeff A f rNN hfP (m - i)
    have e3 : m.choose i * i.factorial * (m - i).factorial = m.factorial :=
      Nat.choose_mul_factorial_mul_factorial hi_le
    have e3R : ((m.choose i : ℕ) : ℝ) * ((i.factorial : ℕ) : ℝ) *
        (((m - i).factorial : ℕ) : ℝ) = ((m.factorial : ℕ) : ℝ) := by
      exact_mod_cast e3
    have harg : m - i + 1 = m + 1 - i := by omega
    have hrearr : (m.choose i : ℝ) * ((i.factorial : ℝ) * p i) *
        (((m - i).factorial : ℝ) * A (m + 1 - i)) =
        ((m.choose i : ℝ) * (i.factorial : ℝ) * (m - i).factorial) *
          (p i * A (m + 1 - i)) := by ring
    rw [e1, e2, harg, hrearr, e3R]
  have hsum_eq : (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (iteratedDeriv i (fun x => Real.exp (f x)) 0) *
        (iteratedDeriv (m - i) (deriv f) 0)) =
      (m.factorial : ℝ) * (∑ i ∈ Finset.range (m + 1), p i * A (m + 1 - i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => hterm i hi)
  have hreflect : (∑ i ∈ Finset.range (m + 1), p i * A (m + 1 - i)) =
      (∑ i ∈ Finset.range (m + 1), A (i + 1) * p (m - i)) := by
    have hR := Finset.sum_range_reflect (fun j => A (j + 1) * p (m - j)) (m + 1)
    have hmid : (∑ j ∈ Finset.range (m + 1), A (m + 1 - 1 - j + 1) * p (m - (m + 1 - 1 - j))) =
        (∑ i ∈ Finset.range (m + 1), A (i + 1) * p (m - i)) := hR
    rw [← hmid]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_le : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have a2 : m + 1 - 1 - j + 1 = m + 1 - j := by omega
    have a3 : m - (m + 1 - 1 - j) = j := by omega
    rw [a2, a3]
    ring
  have hIcc : (∑ k ∈ Finset.Icc 1 (m + 1), A k * p (m + 1 - k)) =
      (∑ i ∈ Finset.range (m + 1), A (i + 1) * p (m - i)) := by
    have himg : (Finset.range (m + 1)).image (fun i => i + 1) = Finset.Icc 1 (m + 1) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, by omega⟩
      · intro h
        exact ⟨k - 1, by omega, by omega⟩
    have hInj : Set.InjOn (fun i => i + 1) (↑(Finset.range (m + 1)) : Set ℕ) := by
      intro a _ b _ h
      exact Nat.add_right_cancel h
    rw [← himg, Finset.sum_image hInj]
    apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have a4 : m + 1 - (i + 1) = m - i := by omega
    show A (i + 1) * p (m + 1 - (i + 1)) = A (i + 1) * p (m - i)
    rw [a4]
  have hfact2 : ((m + 1).factorial : ℝ) = (((m + 1 : ℕ)) : ℝ) * (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ m
  have hmne : (m.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [hfact2] at key
  rw [hsum_eq, hreflect] at key
  rw [hIcc]
  have hkey2 : (m.factorial : ℝ) * ((((m + 1 : ℕ))) * p (m + 1)) =
      (m.factorial : ℝ) * (∑ i ∈ Finset.range (m + 1), A (i + 1) * p (m - i)) := by
    linear_combination key
  exact mul_left_cancel₀ hmne hkey2

end Entry11

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3

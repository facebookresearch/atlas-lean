/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry13Bernoullirecurrence

open scoped Nat Real BigOperators Interval ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry13Bernoullipolyadd (chapter7StieltjesApprox)

noncomputable section

def chapter7StieltjesLaurentTerm (c : ℕ → ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * (c k : ℂ) / (k.factorial : ℂ) * (s - 1) ^ k

private theorem auxNatCpowHasDerivAt (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    HasDerivAt (fun u : ℂ => ((n : ℂ) ^ (-u))) (((n : ℂ) ^ (-s)) * Complex.log n * (-1)) s := by
  have h1 : HasDerivAt (fun u : ℂ => -u) (-1) s := (hasDerivAt_id s).neg
  have h2 := HasDerivAt.const_cpow (c := (n : ℂ)) (f := fun u : ℂ => -u) h1
    (Or.inl (Nat.cast_ne_zero.mpr hn))
  simpa [mul_comm] using h2

private theorem auxNatCpowIterDeriv (n : ℕ) (hn : n ≠ 0) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun u : ℂ => ((n : ℂ) ^ (-u))) s
      = ((-Complex.log (n : ℂ)) ^ k) * ((n : ℂ) ^ (-s)) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hder : HasDerivAt (fun u : ℂ => ((-Complex.log (n : ℂ)) ^ k) * ((n : ℂ) ^ (-u)))
          (((-Complex.log (n : ℂ)) ^ k) * ((((n : ℂ) ^ (-s)) * Complex.log n * (-1)))) s :=
        HasDerivAt.const_mul _ (auxNatCpowHasDerivAt n hn s)
      have hfun : (fun u : ℂ => ((-Complex.log (n : ℂ)) ^ k) * ((n : ℂ) ^ (-u)))
          = iteratedDeriv k (fun u : ℂ => ((n : ℂ) ^ (-u))) := by
        funext u
        exact (ih u).symm
      rw [hfun] at hder
      rw [hder.deriv]
      ring

private theorem auxNatCpowIterDerivAtOne (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    iteratedDeriv k (fun u : ℂ => ((n : ℂ) ^ (-u))) 1
      = (-1 : ℂ) ^ k * (((Real.log (n : ℝ)) : ℝ) : ℂ) ^ k / (n : ℂ) := by
  have hn0 : n ≠ 0 := by omega
  rw [auxNatCpowIterDeriv n hn0 k 1]
  have hlog : Complex.log (n : ℂ) = ((((Real.log (n : ℝ))) : ℝ) : ℂ) := by
    rw [Complex.natCast_log]
  have hcpow : ((n : ℂ) ^ (-(1 : ℂ))) = ((n : ℂ))⁻¹ := by
    have harg : (-(1 : ℂ)) = (-1 : ℂ) := by ring
    rw [harg]
    exact Complex.cpow_neg_one _
  rw [hlog, hcpow]
  rw [div_eq_mul_inv]
  ring

private theorem auxNatCpowDifferentiable (n : ℕ) (hn : n ≠ 0) :
    Differentiable ℂ (fun s : ℂ => ((n : ℂ) ^ (-s))) := by
  apply Differentiable.const_cpow _ (Or.inl (Nat.cast_ne_zero.mpr hn))
  exact differentiable_id.neg

private theorem auxNatCpowIterDifferentiable (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k (fun s : ℂ => ((n : ℂ) ^ (-s)))) := by
  have hform : iteratedDeriv k (fun s : ℂ => ((n : ℂ) ^ (-s)))
      = fun s => ((-Complex.log (n : ℂ)) ^ k) * ((n : ℂ) ^ (-s)) :=
    funext (auxNatCpowIterDeriv n hn k)
  rw [hform]
  exact (auxNatCpowDifferentiable n hn).const_mul _

private theorem auxSumCommFun (ι : Type*) (s : Finset ι) (F : ι → ℂ → ℂ) (k : ℕ)
    (hF : ∀ i ∈ s, Differentiable ℂ (F i)) :
    iteratedDeriv k (fun z => ∑ i ∈ s, F i z)
      = (fun z => ∑ i ∈ s, iteratedDeriv k (F i) z) := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      have hFItk : ∀ i ∈ s, Differentiable ℂ (iteratedDeriv k (F i)) := by
        intro i hi
        have hCD : ContDiff ℂ ⊤ (F i) := (hF i hi).contDiff
        exact hCD.differentiable_iteratedDeriv k (by simp)
      funext x
      conv_lhs => rw [iteratedDeriv_succ, ih]
      have hPi : (fun z => ∑ i ∈ s, iteratedDeriv k (F i) z)
          = ∑ i ∈ s, iteratedDeriv k (F i) :=
        funext (fun z => (Finset.sum_apply z s (fun i => iteratedDeriv k (F i))).symm)
      rw [hPi, deriv_sum (fun i hi => (hFItk i hi).differentiableAt)]
      apply Finset.sum_congr rfl
      intro i _
      rw [iteratedDeriv_succ]

private theorem auxSumComm (ι : Type*) (s : Finset ι) (F : ι → ℂ → ℂ) (k : ℕ)
    (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (x : ℂ) :
    iteratedDeriv k (fun z => ∑ i ∈ s, F i z) x
      = ∑ i ∈ s, iteratedDeriv k (F i) x := by
  have h := auxSumCommFun ι s F k hF
  exact congrFun h x

private theorem auxFinsetSumDeriv (m k : ℕ) :
    iteratedDeriv k (fun s : ℂ => ∑ n ∈ Finset.Icc 1 m, ((n : ℂ) ^ (-s))) 1
      = (-1 : ℂ) ^ k * ∑ n ∈ Finset.Icc 1 m, ((((Real.log (n : ℝ))) : ℝ) : ℂ) ^ k / (n : ℂ) := by
  have hF : ∀ i ∈ Finset.Icc 1 m, Differentiable ℂ (fun s : ℂ => ((i : ℂ) ^ (-s))) := by
    intro n hn
    apply auxNatCpowDifferentiable
    have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  rw [auxSumComm _ _ _ _ hF 1, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n hn => by
    rw [auxNatCpowIterDerivAtOne n (Finset.mem_Icc.mp hn).1 k]; ring)

private noncomputable def SFun (m : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 m, ((n : ℂ) ^ (-s))

private noncomputable def IFun (m : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (1 : ℝ)..(m : ℝ), ((t : ℂ) ^ (-s))

private noncomputable def EFun (m : ℕ) (s : ℂ) : ℂ :=
  SFun m s - IFun m s

private noncomputable def JFun (j m : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (1 : ℝ)..(m : ℝ), ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-s)))

private noncomputable def HFun (m : ℕ) (s : ℂ) : ℂ := EFun (m + 1) s

private def USet : Set ℂ := { s : ℂ | 0 < s.re }

private noncomputable def GFun (s : ℂ) : ℂ :=
  EFun 1 s + ∑' n : ℕ, (EFun (n + 2) s - EFun (n + 1) s)

private theorem auxRealCpowHasDerivAt (t : ℝ) (ht : t ≠ 0) (s : ℂ) :
    HasDerivAt (fun u : ℂ => ((t : ℂ) ^ (-u)))
      (((t : ℂ) ^ (-s)) * Complex.log (t : ℂ) * (-1)) s := by
  have h1 : HasDerivAt (fun u : ℂ => -u) (-1) s := (hasDerivAt_id s).neg
  have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have h2 := HasDerivAt.const_cpow (c := (t : ℂ)) (f := fun u : ℂ => -u) h1 (Or.inl hne)
  simpa [mul_comm] using h2

private theorem auxIntegrandHasDerivAt (t : ℝ) (ht : 0 < t) (j : ℕ) (x : ℂ) :
    HasDerivAt (fun u : ℂ => ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-u))))
      ((-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-x))) x := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hbase := auxRealCpowHasDerivAt t ht0 x
  have hlog : Complex.log (t : ℂ) = ((Real.log t : ℝ) : ℂ) :=
    (Complex.ofReal_log (le_of_lt ht)).symm
  have hmul := HasDerivAt.const_mul ((-(Real.log t : ℂ)) ^ j) hbase
  have heq : ((-(Real.log t : ℂ)) ^ j) *
      (((t : ℂ) ^ (-x)) * Complex.log (t : ℂ) * (-1)) =
      (-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-x)) := by
    rw [hlog]
    ring
  rwa [heq] at hmul

private theorem auxUiccPos (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) (m : ℝ)) :
    0 < t := by
  have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Set.uIcc_of_le h1m, Set.mem_Icc] at ht
  linarith [ht.1]

private theorem auxCpowContOn (m : ℕ) (hm : 1 ≤ m) (s : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (-s))) (Set.uIcc (1 : ℝ) (m : ℝ)) := by
  have hbase : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.uIcc (1 : ℝ) (m : ℝ)) :=
    Complex.continuous_ofReal.continuousOn
  apply ContinuousOn.cpow_const hbase
  intro t ht
  have hpos : 0 < t := auxUiccPos m hm t ht
  exact Complex.ofReal_mem_slitPlane.mpr hpos

private theorem auxLogPowContOn (m j : ℕ) (hm : 1 ≤ m) :
    ContinuousOn (fun t : ℝ => ((-(Real.log t : ℂ)) ^ j)) (Set.uIcc (1 : ℝ) (m : ℝ)) := by
  have hsub : Set.uIcc (1 : ℝ) (m : ℝ) ⊆ {0}ᶜ := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (auxUiccPos m hm t ht)
  have hlog : ContinuousOn Real.log (Set.uIcc (1 : ℝ) (m : ℝ)) :=
    Real.continuousOn_log.mono hsub
  have hcast : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.uIcc (1 : ℝ) (m : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn hlog
  have hneg : ContinuousOn (fun t : ℝ => (-(Real.log t : ℂ))) (Set.uIcc (1 : ℝ) (m : ℝ)) :=
    hcast.neg
  exact hneg.pow j

private theorem auxIntegrandContOn (m j : ℕ) (hm : 1 ≤ m) (s : ℂ) :
    ContinuousOn (fun t : ℝ => ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-s))))
      (Set.uIcc (1 : ℝ) (m : ℝ)) :=
  (auxLogPowContOn m j hm).mul (auxCpowContOn m hm s)

private theorem auxDomBound (m j : ℕ) (hm : 1 ≤ m) (s x : ℂ)
    (hx : x ∈ Metric.ball s 1) (t : ℝ) (ht : t ∈ Set.uIoc (1 : ℝ) (m : ℝ)) :
    ‖(-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-x))‖ ≤
      (Real.log (m : ℝ)) ^ (j + 1) * max 1 (((m : ℝ)) ^ ((1 : ℝ) - s.re)) := by
  have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Set.uIoc_of_le h1m, Set.mem_Ioc] at ht
  obtain ⟨h1t, htm⟩ := ht
  have ht0 : 0 < t := lt_trans (by norm_num) h1t
  have ht1 : 1 ≤ t := le_of_lt h1t
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlog_le : Real.log t ≤ Real.log (m : ℝ) :=
    Real.log_le_log ht0 htm
  have hpow_le : (Real.log t) ^ (j + 1) ≤ (Real.log (m : ℝ)) ^ (j + 1) :=
    pow_le_pow_left₀ hlog_nonneg hlog_le _
  have hnorm_log : ‖(-(Real.log t : ℂ)) ^ (j + 1)‖ = (Real.log t) ^ (j + 1) := by
    rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
  have hnorm_cpow : ‖((t : ℂ) ^ (-x))‖ = t ^ ((-x).re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos ht0 (-x)
  have hxre : (-x).re = -x.re := by simp
  rw [hxre] at hnorm_cpow
  have hball : dist x s < 1 := Metric.mem_ball.mp hx
  have hre_bound : |x.re - s.re| ≤ dist x s := by
    have h := Complex.abs_re_le_norm (x - s)
    rw [Complex.sub_re, ← dist_eq_norm] at h
    exact h
  have habs : |x.re - s.re| < 1 := lt_of_le_of_lt hre_bound hball
  have hexp_le : -x.re ≤ 1 - s.re := by
    have h := abs_lt.mp habs
    linarith
  have hcpow_le : t ^ (-x.re) ≤ max 1 (((m : ℝ)) ^ ((1 : ℝ) - s.re)) := by
    by_cases he : -x.re ≤ 0
    · have h1 : t ^ (-x.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 he
      exact le_trans h1 (le_max_left _ _)
    · have hepos : 0 < -x.re := lt_of_not_ge he
      have h2 : t ^ (-x.re) ≤ (m : ℝ) ^ (-x.re) :=
        Real.rpow_le_rpow (le_trans (by norm_num) ht1) htm (le_of_lt hepos)
      have h3 : (m : ℝ) ^ (-x.re) ≤ (m : ℝ) ^ ((1 : ℝ) - s.re) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hexp_le
      exact le_trans (le_trans h2 h3) (le_max_right _ _)
  have hnonneg1 : 0 ≤ (Real.log t) ^ (j + 1) := pow_nonneg hlog_nonneg _
  have hnonneg2 : 0 ≤ t ^ (-x.re) := Real.rpow_nonneg (le_of_lt ht0) _
  have hnonneg3 : 0 ≤ (Real.log (m : ℝ)) ^ (j + 1) := by
    apply pow_nonneg
    exact Real.log_nonneg (by exact_mod_cast hm)
  calc ‖(-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-x))‖
      = ‖(-(Real.log t : ℂ)) ^ (j + 1)‖ * ‖((t : ℂ) ^ (-x))‖ := norm_mul _ _
    _ = (Real.log t) ^ (j + 1) * (t ^ (-x.re)) := by rw [hnorm_log, hnorm_cpow]
    _ ≤ (Real.log (m : ℝ)) ^ (j + 1) * max 1 (((m : ℝ)) ^ ((1 : ℝ) - s.re)) :=
        mul_le_mul hpow_le hcpow_le hnonneg2 hnonneg3

private theorem auxJHasDerivAt (m j : ℕ) (hm : 1 ≤ m) (s : ℂ) :
    HasDerivAt (JFun j m) (JFun (j + 1) m s) s := by
  have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set C : ℝ := (Real.log (m : ℝ)) ^ (j + 1) * max 1 (((m : ℝ)) ^ ((1 : ℝ) - s.re)) with hC
  have hs : Metric.ball s 1 ∈ 𝓝 s := Metric.ball_mem_nhds s (by norm_num)
  have hF_meas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (fun t : ℝ => ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-x))))
        (MeasureTheory.volume.restrict (Set.uIoc (1 : ℝ) (m : ℝ))) := by
    filter_upwards with x
    have hcont := auxIntegrandContOn m j hm x
    have hsub : Set.uIoc (1 : ℝ) (m : ℝ) ⊆ Set.uIcc (1 : ℝ) (m : ℝ) := Set.uIoc_subset_uIcc
    exact (hcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable
      (fun t : ℝ => ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-s))))
      MeasureTheory.volume (1 : ℝ) (m : ℝ) :=
    (auxIntegrandContOn m j hm s).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => ((-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-s))))
      (MeasureTheory.volume.restrict (Set.uIoc (1 : ℝ) (m : ℝ))) := by
    have hcont := auxIntegrandContOn m (j + 1) hm s
    have hsub : Set.uIoc (1 : ℝ) (m : ℝ) ⊆ Set.uIcc (1 : ℝ) (m : ℝ) := Set.uIoc_subset_uIcc
    exact (hcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (1 : ℝ) (m : ℝ) →
        ∀ x ∈ Metric.ball s 1,
          ‖(-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-x))‖ ≤ (fun _ : ℝ => C) t := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    exact auxDomBound m j hm s x hx t ht
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume
      (1 : ℝ) (m : ℝ) := intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (1 : ℝ) (m : ℝ) →
        ∀ x ∈ Metric.ball s 1,
          HasDerivAt (fun u : ℂ => ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-u))))
            ((-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-x))) x := by
    refine Filter.Eventually.of_forall (fun t ht x _ => ?_)
    have hpos : 0 < t := by
      rw [Set.uIoc_of_le h1m, Set.mem_Ioc] at ht
      exact lt_trans (by norm_num) ht.1
    exact auxIntegrandHasDerivAt t hpos j x
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u : ℂ => fun t : ℝ => ((-(Real.log t : ℂ)) ^ j * ((t : ℂ) ^ (-u))))
    (F' := fun u : ℂ => fun t : ℝ => ((-(Real.log t : ℂ)) ^ (j + 1) * ((t : ℂ) ^ (-u))))
    (x₀ := s) (s := Metric.ball s 1) (a := (1 : ℝ)) (b := (m : ℝ))
    (bound := fun _ : ℝ => C) (μ := MeasureTheory.volume)
    hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  exact hmain.2

private theorem auxJZeroEqI (m : ℕ) : JFun 0 m = IFun m := by
  funext s
  simp only [JFun, IFun, pow_zero, one_mul]

private theorem auxIDifferentiable (m : ℕ) (hm : 1 ≤ m) : Differentiable ℂ (IFun m) := by
  have heq : IFun m = JFun 0 m := (auxJZeroEqI m).symm
  rw [heq]
  exact fun s => (auxJHasDerivAt m 0 hm s).differentiableAt

private theorem auxIterDerivI (m k : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv k (IFun m) = JFun k m := by
  induction k with
  | zero =>
      simp only [iteratedDeriv_zero]
      exact (auxJZeroEqI m).symm
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (auxJHasDerivAt m k hm s).deriv

private theorem auxRealHasDerivAt (k : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log y ^ (k + 1) / ((k : ℝ) + 1))
      (Real.log x ^ k / x) x := by
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
  have hfun : (fun y : ℝ => Real.log y ^ (k + 1) / ((k : ℝ) + 1)) =
      (fun y => (Real.log ^ (k + 1)) y / ((k : ℝ) + 1)) := by
    ext y
    simp [Pi.pow_apply]
  have hval : Real.log x ^ k / x =
      ((((k : ℝ) + 1) * Real.log x ^ k * x⁻¹) / ((k : ℝ) + 1)) := by
    field_simp
  rw [hfun, hval]
  exact hdiv

private theorem auxRealFunContOn (k : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    ContinuousOn (fun x : ℝ => Real.log x ^ k / x) (Set.uIcc (1 : ℝ) (m : ℝ)) := by
  have hpos : ∀ x ∈ Set.uIcc (1 : ℝ) (m : ℝ), x ≠ 0 := by
    intro x hx
    exact ne_of_gt (auxUiccPos m hm x hx)
  refine ContinuousOn.div ?_ continuousOn_id (fun x hx => hpos x hx)
  exact (Real.continuousOn_log.mono (fun x hx => by simpa using hpos x hx)).pow k

private theorem auxRealInt (k m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (1 : ℝ)..(m : ℝ), (Real.log x ^ k / x)) =
      Real.log (m : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) (m : ℝ),
      HasDerivAt (fun y : ℝ => Real.log y ^ (k + 1) / ((k : ℝ) + 1))
        (Real.log x ^ k / x) x := by
    intro x hx
    exact auxRealHasDerivAt k x (ne_of_gt (auxUiccPos m hm x hx))
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x ^ k / x)
      MeasureTheory.volume (1 : ℝ) (m : ℝ) :=
    (auxRealFunContOn k m hm).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h1 : Real.log (1 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) = 0 := by
    simp
  rw [hftc]
  simp only [h1, sub_zero]

private theorem auxJAtOne (k m : ℕ) (hm : 1 ≤ m) :
    JFun k m 1 = (-1 : ℂ) ^ k * (((Real.log (m : ℝ) ^ (k + 1) / ((k : ℝ) + 1) : ℝ) : ℂ)) := by
  have hpoint : ∀ t : ℝ,
      ((-(Real.log t : ℂ)) ^ k * ((t : ℂ) ^ (-(1 : ℂ)))) =
        (-1 : ℂ) ^ k * (((Real.log t ^ k / t : ℝ) : ℂ)) := by
    intro t
    have hcpow : ((t : ℂ) ^ (-(1 : ℂ))) = ((t : ℂ))⁻¹ := by
      have harg : (-(1 : ℂ)) = (-1 : ℂ) := by ring
      rw [harg]
      exact Complex.cpow_neg_one _
    have hinv : ((t : ℂ))⁻¹ = (((t⁻¹ : ℝ)) : ℂ) := (RCLike.ofReal_inv t).symm
    have hneg : ((-(Real.log t : ℂ)) ^ k) = (-1 : ℂ) ^ k * ((Real.log t : ℂ) ^ k) :=
      neg_pow _ _
    have hpow : ((Real.log t : ℂ) ^ k) = (((Real.log t ^ k : ℝ)) : ℂ) :=
      (RCLike.ofReal_pow _ _).symm
    rw [hcpow, hinv, hneg, hpow]
    have hmul : (((Real.log t ^ k : ℝ)) : ℂ) * (((t⁻¹ : ℝ)) : ℂ) =
        (((Real.log t ^ k * t⁻¹ : ℝ)) : ℂ) := (RCLike.ofReal_mul _ _).symm
    rw [mul_assoc, hmul, div_eq_mul_inv]
  have hJ : JFun k m 1 =
      ∫ t in (1 : ℝ)..(m : ℝ), ((-1 : ℂ) ^ k * (((Real.log t ^ k / t : ℝ) : ℂ))) := by
    simp only [JFun]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpoint t
  rw [hJ, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    auxRealInt k m hm]

private theorem auxSDifferentiable (m : ℕ) : Differentiable ℂ (SFun m) := by
  have hF : ∀ n ∈ Finset.Icc 1 m, Differentiable ℂ (fun s : ℂ => ((n : ℂ) ^ (-s))) := by
    intro n hn
    apply auxNatCpowDifferentiable
    have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  exact Differentiable.fun_sum hF

private theorem auxEDifferentiable (m : ℕ) (hm : 1 ≤ m) : Differentiable ℂ (EFun m) := by
  have hS := auxSDifferentiable m
  have hI := auxIDifferentiable m hm
  exact hS.sub hI

private theorem auxIterDerivSub (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (k : ℕ) :
    iteratedDeriv k (fun s => f s - g s) =
      fun s => iteratedDeriv k f s - iteratedDeriv k g s := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      have hfCD : ContDiff ℂ ⊤ f := hf.contDiff
      have hgCD : ContDiff ℂ ⊤ g := hg.contDiff
      have hfk : Differentiable ℂ (iteratedDeriv k f) :=
        hfCD.differentiable_iteratedDeriv k (by simp)
      have hgk : Differentiable ℂ (iteratedDeriv k g) :=
        hgCD.differentiable_iteratedDeriv k (by simp)
      funext x
      rw [iteratedDeriv_succ, ih]
      have hsub : deriv (fun s => iteratedDeriv k f s - iteratedDeriv k g s) x =
          deriv (iteratedDeriv k f) x - deriv (iteratedDeriv k g) x :=
        deriv_sub (hfk.differentiableAt) (hgk.differentiableAt)
      rw [hsub]
      simp only [iteratedDeriv_succ]

private theorem auxSumComplexEqReal (k m : ℕ) :
    (∑ n ∈ Finset.Icc 1 m, ((((Real.log (n : ℝ))) : ℂ) ^ k / (n : ℂ))) =
      (((∑ j ∈ Finset.Icc 1 m, Real.log (j : ℝ) ^ k / (j : ℝ) : ℝ)) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hn : (n : ℂ) = (((n : ℝ)) : ℂ) := (Complex.ofReal_natCast n).symm
  have hpow : ((((Real.log (n : ℝ))) : ℂ) ^ k) = (((Real.log (n : ℝ) ^ k : ℝ)) : ℂ) :=
    (Complex.ofReal_pow _ _).symm
  rw [hn, hpow, ← Complex.ofReal_div]

private theorem auxIterDerivE (k m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv k (EFun m) 1 = (-1 : ℂ) ^ k * (((chapter7StieltjesApprox k m : ℝ)) : ℂ) := by
  have hS := auxSDifferentiable m
  have hI := auxIDifferentiable m hm
  have hsub := auxIterDerivSub (SFun m) (IFun m) hS hI k
  have hEfun : EFun m = fun s => SFun m s - IFun m s := rfl
  have hE : iteratedDeriv k (EFun m) 1 =
      iteratedDeriv k (SFun m) 1 - iteratedDeriv k (IFun m) 1 := by
    rw [hEfun, hsub]
  have hS1 : iteratedDeriv k (SFun m) 1 =
      (-1 : ℂ) ^ k * ∑ n ∈ Finset.Icc 1 m, ((((Real.log (n : ℝ))) : ℂ) ^ k / (n : ℂ)) :=
    auxFinsetSumDeriv m k
  have hI1 : iteratedDeriv k (IFun m) 1 = JFun k m 1 := by
    have h := auxIterDerivI m k hm
    exact congrFun h 1
  rw [hE, hS1, hI1, auxJAtOne k m hm, auxSumComplexEqReal k m]
  have happrox : (chapter7StieltjesApprox k m : ℝ) =
      (∑ j ∈ Finset.Icc 1 m, Real.log (j : ℝ) ^ k / (j : ℝ)) -
        Real.log (m : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
    simp only [chapter7StieltjesApprox]
  rw [happrox, Complex.ofReal_sub]
  ring

private theorem auxCpowContOnIcc (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (s : ℂ) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (-s))) (Set.uIcc a b) := by
  have hbase : ContinuousOn (fun t : ℝ => (t : ℂ)) (Set.uIcc a b) :=
    Complex.continuous_ofReal.continuousOn
  apply ContinuousOn.cpow_const hbase
  intro t ht
  have hpos : 0 < t := by
    have hmem : t ∈ Set.Icc a b := by
      have hu : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
      rw [hu] at ht
      exact ht
    have hle : a ≤ t := hmem.1
    linarith
  exact Complex.ofReal_mem_slitPlane.mpr hpos

private theorem auxIncrementEq (m : ℕ) (hm : 1 ≤ m) (s : ℂ) :
    EFun (m + 1) s - EFun m s =
      ∫ t in (m : ℝ)..((m + 1 : ℕ) : ℝ), ((((m + 1 : ℕ) : ℂ) ^ (-s)) - ((t : ℂ) ^ (-s))) := by
  have hsum : SFun (m + 1) s - SFun m s = (((m + 1 : ℕ) : ℂ) ^ (-s)) := by
    simp only [SFun]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    simp [add_sub_cancel_left]
  have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm1 : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have h : (m : ℝ) + 1 = (((m + 1 : ℕ)) : ℝ) := by push_cast; ring
    linarith
  have h1m1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := le_trans h1m hm1
  have hcont1 : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (-s)))
      (Set.uIcc (1 : ℝ) (m : ℝ)) :=
    auxCpowContOnIcc 1 (m : ℝ) (by norm_num) h1m s
  have hcont2 : ContinuousOn (fun t : ℝ => ((t : ℂ) ^ (-s)))
      (Set.uIcc (m : ℝ) (((m + 1 : ℕ)) : ℝ)) := by
    have hpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
    exact auxCpowContOnIcc (m : ℝ) (((m + 1 : ℕ)) : ℝ) hpos hm1 s
  have hint1 : IntervalIntegrable (fun t : ℝ => ((t : ℂ) ^ (-s)))
      MeasureTheory.volume (1 : ℝ) (m : ℝ) := hcont1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => ((t : ℂ) ^ (-s)))
      MeasureTheory.volume (m : ℝ) (((m + 1 : ℕ)) : ℝ) := hcont2.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hI : IFun (m + 1) s - IFun m s =
      ∫ t in (m : ℝ)..(((m + 1 : ℕ)) : ℝ), ((t : ℂ) ^ (-s)) := by
    simp only [IFun]
    have heq : (∫ t in (1 : ℝ)..(m : ℝ), ((t : ℂ) ^ (-s))) +
        (∫ t in (m : ℝ)..(((m + 1 : ℕ)) : ℝ), ((t : ℂ) ^ (-s))) =
        ∫ t in (1 : ℝ)..(((m + 1 : ℕ)) : ℝ), ((t : ℂ) ^ (-s)) := hadd
    rw [← heq, add_sub_cancel_left]
  have hconst : (∫ _ in (m : ℝ)..(((m + 1 : ℕ)) : ℝ), ((((m + 1 : ℕ) : ℂ) ^ (-s)))) =
      ((((m + 1 : ℕ) : ℂ) ^ (-s))) := by
    rw [intervalIntegral.integral_const]
    have hsub : ((((m + 1 : ℕ)) : ℝ) - (m : ℝ)) = 1 := by push_cast; ring
    rw [hsub, one_smul]
  have hconstInt : IntervalIntegrable (fun _ : ℝ => ((((m + 1 : ℕ) : ℂ) ^ (-s))))
      MeasureTheory.volume (m : ℝ) (((m + 1 : ℕ)) : ℝ) := intervalIntegrable_const
  have hsub := intervalIntegral.integral_sub hconstInt hint2
  have hIntEq : (∫ t in (m : ℝ)..(((m + 1 : ℕ)) : ℝ),
        ((((m + 1 : ℕ) : ℂ) ^ (-s)) - ((t : ℂ) ^ (-s)))) =
      ((((m + 1 : ℕ) : ℂ) ^ (-s))) -
        (∫ t in (m : ℝ)..(((m + 1 : ℕ)) : ℝ), ((t : ℂ) ^ (-s))) := by
    rw [hsub, hconst]
  rw [hIntEq]
  simp only [EFun]
  linear_combination hsum - hI

private theorem auxRealDerivBound (m : ℕ) (hm : 1 ≤ m) (s : ℂ) (hs : 0 < s.re)
    (t : ℝ) (ht : t ∈ Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ)) :
    HasDerivWithinAt (fun y : ℝ => ((y : ℂ) ^ (-s))) ((-s) * ((t : ℂ) ^ (-s - 1)))
      (Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ)) t ∧
    ‖(-s) * ((t : ℂ) ^ (-s - 1))‖ ≤ ‖s‖ * ((m : ℝ) ^ (-s.re - 1)) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have htge : (m : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
  have ht0 : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hmR) htge
  have htne : t ≠ 0 := ne_of_gt ht0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hrs : (-s) ≠ 0 := neg_ne_zero.mpr hs0
  have hderiv : HasDerivAt (fun y : ℝ => ((y : ℂ) ^ (-s))) ((-s) * ((t : ℂ) ^ (-s - 1))) t :=
    hasDerivAt_ofReal_cpow_const htne hrs
  have hwithin : HasDerivWithinAt (fun y : ℝ => ((y : ℂ) ^ (-s))) ((-s) * ((t : ℂ) ^ (-s - 1)))
      (Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ)) t := hderiv.hasDerivWithinAt
  have hnorm : ‖(-s) * ((t : ℂ) ^ (-s - 1))‖ = ‖s‖ * (t ^ (-s.re - 1)) := by
    have h1 : ‖(-s)‖ = ‖s‖ := norm_neg s
    have h2 : ‖((t : ℂ) ^ (-s - 1))‖ = t ^ ((-s - 1).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos ht0 (-s - 1)
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre] at h2
    rw [norm_mul, h1, h2]
  have hexp_nonpos : -s.re - 1 ≤ 0 := by linarith
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
  have hrpow_le : t ^ (-s.re - 1) ≤ (m : ℝ) ^ (-s.re - 1) :=
    Real.rpow_le_rpow_of_nonpos hmpos htge hexp_nonpos
  have hle : ‖s‖ * (t ^ (-s.re - 1)) ≤ ‖s‖ * ((m : ℝ) ^ (-s.re - 1)) :=
    mul_le_mul_of_nonneg_left hrpow_le (norm_nonneg s)
  exact ⟨hwithin, by rw [hnorm]; exact hle⟩

private theorem auxIncrementBound (m : ℕ) (hm : 1 ≤ m) (s : ℂ) (hs : 0 < s.re) :
    ‖EFun (m + 1) s - EFun m s‖ ≤ ‖s‖ * ((m : ℝ) ^ (-s.re - 1)) := by
  have hEq := auxIncrementEq m hm s
  rw [hEq]
  set C : ℝ := ‖s‖ * ((m : ℝ) ^ (-s.re - 1)) with hC
  have hCnonneg : 0 ≤ C := by
    apply mul_nonneg (norm_nonneg s)
    exact Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hm1 : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have h : (m : ℝ) + 1 = (((m + 1 : ℕ)) : ℝ) := by push_cast; ring
    linarith
  have hconv : Convex ℝ (Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ)) := convex_Icc _ _
  have hderiv : ∀ x ∈ Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ),
      HasDerivWithinAt (fun y : ℝ => ((y : ℂ) ^ (-s))) ((-s) * ((x : ℂ) ^ (-s - 1)))
        (Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ)) x := by
    intro x hx
    exact (auxRealDerivBound m hm s hs x hx).1
  have hbound : ∀ x ∈ Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ),
      ‖(-s) * ((x : ℂ) ^ (-s - 1))‖ ≤ C := by
    intro x hx
    exact (auxRealDerivBound m hm s hs x hx).2
  have hM1 : ((m + 1 : ℕ) : ℝ) ∈ Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ) :=
    Set.mem_Icc.mpr ⟨hm1, le_rfl⟩
  have hpoint : ∀ t ∈ Set.uIoc (m : ℝ) (((m + 1 : ℕ)) : ℝ),
      ‖((((m + 1 : ℕ) : ℂ) ^ (-s)) - ((t : ℂ) ^ (-s)))‖ ≤ C := by
    intro t ht
    have htIcc : t ∈ Set.Icc (m : ℝ) (((m + 1 : ℕ)) : ℝ) := by
      have hsub : Set.uIoc (m : ℝ) (((m + 1 : ℕ)) : ℝ) ⊆
          Set.uIcc (m : ℝ) (((m + 1 : ℕ)) : ℝ) := Set.uIoc_subset_uIcc
      have hmem := hsub ht
      rw [Set.uIcc_of_le hm1] at hmem
      exact hmem
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hconv
      htIcc hM1
    have hconst_eq : ((((m + 1 : ℕ) : ℂ) ^ (-s))) =
        ((fun y : ℝ => ((y : ℂ) ^ (-s))) (((m + 1 : ℕ)) : ℝ)) := rfl
    have hnorm_dist : ‖((((m + 1 : ℕ)) : ℝ) - t)‖ ≤ 1 := by
      have hmem : t ∈ Set.Ioc (m : ℝ) (((m + 1 : ℕ)) : ℝ) := by
        have hu : Set.uIoc (m : ℝ) (((m + 1 : ℕ)) : ℝ) =
            Set.Ioc (m : ℝ) (((m + 1 : ℕ)) : ℝ) := Set.uIoc_of_le hm1
        rw [hu] at ht
        exact ht
      obtain ⟨hlt, hle⟩ := Set.mem_Ioc.mp hmem
      have hsub_nonneg : 0 ≤ ((((m + 1 : ℕ)) : ℝ) - t) := by linarith
      have hsub_le : ((((m + 1 : ℕ)) : ℝ) - t) ≤ 1 := by
        have h1 : (m : ℝ) + 1 = (((m + 1 : ℕ)) : ℝ) := by push_cast; ring
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hsub_nonneg]
      exact hsub_le
    have hle : C * ‖((((m + 1 : ℕ)) : ℝ) - t)‖ ≤ C * 1 :=
      mul_le_mul_of_nonneg_left hnorm_dist hCnonneg
    rw [mul_one] at hle
    have hmvt' : ‖((fun y : ℝ => ((y : ℂ) ^ (-s))) (((m + 1 : ℕ)) : ℝ)) -
        ((fun y : ℝ => ((y : ℂ) ^ (-s))) t)‖ ≤ C := le_trans hmvt hle
    simpa [hconst_eq] using hmvt'
  have hIntBound : ‖∫ t in (m : ℝ)..(((m + 1 : ℕ)) : ℝ),
      ((((m + 1 : ℕ) : ℂ) ^ (-s)) - ((t : ℂ) ^ (-s)))‖ ≤ C * |((((m + 1 : ℕ)) : ℝ) - (m : ℝ))| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have habs : |((((m + 1 : ℕ)) : ℝ) - (m : ℝ))| = 1 := by
    have hsub : ((((m + 1 : ℕ)) : ℝ) - (m : ℝ)) = 1 := by push_cast; ring
    rw [hsub, abs_one]
  rw [habs, mul_one] at hIntBound
  exact hIntBound

private theorem auxUOpen : IsOpen USet := by
  have h : USet = { s : ℂ | (0 : ℝ) < s.re } := rfl
  rw [h]
  exact isOpen_lt continuous_const Complex.continuous_re

private theorem auxUConvex : Convex ℝ USet := convex_halfSpace_re_gt 0

private theorem auxUPreconnected : IsPreconnected USet := auxUConvex.isPreconnected

private theorem auxMemUOne : (1 : ℂ) ∈ USet := by
  simp [USet]

private theorem auxMemUTwo : (2 : ℂ) ∈ USet := by
  simp [USet]

private theorem auxUniformOnCompact (K : Set ℂ) (hKU : K ⊆ USet) (hK : IsCompact K) :
    TendstoUniformlyOn HFun GFun atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  · obtain ⟨x0, hx0K, hx0min⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨y0, _, hy0max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    set δ : ℝ := x0.re with hδ
    set R : ℝ := ‖y0‖ with hR
    have hδpos : 0 < δ := hKU hx0K
    have hRnonneg : 0 ≤ R := norm_nonneg y0
    have hδle : ∀ s ∈ K, δ ≤ s.re := fun s hs => hx0min hs
    have hRle : ∀ s ∈ K, ‖s‖ ≤ R := fun s hs => hy0max hs
    have h1δ : (1 : ℝ) < 1 + δ := by linarith
    have hsum_base : Summable (fun n : ℕ => (((n : ℝ) ^ (1 + δ))⁻¹ : ℝ)) :=
      Real.summable_nat_rpow_inv.mpr h1δ
    have hsum_shift : Summable (fun n : ℕ => (((((n + 1 : ℕ)) : ℝ) ^ (1 + δ))⁻¹ : ℝ)) := by
      have h := (summable_nat_add_iff
        (f := fun n : ℕ => (((n : ℝ) ^ (1 + δ))⁻¹ : ℝ)) 1).mpr hsum_base
      simpa using h
    have hsum_u : Summable (fun n : ℕ => R * (((((n + 1 : ℕ)) : ℝ) ^ (1 + δ))⁻¹ : ℝ)) :=
      Summable.mul_left R hsum_shift
    have hbound : ∀ n : ℕ, ∀ s ∈ K,
        ‖EFun (n + 2) s - EFun (n + 1) s‖ ≤ R * (((((n + 1 : ℕ)) : ℝ) ^ (1 + δ))⁻¹) := by
      intro n s hs
      have hm : 1 ≤ n + 1 := Nat.le_add_left 1 n
      have hsU : s ∈ USet := hKU hs
      have hsre : 0 < s.re := hsU
      have hinc := auxIncrementBound (n + 1) hm s hsre
      have hδs : δ ≤ s.re := hδle s hs
      have hRs : ‖s‖ ≤ R := hRle s hs
      have hexp_le : -s.re - 1 ≤ -1 - δ := by linarith
      have hmpos : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hm
      have hrpow_le : ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) ≤ ((n + 1 : ℕ) : ℝ) ^ (-1 - δ) :=
        Real.rpow_le_rpow_of_exponent_le hmpos hexp_le
      have hnonneg1 : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
        Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hle1 : ‖s‖ * (((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) ≤ R * (((n + 1 : ℕ) : ℝ) ^ (-1 - δ)) :=
        mul_le_mul hRs hrpow_le hnonneg1 hRnonneg
      have hrpow_eq : (((n + 1 : ℕ) : ℝ) ^ (-1 - δ)) = (((((n + 1 : ℕ)) : ℝ) ^ (1 + δ))⁻¹) := by
        have h1 : (-1 - δ) = -(1 + δ) := by ring
        rw [h1, Real.rpow_neg (Nat.cast_nonneg _)]
      rw [hrpow_eq] at hle1
      have hmcast : ((n + 1 : ℕ) + 1) = n + 2 := by omega
      have hinc' : ‖EFun (n + 2) s - EFun (n + 1) s‖ ≤ ‖s‖ * (((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
        have h := hinc
        rw [hmcast] at h
        exact h
      exact le_trans hinc' hle1
    have hM := tendstoUniformlyOn_tsum_nat hsum_u (s := K)
      (f := fun n : ℕ => fun s : ℂ => EFun (n + 2) s - EFun (n + 1) s)
      (u := fun n : ℕ => R * (((((n + 1 : ℕ)) : ℝ) ^ (1 + δ))⁻¹))
      (fun n s hs => hbound n s hs)
    have htele : ∀ N : ℕ, ∀ s : ℂ,
        (∑ n ∈ Finset.range N, (EFun (n + 2) s - EFun (n + 1) s)) =
          EFun (N + 1) s - EFun 1 s := by
      intro N s
      have h := Finset.sum_range_sub (fun i => EFun (i + 1) s) N
      simpa using h
    have hH : ∀ N : ℕ, ∀ s : ℂ, HFun N s =
        EFun 1 s + (∑ n ∈ Finset.range N, (EFun (n + 2) s - EFun (n + 1) s)) := by
      intro N s
      simp only [HFun]
      have h := htele N s
      rw [h]
      ring
    have hG : ∀ s : ℂ, GFun s =
        EFun 1 s + (∑' n : ℕ, (EFun (n + 2) s - EFun (n + 1) s)) := fun s => rfl
    rw [Metric.tendstoUniformlyOn_iff] at hM ⊢
    intro ε hε
    filter_upwards [hM ε hε] with N hN s hs
    have hdist : dist (GFun s) (HFun N s) =
        dist (∑' n : ℕ, (EFun (n + 2) s - EFun (n + 1) s))
          (∑ n ∈ Finset.range N, (EFun (n + 2) s - EFun (n + 1) s)) := by
      rw [hH N s, hG s, dist_eq_norm, dist_eq_norm]
      congr 1
      rw [add_sub_add_left_eq_sub]
    rw [hdist]
    exact hN s hs

private theorem auxHToGLocallyUniform :
    TendstoLocallyUniformlyOn HFun GFun atTop USet :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact auxUOpen).mpr auxUniformOnCompact

private theorem auxHDifferentiableOn :
    ∀ᶠ n in atTop, DifferentiableOn ℂ (HFun n) USet :=
  Filter.Eventually.of_forall
    (fun n => (auxEDifferentiable (n + 1) (Nat.le_add_left 1 n)).differentiableOn)

private theorem auxGDifferentiableOn : DifferentiableOn ℂ GFun USet :=
  auxHToGLocallyUniform.differentiableOn auxHDifferentiableOn auxUOpen

private theorem auxSumIccEqRange (f : ℕ → ℂ) (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 m, f n = ∑ n ∈ Finset.range m, f (n + 1) := by
  induction m with
  | zero =>
      rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (1 : ℕ) ≤ 0)]
      simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), Finset.sum_range_succ, ih]

private theorem auxSToZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun m : ℕ => SFun (m + 1) s) atTop (𝓝 (riemannZeta s)) := by
  have hzeta0 := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hcast : ∀ n : ℕ, ((((n + 1 : ℕ)) : ℂ)) = ((n : ℂ) + 1) := by
    intro n
    push_cast
    ring
  have hzeta : riemannZeta s = ∑' n : ℕ, (1 / (((n + 1 : ℕ)) : ℂ) ^ s) := by
    rw [hzeta0]
    apply tsum_congr
    intro n
    rw [hcast n]
  have hsumm_base : Summable (fun n : ℕ => (1 / ((n : ℂ) ^ s))) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hsumm : Summable (fun n : ℕ => (1 / ((((n + 1 : ℕ)) : ℂ) ^ s))) := by
    have h := (summable_nat_add_iff
      (f := fun n : ℕ => (1 / ((n : ℂ) ^ s))) 1).mpr hsumm_base
    simpa using h
  have hHas : HasSum (fun n : ℕ => (1 / ((((n + 1 : ℕ)) : ℂ) ^ s))) (riemannZeta s) := by
    have h := hsumm.hasSum
    rw [← hzeta] at h
    exact h
  have hrange : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      (1 / ((((n + 1 : ℕ)) : ℂ) ^ s))) atTop (𝓝 (riemannZeta s)) :=
    hHas.tendsto_sum_nat
  have hshift : Tendsto (fun m : ℕ => ∑ n ∈ Finset.range (m + 1),
      (1 / ((((n + 1 : ℕ)) : ℂ) ^ s))) atTop (𝓝 (riemannZeta s)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hrange
  have heq : ∀ m : ℕ, SFun (m + 1) s =
      ∑ n ∈ Finset.range (m + 1), (1 / ((((n + 1 : ℕ)) : ℂ) ^ s)) := by
    intro m
    simp only [SFun]
    rw [auxSumIccEqRange (fun n : ℕ => ((n : ℂ) ^ (-s))) (m + 1)]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.cpow_neg, one_div]
  simpa [heq] using hshift

private theorem auxIToInv (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun m : ℕ => IFun (m + 1) s) atTop (𝓝 (1 / (s - 1))) := by
  have hsne1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have h1s_ne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne1)
  have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hsne1
  have hpow0 : Tendsto (fun m : ℕ => ((((m + 1 : ℕ)) : ℂ) ^ (1 - s))) atTop (𝓝 0) := by
    have hpos : 0 < s.re - 1 := by linarith
    have hbase : Tendsto (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hrpow : Tendsto (fun m : ℕ => ((((m + 1 : ℕ)) : ℝ) ^ (s.re - 1))) atTop atTop :=
      (tendsto_rpow_atTop hpos).comp hbase
    have hinv : Tendsto (fun m : ℕ => (((((m + 1 : ℕ)) : ℝ) ^ (s.re - 1))⁻¹ : ℝ))
        atTop (𝓝 0) := hrpow.inv_tendsto_atTop
    have heq : ∀ m : ℕ, ‖((((m + 1 : ℕ)) : ℂ) ^ (1 - s))‖ =
        (((((m + 1 : ℕ)) : ℝ) ^ (s.re - 1))⁻¹ : ℝ) := by
      intro m
      have hnorm := Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m) (1 - s)
      have hre : (1 - s).re = 1 - s.re := by simp
      rw [hre] at hnorm
      have hrw : ((1 : ℝ) - s.re) = -(s.re - 1) := by ring
      rw [hrw, Real.rpow_neg (Nat.cast_nonneg _)] at hnorm
      exact hnorm
    have hnorm : Tendsto (fun m : ℕ => ‖((((m + 1 : ℕ)) : ℂ) ^ (1 - s))‖) atTop (𝓝 0) :=
      hinv.congr (fun m => (heq m).symm)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hIF : ∀ m : ℕ, IFun (m + 1) s =
      (((((m + 1 : ℕ)) : ℂ) ^ (1 - s)) - 1) / (1 - s) := by
    intro m
    simp only [IFun]
    have hcond : -1 < (-s).re ∨ (-s) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((((m + 1 : ℕ)) : ℝ)) := by
      right
      constructor
      · intro h
        apply hsne1
        have hneg : -(-s) = -(-1 : ℂ) := by rw [h]
        simpa using hneg
      · have hle : (1 : ℝ) ≤ ((((m + 1 : ℕ)) : ℝ)) := by
          have h : (1 : ℝ) ≤ ((m : ℝ) + 1) := by
            have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
            linarith
          have hcast : ((((m + 1 : ℕ)) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          exact h
        rw [Set.uIcc_of_le hle]
        intro hmem
        have h1 : (1 : ℝ) ≤ (0 : ℝ) := (Set.mem_Icc.mp hmem).1
        norm_num at h1
    have hcpow := integral_cpow (a := (1 : ℝ)) (b := ((((m + 1 : ℕ)) : ℝ))) (r := -s) hcond
    have hr1 : (-s) + 1 = 1 - s := by ring
    have hbcast : ((((m + 1 : ℕ)) : ℝ) : ℂ) = ((((m + 1 : ℕ)) : ℂ)) :=
      Complex.ofReal_natCast _
    rw [hr1] at hcpow
    have h1pow : ((1 : ℝ) : ℂ) ^ (1 - s) = 1 := Complex.one_cpow _
    have hcpow2 : (∫ x : ℝ in (1 : ℝ)..((((m + 1 : ℕ)) : ℝ)), (x : ℂ) ^ (-s)) =
        (((((m + 1 : ℕ)) : ℝ) : ℂ) ^ (1 - s) - ((1 : ℝ) : ℂ) ^ (1 - s)) / (1 - s) := hcpow
    rw [hbcast, h1pow] at hcpow2
    exact hcpow2
  have hlim : Tendsto (fun m : ℕ => (((((m + 1 : ℕ)) : ℂ) ^ (1 - s)) - 1) / (1 - s))
      atTop (𝓝 ((-1 : ℂ) / (1 - s))) := by
    have hsub : Tendsto (fun m : ℕ => ((((m + 1 : ℕ)) : ℂ) ^ (1 - s)) - 1)
        atTop (𝓝 ((0 : ℂ) - 1)) := hpow0.sub_const 1
    have hdiv := hsub.div_const (1 - s)
    simpa using hdiv
  have heq2 : ((-1 : ℂ) / (1 - s)) = 1 / (s - 1) := by
    field_simp
    ring
  rw [heq2] at hlim
  simpa [hIF] using hlim

private theorem auxHToZeta0OnGtOne (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun m : ℕ => HFun m s) atTop (𝓝 (riemannZeta₀ s)) := by
  have hsne1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hS := auxSToZeta s hs
  have hI := auxIToInv s hs
  have hsub := hS.sub hI
  have heq : riemannZeta s - 1 / (s - 1) = riemannZeta₀ s := by
    rw [riemannZeta_eq_inv_sub_add hsne1, one_div, add_sub_cancel_left]
  rw [heq] at hsub
  have hfun : (fun m : ℕ => SFun (m + 1) s - IFun (m + 1) s) = fun m : ℕ => HFun m s := by
    funext m
    rfl
  rw [hfun] at hsub
  exact hsub

private theorem auxGEqZeta0OnGtOne : Set.EqOn GFun riemannZeta₀ { s : ℂ | 1 < s.re } := by
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  have hsU : s ∈ USet := by
    simp only [USet, Set.mem_ofPred_eq]
    linarith
  have hG := auxHToGLocallyUniform.tendsto_at hsU
  have hZ := auxHToZeta0OnGtOne s hs
  exact tendsto_nhds_unique hG hZ

private theorem auxGEqZeta0OnU : Set.EqOn GFun riemannZeta₀ USet := by
  have hGana : AnalyticOnNhd ℂ GFun USet :=
    auxGDifferentiableOn.analyticOnNhd auxUOpen
  have hZana : AnalyticOnNhd ℂ riemannZeta₀ USet :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd auxUOpen
  have hVopen : IsOpen { s : ℂ | (1 : ℝ) < s.re } :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2memV : (2 : ℂ) ∈ { s : ℂ | (1 : ℝ) < s.re } := by simp
  have hVmem : { s : ℂ | (1 : ℝ) < s.re } ∈ 𝓝 (2 : ℂ) := hVopen.mem_nhds h2memV
  have hev : GFun =ᶠ[𝓝 (2 : ℂ)] riemannZeta₀ := by
    filter_upwards [hVmem] with s hs
    exact auxGEqZeta0OnGtOne hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hGana hZana
    auxUPreconnected auxMemUTwo hev

private theorem auxHToZeta0LocallyUniform :
    TendstoLocallyUniformlyOn HFun riemannZeta₀ atTop USet :=
  auxHToGLocallyUniform.congr_right auxGEqZeta0OnU

private theorem auxDerivIterConverge (j : ℕ) :
    TendstoLocallyUniformlyOn (fun m : ℕ => deriv^[j] (HFun m))
      (deriv^[j] riemannZeta₀) atTop USet := by
  induction j with
  | zero =>
      simpa [Function.iterate_zero] using auxHToZeta0LocallyUniform
  | succ j ih =>
      have hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (deriv^[j] (HFun n)) USet := by
        refine Filter.Eventually.of_forall (fun n => ?_)
        have hdiff : Differentiable ℂ (HFun n) :=
          auxEDifferentiable (n + 1) (Nat.le_add_left 1 n)
        have hCD : ContDiff ℂ ⊤ (HFun n) := hdiff.contDiff
        have hiter : Differentiable ℂ (iteratedDeriv j (HFun n)) :=
          hCD.differentiable_iteratedDeriv j (by simp)
        have heq : deriv^[j] (HFun n) = iteratedDeriv j (HFun n) :=
          (iteratedDeriv_eq_iterate).symm
        rw [heq]
        exact hiter.differentiableOn
      have hderiv := ih.deriv hF auxUOpen
      have heqF : (deriv ∘ (fun m : ℕ => deriv^[j] (HFun m))) =
          (fun m : ℕ => deriv^[j + 1] (HFun m)) := by
        funext m
        simp only [Function.comp_apply]
        rw [show j + 1 = j.succ from rfl, Function.iterate_succ']
        rfl
      have heqLim : deriv (deriv^[j] riemannZeta₀) = deriv^[j + 1] riemannZeta₀ := by
        rw [show j + 1 = j.succ from rfl, Function.iterate_succ']
        rfl
      rw [heqF, heqLim] at hderiv
      exact hderiv

private theorem auxCoeff (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) (k : ℕ) :
    iteratedDeriv k riemannZeta₀ 1 = (-1 : ℂ) ^ k * (c k : ℂ) := by
  have hconv := auxDerivIterConverge k
  have hAt := hconv.tendsto_at auxMemUOne
  have heqIter : ∀ f : ℂ → ℂ, ∀ x : ℂ, deriv^[k] f x = iteratedDeriv k f x := by
    intro f x
    exact congrFun (iteratedDeriv_eq_iterate).symm x
  have hleft : Tendsto (fun m : ℕ => (-1 : ℂ) ^ k * (((chapter7StieltjesApprox k (m + 1) : ℝ)) : ℂ))
      atTop (𝓝 (iteratedDeriv k riemannZeta₀ 1)) := by
    have h1 : Tendsto (fun m : ℕ => deriv^[k] (HFun m) 1) atTop (𝓝 (deriv^[k] riemannZeta₀ 1)) :=
      hAt
    have heq1 : ∀ m : ℕ, deriv^[k] (HFun m) 1 =
        (-1 : ℂ) ^ k * (((chapter7StieltjesApprox k (m + 1) : ℝ)) : ℂ) := by
      intro m
      rw [heqIter]
      have hH : HFun m = EFun (m + 1) := rfl
      rw [hH]
      exact auxIterDerivE k (m + 1) (Nat.le_add_left 1 m)
    have heq2 : deriv^[k] riemannZeta₀ 1 = iteratedDeriv k riemannZeta₀ 1 := heqIter _ _
    rw [heq2] at h1
    exact h1.congr (fun m => heq1 m)
  have hshift : Tendsto (fun m : ℕ => chapter7StieltjesApprox k (m + 1)) atTop (𝓝 (c k)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hc k)
  have hOfReal : Tendsto (fun m : ℕ => (((chapter7StieltjesApprox k (m + 1) : ℝ)) : ℂ))
      atTop (𝓝 ((c k : ℝ) : ℂ)) := Filter.Tendsto.ofReal hshift
  have hright : Tendsto
      (fun m : ℕ => (-1 : ℂ) ^ k * (((chapter7StieltjesApprox k (m + 1) : ℝ)) : ℂ))
      atTop (𝓝 ((-1 : ℂ) ^ k * (c k : ℂ))) :=
    Filter.Tendsto.const_mul ((-1 : ℂ) ^ k) hOfReal
  exact tendsto_nhds_unique hleft hright

private theorem auxStep0 (c : ℕ → ℝ)
    (hcoeff : ∀ k : ℕ, iteratedDeriv k riemannZeta₀ 1 = (-1 : ℂ) ^ k * (c k : ℂ))
    (s : ℂ) (hs : s ≠ 1) :
    HasSum (chapter7StieltjesLaurentTerm c s) (riemannZeta s - 1 / (s - 1)) := by
  have hz : riemannZeta s - 1 / (s - 1) = riemannZeta₀ s := by
    rw [riemannZeta_eq_inv_sub_add hs, one_div, add_sub_cancel_left]
  rw [hz]
  have hT := Complex.hasSum_taylorSeries_of_entire differentiable_riemannZeta₀ 1 s
  apply hT.congr_fun
  intro k
  rw [hcoeff k]
  simp [chapter7StieltjesLaurentTerm, smul_eq_mul]
  ring

/-- **Laurent expansion of $\zeta$ at $s = 1$.** Let $(c_k)_{k \ge 0}$ be real numbers such that,
for every $k \ge 0$, $\sum_{j=1}^{m} (\log j)^k / j - (\log m)^{k+1} / (k+1)$ tends to $c_k$ as
$m \to \infty$. Then for every complex $s \ne 1$ the series
$$\sum_{k=0}^{\infty} \frac{(-1)^k c_k}{k!} (s-1)^k$$
converges absolutely, and its sum is $\zeta(s) - \frac{1}{s-1}$.

Proves `Wanted` entry `ramanujan_part1_ch7_entry13_bernoullirecurrence`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 13.
-/
theorem ramanujan_part1_ch7_entry13_bernoullirecurrence
    (c : ℕ → ℝ)
    (hc : ∀ k : ℕ,
      Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
    ∀ s : ℂ, s ≠ 1 →
      HasSum (chapter7StieltjesLaurentTerm c s)
        (riemannZeta s - 1 / (s - 1)) := by
  intro s hs
  have hcoeff : ∀ k : ℕ, iteratedDeriv k riemannZeta₀ 1 = (-1 : ℂ) ^ k * (c k : ℂ) :=
    auxCoeff c hc
  exact auxStep0 c hcoeff s hs

end
end Entry13Bernoullirecurrence
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end

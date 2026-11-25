/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatIteratedDerivatives
import MathlibExt.Analysis.PDE.BurgersExponentialGrowth
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open MeasureTheory Real Set
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

example {g : ℝ → ℝ} (n : ℕ) (hg : ContDiff ℝ n g)
    (hb : ∀ k ≤ n, HasExpGrowth (iteratedDeriv k g)) (t x : ℝ) :
    iteratedDeriv n (heatSolution g t) x = heatSolution (iteratedDeriv n g) t x :=
  heatSolution_iteratedDeriv_of_exp_growth hg hb t x

example {f : ℝ → ℝ → ℝ} {ν T : ℝ} (n : ℕ) (hν : 0 ≤ ν)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ n (f s))
    (hc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (f p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hb : ∀ k ≤ n, MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s y => iteratedDeriv k (f s) y) T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    iteratedDeriv n (heatDuhamel ν f t) x =
      heatDuhamel ν (fun s y => iteratedDeriv n (f s) y) t x :=
  heatDuhamel_iteratedDeriv hν hf hc hb ht x

private theorem time_cusp_growth {g : ℝ → ℝ} (hg : HasExpGrowth g) (T : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip (fun s x => |s - 1| * g x) T := by
  obtain ⟨M, c, hM, hc, hb⟩ := hg
  refine ⟨(|T| + 1) * M, c, by positivity, hc, fun s hs x => ?_⟩
  have htime : |s - 1| ≤ |T| + 1 := calc
    |s - 1| ≤ |s| + 1 := by simpa using abs_sub s 1
    _ ≤ |T| + 1 := add_le_add (by rw [abs_of_nonneg hs.1]; exact hs.2.trans (le_abs_self _)) le_rfl
  rw [abs_mul, abs_abs, mul_assoc]
  exact mul_le_mul htime (hb x) (abs_nonneg _) (by positivity)

private theorem exp_jet (k : ℕ) (s x : ℝ) :
    iteratedDeriv k (fun y => |s - 1| * exp (-2 * y)) x = |s - 1| * ((-2)^k * exp (-2 * x)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]

private theorem exp_jet_cont (k : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (fun y => |p.1 - 1| * exp (-2 * y)) p.2)
      (Icc 0 T ×ˢ univ) := by
  simp_rw [exp_jet]
  fun_prop

private theorem exp_jet_growth (k : ℕ) (T : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => iteratedDeriv k (fun y => |s - 1| * exp (-2 * y)) x) T := by
  simp_rw [exp_jet]
  exact time_cusp_growth ((HasExpGrowth.exp_linear (-2)).const_mul ((-2)^k)) T

-- Arbitrary order and a negative exponent distinguish derivative signs and coefficients.
example (n : ℕ) (t x : ℝ) :
    iteratedDeriv n (heatSolution (fun y => exp (-2 * y)) t) x =
      (-2)^n * heatSolution (fun y => exp (-2 * y)) t x := by
  have hg (k : ℕ) (_ : k ≤ n) : HasExpGrowth (iteratedDeriv k (fun y => exp (-2 * y))) := by
    rw [iteratedDeriv_exp_const_mul]
    exact (HasExpGrowth.exp_linear (-2)).const_mul _
  simpa only [iteratedDeriv_exp_const_mul, heatSolution_const_mul] using
    heatSolution_iteratedDeriv_of_exp_growth (n := n) (by fun_prop) hg t x

-- No forcing time derivative is assumed, even at its time cusp.
example {ν T t : ℝ} (n : ℕ) (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    iteratedDeriv n (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) t) x =
      heatDuhamel ν (fun s y => |s - 1| * ((-2)^n * exp (-2 * y))) t x := by
  simpa only [exp_jet] using heatDuhamel_iteratedDeriv hν (n := n)
    (fun s _ => by fun_prop) (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T) ht x

example {ν T : ℝ} (n : ℕ) (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n
      (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) p.1) p.2) (Icc 0 T ×ˢ univ) :=
  heatDuhamel_iteratedDeriv_continuousOn hν hT (fun s _ => by fun_prop)
    (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T)

example {ν T : ℝ} (n : ℕ) (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun t x => iteratedDeriv n (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) t) x) T :=
  heatDuhamel_iteratedDeriv_hasExpGrowthOnStrip hν hT (fun s _ => by fun_prop)
    (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T)

example {ν T t : ℝ} (n : ℕ) (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    DifferentiableAt ℝ (iteratedDeriv n
      (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) t)) x :=
  (heatDuhamel_hasDerivAt_iteratedDeriv hν (fun s _ => by fun_prop)
    (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T) ht x).differentiableAt

example {ν T : ℝ} (n : ℕ) (hν : 0 < ν) (hT : 0 ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv (n + 1)
      (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) p.1) p.2) (Icc 0 T ×ˢ univ) :=
  heatDuhamel_iteratedDeriv_succ_continuousOn hν hT (fun s _ => by fun_prop)
    (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T)

example {ν T : ℝ} (n : ℕ) (hν : 0 < ν) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun t x => iteratedDeriv (n + 1) (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) t) x) T :=
  heatDuhamel_iteratedDeriv_succ_hasExpGrowthOnStrip hν (fun s _ => by fun_prop)
    (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T)

-- At t=1 the source has a time cusp. The mixed derivative uses spatial order n+2.
example {ν T : ℝ} (hν : 0 < ν) (hT : 1 < T) (x : ℝ) :
    HasDerivAt (fun t => iteratedDeriv 1
      (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) t) x)
      (ν * heatDuhamel ν (fun s y => |s - 1| * ((-2)^3 * exp (-2 * y))) 1 x) 1 := by
  simpa only [exp_jet, sub_self, abs_zero, zero_mul, iteratedDeriv_one, deriv_const, zero_add, Nat.reduceAdd] using
    heatDuhamel_iteratedDeriv_hasDerivAt_time (n := 1) hν (fun s _ => by fun_prop)
      (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T) ⟨by norm_num, hT⟩ x

private theorem power_growth (m : ℕ) : HasExpGrowth (fun x : ℝ => x ^ m) := by
  refine ⟨1, m, by norm_num, by positivity, fun x => ?_⟩
  rw [one_mul, abs_pow, exp_nat_mul]
  exact pow_le_pow_left₀ (abs_nonneg x)
    ((le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp |x|)) m

private theorem cubic_jet (k : ℕ) (s x : ℝ) :
    iteratedDeriv k (fun y => |s - 1| * y ^ 3) x =
      |s - 1| * ((3 : ℕ).descFactorial k * x ^ (3 - k)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]

private theorem cubic_jet_cont (k : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (fun y => |p.1 - 1| * y ^ 3) p.2)
      (Icc 0 T ×ˢ univ) := by
  simp_rw [cubic_jet]
  fun_prop

private theorem cubic_jet_growth (k : ℕ) (T : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => iteratedDeriv k (fun y => |s - 1| * y ^ 3) x) T := by
  simp_rw [cubic_jet]
  exact time_cusp_growth ((power_growth (3 - k)).const_mul ((3 : ℕ).descFactorial k)) T

-- Third differentiation checks the factorial and a nonzero time-integral normalization.
-- The same assertion includes zero viscosity.
example {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    iteratedDeriv 3 (heatDuhamel ν (fun s y => |s - 1| * y ^ 3) 1) x = 3 := by
  rw [heatDuhamel_iteratedDeriv (T := 1) hν (fun s _ => by fun_prop)
    (fun k _ => cubic_jet_cont k 1) (fun k _ => cubic_jet_growth k 1) ⟨by norm_num, le_rfl⟩]
  simp_rw [cubic_jet]
  norm_num only [Nat.descFactorial, Nat.cast_ofNat, Nat.reduceSub, pow_zero, mul_one]
  rw [heatDuhamel_time_only]
  have he : (∫ s in (0 : ℝ)..1, |s - 1| * 6) = ∫ s in (0 : ℝ)..1, (1 - s) * 6 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa using hs
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hs'.2)]
    ring
  rw [he, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun s : ℝ => s)
      intervalIntegrable_const ((show Continuous (fun s : ℝ => s) from by fun_prop).intervalIntegrable 0 1)]
  norm_num

-- A continuous forcing with spatial cusps gains a derivative: n=0 needs no C1 assumption.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    DifferentiableAt ℝ (heatDuhamel ν (fun _ y => |sin y|) t) x := by
  have hb : MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun (_ : ℝ) y => |sin y|) T :=
    .of_bounded ⟨1, fun _ _ y => by simpa only [abs_abs] using abs_sin_le_one y⟩
  simpa only [iteratedDeriv_zero] using
    (heatDuhamel_hasDerivAt_iteratedDeriv (f := fun _ y => |sin y|) (n := 0) hν
      (fun s _ => by exact contDiff_zero.mpr (by fun_prop))
      (fun k hk => by
        have hk0 : k = 0 := by omega
        subst k
        simp only [iteratedDeriv_zero]
        fun_prop)
      (fun k hk => by
        have hk0 : k = 0 := by omega
        subst k
        simpa only [iteratedDeriv_zero] using hb)
      ht x).differentiableAt

-- Degenerate time strips still give a genuine derivative of the zero Duhamel slice.
example (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n (heatDuhamel 1 (fun s y => |s - 1| * exp (-2 * y)) 0)) 0 x := by
  have hd (f : ℝ → ℝ → ℝ) : heatDuhamel 1 f 0 = fun _ => 0 :=
    funext (heatDuhamel_zero_time 1 f)
  simpa only [hd, deriv_const] using
    heatDuhamel_hasDerivAt_iteratedDeriv (f := fun s y => |s - 1| * exp (-2 * y))
      (n := n) (ν := 1) (t := 0) (T := 0) (by norm_num) (fun s _ => by fun_prop)
      (fun k _ => exp_jet_cont k 0) (fun k _ => exp_jet_growth k 0) ⟨le_rfl, le_rfl⟩ x

-- An actual C1 profile with a nonsmooth first derivative exercises the n=1 gain.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    DifferentiableAt ℝ (iteratedDeriv 1 (heatDuhamel ν
      (fun _ => ColeHopf.initialHeatProfile 1 (fun y => |sin y|) 0) t)) x := by
  let g := ColeHopf.initialHeatProfile 1 (fun y => |sin y|) 0
  have hb : ∃ M, ∀ y : ℝ, abs (|sin y|) ≤ M :=
    ⟨1, fun y => by simpa only [abs_abs] using abs_sin_le_one y⟩
  have hgc : ContDiff ℝ 1 g := ColeHopf.initialHeatProfile_contDiff (by fun_prop) 1 0
  have hgg : HasExpGrowth g := ColeHopf.initialHeatProfile_hasExpGrowth hb (by norm_num) 0
  have hgd : HasExpGrowth (deriv g) :=
    ColeHopf.initialHeatProfile_deriv_hasExpGrowth (by fun_prop) hb (by norm_num) 0
  have hc (k : ℕ) (hk : k ≤ 1) : Continuous (iteratedDeriv k g) :=
    (contDiff_nat_iff_iteratedDeriv.mp hgc).1 k hk
  have hg (k : ℕ) (hk : k ≤ 1) : HasExpGrowth (iteratedDeriv k g) := by
    interval_cases k
    · simpa only [iteratedDeriv_zero] using hgg
    · simpa only [iteratedDeriv_one] using hgd
  exact (heatDuhamel_hasDerivAt_iteratedDeriv (f := fun _ => g) hν (fun _ _ => hgc)
    (fun k hk => ((hc k hk).comp continuous_snd).continuousOn)
    (fun k hk => by
      obtain ⟨M, c, hM, hc, hb⟩ := hg k hk
      exact ⟨M, c, hM, hc, fun _ _ y => hb y⟩) ht x).differentiableAt

-- Away from the cusp the source term is nonzero as well as the diffusion term.
example {ν T : ℝ} (hν : 0 < ν) (hT : 2 < T) (x : ℝ) :
    HasDerivAt (fun t => iteratedDeriv 1
      (heatDuhamel ν (fun s y => |s - 1| * exp (-2 * y)) t) x)
      (-2 * exp (-2 * x) +
        ν * heatDuhamel ν (fun s y => |s - 1| * ((-2)^3 * exp (-2 * y))) 2 x) 2 := by
  have h := heatDuhamel_iteratedDeriv_hasDerivAt_time (f := fun s y => |s - 1| * exp (-2 * y))
    (n := 1) (t := 2) hν (fun s _ => by fun_prop)
    (fun k _ => exp_jet_cont k T) (fun k _ => exp_jet_growth k T) ⟨by norm_num, hT⟩ x
  simp only [exp_jet] at h
  norm_num only [Nat.reduceAdd, pow_one, show |(2 : ℝ)-1| = 1 by norm_num, one_mul] at h
  convert h using 1
  norm_num

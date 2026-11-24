/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.PotentialHeatSpatial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open Set Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

example {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ} (n : ℕ) (hν : 0 < ν)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ n (q s))
    (hqc : ∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioc 0 T) :
    ContDiff ℝ n (potentialHeatSolution ν q g t) :=
  potentialHeatSolution_contDiff_space hν hqs hqc hqb hg hgg ht

private theorem exp_abs_growth : HasExpGrowth (fun y : ℝ => exp |y|) :=
  ⟨1, 1, by norm_num, by norm_num, fun y => by simp [abs_of_pos (exp_pos _)]⟩

private theorem trig_jet_bound (k : ℕ) :
    (∀ x : ℝ, |iteratedDeriv k sin x| ≤ 1) ∧ (∀ x : ℝ, |iteratedDeriv k cos x| ≤ 1) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using And.intro abs_sin_le_one abs_cos_le_one
  | succ k ih =>
    constructor
    · simpa only [iteratedDeriv_add_one_sin] using ih.2
    · simpa only [iteratedDeriv_add_one_cos, Pi.neg_apply, abs_neg] using ih.1

private theorem smooth_jet (k : ℕ) (s x : ℝ) :
    iteratedDeriv k (fun y => sin (s+y)) x = iteratedDeriv k sin (s+x) := by
  rw [iteratedDeriv_comp_const_add]

private theorem smooth_cont (k : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (fun y => sin (p.1+y)) p.2)
      (Icc 0 T ×ˢ univ) := by
  simp_rw [smooth_jet]
  exact ((differentiable_iteratedDeriv_sin k).continuous.comp (by fun_prop)).continuousOn

private theorem smooth_bound (k : ℕ) (T : ℝ) :
    ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (fun y => sin (s+y)) x| ≤ M :=
  ⟨1, fun s _ x => by rw [smooth_jet]; exact (trig_jet_bound k).1 _⟩

private theorem rough_jet (k : ℕ) (s x : ℝ) :
    iteratedDeriv k (fun y => |sin s| * sin y) x = |sin s| * iteratedDeriv k sin x := by
  rw [iteratedDeriv_const_mul_field]

private theorem rough_cont (k : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (fun y => |sin p.1| * sin y) p.2)
      (Icc 0 T ×ˢ univ) := by
  simp_rw [rough_jet]
  exact ((continuous_sin.comp continuous_fst).abs.mul
    ((differentiable_iteratedDeriv_sin k).continuous.comp continuous_snd)).continuousOn

private theorem rough_bound (k : ℕ) (T : ℝ) :
    ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (fun y => |sin s| * sin y) x| ≤ M := by
  refine ⟨1, fun s _ x => ?_⟩
  rw [rough_jet, abs_mul, abs_abs]
  exact (mul_le_mul (abs_sin_le_one s) ((trig_jet_bound k).1 x) (abs_nonneg _) zero_le_one).trans
    (by norm_num)

-- The initial datum is unbounded and not C1 at zero; the potential is space-time dependent.
example {ν T t : ℝ} (n : ℕ) (hν : 0 < ν) (ht : t ∈ Ioc 0 T) :
    ContDiff ℝ n (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) t) :=
  potentialHeatSolution_contDiff_space hν (fun s _ => by fun_prop)
    (fun k _ => smooth_cont k T) (fun k _ => smooth_bound k T) (by fun_prop) exp_abs_growth ht

example {ν T a : ℝ} (n : ℕ) (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (potentialHeatSolution ν
      (fun s y => sin (s+y)) (fun y => exp |y|) p.1) p.2) (Icc a T ×ˢ univ) :=
  potentialHeatSolution_iteratedDeriv_continuousOn hν (fun s _ => by fun_prop)
    (fun k _ => smooth_cont k T) (fun k _ => smooth_bound k T) (by fun_prop) exp_abs_growth ha haT

example {ν T a : ℝ} (n : ℕ) (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => iteratedDeriv n (potentialHeatSolution ν
        (fun r y => sin (r+y)) (fun y => exp |y|) (a+s)) x) (T-a) :=
  potentialHeatSolution_iteratedDeriv_hasExpGrowthOnStrip hν (fun s _ => by fun_prop)
    (fun k _ => smooth_cont k T) (fun k _ => smooth_bound k T) (by fun_prop) exp_abs_growth ha haT

example {ν T a b : ℝ} (n : ℕ) (hν : 0 < ν) (ha : 0 < a) (hb : 0 ≤ b) (hab : a+b ≤ T)
    (x : ℝ) :
    iteratedDeriv n (potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) (a+b)) x =
      heatSolution (iteratedDeriv n (potentialHeatSolution ν
        (fun s y => sin (s+y)) (fun y => exp |y|) a)) (ν*b) x +
      heatDuhamel ν (fun s y => iteratedDeriv n (fun z => sin (a+s+z) *
        potentialHeatSolution ν (fun r y => sin (r+y)) (fun y => exp |y|) (a+s) z) y) b x :=
  potentialHeatSolution_iteratedDeriv_restart_mild hν (fun s _ => by fun_prop)
    (fun k _ => smooth_cont k T) (fun k _ => smooth_bound k T) (by fun_prop) exp_abs_growth
    ha hb hab x

-- A potential with a time cusp still gives arbitrary spatial regularity.
example {ν T t : ℝ} (n : ℕ) (hν : 0 < ν) (ht : t ∈ Ioc 0 T) :
    ContDiff ℝ n (potentialHeatSolution ν (fun s y => |sin s| * sin y) (fun y => exp |y|) t) :=
  potentialHeatSolution_contDiff_space hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ht

example {ν T a : ℝ} (n : ℕ) (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (fun y => exp |y|) p.1) p.2) (Icc a T ×ˢ univ) :=
  potentialHeatSolution_iteratedDeriv_continuousOn hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ha haT

example {ν T a : ℝ} (n : ℕ) (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => iteratedDeriv n (potentialHeatSolution ν
        (fun r y => |sin r| * sin y) (fun y => exp |y|) (a+s)) x) (T-a) :=
  potentialHeatSolution_iteratedDeriv_hasExpGrowthOnStrip hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ha haT

-- The closed positive-time strip includes its terminal slice, even when a=T.
example {ν T : ℝ} (n : ℕ) (hν : 0 < ν) (hT : 0 < T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s x => iteratedDeriv n (potentialHeatSolution ν
        (fun r y => |sin r| * sin y) (fun y => exp |y|) (T+s)) x) 0 := by
  simpa only [sub_self] using potentialHeatSolution_iteratedDeriv_hasExpGrowthOnStrip
    (n := n) hν (fun s _ => by fun_prop) (fun k _ => rough_cont k T)
    (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth hT le_rfl

example {ν T : ℝ} (n : ℕ) (hν : 0 < ν) (hT : 0 < T) :
    ContDiff ℝ n (potentialHeatSolution ν (fun s y => |sin s| * sin y) (fun y => exp |y|) T) :=
  potentialHeatSolution_contDiff_space hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T)
    (by fun_prop) exp_abs_growth ⟨hT, le_rfl⟩

-- Spatial smoothness does not assert any potential time derivative.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioc 0 T) :
    ContDiff ℝ ∞ (potentialHeatSolution ν (fun s y => |sin s| * sin y) (fun y => exp |y|) t) := by
  apply contDiff_infty.mpr
  intro n
  exact potentialHeatSolution_contDiff_space hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ht

example {ν T : ℝ} (n : ℕ) (hν : 0 < ν) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (fun y => exp |y|) p.1) p.2) (Ioc 0 T ×ˢ univ) :=
  potentialHeatSolution_iteratedDeriv_continuousOn_pos hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth

-- Differentiated restart is usable directly with ordinary deriv and a time-cusp potential.
example {ν T a b : ℝ} (hν : 0 < ν) (ha : 0 < a) (hb : 0 ≤ b) (hab : a+b ≤ T) (x : ℝ) :
    deriv (potentialHeatSolution ν (fun s y => |sin s| * sin y) (fun y => exp |y|) (a+b)) x =
      heatSolution (deriv (potentialHeatSolution ν (fun s y => |sin s| * sin y)
        (fun y => exp |y|) a)) (ν*b) x +
      heatDuhamel ν (fun s y => deriv (fun z => |sin (a+s)| * sin z *
        potentialHeatSolution ν (fun r y => |sin r| * sin y) (fun y => exp |y|) (a+s) z) y) b x := by
  simpa only [iteratedDeriv_one] using potentialHeatSolution_iteratedDeriv_restart_mild
    (n := 1) hν (fun s _ => by fun_prop) (fun k _ => rough_cont k T)
    (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ha hb hab x

-- Actual derivatives exist, not merely totalized values with a continuity property.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioc 0 T) (x : ℝ) :
    HasDerivAt (iteratedDeriv 2 (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (fun y => exp |y|) t))
      (iteratedDeriv 3 (potentialHeatSolution ν
        (fun s y => |sin s| * sin y) (fun y => exp |y|) t) x) x := by
  have hc := potentialHeatSolution_contDiff_space (n := 3) hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ht
  simpa only [show 3 = 2+1 from rfl, iteratedDeriv_succ] using
    ((contDiff_nat_iff_iteratedDeriv.mp hc).2 2 (by norm_num) x).hasDerivAt

-- Zero potential recovers heat evolution with the correct nonzero third-derivative coefficient.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioc 0 T) (x : ℝ) :
    ContDiff ℝ 3 (potentialHeatSolution ν (fun _ _ => 0) (fun y => exp (-2*y)) t) ∧
      iteratedDeriv 3 (potentialHeatSolution ν (fun _ _ => 0) (fun y => exp (-2*y)) t) x =
        -8 * heatSolution (fun y => exp (-2*y)) (ν*t) x := by
  constructor
  · exact potentialHeatSolution_contDiff_space (q := fun _ _ => 0) hν (fun s _ => by fun_prop)
      (fun k _ => by simpa using
        (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) (Icc 0 T ×ˢ univ)))
      (fun k _ => ⟨0, fun _ _ _ => by simp⟩) (by fun_prop) (HasExpGrowth.exp_linear (-2)) ht
  · have hz : potentialHeatSolution ν (fun _ _ => 0) (fun y => exp (-2*y)) t =
        heatSolution (fun y => exp (-2*y)) (ν*t) :=
      funext (potentialHeatSolution_zero_potential ν _ t)
    have hb (k : ℕ) (_ : k ≤ 3) : HasExpGrowth (iteratedDeriv k (fun y => exp (-2*y))) := by
      rw [iteratedDeriv_exp_const_mul]
      exact (HasExpGrowth.exp_linear (-2)).const_mul _
    rw [hz, heatSolution_iteratedDeriv_of_exp_growth (by fun_prop) hb]
    simp only [iteratedDeriv_exp_const_mul, heatSolution_const_mul]
    norm_num

-- Differentiated actual forcing supplies the integrable field for the next time-regularity step.
example {ν T a : ℝ} (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv 3 (fun y => |sin (a+p.1)| * sin y *
      potentialHeatSolution ν (fun s z => |sin s| * sin z) (fun z => exp |z|) (a+p.1) y) p.2)
      (Icc 0 (T-a) ×ˢ univ) :=
  potentialHeatSolution_forcing_iteratedDeriv_continuousOn
    (q := fun s y => |sin s| * sin y) (g := fun y => exp |y|) (n := 3) hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ha haT

example {ν T a : ℝ} (hν : 0 < ν) (ha : 0 < a) (haT : a ≤ T) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip (fun s x => iteratedDeriv 3
      (fun y => |sin (a+s)| * sin y * potentialHeatSolution ν
        (fun r z => |sin r| * sin z) (fun z => exp |z|) (a+s) y) x) (T-a) :=
  potentialHeatSolution_forcing_iteratedDeriv_hasExpGrowthOnStrip
    (q := fun s y => |sin s| * sin y) (g := fun y => exp |y|) (n := 3) hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ha haT

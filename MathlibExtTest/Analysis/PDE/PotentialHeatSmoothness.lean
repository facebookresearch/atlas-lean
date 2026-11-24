/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.PotentialHeatSmoothness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open Set Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

example {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T t : ℝ} (n : ℕ) (hν : 0 < ν)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ (n + 2) (q s))
    (hqc : ∀ k ≤ n + 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ n + 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => iteratedDeriv n (potentialHeatSolution ν q g r) x)
      (ν * iteratedDeriv (n + 2) (potentialHeatSolution ν q g t) x +
        iteratedDeriv n (fun y => q t y * potentialHeatSolution ν q g t y) x) t :=
  potentialHeatSolution_iteratedDeriv_hasDerivAt_time hν hqs hqc hqb hg hgg ht x

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

private theorem sine_linear_frechet_bound (L : ℝ × ℝ →L[ℝ] ℝ) (n : ℕ) (p : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun z => sin (L z)) p‖ ≤ ‖L‖^n := by
  have h := L.iteratedFDeriv_comp_right (f := sin) (show ContDiff ℝ ∞ sin from by fun_prop)
    p (i := n) (by simp)
  change iteratedFDeriv ℝ n (fun z => sin (L z)) p = _ at h
  rw [h]
  have hb := (iteratedFDeriv ℝ n sin (L p)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  exact hb.trans (by nlinarith [(trig_jet_bound n).1 (L p), pow_nonneg (norm_nonneg L) n])

private theorem spacetime_sine_bound (T : ℝ) (n : ℕ) :
    ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry (fun t x : ℝ => sin (t+x))) p‖ ≤ M := by
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  refine ⟨‖L‖^n, fun p _ => ?_⟩
  simpa only [L, add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Function.uncurry_def] using sine_linear_frechet_bound L n p

-- Joint smoothness of the construction with a nonconstant space-time potential and rough data.
example {ν T : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (Function.uncurry (potentialHeatSolution ν
      (fun t x => sin (t+x)) (fun x => exp |x|))) (Ioo 0 T ×ˢ univ) :=
  potentialHeatSolution_contDiffOn hν (by fun_prop) (spacetime_sine_bound T)
    (by fun_prop) exp_abs_growth

example {ν T : ℝ} (hν : 0 < ν) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (potentialHeatSolution ν
      (fun t x => sin (t+x)) (fun x => exp |x|) p.1) p.2) (Ioo 0 T ×ˢ univ) :=
  potentialHeatSolution_iteratedDeriv_contDiffOn hν (by fun_prop) (spacetime_sine_bound T)
    (by fun_prop) exp_abs_growth k

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) r x)
      (ν * deriv (deriv (potentialHeatSolution ν (fun s y => sin (s+y))
        (fun y => exp |y|) t)) x + sin (t+x) *
        potentialHeatSolution ν (fun s y => sin (s+y)) (fun y => exp |y|) t x) t :=
  potentialHeatSolution_hasDerivAt_time_of_contDiff hν (by fun_prop) (spacetime_sine_bound T)
    (by fun_prop) exp_abs_growth ht x

-- The weaker finite-order time-jet theorem permits a potential time cusp.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 T) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun r => iteratedDeriv n (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (fun y => exp |y|) r) x)
      (ν * iteratedDeriv (n+2) (potentialHeatSolution ν
        (fun s y => |sin s| * sin y) (fun y => exp |y|) t) x +
        iteratedDeriv n (fun y => |sin t| * sin y * potentialHeatSolution ν
          (fun s z => |sin s| * sin z) (fun z => exp |z|) t y) x) t :=
  potentialHeatSolution_iteratedDeriv_hasDerivAt_time hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ht x

example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => potentialHeatSolution ν (fun s y => |sin s| * sin y)
      (fun y => exp |y|) r x)
      (ν * deriv (deriv (potentialHeatSolution ν (fun s y => |sin s| * sin y)
        (fun y => exp |y|) t)) x + |sin t| * sin x *
        potentialHeatSolution ν (fun s y => |sin s| * sin y) (fun y => exp |y|) t x) t :=
  potentialHeatSolution_hasDerivAt_time hν (fun s _ => by fun_prop)
    (fun k _ => rough_cont k T) (fun k _ => rough_bound k T) (by fun_prop) exp_abs_growth ht x

-- At the interior cusp t=π the spatially differentiated forcing vanishes.
example {ν T : ℝ} (hν : 0 < ν) (hT : π < T) (x : ℝ) :
    HasDerivAt (fun r => deriv (potentialHeatSolution ν
      (fun s y => |sin s| * sin y) (fun y => exp |y|) r) x)
      (ν * iteratedDeriv 3 (potentialHeatSolution ν
        (fun s y => |sin s| * sin y) (fun y => exp |y|) π) x) π := by
  have h := potentialHeatSolution_iteratedDeriv_hasDerivAt_time (n := 1) hν
    (fun s _ => by fun_prop) (fun k _ => rough_cont k T) (fun k _ => rough_bound k T)
    (by fun_prop) exp_abs_growth ⟨pi_pos, hT⟩ x
  simpa only [sin_pi, abs_zero, zero_mul, iteratedDeriv_one, deriv_const, add_zero, Nat.reduceAdd]
    using h

-- Both the potential sign and viscosity factor survive specialization to a nonzero source point.
example {T : ℝ} (hT : 1 < T) :
    HasDerivAt (fun r => potentialHeatSolution 3 (fun s y => sin (s+y))
      (fun y => exp |y|) r (π/2-1))
      (3 * deriv (deriv (potentialHeatSolution 3 (fun s y => sin (s+y))
        (fun y => exp |y|) 1)) (π/2-1) +
        potentialHeatSolution 3 (fun s y => sin (s+y)) (fun y => exp |y|) 1 (π/2-1)) 1 := by
  have h := potentialHeatSolution_hasDerivAt_time_of_contDiff (q := fun s y => sin (s+y))
    (ν := 3) (by norm_num) (by fun_prop) (spacetime_sine_bound T) (by fun_prop) exp_abs_growth
    (t := 1) ⟨by norm_num, hT⟩ (π/2-1)
  have hx : (1 : ℝ)+(π/2-1) = π/2 := by ring
  simpa only [hx, sin_pi_div_two, one_mul] using h

-- A nonzero q_x term appears in the first spatial jet's actual time derivative.
example {T : ℝ} (hT : 1 < T) :
    HasDerivAt (fun r => deriv (potentialHeatSolution 2 (fun s y => sin (s+y))
      (fun y => exp |y|) r) (-1))
      (2 * iteratedDeriv 3 (potentialHeatSolution 2 (fun s y => sin (s+y))
        (fun y => exp |y|) 1) (-1) +
        potentialHeatSolution 2 (fun s y => sin (s+y)) (fun y => exp |y|) 1 (-1)) 1 := by
  have hc := potentialHeatSolution_contDiff_space (n := 1) (ν := 2) (by norm_num)
    (fun s _ => by fun_prop) (fun k _ => smooth_cont k T) (fun k _ => smooth_bound k T)
    (by fun_prop) exp_abs_growth (t := 1) ⟨by norm_num, hT.le⟩
  have hphi := ((hc.differentiable (by norm_num)) (-1)).hasDerivAt
  have hq : HasDerivAt (fun y : ℝ => sin (1+y)) 1 (-1) := by
    simpa [Function.comp_def] using!
      (hasDerivAt_sin (1+(-1 : ℝ))).comp (-1) ((hasDerivAt_id (-1 : ℝ)).const_add 1)
  have hprod : deriv (fun y => sin (1+y) * potentialHeatSolution 2
      (fun s z => sin (s+z)) (fun z => exp |z|) 1 y) (-1) =
      potentialHeatSolution 2 (fun s z => sin (s+z)) (fun z => exp |z|) 1 (-1) := by
    simpa [Pi.mul_def] using (hq.mul hphi).deriv
  have h := potentialHeatSolution_iteratedDeriv_hasDerivAt_time (n := 1) (ν := 2)
    (by norm_num) (fun s _ => by fun_prop) (fun k _ => smooth_cont k T)
    (fun k _ => smooth_bound k T) (by fun_prop) exp_abs_growth (t := 1) ⟨by norm_num, hT⟩ (-1)
  simpa only [iteratedDeriv_one, hprod, Nat.reduceAdd] using h

-- A zero horizon gives an empty open smoothness domain, without asserting a time derivative at zero.
example {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (Function.uncurry (potentialHeatSolution ν
      (fun t x => sin (t+x)) (fun x => exp |x|))) (Ioo 0 0 ×ˢ univ) :=
  potentialHeatSolution_contDiffOn hν (by fun_prop) (spacetime_sine_bound 0)
    (by fun_prop) exp_abs_growth

-- The joint theorem supplies ordinary Fréchet differentiability at interior points.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    DifferentiableAt ℝ (Function.uncurry (potentialHeatSolution ν
      (fun s y => sin (s+y)) (fun y => exp |y|))) (t,x) :=
  ((potentialHeatSolution_contDiffOn hν (by fun_prop) (spacetime_sine_bound T)
    (by fun_prop) exp_abs_growth).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).differentiableAt (by simp)

-- Constant potential and datum identify an explicit, nonzero time derivative of the construction.
example {ν T t : ℝ} (hν : 0 < ν) (ht : t ∈ Ioo 0 T) (x : ℝ) :
    HasDerivAt (fun r => potentialHeatSolution ν (fun _ _ => 2) (fun _ => 3) r x)
      (6 * exp (2*t)) t := by
  have hc (k : ℕ) : ContinuousOn
      (fun p : ℝ × ℝ => iteratedDeriv k (fun _ : ℝ => (2 : ℝ)) p.2) (Icc 0 T ×ˢ univ) := by
    simp_rw [iteratedDeriv_const]
    exact continuousOn_const
  have hb (k : ℕ) : ∃ M, ∀ s ∈ Icc 0 T, ∀ x,
      |iteratedDeriv k (fun _ : ℝ => (2 : ℝ)) x| ≤ M := by
    refine ⟨2, fun _ _ _ => ?_⟩
    rw [iteratedDeriv_const]
    split_ifs <;> norm_num
  have h := potentialHeatSolution_hasDerivAt_time (q := fun _ _ => 2) (g := fun _ => 3)
    hν (fun _ _ => contDiff_const) (fun k _ => hc k) (fun k _ => hb k)
    continuous_const (HasExpGrowth.of_bounded ⟨3, fun _ => by norm_num⟩) ht x
  have he : potentialHeatSolution ν (fun _ _ => 2) (fun _ => 3) t = fun _ => 3 * exp (2*t) :=
    funext (potentialHeatSolution_const ν 2 3 t)
  simpa only [he, deriv_const', deriv_const, mul_zero, zero_add, show (2 : ℝ)*3 = 6 by norm_num,
    ← mul_assoc] using h

-- Sign-changing unbounded data are also admitted; positivity is not a smoothness hypothesis.
example {ν T : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (Function.uncurry (potentialHeatSolution ν
      (fun t x => sin (t+x)) (fun x => x))) (Ioo 0 T ×ˢ univ) := by
  have hg : HasExpGrowth (fun x : ℝ => x) := by
    refine ⟨1, 1, by norm_num, by norm_num, fun x => ?_⟩
    simpa only [one_mul] using
      (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp |x|)
  exact potentialHeatSolution_contDiffOn hν (by fun_prop) (spacetime_sine_bound T)
    (by fun_prop) hg

-- Zero-potential compatibility recovers joint smoothness of the actual free heat field.
example {ν T : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => heatSolution (fun x => exp |x|) (ν*p.1) p.2)
      (Ioo 0 T ×ˢ univ) := by
  have hb (n : ℕ) : ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) p‖ ≤ M := by
    refine ⟨0, fun p _ => ?_⟩
    simp [Function.uncurry_def]
  simpa only [Function.uncurry_def, potentialHeatSolution_zero_potential] using
    potentialHeatSolution_contDiffOn (q := fun _ _ => 0) hν (by fun_prop) hb
      (by fun_prop) exp_abs_growth

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.InitialInverseColeHopf
import MathlibExt.Analysis.PDE.BurgersBounds
import MathlibExt.Analysis.PDE.HeatKernelUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Filter
open scoped ContDiff Topology
open ColeHopf
open MathlibExt.Analysis.PDE.HeatWholeLine

-- The initial profile and positivity do not require any initial spatial derivative.
example (ν : ℝ) (u : ℝ → ℝ → ℝ) (a x : ℝ) :
    initialInverseProfile ν u a 0 x = initialHeatProfile ν (u 0) a x :=
  initialInverseProfile_zero ν u a x

example (ν : ℝ) (u : ℝ → ℝ → ℝ) (a t x : ℝ) :
    0 < initialInverseProfile ν u a t x := initialInverseProfile_pos ν u a t x

example {u : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ)) (ν a : ℝ) :
    ContinuousOn (Function.uncurry (initialInverseProfile ν u a)) (Ici 0 ×ˢ univ) :=
  initialInverseProfile_continuousOn hc ν a

example {u : ℝ → ℝ → ℝ} (ν a T : ℝ)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) :
    HasExpGrowthOnStrip (initialInverseProfile ν u a) T :=
  initialInverseProfile_hasExpGrowthOnStrip hc hb ν a

open MeasureTheory Real
open scoped Interval
open MathlibExt.Analysis.PDE.HeatKernel

-- A nonzero constant velocity needs a nontrivial time factor. This checks its sign,
-- coefficient, initial correction, and arbitrary translated spatial anchor.
private theorem constant_profile (c ν a t x : ℝ) :
    initialInverseProfile ν (fun _ _ => c) a t x =
      exp (t * c ^ 2 / (4 * ν) - (x - a) * c / (2 * ν)) := by
  simp only [initialInverseProfile, initialInverseNormalization, initialInverseMoment,
    sub_self, zero_div, initialInverseRate, intervalIntegral.integral_const, smul_eq_mul,
    add_sub_cancel_left, one_mul, sub_zero, zero_add]
  congr 1
  ring

example (a t x : ℝ) : initialInverseProfile 3 (fun _ _ => -2) a t x =
    exp (t / 3 + (x - a) / 3) := by
  rw [constant_profile]
  congr 1
  ring

example (ν a t x : ℝ) : initialInverseProfile ν (fun _ _ => 0) a t x = 1 := by
  simp [constant_profile]

-- Recovery works even at zero with a nonsmooth spatial slice.
example (a x : ℝ) :
    classicalTransform 3 (initialInverseProfile 3 (fun _ y => |sin y|) a) 0 x = |sin x| :=
  classicalTransform_initialInverseProfile continuous_sin.abs (by norm_num) a x

-- The algebraic inverse and heat equation also work for negative nonzero viscosity.
example (c a t x : ℝ) (ht : 0 < t) :
    deriv (fun s => initialInverseProfile (-2) (fun _ _ => c) a s x) t =
      -2 * iteratedDeriv 2 (initialInverseProfile (-2) (fun _ _ => c) a t) x := by
  apply initialInverseProfile_heat continuousOn_const contDiffOn_const ht
    (fun y => by simp [iteratedDeriv_const]) (by norm_num)

-- Nothing is assumed of the input at negative times, even if it has a jump there.
private noncomputable def badPast (t x : ℝ) : ℝ := if 0 ≤ t then 2 else |x| + t⁻¹

private theorem badPast_continuous :
    ContinuousOn (Function.uncurry badPast) (Ici 0 ×ˢ univ) :=
  (continuousOn_const (c := (2 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, badPast, show 0 ≤ p.1 from hp.1])

private theorem badPast_smooth :
    ContDiffOn ℝ 2 (Function.uncurry badPast) (Ioi 0 ×ˢ univ) :=
  (contDiffOn_const (c := (2 : ℝ))).congr (fun p hp => by
    simp [Function.uncurry_def, badPast, le_of_lt hp.1])

example (a : ℝ) : ContinuousOn (Function.uncurry (initialInverseProfile 1 badPast a))
    (Ici 0 ×ˢ univ) := initialInverseProfile_continuousOn badPast_continuous 1 a

example (a t : ℝ) (ht : 0 < t) : ContDiff ℝ 2 (initialInverseProfile 1 badPast a t) := by
  apply initialInverseProfile_contDiff_space
  have he : badPast t = fun _ => (2 : ℝ) := funext (fun x => by simp [badPast, ht.le])
  rw [he]
  exact contDiff_const

-- Growth requires no PDE and allows zero viscosity and a collapsed time strip.
example (a : ℝ) : HasExpGrowthOnStrip (initialInverseProfile 0 badPast a) 0 := by
  apply initialInverseProfile_hasExpGrowthOnStrip badPast_continuous
    (ν := 0) (a := a)
  refine ⟨2, fun t ht x => ?_⟩
  simp [badPast, ht.1]

example (ν a : ℝ) : HasExpGrowthOnStrip
    (initialInverseProfile ν (fun t x => t * sin x) a) (-1) := by
  apply initialInverseProfile_hasExpGrowthOnStrip (by fun_prop)
  exact ⟨0, fun t ht _ => (by linarith [ht.1, ht.2])⟩

-- End-to-end bridge: all hypotheses of heat uniqueness can be discharged from
-- a bounded continuous Burgers field, without regularity of u_x at time zero.
private theorem profile_eq_heat {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
      initialInverseProfile ν u a t x = heatSolution (initialHeatProfile ν (u 0) a) (ν * t) x := by
  have h0 : Continuous (u 0) := by
    rw [← continuousOn_univ]
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨le_rfl, hx⟩)
  have hb0 : ∃ M, ∀ x, |u 0 x| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, hM 0 ⟨le_rfl, hT⟩⟩
  apply eq_heatSolution_of_exp_growth hν (initialHeatProfile_contDiff h0 ν a).continuous
    (initialHeatProfile_hasExpGrowth hb0 hν a)
    ((initialInverseProfile_continuousOn hc ν a).mono (fun _ hp => ⟨hp.1.1, hp.2⟩))
    (fun t ht x => ?_)
    (fun t ht x => (initialInverseProfile_hasDerivAt_heat hc hu ht.1
      (hpde t ht.1) hν.ne' a x).hasDerivWithinAt)
    (fun _ _ _ => rfl) (initialInverseProfile_hasExpGrowthOnStrip hc hb ν a)
    (initialInverseProfile_zero ν u a)
  have hs : ContDiff ℝ 2 (u t) := by
    rw [← contDiffOn_univ]
    exact hu.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨ht.1, hx⟩)
  exact (initialInverseProfile_contDiff_space hs ν a).contDiffAt

-- The bridge applies to the actual solution of bounded, nondifferentiable data.
private noncomputable def corner (x : ℝ) : ℝ := |sin x|
private theorem corner_continuous : Continuous corner := continuous_sin.abs
private theorem corner_bound : ∀ x, |corner x| ≤ 1 := by
  intro x
  simpa [corner] using abs_sin_le_one x

example (T : ℝ) (hT : 0 ≤ T) : ∀ t ∈ Icc 0 T, ∀ x,
    initialInverseProfile 3 (burgersSolution 3 corner 7) 7 t x =
      heatSolution (initialHeatProfile 3 corner 7) (3 * t) x := by
  have h := profile_eq_heat (u := burgersSolution 3 corner 7) (by norm_num) hT
    (burgersSolution_continuous_of_bounded corner_continuous ⟨1, corner_bound⟩
      (by norm_num) 7).continuousOn
    (burgersSolution_contDiffOn_of_bounded corner_continuous ⟨1, corner_bound⟩ (by norm_num) 7)
    ⟨1, fun t _ x => abs_burgersSolution_le corner_continuous (by norm_num) corner_bound 7 t x⟩
    (fun t ht x => burgersSolution_burgers_of_bounded corner_continuous ⟨1, corner_bound⟩
      (by norm_num) 7 t x ht) 7
  have he : burgersSolution 3 corner 7 0 = corner := by
    funext x
    exact burgersSolution_zero corner_continuous (by norm_num) 7 x
  simpa only [he] using h

example (a x : ℝ) : Tendsto
    (Function.uncurry (initialInverseProfile 3 (fun _ y => |sin y|) a))
    (𝓝[Ici 0 ×ˢ univ] (0, x)) (𝓝 (initialHeatProfile 3 (fun y => |sin y|) a x)) :=
  initialInverseProfile_tendsto_initial (by fun_prop) 3 a x

-- The PDE remains local to positive time despite completely unrelated past values.
example (a t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => initialInverseProfile 3 badPast a s x)
      (3 * iteratedDeriv 2 (initialInverseProfile 3 badPast a t) x) t := by
  apply initialInverseProfile_hasDerivAt_heat badPast_continuous badPast_smooth ht
    (hν := by norm_num)
  intro y
  have he : (fun s => badPast s y) =ᶠ[𝓝 t] (fun _ => (2 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [badPast, hs.le]
  have hx : badPast t = fun _ => (2 : ℝ) := funext (fun z => by simp [badPast, ht.le])
  rw [he.deriv_eq, hx]
  simp [iteratedDeriv_const]

-- A genuinely time-dependent solution exercises the weighted-moment cancellation.
-- It is spatially unbounded: the heat identity itself has no boundedness assumption.
private noncomputable def expanding (t x : ℝ) : ℝ := x / (t + 1)

private theorem expanding_smooth :
    ContDiffOn ℝ 2 (Function.uncurry expanding) (Ioi 0 ×ˢ univ) := by
  apply contDiffOn_snd.div (contDiffOn_fst.add contDiffOn_const)
  intro p hp
  have ht : 0 < p.1 := hp.1
  linarith

private theorem expanding_continuous :
    ContinuousOn (Function.uncurry expanding) (Ici 0 ×ˢ univ) := by
  apply continuousOn_snd.div (continuousOn_fst.add continuousOn_const)
  intro p hp
  have ht : 0 ≤ p.1 := hp.1
  change p.1 + 1 ≠ 0
  linarith

private theorem expanding_burgers (ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => expanding s x) t + expanding t x * deriv (expanding t) x =
      ν * iteratedDeriv 2 (expanding t) x := by
  have hn : t + 1 ≠ 0 := by linarith
  have htime : HasDerivAt (fun s => expanding s x) (-x / (t + 1) ^ 2) t := by
    change HasDerivAt (fun s => x / (s + 1)) _ t
    simpa only [Pi.div_apply, zero_mul, mul_one, zero_sub] using!
      (hasDerivAt_const t x).div ((hasDerivAt_id' t).add_const 1) hn
  have hx : deriv (expanding t) = fun _ => 1 / (t + 1) :=
    funext (fun y => ((hasDerivAt_id' y).div_const (t + 1)).deriv)
  rw [htime.deriv, iteratedDeriv_succ, iteratedDeriv_one, hx, deriv_const]
  dsimp [expanding]
  field_simp
  ring

example (ν a t x : ℝ) (hν : ν ≠ 0) (ht : 0 < t) :
    deriv (fun s => initialInverseProfile ν expanding a s x) t =
      ν * iteratedDeriv 2 (initialInverseProfile ν expanding a t) x :=
  initialInverseProfile_heat expanding_continuous expanding_smooth ht
    (fun y => expanding_burgers ν t y ht) hν a x

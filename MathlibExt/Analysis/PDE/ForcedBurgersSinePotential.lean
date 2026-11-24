/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.ForcedBurgersUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import MathlibExt.Analysis.Calculus.IteratedDerivPartial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# An explicit spatially forced Burgers initial-value solution

The positive profile `exp(t * sin x)` solves potential heat with potential
`sin x + nu * t * sin x - nu * t^2 * cos x^2`. Its logarithmic derivative is
`-2 * nu * t * cos x`, with zero initial velocity. All Frechet derivative bounds
of the potential on finite strips are proved from compact time bounds and
bounded trigonometric derivatives. Classical uniqueness identifies the explicit
profile with the actual potential-heat construction before recovering the
actual Burgers initial-value field.

This is a direct substitution example of the forced Cole–Hopf identity in
Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Theorem 3.3, https://arxiv.org/abs/solv-int/9812025.
-/

@[expose] public section

open Set Real
open scoped ContDiff Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- The potential for the positive profile `exp(t * sin x)`. -/
noncomputable def sinePotential (ν t x : ℝ) : ℝ :=
  sin x + ν*t*sin x - ν*t^2*cos x^2

/-- The explicit sine potential is jointly smooth for every real viscosity. -/
theorem sinePotential_contDiff (ν : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (sinePotential ν)) := by
  unfold sinePotential Function.uncurry
  fun_prop

private def BoundedJets (S : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ M : ℝ, ∀ p ∈ S, ‖iteratedFDeriv ℝ n f p‖ ≤ M

private theorem boundedJets_add {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfb : BoundedJets S f)
    (hgb : BoundedJets S g) : BoundedJets S (fun p => f p+g p) := by
  intro n
  obtain ⟨A,hA⟩ := hfb n
  obtain ⟨B,hB⟩ := hgb n
  refine ⟨A+B,fun p hp => ?_⟩
  change ‖iteratedFDeriv ℝ n (f+g) p‖ ≤ A+B
  rw [iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hA p hp) (hB p hp))

private theorem boundedJets_mul {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfb : BoundedJets S f)
    (hgb : BoundedJets S g) : BoundedJets S (fun p => f p*g p) := by
  choose A hA using hfb
  choose B hB using hgb
  intro n
  refine ⟨∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |A i| * |B (n-i)|,fun p hp => ?_⟩
  apply (norm_iteratedFDeriv_mul_le hf hg p (by simp)).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left ((hA i p hp).trans (le_abs_self _)) (Nat.cast_nonneg _))
    ((hB (n-i) p hp).trans (le_abs_self _)) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

private theorem boundedJets_time {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (T : ℝ) :
    BoundedJets (Icc 0 T ×ˢ univ) (fun p => f p.1) := by
  intro n
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv (m := n) (by simp) hf).continuousOn
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  refine ⟨|M| * ‖L‖^n,fun p hp => ?_⟩
  have he := L.iteratedFDeriv_comp_right hf p (i := n) (by simp)
  change iteratedFDeriv ℝ n (fun z => f z.1) p = _ at he
  rw [he]
  have h := (iteratedFDeriv ℝ n f p.1).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_right ((hM p.1 hp.1).trans (le_abs_self _))
    (pow_nonneg (norm_nonneg L) n))

private theorem boundedJets_space {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ n : ℕ, ∀ x, |iteratedDeriv n f x| ≤ 1) (T : ℝ) :
    BoundedJets (Icc 0 T ×ˢ univ) (fun p => f p.2) := by
  intro n
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  refine ⟨‖L‖^n,fun p hp => ?_⟩
  have he := L.iteratedFDeriv_comp_right hf p (i := n) (by simp)
  change iteratedFDeriv ℝ n (fun z => f z.2) p = _ at he
  rw [he]
  have h := (iteratedFDeriv ℝ n f p.2).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] at h
  exact h.trans (by nlinarith [hb n p.2,pow_nonneg (norm_nonneg L) n])

/-- Every Frechet derivative order of the explicit potential has a uniform bound
on each finite closed time strip. The bound is proved, not an input hypothesis. -/
theorem sinePotential_bounded_jets (ν T : ℝ) (n : ℕ) :
    ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry (sinePotential ν)) p‖ ≤ M := by
  have hs := boundedJets_space (show ContDiff ℝ ∞ sin from by fun_prop)
    Real.abs_iteratedDeriv_sin_le_one T
  have hc := boundedJets_space (show ContDiff ℝ ∞ cos from by fun_prop)
    Real.abs_iteratedDeriv_cos_le_one T
  have ht := boundedJets_time (show ContDiff ℝ ∞ (fun t : ℝ => ν*t) from by fun_prop) T
  have htt := boundedJets_time (show ContDiff ℝ ∞ (fun t : ℝ => -ν*t^2) from by fun_prop) T
  have h1 := boundedJets_mul (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ν*p.1))
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => sin p.2)) ht hs
  have h2 := boundedJets_mul (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cos p.2))
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cos p.2)) hc hc
  have h3 := boundedJets_mul (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => -ν*p.1^2))
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cos p.2*cos p.2)) htt h2
  have h4 := boundedJets_add (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => sin p.2))
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ν*p.1*sin p.2)) hs h1
  have h5 := boundedJets_add
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => sin p.2+ν*p.1*sin p.2))
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (-ν*p.1^2)*(cos p.2*cos p.2))) h4 h3
  have he : Function.uncurry (sinePotential ν) =
      fun p : ℝ × ℝ => (sin p.2+ν*p.1*sin p.2)+(-ν*p.1^2)*(cos p.2*cos p.2) := by
    funext p
    simp only [Function.uncurry_def,sinePotential]
    ring
  rw [he]
  exact h5 n

private theorem sine_profile_hasDerivAt_x (t x : ℝ) :
    HasDerivAt (fun y => exp (t*sin y)) (t*cos x*exp (t*sin x)) x := by
  simpa only [mul_comm] using ((hasDerivAt_sin x).const_mul t).exp

private theorem sine_profile_iteratedDeriv_two (t x : ℝ) :
    iteratedDeriv 2 (fun y => exp (t*sin y)) x =
      (t^2*cos x^2-t*sin x)*exp (t*sin x) := by
  have he : deriv (fun y => exp (t*sin y)) = fun y => t*cos y*exp (t*sin y) :=
    funext (fun y => (sine_profile_hasDerivAt_x t y).deriv)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,he]
  have hd : HasDerivAt (fun y => t*cos y*exp (t*sin y))
      (t*(-sin x)*exp (t*sin x)+(t*cos x)*(t*cos x*exp (t*sin x))) x := by
    simpa only [Pi.mul_apply] using!
      (((hasDerivAt_cos x).const_mul t).mul (sine_profile_hasDerivAt_x t x))
  rw [hd.deriv]
  ring

private theorem sine_profile_hasDerivAt_potential (ν t x : ℝ) :
    HasDerivAt (fun s => exp (s*sin x))
      (ν*iteratedDeriv 2 (fun y => exp (t*sin y)) x + sinePotential ν t x*exp (t*sin x)) t := by
  have hd : HasDerivAt (fun s => exp (s*sin x)) (sin x*exp (t*sin x)) t := by
    simpa only [id_eq,mul_comm,one_mul] using! ((hasDerivAt_id t).mul_const (sin x)).exp
  convert hd using 1
  rw [sine_profile_iteratedDeriv_two]
  simp only [sinePotential]
  ring

/-- The actual potential-heat evolution of the constant datum one is the explicit
positive profile `exp(t * sin x)` for every nonnegative time. -/
theorem potentialHeatSolution_sinePotential {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (x : ℝ) :
    potentialHeatSolution ν (sinePotential ν) (fun _ => 1) t x = exp (t*sin x) := by
  have hq := sinePotential_contDiff ν
  have hqs (s : ℝ) (hs : s ∈ Icc 0 t) : ContDiff ℝ 2 (sinePotential ν s) := by
    have h : ContDiff ℝ ∞ (sinePotential ν s) := by
      simpa only [Function.comp_def,Function.uncurry_def,id_eq] using
        hq.comp (contDiff_const.prodMk contDiff_id)
    exact h.of_le (by simp)
  have hqc (k : ℕ) (hk : k ≤ 2) : ContinuousOn
      (fun p : ℝ × ℝ => iteratedDeriv k (sinePotential ν p.1) p.2) (Icc 0 t ×ˢ univ) :=
    (hq.contDiff_iteratedDeriv_snd k).continuous.continuousOn
  have hqb (k : ℕ) (hk : k ≤ 2) : ∃ M, ∀ s ∈ Icc 0 t, ∀ y,
      |iteratedDeriv k (sinePotential ν s) y| ≤ M := by
    obtain ⟨M,hM⟩ := sinePotential_bounded_jets ν t k
    refine ⟨M,fun s hs y => ?_⟩
    have h : |iteratedDeriv k (sinePotential ν s) y| ≤
        ‖iteratedFDeriv ℝ k (Function.uncurry (sinePotential ν)) (s,y)‖ := by
      simpa only [Real.norm_eq_abs] using
        (hq.of_le (by simp : (k : WithTop ℕ∞) ≤ ∞)).norm_iteratedDeriv_snd_le (s,y)
    exact h.trans (hM (s,y) ⟨hs,mem_univ y⟩)
  have hg : HasExpGrowth (fun _ : ℝ => (1 : ℝ)) :=
    .of_bounded ⟨1,fun _ => by norm_num⟩
  have hgrowth : MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
      (fun s y => exp (s*sin y)) t := by
    refine ⟨exp t,0,(exp_pos _).le,le_rfl,fun s hs y => ?_⟩
    simp only [abs_of_pos (exp_pos _),zero_mul,exp_zero,mul_one]
    exact exp_le_exp.mpr ((mul_le_of_le_one_right hs.1 (sin_le_one y)).trans hs.2)
  have he := eq_potentialHeatSolution_of_exp_growth (u := fun s y => exp (s*sin y))
    hν hqs hqc hqb continuous_const hg (by fun_prop)
    (fun _ _ _ => by fun_prop) (fun s hs y => sine_profile_hasDerivAt_potential ν s y)
    (fun _ _ _ => rfl) hgrowth (fun _ => by simp) t ⟨ht,le_rfl⟩ x
  exact he.symm

/-- The actual forced Burgers initial-value solution for the explicit sine potential
and zero initial velocity is `-2 * nu * t * cos x`, independently of the anchor. -/
theorem forcedBurgersSolution_sinePotential {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (a x : ℝ) :
    forcedBurgersSolution ν (sinePotential ν) (fun _ => 0) a t x = -2*ν*t*cos x := by
  have hg : initialHeatProfile ν (fun _ => 0) a = fun _ => 1 := by
    funext y
    simp [initialHeatProfile]
  have he : forcedBurgersProfile ν (sinePotential ν) (fun _ => 0) a t =
      fun y => exp (t*sin y) := by
    funext y
    simp only [forcedBurgersProfile,hg]
    exact potentialHeatSolution_sinePotential hν ht y
  simp only [forcedBurgersSolution,classicalTransform,he,(sine_profile_hasDerivAt_x t x).deriv]
  have hp : exp (t*sin x) ≠ 0 := ne_of_gt (exp_pos _)
  field_simp

end ColeHopf

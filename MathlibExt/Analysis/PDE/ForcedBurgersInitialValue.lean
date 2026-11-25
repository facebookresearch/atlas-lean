/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.PotentialHeatPositivity
public import MathlibExt.Analysis.PDE.BurgersExponentialGrowth
public import MathlibExt.Analysis.PDE.LocalColeHopf
import MathlibExt.Analysis.Calculus.IteratedDerivPartial
import Mathlib.Tactic.FunProp

/-!
# The actual forced Burgers initial-value construction

The logarithmic derivative of the constructed positive potential-heat solution
recovers every bounded continuous initial velocity. For bounded smooth potentials,
the velocity is jointly continuous on the closed time strip and jointly smooth
at positive interior times, where it satisfies the forced Burgers equation with
forcing `-2 * nu * q_x`. Initial velocities need not be differentiable.

The profile is the actual convergent Volterra construction, not an assumed
solution. Uniform velocity bounds and bounded classical uniqueness are separate
results. No ordinary time derivative at either endpoint is asserted here.

Reference: Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Lemmas 3.1–3.2 and Theorem 3.3(ii), https://arxiv.org/abs/solv-int/9812025,
for the transform identities. The forced residual is applied through the local
Cole–Hopf theorem; the initial-value existence and growth estimates come from
the proved potential-heat construction.
-/

@[expose] public section

open Set Filter Real
open scoped ContDiff Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- The actual positive potential-heat profile obtained from the initial velocity's
exponential primitive. Its evolution properties require the hypotheses below. -/
noncomputable def forcedBurgersProfile (ν : ℝ) (q : ℝ → ℝ → ℝ)
    (u₀ : ℝ → ℝ) (a t x : ℝ) : ℝ :=
  potentialHeatSolution ν q (initialHeatProfile ν u₀ a) t x

/-- The forced Burgers field is the logarithmic derivative of the actual
potential-heat profile. Evolution claims concern nonnegative strip times. -/
noncomputable def forcedBurgersSolution (ν : ℝ) (q : ℝ → ℝ → ℝ)
    (u₀ : ℝ → ℝ) (a t x : ℝ) : ℝ :=
  classicalTransform ν (forcedBurgersProfile ν q u₀ a) t x

/-- The potential-heat profile has exactly the prescribed exponential-primitive datum. -/
@[simp] theorem forcedBurgersProfile_initial (ν : ℝ) (q : ℝ → ℝ → ℝ)
    (u₀ : ℝ → ℝ) (a x : ℝ) :
    forcedBurgersProfile ν q u₀ a 0 x = initialHeatProfile ν u₀ a x := by
  simp [forcedBurgersProfile]

/-- Continuous initial velocity is recovered exactly, without a primitive bound
or any potential regularity assumption at this purely initial-time identity. -/
@[simp] theorem forcedBurgersSolution_initial {u₀ : ℝ → ℝ} (hu : Continuous u₀)
    {ν : ℝ} (hν : ν ≠ 0) (q : ℝ → ℝ → ℝ) (a x : ℝ) :
    forcedBurgersSolution ν q u₀ a 0 x = u₀ x := by
  have he : forcedBurgersProfile ν q u₀ a 0 = initialHeatProfile ν u₀ a :=
    funext (forcedBurgersProfile_initial ν q u₀ a)
  simp only [forcedBurgersSolution, classicalTransform, he]
  exact initialHeatProfile_recovery hu hν a x

/-- Zero potential gives the existing unforced Burgers construction, including
its algebraic extension to arbitrary parameters and times. -/
@[simp] theorem forcedBurgersSolution_zero_potential (ν : ℝ) (u₀ : ℝ → ℝ)
    (a t x : ℝ) :
    forcedBurgersSolution ν (fun _ _ => 0) u₀ a t x = burgersSolution ν u₀ a t x := by
  have he : forcedBurgersProfile ν (fun _ _ => 0) u₀ a =
      (fun s y => heatSolution (initialHeatProfile ν u₀ a) (ν * s) y) := by
    funext s y
    exact potentialHeatSolution_zero_potential ν (initialHeatProfile ν u₀ a) s y
  simp only [forcedBurgersSolution, he, burgersSolution, burgersFromHeat]

private theorem potential_spatial_data {q : ℝ → ℝ → ℝ} {T : ℝ}
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (n : ℕ) :
    (∀ s ∈ Icc 0 T, ContDiff ℝ n (q s)) ∧
    (∀ k ≤ n, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ)) ∧
    (∀ k ≤ n, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M) := by
  refine ⟨fun s _ => ?_, fun k _ => (hq.contDiff_iteratedDeriv_snd k).continuous.continuousOn,
    fun k _ => ?_⟩
  · have hs : ContDiff ℝ ∞ (q s) := by
      simpa only [Function.comp_def,Function.uncurry_def,id_eq] using
        hq.comp (contDiff_const.prodMk contDiff_id)
    exact hs.of_le (by simp)
  · obtain ⟨M,hM⟩ := hb k
    refine ⟨M, fun s hs x => ?_⟩
    have he := (hq.of_le (by simp : (k : WithTop ℕ∞) ≤ ∞)).norm_iteratedDeriv_snd_le (s,x)
    have he' : |iteratedDeriv k (q s) x| ≤ ‖iteratedFDeriv ℝ k (Function.uncurry q) (s,x)‖ := by
      simpa only [Real.norm_eq_abs] using he
    exact he'.trans (hM (s,x) ⟨hs,mem_univ x⟩)

/-- The actual constructed profile is strictly positive throughout the closed strip
for bounded continuous velocity and bounded smooth potential. -/
theorem forcedBurgersProfile_pos {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M)
    (ht : t ∈ Icc 0 T) (a x : ℝ) : 0 < forcedBurgersProfile ν q u₀ a t x := by
  obtain ⟨hqs,hqc,hqb⟩ := potential_spatial_data hq hb 2
  exact potentialHeatSolution_pos hν hqs hqc hqb (initialHeatProfile_contDiff hu ν a).continuous
    (initialHeatProfile_hasExpGrowth hub hν a) (initialHeatProfile_pos ν u₀ a) ht x

/-- The actual forced Burgers field is jointly continuous through initial and terminal
 time. Continuous bounded initial velocity suffices, even with spatial cusps. -/
theorem forcedBurgersSolution_continuousOn {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a : ℝ) :
    ContinuousOn (Function.uncurry (forcedBurgersSolution ν q u₀ a)) (Icc 0 T ×ˢ univ) := by
  obtain ⟨_,_,hqb⟩ := potential_spatial_data hq hb 0
  obtain ⟨Q,hQb⟩ := hqb 0 le_rfl
  simp only [iteratedDeriv_zero] at hQb
  have hQ : 0 ≤ Q := (abs_nonneg _).trans (hQb 0 ⟨le_rfl,hT⟩ 0)
  have hf := initialHeatProfile_contDiff hu ν a
  have hfg := initialHeatProfile_hasExpGrowth hub hν a
  have hc := potentialHeatSolution_continuousOn hν.le hT hq.continuous.continuousOn
    hQ hQb hf.continuous hfg
  have hdc := potentialHeatSolution_deriv_continuousOn_of_contDiff hν hT
    hq.continuous.continuousOn hQ hQb hf hfg (initialHeatProfile_deriv_hasExpGrowth hu hub hν a)
  exact continuousOn_const.mul (hdc.div hc
    (fun p hp => ne_of_gt (forcedBurgersProfile_pos hν hu hub hq hb hp.1 a p.2)))

/-- The actual constructed velocity is jointly smooth at positive interior times.
No smoothness of the initial velocity is assumed. -/
theorem forcedBurgersSolution_contDiffOn {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (forcedBurgersSolution ν q u₀ a)) (Ioo 0 T ×ˢ univ) := by
  have hf := (initialHeatProfile_contDiff hu ν a).continuous
  have hfg := initialHeatProfile_hasExpGrowth hub hν a
  have hc := potentialHeatSolution_contDiffOn hν hq hb hf hfg
  have hd := potentialHeatSolution_iteratedDeriv_contDiffOn hν hq hb hf hfg 1
  simp only [iteratedDeriv_one] at hd
  exact contDiffOn_const.mul (hd.div hc
    (fun p hp => ne_of_gt (forcedBurgersProfile_pos hν hu hub hq hb ⟨hp.1.1.le,hp.1.2.le⟩ a p.2)))

/-- The actual constructed solution satisfies the forced Burgers equation at every
positive interior time, with forcing exactly `-2 * ν * ∂x q`. -/
theorem forcedBurgersSolution_forced_burgers
    {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M)
    (ht : t ∈ Ioo 0 T) (a x : ℝ) :
    deriv (fun s => forcedBurgersSolution ν q u₀ a s x) t +
      forcedBurgersSolution ν q u₀ a t x * deriv (forcedBurgersSolution ν q u₀ a t) x -
      ν * iteratedDeriv 2 (forcedBurgersSolution ν q u₀ a t) x = -2 * ν * deriv (q t) x := by
  have hf := (initialHeatProfile_contDiff hu ν a).continuous
  have hfg := initialHeatProfile_hasExpGrowth hub hν a
  have hc := potentialHeatSolution_contDiffOn hν hq hb hf hfg
  have hqs := (potential_spatial_data hq hb 1).1 t ⟨ht.1.le,ht.2.le⟩
  apply OnInterval.classicalTransform_forced_burgers isOpen_Ioo isOpen_univ ν
    (forcedBurgersProfile ν q u₀ a) q (hc.of_le (by simp)) t x ht (mem_univ x)
    (ne_of_gt (forcedBurgersProfile_pos hν hu hub hq hb ⟨ht.1.le,ht.2.le⟩ a x))
    (hqs.differentiable (by norm_num) x)
  have he : forcedBurgersProfile ν q u₀ a t =
      potentialHeatSolution ν q (initialHeatProfile ν u₀ a) t := rfl
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [he, forcedBurgersProfile,iteratedDeriv_succ,iteratedDeriv_zero] using
      (potentialHeatSolution_hasDerivAt_time_of_contDiff hν hq hb hf hfg ht y).deriv)

/-- The actual velocity has the prescribed joint initial trace from the closed strip. -/
theorem forcedBurgersSolution_tendsto_initial
    {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a x : ℝ) :
    Tendsto (Function.uncurry (forcedBurgersSolution ν q u₀ a))
      (𝓝[Icc 0 T ×ˢ univ] (0,x)) (𝓝 (u₀ x)) := by
  have hc := forcedBurgersSolution_continuousOn hν hT hu hub hq hb a
    (0,x) ⟨⟨le_rfl,hT⟩,mem_univ x⟩
  simpa only [Function.uncurry_apply_pair,forcedBurgersSolution_initial hu hν.ne'] using hc.tendsto

end ColeHopf

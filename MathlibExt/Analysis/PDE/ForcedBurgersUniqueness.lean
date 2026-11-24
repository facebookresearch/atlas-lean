/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.InitialForcedInverseColeHopf
public import MathlibExt.Analysis.PDE.ForcedBurgersBounds
import MathlibExt.Analysis.Calculus.IteratedDerivPartial
import Mathlib.Tactic.FunProp

/-!
# Bounded classical uniqueness for forced Burgers

A bounded velocity solving forced Burgers on a finite strip equals the actual
potential-heat construction. The competitor class uses closed-strip continuity,
spatial C2 slices and a continuous actual first time derivative in the interior.
It contains the usual bounded C1,2 class and requires no mixed or second time
derivatives. Its inverse profile is identified by potential-heat uniqueness;
spatial differentiation recovers the velocity even at the strip endpoints.

For smooth potentials with uniformly bounded Frechet jets on the strip, the
actual constructed velocity belongs to this class. Thus the uniqueness theorem
applies to an explicitly constructed solution, not an assumed solution.
Equality is asserted only on the strip: exterior values remain unrestricted.

The transform background is Gesztesy and Holden, *The Cole–Hopf and Miura
transformations revisited*, Theorem 3.3 and Remark 3.4,
https://arxiv.org/abs/solv-int/9812025. Uniqueness uses whole-line potential-heat
comparison in the uniform exponential-growth class.
-/

@[expose] public section

open Set Real
open scoped ContDiff Topology
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- Bounded forced Burgers solutions on a finite strip, with actual derivatives.
The velocity is continuous on the closed strip, has C2 spatial slices and a
continuous actual first time derivative in the interior, solves the PDE there,
and has the prescribed initial trace and one uniform velocity bound. No mixed
or second time derivative, nor regularity outside the strip, is required. -/
structure IsBoundedForcedBurgersSolutionOn (ν : ℝ) (q : ℝ → ℝ → ℝ)
    (u₀ : ℝ → ℝ) (T : ℝ) (u : ℝ → ℝ → ℝ) : Prop where
  /-- Joint continuity includes both time endpoints. -/
  continuousOn : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ)
  /-- Each interior spatial slice is twice continuously differentiable. -/
  contDiff_space : ∀ t ∈ Ioo 0 T, ContDiff ℝ 2 (u t)
  /-- The ordinary first time derivative exists at every interior point. -/
  differentiable_time : ∀ t ∈ Ioo 0 T, ∀ x, DifferentiableAt ℝ (fun s => u s x) t
  /-- The actual first time derivative is jointly continuous in the interior. -/
  continuousOn_timeDeriv : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => u s p.2) p.1)
    (Ioo 0 T ×ˢ univ)
  /-- The actual derivative fields satisfy forced Burgers at interior times. -/
  equation : ∀ t ∈ Ioo 0 T, ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
    ν * iteratedDeriv 2 (u t) x - 2 * ν * deriv (q t) x
  /-- Initial velocity equals the prescribed datum. -/
  initial : ∀ x, u 0 x = u₀ x
  /-- One constant bounds velocity on the entire closed strip. -/
  bounded : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M

namespace IsBoundedForcedBurgersSolutionOn

private theorem continuous_slice {u q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T t : ℝ}
    (hu : IsBoundedForcedBurgersSolutionOn ν q u₀ T u) (ht : t ∈ Icc 0 T) :
    Continuous (u t) := by
  rw [← continuousOn_univ]
  exact hu.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hy => ⟨ht,hy⟩)

/-- The normalized inverse profile of a bounded competitor is the actual
potential-heat evolution of its initial exponential primitive. Finite spatial C2
potential regularity suffices; no mild representation is assumed. -/
theorem inverseProfile_eq {u q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hu : IsBoundedForcedBurgersSolutionOn ν q u₀ T u)
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
    initialForcedInverseProfile ν u q a t x = forcedBurgersProfile ν q u₀ a t x := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl,hT⟩
  have he : u 0 = u₀ := funext hu.initial
  have hc0 : Continuous u₀ := he ▸ hu.continuous_slice h0
  have hb0 : ∃ M, ∀ x, |u₀ x| ≤ M := by
    obtain ⟨M,hM⟩ := hu.bounded
    exact ⟨M,fun x => by rw [← hu.initial x]; exact hM 0 h0 x⟩
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero,Function.uncurry_def] using hqc 0 (by omega)
  apply eq_potentialHeatSolution_of_exp_growth hν hqs hqc hqb
    (initialHeatProfile_contDiff hc0 ν a).continuous (initialHeatProfile_hasExpGrowth hb0 hν a)
    (initialForcedInverseProfile_continuousOn hT hu.continuousOn hq ν a)
    (fun t ht x =>
      (initialForcedInverseProfile_contDiff_space (hu.contDiff_space t ht) ν a).contDiffAt)
    (fun t ht x => initialForcedInverseProfile_hasDerivAt_potential hu.continuousOn hq
      hu.continuousOn_timeDeriv hu.differentiable_time (hu.contDiff_space t ht)
      ((hqs t ⟨ht.1.le,ht.2.le⟩).differentiable (by norm_num)) ht (hu.equation t ht) hν.ne' a x)
    (fun _ _ _ => rfl)
    (initialForcedInverseProfile_hasExpGrowthOnStrip hT hu.continuousOn hq hu.bounded ν a)
  intro x
  simp only [initialForcedInverseProfile_zero,he]

/-- Every bounded classical competitor equals the actual forced Burgers solution
throughout the closed strip, including both endpoints. The uniqueness class
requires no mixed or second time derivative of the velocity. -/
theorem eq_forcedBurgersSolution {u q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hu : IsBoundedForcedBurgersSolutionOn ν q u₀ T u)
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x, u t x = forcedBurgersSolution ν q u₀ a t x := by
  intro t ht x
  have he : initialForcedInverseProfile ν u q a t = forcedBurgersProfile ν q u₀ a t :=
    funext (hu.inverseProfile_eq hν hT hqs hqc hqb a t ht)
  rw [← classicalTransform_initialForcedInverseProfile (q := q) (hu.continuous_slice ht) hν.ne' a x]
  simp only [forcedBurgersSolution,classicalTransform,he]

/-- Smooth bounded-jet potentials specialize the finite-regularity uniqueness
result to the hypotheses of the actual initial-value construction. -/
theorem eq_forcedBurgersSolution_of_contDiff
    {u q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hu : IsBoundedForcedBurgersSolutionOn ν q u₀ T u)
    (hν : 0 < ν) (hT : 0 ≤ T) (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a : ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x, u t x = forcedBurgersSolution ν q u₀ a t x := by
  apply hu.eq_forcedBurgersSolution hν hT ?_ ?_ ?_ a
  · intro s hs
    have h : ContDiff ℝ ∞ (q s) := by
      simpa only [Function.comp_def,Function.uncurry_def,id_eq] using
        hq.comp (contDiff_const.prodMk contDiff_id)
    exact h.of_le (by simp)
  · intro k hk
    exact (hq.contDiff_iteratedDeriv_snd k).continuous.continuousOn
  · intro k hk
    obtain ⟨M,hM⟩ := hb k
    refine ⟨M,fun s hs x => ?_⟩
    have h : |iteratedDeriv k (q s) x| ≤
        ‖iteratedFDeriv ℝ k (Function.uncurry q) (s,x)‖ := by
      simpa only [Real.norm_eq_abs] using
        (hq.of_le (by simp : (k : WithTop ℕ∞) ≤ ∞)).norm_iteratedDeriv_snd_le (s,x)
    exact h.trans (hM (s,x) ⟨hs,mem_univ x⟩)

end IsBoundedForcedBurgersSolutionOn

/-- The actual constructed velocity belongs to the bounded classical uniqueness
class for smooth potentials with uniformly bounded Frechet jets on the strip.
Only bounded continuous initial velocity is needed, with no initial derivatives
or bounded primitive. -/
theorem forcedBurgersSolution_isBoundedForcedBurgersSolutionOn
    {q : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hu : Continuous u₀) (hub : ∃ M, ∀ x, |u₀ x| ≤ M)
    (hq : ContDiff ℝ ∞ (Function.uncurry q))
    (hb : ∀ n : ℕ, ∃ M, ∀ p ∈ Icc 0 T ×ˢ (univ : Set ℝ),
      ‖iteratedFDeriv ℝ n (Function.uncurry q) p‖ ≤ M) (a : ℝ) :
    IsBoundedForcedBurgersSolutionOn ν q u₀ T (forcedBurgersSolution ν q u₀ a) := by
  have hs := forcedBurgersSolution_contDiffOn hν hu hub hq hb a
  refine ⟨forcedBurgersSolution_continuousOn hν hT hu hub hq hb a,?_,?_,?_,?_,
    forcedBurgersSolution_initial hu hν.ne' q a,
    forcedBurgersSolution_boundedOnStrip hν hT hu hub hq hb a⟩
  · intro t ht
    rw [contDiff_iff_contDiffAt]
    intro x
    have hp : ContDiffAt ℝ ∞ (Function.uncurry (forcedBurgersSolution ν q u₀ a)) (t,x) :=
      hs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    exact (hp.comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  · intro t ht x
    exact (OnInterval.time_derivative isOpen_Ioo isOpen_univ hs (by simp) t x ht
      (mem_univ x)).differentiableAt
  · simpa only [Function.uncurry_def] using
      (OnInterval.contDiffOn_timeDeriv (m := 0) isOpen_Ioo isOpen_univ hs
        (by simp) (by simp)).continuousOn
  · intro t ht x
    have he := forcedBurgersSolution_forced_burgers hν hu hub hq hb ht a x
    linarith

end ColeHopf

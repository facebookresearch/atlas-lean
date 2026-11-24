/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.PotentialHeatComparison
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Time-only gauges for the actual potential-heat evolution

Adding a continuous time-only potential multiplies the actual Volterra solution
by the exponential of its time integral. The proof identifies the product using
classical potential-heat uniqueness, after proving its actual derivatives,
initial values and uniform exponential growth. Finite spatial C2 regularity of
the original potential suffices; the time-only correction needs only continuity
on the finite closed strip.

This is the scalar integrating-factor identity underlying the normalization in
Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Theorem 3.3 and Remark 3.4, https://arxiv.org/abs/solv-int/9812025.
-/

@[expose] public section

open Set Real MeasureTheory
open scoped ContDiff Topology Interval
open MathlibExt.Analysis MathlibExt.Analysis.PDE.HeatWholeLine

namespace MathlibExt.Analysis.PDE.HeatKernel

private theorem primitive_continuousOn {r : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hr : ContinuousOn r (Icc 0 T)) :
    ContinuousOn (fun t => ∫ s in 0..t, r s) (Icc 0 T) := by
  simpa only [uIcc_of_le hT] using
    intervalIntegral.continuousOn_primitive_interval' (hr.intervalIntegrable_of_Icc hT)
      (show (0 : ℝ) ∈ uIcc 0 T from left_mem_uIcc)

private theorem primitive_hasDerivAt {r : ℝ → ℝ} {T t : ℝ}
    (hr : ContinuousOn r (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun t => ∫ s in 0..t, r s) (r t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hr.mono (fun s (hs : s ∈ Icc 0 t) =>
      ⟨hs.1,hs.2.trans ht.2.le⟩)).intervalIntegrable_of_Icc ht.1.le)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hr.mono Ioo_subset_Icc_self) t ht)
    (hr.continuousAt (Icc_mem_nhds ht.1 ht.2))

private theorem shifted_spatial_data {q : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {T : ℝ}
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hr : ContinuousOn r (Icc 0 T)) :
    (∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x => q s x+r s)) ∧
    (∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ =>
      iteratedDeriv k (fun x => q p.1 x+r p.1) p.2) (Icc 0 T ×ˢ univ)) ∧
    (∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x,
      |iteratedDeriv k (fun y => q s y+r s) x| ≤ M) := by
  have he (k : ℕ) (hk : k ≠ 0) (s x : ℝ) :
      iteratedDeriv k (fun y => q s y+r s) x = iteratedDeriv k (q s) x := by
    simpa only [add_comm] using
      iteratedDeriv_const_add (f := q s) (x := x) (Nat.pos_of_ne_zero hk) (r s)
  refine ⟨fun s hs => (hqs s hs).add contDiff_const,?_,?_⟩
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa only [iteratedDeriv_zero,Pi.add_apply,Function.comp_def] using!
        (hqc 0 hk).add (hr.comp continuousOn_fst (fun p hp => hp.1))
    · simpa only [he k hk0] using hqc k hk
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      obtain ⟨Q,hQ⟩ := hqb 0 hk
      obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
      refine ⟨Q+R,fun s hs x => ?_⟩
      simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using
        (abs_add_le (q s x) (r s)).trans (add_le_add (hQ s hs x) (hR s hs))
    · simpa only [he k hk0] using hqb k hk

/-- Adding a continuous time-only potential rescales the actual potential-heat
solution by its positive time-integrating factor on the entire closed strip.
Only finite spatial C2 regularity is assumed of the original potential. -/
theorem potentialHeatSolution_add_time_potential
    {q : ℝ → ℝ → ℝ} {g r : ℝ → ℝ} {ν T t : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hqs : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (q s))
    (hqc : ∀ k ≤ 2, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv k (q p.1) p.2)
      (Icc 0 T ×ˢ univ))
    (hqb : ∀ k ≤ 2, ∃ M, ∀ s ∈ Icc 0 T, ∀ x, |iteratedDeriv k (q s) x| ≤ M)
    (hg : Continuous g) (hgg : HasExpGrowth g) (hr : ContinuousOn r (Icc 0 T))
    (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν (fun s y => q s y+r s) g t x =
      exp (∫ s in 0..t, r s) * potentialHeatSolution ν q g t x := by
  let H : ℝ → ℝ := fun s => exp (∫ τ in 0..s, r τ)
  have hH : ContinuousOn H (Icc 0 T) := (primitive_continuousOn hT hr).rexp
  have hHd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt H (r s*H s) s := by
    simpa only [H,mul_comm] using (primitive_hasDerivAt hr hs).exp
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) := by
    simpa only [iteratedDeriv_zero,Function.uncurry_def] using hqc 0 (by omega)
  obtain ⟨Q,hQ⟩ := hqb 0 (by omega)
  simp only [iteratedDeriv_zero] at hQ
  have hQ0 : 0 ≤ Q := (abs_nonneg _).trans (hQ 0 ⟨le_rfl,hT⟩ 0)
  have hc := potentialHeatSolution_continuousOn hν.le hT hq hQ0 hQ hg hgg
  have hspace (s : ℝ) (hs : s ∈ Ioo 0 T) :
      ContDiff ℝ 2 (potentialHeatSolution ν q g s) :=
    potentialHeatSolution_contDiff_space hν hqs hqc hqb hg hgg ⟨hs.1,hs.2.le⟩
  have hgrowth : HasExpGrowthOnStrip (fun s y => H s*potentialHeatSolution ν q g s y) T := by
    obtain ⟨M,c,hM,hc0,hb⟩ := potentialHeatSolution_hasExpGrowthOnStrip hν.le hq hQ0 hQ hg hgg
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl,hT⟩)
    refine ⟨C*M,c,mul_nonneg hC0 hM,hc0,fun s hs y => ?_⟩
    rw [abs_mul,mul_assoc]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC s hs)
      (hb s hs y) (abs_nonneg _) hC0
  obtain ⟨hsq,hcq,hbq⟩ := shifted_spatial_data hqs hqc hqb hr
  have he := eq_potentialHeatSolution_of_exp_growth
    (u := fun s y => H s*potentialHeatSolution ν q g s y) hν hsq hcq hbq hg hgg
    ((hH.comp continuousOn_fst (fun p (hp : p ∈ Icc 0 T ×ˢ (univ : Set ℝ)) => hp.1)).mul hc)
    (fun s hs y => (contDiff_const.mul (hspace s hs)).contDiffAt)
    (ut := fun s y => ν*iteratedDeriv 2 (fun z => H s*potentialHeatSolution ν q g s z) y +
      (q s y+r s)*(H s*potentialHeatSolution ν q g s y))
    (fun s hs y => ?_) (fun _ _ _ => rfl) hgrowth (fun y => by simp [H]) t ht x
  · exact he.symm
  · have hd := (hHd s hs).mul (potentialHeatSolution_hasDerivAt_time hν hqs hqc hqb hg hgg hs y)
    convert hd using 1
    rw [iteratedDeriv_const_mul_field]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    ring

end MathlibExt.Analysis.PDE.HeatKernel

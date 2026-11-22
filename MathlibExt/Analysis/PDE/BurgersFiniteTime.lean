/-
Copyright (c) 2025–2026 the contributors.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.FiniteInverseColeHopf
public import MathlibExt.Analysis.PDE.BurgersUniqueness

/-!
# Finite-lifespan Burgers uniqueness

A bounded velocity continuous on `[0,T] × ℝ`, jointly `C²` and solving Burgers
only on `(0,T) × ℝ`, equals the explicit solution throughout the closed strip.
No differentiability or PDE is required at the endpoints, and no assumptions
are imposed outside the strip. The terminal trace follows by continuity of the
inverse heat profile.
-/

@[expose] public section

open Set
open scoped ContDiff
open MathlibExt.Analysis.PDE.HeatKernel

namespace ColeHopf

/-- The finite-lifespan inverse profile equals heat evolution, including the terminal trace. -/
theorem initialInverseProfile_eq_heatSolution_finite {u : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
      initialInverseProfile ν u a t x = heatSolution (initialHeatProfile ν (u 0) a) (ν * t) x := by
  have h0 : Continuous (u 0) := by
    rw [← continuousOn_univ]
    exact hc.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hx => ⟨⟨le_rfl, hT⟩, hx⟩)
  have hb0 : ∃ M, ∀ x, |u 0 x| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, hM 0 ⟨le_rfl, hT⟩⟩
  have hf := (initialHeatProfile_contDiff h0 ν a).continuous
  have hg := initialHeatProfile_hasExpGrowth hb0 hν a
  have hcont := initialInverseProfile_continuousOn_finite hT hc ν a
  have hgrowth := initialInverseProfile_hasExpGrowthOnStrip_finite hT hc hb ν a
  have hint {s : ℝ} (hs : s ∈ Ioo 0 T) : ∀ x,
      initialInverseProfile ν u a s x = heatSolution (initialHeatProfile ν (u 0) a) (ν * s) x := by
    have hsub : Icc 0 s ⊆ Icc 0 T := fun _ ht => ⟨ht.1, ht.2.trans hs.2.le⟩
    have hgs : MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip
        (initialInverseProfile ν u a) s := by
      obtain ⟨M, c, hM, hc', hh⟩ := hgrowth
      exact ⟨M, c, hM, hc', fun t ht x => hh t (hsub ht) x⟩
    have hh := eq_heatSolution_of_exp_growth hν hf hg
      (hcont.mono (fun _ hp => ⟨hsub hp.1, hp.2⟩))
      (fun t ht x => ?_)
      (fun t ht x => (initialInverseProfile_hasDerivAt_heat_finite hc hu
        ⟨ht.1, ht.2.trans_lt hs.2⟩ (hpde t ⟨ht.1, ht.2.trans_lt hs.2⟩)
        hν.ne' a x).hasDerivWithinAt)
      (fun _ _ _ => rfl) hgs (initialInverseProfile_zero ν u a)
    · exact hh s ⟨hs.1.le, le_rfl⟩
    · have hslice : ContDiff ℝ 2 (u t) := by
        rw [← contDiffOn_univ]
        exact hu.comp (contDiffOn_const.prodMk contDiffOn_id)
          (fun _ hx => ⟨⟨ht.1, ht.2.trans_lt hs.2⟩, hx⟩)
      exact (initialInverseProfile_contDiff_space hslice ν a).contDiffAt
  intro t ht x
  rcases hT.eq_or_lt with hT | hT
  · have ht0 : t = 0 := by
      exact le_antisymm (ht.2.trans_eq hT.symm) ht.1
    subst t
    simp only [initialInverseProfile_zero, mul_zero, heatSolution_zero]
  · have he : EqOn (fun s => initialInverseProfile ν u a s x)
        (fun s => heatSolution (initialHeatProfile ν (u 0) a) (ν * s) x) (Ioo 0 T) :=
      fun _ hs => hint hs x
    have hleft : ContinuousOn (fun s => initialInverseProfile ν u a s x) (Icc 0 T) :=
      hcont.comp (f := fun s : ℝ => (s, x))
        (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, mem_univ _⟩)
    have hright : Continuous (fun s => heatSolution (initialHeatProfile ν (u 0) a) (ν * s) x) :=
      (heatSolution_continuous_of_exp_growth hf hg).comp (f := fun s : ℝ => (ν * s, x))
        ((continuous_const.mul continuous_id).prodMk continuous_const)
    exact he.of_subset_closure hleft hright.continuousOn
      Ioo_subset_Icc_self (by rw [closure_Ioo (ne_of_lt hT)]) ht

/-- Every bounded classical competitor on a finite strip is the explicit Burgers solution. -/
theorem eq_burgersSolution_finite {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x, u t x = burgersSolution ν (u 0) a t x := by
  intro t ht x
  have hh := initialInverseProfile_eq_heatSolution_finite hν (ht.1.trans ht.2) hc hu hb hpde a
  have hs : Continuous (u t) := by
    rw [← continuousOn_univ]
    exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨ht, hx⟩)
  have he : initialInverseProfile ν u a t = heatSolution (initialHeatProfile ν (u 0) a) (ν * t) :=
    funext (hh t ht)
  rw [← classicalTransform_initialInverseProfile hs hν.ne' a x]
  change -2 * ν * (deriv (initialInverseProfile ν u a t) x / initialInverseProfile ν u a t x) =
    -2 * ν * (deriv (heatSolution (initialHeatProfile ν (u 0) a) (ν * t)) x /
      heatSolution (initialHeatProfile ν (u 0) a) (ν * t) x)
  rw [he]

/-- Equal initial values determine the same bounded classical solution on a closed strip. -/
theorem burgers_eq_finite {u v : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ 2 (Function.uncurry v) (Ioo 0 T ×ˢ univ))
    (hbu : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hbv : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M)
    (hpu : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (hpv : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => v s x) t + v t x * deriv (v t) x = ν * iteratedDeriv 2 (v t) x)
    (h0 : ∀ x, u 0 x = v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x = v t x := by
  intro t ht x
  rw [eq_burgersSolution_finite hν hcu hu hbu hpu 0 t ht x,
    eq_burgersSolution_finite hν hcv hv hbv hpv 0 t ht x, funext h0]

end ColeHopf

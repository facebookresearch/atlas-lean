/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Smooth pullback of real differential forms

The pointwise pullback of a smooth real form along a smooth map is smooth
in the chart-normalized form model.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms AnalyticCyclePairings
open Set Filter ContinuousAlternatingMap
open scoped Manifold ContDiff Topology

private theorem smoothPrecomp (n d p : ℕ)
    (a : Coordinates d → Coordinates n [⋀^Fin p]→L[ℝ] ℝ)
    (b : Coordinates d → Coordinates d →L[ℝ] Coordinates n) (z : Coordinates d)
    (ha : ContDiffAt ℝ ∞ a z) (hb : ContDiffAt ℝ ∞ b z) :
    ContDiffAt ℝ ∞ (fun x ↦ (a x).compContinuousLinearMap (b x)) z := by
  induction p with
  | zero =>
    have h := (constOfIsEmptyLIE ℝ (Coordinates d) ℝ (Fin 0)).contDiff.contDiffAt.comp z
      (ha.continuousLinearMap_comp (apply ℝ (Coordinates n) ℝ 0))
    convert h using 1
    ext x v
    change (a x) ((b x) ∘ v) = (a x) 0
    congr 1
    exact Subsingleton.elim _ _
  | succ p ih =>
    have h : ContDiffAt ℝ ∞
        (fun x ↦ ((a x).compContinuousLinearMap (b x)).curryLeft) z := by
      apply contDiffWithinAt_clm_apply.mpr
      intro v
      have hd := ih (fun x ↦ (a x).curryLeft (b x v))
        ((ha.continuousLinearMap_comp curryLeftLI.toContinuousLinearMap).clm_apply
          (hb.clm_apply contDiffAt_const))
      simpa only [curryLeft_compContinuousLinearMap] using hd.contDiffWithinAt
    have h' := h.continuousLinearMap_comp
      (alternatizeUncurryFinCLM ℝ (Coordinates d) ℝ)
    have h'' := h'.const_smul ((p + 1 : ℝ)⁻¹)
    convert h'' using 1
    ext x
    simp only [Function.comp_def, alternatizeUncurryFinCLM_apply,
      alternatizeUncurryFin_curryLeft]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [inv_mul_cancel₀ (by positivity : (p : ℝ) + 1 ≠ 0)]

end MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

namespace WantedExt.AlgebraicGeometry.AnalyticCyclePairingsWanted

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms AnalyticCyclePairings
open Set Filter ContinuousAlternatingMap
open scoped Manifold ContDiff Topology

/-- The pullback of a smooth form along a smooth map is smooth. -/
public theorem pullbackTheory (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    (d : ℕ) (Y : Type) [TopologicalSpace Y] [ChartedSpace (Coordinates d) Y]
    [IsManifold 𝓘(ℝ, Coordinates d) ∞ Y] (f : Y → M)
    (hf : ContMDiff 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n) ∞ f) :
    PullbackTheory n M d Y f := by
  constructor
  intro p a y z hz
  have hz' : z ∈ (extChartAt 𝓘(ℝ, Coordinates d) y).target := hz.1
  let s := (extChartAt 𝓘(ℝ, Coordinates d) y).symm
  let x := f (s z)
  let t := extChartAt 𝓘(ℝ, Coordinates n) x
  let g := f ∘ s
  let F := t ∘ g
  have hs : ContMDiffAt 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates d) ∞ s z :=
    (contMDiffWithinAt_extChartAt_symm_target y hz').contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hz')
  have hg : ContMDiffAt 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n) ∞ g z :=
    (hf (s z)).comp z hs
  have hF : ContDiffAt ℝ ∞ F z :=
    (contMDiffAt_extChartAt.comp z hg).contDiffAt
  have htz : F z ∈ chartDomain ℝ (Coordinates n) M ⊤ x := by
    exact ⟨mem_extChartAt_target x, Set.mem_univ _⟩
  have ha : ContDiffAt ℝ ∞ (chartForm ℝ (Coordinates n) M a.val x) (F z) :=
    (a.property x (F z) htz).contDiffAt (by
      simpa only [chartDomain, TopologicalSpace.Opens.coe_top, preimage_univ, inter_univ] using
        (isOpen_extChartAt_target x).mem_nhds htz.1)
  have h := smoothPrecomp n d p
    (chartForm ℝ (Coordinates n) M a.val x ∘ F) (fderiv ℝ F) z
    (ha.comp z hF) (hF.fderiv_right (by simp))
  apply (h.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hsource : ∀ᶠ w in 𝓝 z, w ∈ (extChartAt 𝓘(ℝ, Coordinates d) y).target :=
    (isOpen_extChartAt_target y).mem_nhds hz'
  have htarget : ∀ᶠ w in 𝓝 z, g w ∈ t.source :=
    hg.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds x)
  filter_upwards [hsource, htarget] with w hw hv
  have hw' : w ∈ chartDomain ℝ (Coordinates d) Y ⊤ y := ⟨hw, Set.mem_univ _⟩
  have hv' : F w ∈ chartDomain ℝ (Coordinates n) M ⊤ x :=
    ⟨t.map_source hv, Set.mem_univ _⟩
  have hsw : MDifferentiableAt 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates d) s w :=
    ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) y hw).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hw)).mdifferentiableAt (by simp)
  have hgw : MDifferentiableAt 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n) g w :=
    (hf.mdifferentiable (by simp) (s w)).comp w hsw
  have htw : MDifferentiableAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n) t (g w) :=
    mdifferentiableAt_extChartAt (by simpa only [t, extChartAt_source] using hv)
  have hder : fderiv ℝ F w =
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n) t (g w)).comp
        ((mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n) f (s w)).comp
          (mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates d) s w)) := by
    have h1 := mfderiv_comp w htw hgw
    have h2 := mfderiv_comp w (hf.mdifferentiable (by simp) (s w)) hsw
    rw [mfderiv_eq_fderiv] at h1
    change fderiv ℝ F w = _ at h1
    rw [h2] at h1
    exact h1
  have hcancel :
      (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n) t.symm (F w)).comp
        (mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n) t (g w)) =
        ContinuousLinearMap.id ℝ (Coordinates n) := by
    have hc := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hv
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hc
    exact hc
  ext v
  simp only [Function.comp_apply, chartForm, dite_eq_left hw', dite_eq_left hv',
    pullbackRough, compContinuousLinearMap_apply]
  change a.val ⟨g w, _⟩
      (fun i ↦ mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n) f (s w)
        (mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates d) s w (v i))) =
    a.val ⟨t.symm (F w), _⟩
      (fun i ↦ mfderiv 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates n) t.symm (F w)
        (fderiv ℝ F w (v i)))
  erw [t.left_inv hv, hder]
  congr 1
  funext i
  exact (congrArg (fun L ↦ L (((mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n)
    f (s w)).comp (mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates d) s w)) (v i)))
      hcancel).symm

end WantedExt.AlgebraicGeometry.AnalyticCyclePairingsWanted

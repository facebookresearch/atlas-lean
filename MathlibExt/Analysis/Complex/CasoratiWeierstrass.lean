/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

open Set Metric Filter Topology

namespace MathlibExt.Analysis.Complex.CasoratiWeierstrass

/--
**Casorati–Weierstrass theorem.** Let $c \in \mathbb{C}$, $r > 0$, and let
$f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the punctured disc $0 < |z - c| < r$ and not
meromorphic at $c$ (that is, $c$ is neither a removable singularity nor a pole of $f$). Then the
image of the punctured disc $0 < |z - c| < r$ under $f$ is dense in $\mathbb{C}$.

Source: L. V. Ahlfors, Complex Analysis, 3rd ed., isolated singularities.
Proves `Wanted` entry `casoratiWeierstrass`.
-/
theorem casoratiWeierstrass
    {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r \ {c}))
    (hess : ¬ MeromorphicAt f c) :
    Dense (f '' (Metric.ball c r \ {c})) := by
  by_contra hnd
  obtain ⟨w, hw⟩ : ∃ w, w ∉ closure (f '' (Metric.ball c r \ {c})) := by
    by_contra hcon
    push Not at hcon
    exact hnd hcon
  have hfar : ∃ ε > 0, ∀ b ∈ f '' (Metric.ball c r \ {c}), ε ≤ dist w b := by
    by_contra hcon
    push Not at hcon
    rw [Metric.mem_closure_iff] at hw
    exact hw hcon
  obtain ⟨ε, hε, hball⟩ := hfar
  have hnorm_le : ∀ z ∈ Metric.ball c r \ {c}, ε ≤ ‖f z - w‖ := by
    intro z hz
    have hmem : f z ∈ f '' (Metric.ball c r \ {c}) := ⟨z, hz, rfl⟩
    have hle : ε ≤ dist w (f z) := hball _ hmem
    rw [dist_eq_norm, norm_sub_rev] at hle
    exact hle
  have hne : ∀ z ∈ Metric.ball c r \ {c}, f z - w ≠ 0 := by
    intro z hz
    have hpos : 0 < ‖f z - w‖ := lt_of_lt_of_le hε (hnorm_le z hz)
    exact norm_ne_zero_iff.mp (ne_of_gt hpos)
  have hsub : DifferentiableOn ℂ (fun z => f z - w) (Metric.ball c r \ {c}) :=
    hf.sub_const w
  have hginv : DifferentiableOn ℂ ((fun z => f z - w)⁻¹) (Metric.ball c r \ {c}) :=
    hsub.inv hne
  have hbdd : BddAbove (norm ∘ ((fun z => f z - w)⁻¹) '' (Metric.ball c r \ {c})) := by
    refine ⟨ε⁻¹, ?_⟩
    rw [mem_upperBounds]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    change ‖(f z - w)⁻¹‖ ≤ ε⁻¹
    rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hε (hnorm_le z hz)
  have hG : DifferentiableOn ℂ
      (Function.update ((fun z => f z - w)⁻¹) c
        (limUnder (𝓝[≠] c) ((fun z => f z - w)⁻¹)))
      (Metric.ball c r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hr) hginv hbdd
  have hGan : AnalyticAt ℂ (Function.update ((fun z => f z - w)⁻¹) c
      (limUnder (𝓝[≠] c) ((fun z => f z - w)⁻¹))) c :=
    hG.analyticAt (Metric.ball_mem_nhds c hr)
  have hGmer : MeromorphicAt (Function.update ((fun z => f z - w)⁻¹) c
      (limUnder (𝓝[≠] c) ((fun z => f z - w)⁻¹))) c :=
    hGan.meromorphicAt
  have hGinv : MeromorphicAt ((Function.update ((fun z => f z - w)⁻¹) c
      (limUnder (𝓝[≠] c) ((fun z => f z - w)⁻¹)))⁻¹) c :=
    hGmer.inv
  have hcongr : (Function.update ((fun z => f z - w)⁻¹) c
      (limUnder (𝓝[≠] c) ((fun z => f z - w)⁻¹)))⁻¹ =ᶠ[𝓝[≠] c] (fun z => f z - w) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzne : z ≠ c := by simpa using hz
    rw [Pi.inv_apply, Function.update_of_ne hzne _ _]
    change ((f z - w)⁻¹)⁻¹ = f z - w
    exact inv_inv _
  have hsubmer : MeromorphicAt (fun z => f z - w) c :=
    (MeromorphicAt.meromorphicAt_congr hcongr).mp hGinv
  have hfmer : MeromorphicAt f c := by
    have hconst : MeromorphicAt (fun _ : ℂ => w) c := MeromorphicAt.const w c
    have hadd := hsubmer.add hconst
    have heq : (fun z => f z - w) + (fun _ : ℂ => w) = f := by
      funext z
      simp [Pi.add_apply, sub_add_cancel]
    rwa [heq] at hadd
  exact hess hfmer

end MathlibExt.Analysis.Complex.CasoratiWeierstrass

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Complex.AnalyticL2.Submodule
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Closedness from compact-set analytic L2 estimates

Let `G` be open in the complex plane and use planar volume restricted to
`G`. Suppose that on every compact `K ⊆ G` there is a positive real
constant `C` such that all analytic representatives `g,k` of L2 classes
`f,h` satisfy `|g(z)-k(z)| ≤ C ‖f-h‖₂` on `K`. Then the submodule of
analytic-representative L2 classes is closed in the original restricted-
volume L2 norm. The constant may depend on `K`; the estimate quantifies
over every pair of classes and representatives. Empty and unbounded open
domains are allowed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace AnalyticL2

/-- A positive uniform analytic difference estimate on every compact subset of an open domain makes
its restricted-volume analytic L2 submodule closed.

```lean
theorem isClosed_of_local_bound (G : Set ℂ) (hG : IsOpen G)
    (hBound : ∀ K : Set ℂ, K ⊆ G → IsCompact K →
      ∃ C : ℝ, 0 < C ∧ ∀ (f h : Lp ℂ 2 (volume.restrict G)) (g k : ℂ → ℂ),
        AnalyticOn ℂ g G → AnalyticOn ℂ k G →
        (∀ᵐ z ∂volume.restrict G, f z = g z) →
        (∀ᵐ z ∂volume.restrict G, h z = k z) →
        ∀ z ∈ K, ‖g z - k z‖ ≤ C * ‖f - h‖) :
    IsClosed (submodule G (volume.restrict G) : Set (Lp ℂ 2 (volume.restrict G)))
``` -/
theorem isClosed_of_local_bound (G : Set ℂ) (hG : IsOpen G)
    (hBound : ∀ K : Set ℂ, K ⊆ G → IsCompact K →
      ∃ C : ℝ, 0 < C ∧ ∀ (f h : Lp ℂ 2 (volume.restrict G)) (g k : ℂ → ℂ),
        AnalyticOn ℂ g G → AnalyticOn ℂ k G →
        (∀ᵐ z ∂volume.restrict G, f z = g z) →
        (∀ᵐ z ∂volume.restrict G, h z = k z) →
        ∀ z ∈ K, ‖g z - k z‖ ≤ C * ‖f - h‖) :
    IsClosed (submodule G (volume.restrict G) : Set (Lp ℂ 2 (volume.restrict G))) := by
  classical
  apply isSeqClosed_iff_isClosed.mp
  intro u f hu huf
  choose g hg hgu using hu
  have hCauchy : CauchySeq u := huf.cauchySeq
  have hPoint : ∀ z ∈ G, CauchySeq (fun n => g n z) := by
    intro z hz
    obtain ⟨C, hC, hEstimate⟩ := hBound {z} (singleton_subset_iff.mpr hz) isCompact_singleton
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hCauchy (ε / C) (div_pos hε hC)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hmn : ‖u m - u n‖ < ε / C := by simpa only [dist_eq_norm] using hN m hm n hn
    exact (hEstimate (u m) (u n) (g m) (g n) (hg m) (hg n) (hgu m) (hgu n)
      z (mem_singleton z)).trans_lt ((mul_lt_mul_of_pos_left hmn hC).trans_eq
        (mul_div_cancel₀ ε hC.ne'))
  have hLimit : ∀ z ∈ G, ∃ w : ℂ, Tendsto (fun n => g n z) atTop (𝓝 w) := by
    intro z hz
    exact cauchySeq_tendsto_of_complete (hPoint z hz)
  let gLimit : ℂ → ℂ := fun z => if hz : z ∈ G then Classical.choose (hLimit z hz) else 0
  have hgLimit (z : ℂ) (hz : z ∈ G) : Tendsto (fun n => g n z) atTop (𝓝 (gLimit z)) := by
    simpa only [gLimit, dif_pos hz] using Classical.choose_spec (hLimit z hz)
  have hUniform : TendstoLocallyUniformlyOn g gLimit atTop G := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hG]
    intro K hKG hK
    obtain ⟨C, hC, hEstimate⟩ := hBound K hKG hK
    have hUC : UniformCauchySeqOn g atTop K := by
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hCauchy (ε / C) (div_pos hε hC)
      refine ⟨N, fun m hm n hn z hz => ?_⟩
      rw [dist_eq_norm]
      have hmn : ‖u m - u n‖ < ε / C := by simpa only [dist_eq_norm] using hN m hm n hn
      exact (hEstimate (u m) (u n) (g m) (g n) (hg m) (hg n) (hgu m) (hgu n) z hz).trans_lt
        ((mul_lt_mul_of_pos_left hmn hC).trans_eq (mul_div_cancel₀ ε hC.ne'))
    exact hUC.tendstoUniformlyOn_of_tendsto (fun z hz => hgLimit z (hKG hz))
  have hAnalytic : AnalyticOn ℂ gLimit G :=
    (hUniform.differentiableOn (Eventually.of_forall fun n => (hg n).differentiableOn) hG).analyticOn hG
  obtain ⟨s, hs, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  refine ⟨gLimit, hAnalytic, ?_⟩
  have hAll : ∀ᵐ z ∂volume.restrict G, ∀ n : ℕ, u n z = g n z := by
    exact ae_all_iff.mpr hgu
  filter_upwards [hAE, hAll, ae_restrict_mem hG.measurableSet] with z hz hzg hzG
  have hSub : Tendsto (fun n => g (s n) z) atTop (𝓝 (gLimit z)) :=
    (hgLimit z hzG).comp hs.tendsto_atTop
  have hfz : Tendsto (fun n => g (s n) z) atTop (𝓝 (f z)) := by
    simpa only [hzg] using hz
  exact tendsto_nhds_unique hfz hSub

end AnalyticL2

end

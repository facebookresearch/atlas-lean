/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.IsolatedSingularity

open Set Filter Topology Metric
open MathlibExt.Analysis.Complex.IsolatedSingularityWanted

-- A function that is zero away from the center extends with value zero
-- even when its assigned value at the center is one.
example {c : ℂ} {r : ℝ} (hr : 0 < r) :
    let f := Function.update (fun _ : ℂ => (0 : ℂ)) c 1
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧ EqOn f g (ball c r \ {c}) ∧ g c = 0 := by
  intro f
  have hzero : EqOn f (fun _ => 0) (ball c r \ {c}) := fun _ hz =>
    Function.update_of_ne hz.2 _ _
  have hdisc := sdiff_mem_nhdsWithin_compl (ball_mem_nhds c hr) {c}
  have hlim : Tendsto f (𝓝[≠] c) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.eventuallyEq_of_mem hdisc).symm
  have hf := (differentiableOn_const (𝕜 := ℂ) (0 : ℂ)).congr (fun z hz => hzero hz)
  rcases isolatedSingularity_trichotomy hr hf with ⟨g, hg, hfg⟩ | hpole | hdense
  · refine ⟨g, hg, hfg, tendsto_nhds_unique ?_ (hlim.congr' (hfg.eventuallyEq_of_mem hdisc))⟩
    exact (hg.differentiableAt (ball_mem_nhds c hr)).continuousAt.continuousWithinAt.tendsto
  · exact (not_tendsto_atTop_of_tendsto_nhds hlim.norm hpole).elim
  · have hsub : f '' (ball c r \ {c}) ⊆ ({0} : Set ℂ) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hzero hz
    have hone := (hdense r hr).mono hsub (1 : ℂ)
    simp at hone

-- Two distinct finite subsequential limits force density, even on a larger disc.
example {c : ℂ} {r : ℝ} {f : ℂ → ℂ} {u v : ℕ → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r \ {c}))
    (hu : Tendsto u atTop (𝓝[≠] c)) (hv : Tendsto v atTop (𝓝[≠] c))
    (hu₀ : Tendsto (f ∘ u) atTop (𝓝 0)) (hv₁ : Tendsto (f ∘ v) atTop (𝓝 1)) :
    Dense (f '' (ball c (r + r) \ {c})) := by
  rcases isolatedSingularity_trichotomy hr hf with ⟨g, hg, heq⟩ | hpole | hdense
  · have hdisc := sdiff_mem_nhdsWithin_compl (ball_mem_nhds c hr) {c}
    have hlim : Tendsto f (𝓝[≠] c) (𝓝 (g c)) :=
      (hg.differentiableAt (ball_mem_nhds c hr)).continuousAt.continuousWithinAt.tendsto.congr'
        (heq.eventuallyEq_of_mem hdisc).symm
    exact (zero_ne_one ((tendsto_nhds_unique hu₀ (hlim.comp hu)).trans
      (tendsto_nhds_unique (hlim.comp hv) hv₁))).elim
  · exact (not_tendsto_atTop_of_tendsto_nhds hu₀.norm (hpole.comp hu)).elim
  · exact hdense (r + r) (add_pos hr hr)

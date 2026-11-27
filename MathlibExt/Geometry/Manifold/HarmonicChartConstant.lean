/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import MathlibExt.Analysis.PDE.PlanarHarmonicMaximumPrinciple

/-!
# Harmonic functions on a compact Riemann surface are constant

A real function on a compact connected Riemann surface that is harmonic in the holomorphic
charts is constant: it attains its maximum, the set where it does is open by the strong maximum
principle in a chart, and closed, so it is everything. R. de Jong, *Arakelov invariants of
Riemann surfaces*, Doc. Math. 10 (2005), 311–329, uses this in the proof of Lemma 3.1 (p. 316): an
isomorphism of hermitian line bundles with the same curvature form that matches the divisors of
their canonical sections has constant norm.

The statement here is for any compact connected topological space `X` with an atlas of charts to
`ℂ` (`ChartedSpace ℂ X`), so in particular for a compact connected Riemann surface, and asks for
harmonicity only in the preferred chart `chartAt ℂ x` at each point `x`. Continuity of `f` and the
holomorphic compatibility of the charts are not needed.
-/

@[expose] public section

open InnerProductSpace Set Topology

namespace ChartedSpace

/-- **Harmonic functions on a compact Riemann surface are constant.** Let `X` be a compact
connected topological space with charts to `ℂ` (for instance a compact connected Riemann surface)
and let `f : X → ℝ` be such that, for every `x ∈ X`, the function `f ∘ (chartAt ℂ x)⁻¹` is
harmonic at `chartAt ℂ x x`. Then `f` is constant.

R. de Jong, *Arakelov invariants of Riemann surfaces*, Doc. Math. 10 (2005), proof of Lemma 3.1,
p. 316 ("The norm is constant on X because both sides have the same curvature form, and the
divisors of their canonical sections are equal"), where it is applied to the logarithm of the
norm of an isomorphism of line bundles. The source's continuity of `f` follows from the
hypothesis, and only the charts `chartAt ℂ x` are used. -/
theorem exists_eq_const_of_harmonicAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [CompactSpace X] [ConnectedSpace X] {f : X → ℝ}
    (hf : ∀ x, HarmonicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) :
    ∃ c, ∀ x, f x = c := by
  -- `f` is continuous: near `x` it is `(f ∘ (chartAt ℂ x).symm) ∘ chartAt ℂ x`.
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have h1 : ContinuousAt ((f ∘ (chartAt ℂ x).symm) ∘ chartAt ℂ x) x :=
      ContinuousAt.comp (hf x).1.continuousAt ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
    refine h1.congr ?_
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    simp [(chartAt ℂ x).left_inv hy]
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.continuousOn
  refine ⟨f x₀, fun x => ?_⟩
  set S := {y | f y = f x₀} with hS
  have hclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    set e := chartAt ℂ x
    set u := f ∘ e.symm
    have hev : ∀ᶠ w in 𝓝 (e x), HarmonicAt u w ∧ w ∈ e.target :=
      (hf x).eventually.and (e.open_target.mem_nhds (mem_chart_target ℂ x))
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hev
    have hharm : HarmonicOnNhd u V := fun w hw => (hVsub hw).1
    have hmax : IsMaxOn u V (e x) := by
      intro w _
      simp only [mem_ofPred_eq, u, Function.comp_apply, e.left_inv (mem_chart_source ℂ x)]
      rw [show f x = f x₀ from hx]
      exact hx₀ (mem_univ _)
    obtain ⟨r, hr, -, hconst⟩ :=
      MathlibExt.Analysis.PDE.PlanarHarmonicMaximumPrinciple.exists_ball_eqOn_of_isMaxOn_complex
        hVopen hharm hxV hmax
    have hW : e.source ∩ e ⁻¹' Metric.ball (e x) r ∈ 𝓝 x :=
      (e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball).mem_nhds
        ⟨mem_chart_source ℂ x, Metric.mem_ball_self hr⟩
    filter_upwards [hW] with y hy
    have h1 : u (e y) = u (e x) := hconst hy.2
    simp only [u, Function.comp_apply, e.left_inv hy.1, e.left_inv (mem_chart_source ℂ x)] at h1
    rw [mem_ofPred_eq, h1]
    exact hx
  have := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x₀, rfl⟩)
  exact (this ▸ mem_univ x : x ∈ S)

end ChartedSpace

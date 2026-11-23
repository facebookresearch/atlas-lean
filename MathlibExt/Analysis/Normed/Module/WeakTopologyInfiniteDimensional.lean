/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The weak topology on an infinite-dimensional normed space

In finite dimensions the weak topology agrees with the norm topology, but in
infinite dimensions it is genuinely coarser. This file proves the three
classical ways of seeing that:

* every nonempty weakly open set is unbounded in norm, because it contains a
  whole line through each of its points;
* the weak closure of the unit sphere is the closed unit ball, so the sphere
  is neither weakly open, weakly closed, nor weakly compact;
* the identity map from the norm topology to the weak topology is an open map
  in finite dimensions but not in infinite dimensions.

The weak topology is the topology induced by evaluation against all continuous
linear functionals. The key point is that a basic weak neighbourhood of a point
only constrains finitely many functionals, and finitely many functionals always
have a common nonzero kernel vector in infinite dimensions.

Companion to the weak-convergence material of the source book; see in
particular the discussion of dual spaces and weak convergence in
`IntroductionToFunctionalAnalysis` (v1). No statement here is one of the
book's 72 formalized targets.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.WeakTopologyInfiniteDimensional

open Set Metric Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The evaluation map exhibiting the weak topology as the topology induced by
all continuous linear functionals. -/
private def weakEval : WeakSpace 𝕜 E → (E →L[𝕜] 𝕜) → 𝕜 :=
  fun x f => (topDualPairing 𝕜 E).flip x f

private theorem weakEval_toWeakSpace (x : E) (f : E →L[𝕜] 𝕜) :
    weakEval (toWeakSpace 𝕜 E x) f = f x := by
  rfl

private theorem isEmbedding_weakEval : Topology.IsEmbedding (weakEval (𝕜 := 𝕜) (E := E)) := by
  have hinj : Function.Injective (topDualPairing 𝕜 E).flip := by
    intro x y h
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := 𝕜) hne
    exact hf (DFunLike.congr_fun h f)
  exact WeakBilin.isEmbedding hinj

/-- An infinite-dimensional normed space has a nonzero vector. -/
private theorem exists_ne_zero_of_not_finiteDimensional (hInf : ¬ FiniteDimensional 𝕜 E) :
    ∃ v : E, v ≠ 0 := by
  by_contra hcon
  apply hInf
  have hsub : Subsingleton E := ⟨fun a b => by
    have ha : a = 0 := by by_contra ha; exact hcon ⟨a, ha⟩
    have hb : b = 0 := by by_contra hb; exact hcon ⟨b, hb⟩
    rw [ha, hb]⟩
  exact Module.finite_of_rank_eq_zero (rank_subsingleton' 𝕜 E)

/-- Finitely many continuous linear functionals on an infinite-dimensional
normed space have a common nonzero kernel vector. -/
theorem exists_ne_zero_forall_dual_apply_eq_zero (hInf : ¬ FiniteDimensional 𝕜 E)
    (S : Finset (E →L[𝕜] 𝕜)) :
    ∃ v : E, v ≠ 0 ∧ ∀ f ∈ S, f v = 0 := by
  classical
  let T : E →ₗ[𝕜] (S → 𝕜) := LinearMap.pi fun f : S => (f : E →ₗ[𝕜] 𝕜)
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro h
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp h
    exact hInf (FiniteDimensional.of_injective T hinj)
  obtain ⟨v, hvker, hv0⟩ : ∃ v ∈ LinearMap.ker T, v ≠ 0 := by
    by_contra hcon
    apply hker
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hv
      by_contra hv0
      exact hcon ⟨v, hv, hv0⟩
    · intro hv
      rw [hv, map_zero]
  refine ⟨v, hv0, fun f hf => ?_⟩
  have h2 := congrFun (LinearMap.mem_ker.mp hvker) ⟨f, hf⟩
  simpa [T] using h2

/-- Every nonempty weakly open set contains a whole line through each of its
points: if `U` is weakly open and `x ∈ U`, then `x + t • v ∈ U` for all scalars
`t` and some nonzero `v` (a common kernel vector of the finitely many
functionals constraining a basic weak neighbourhood of `x`). -/
theorem exists_line_subset_of_isOpen (hInf : ¬ FiniteDimensional 𝕜 E)
    {U : Set (WeakSpace 𝕜 E)} (hU : IsOpen U) {x : E}
    (hx : toWeakSpace 𝕜 E x ∈ U) :
    ∃ v : E, v ≠ 0 ∧ ∀ t : 𝕜, toWeakSpace 𝕜 E (x + t • v) ∈ U := by
  classical
  obtain ⟨V, hV, hUV⟩ := isEmbedding_weakEval.isInducing.isOpen_iff.mp hU
  have hmemU {z : E} (hz : weakEval (toWeakSpace 𝕜 E z) ∈ V) :
      toWeakSpace 𝕜 E z ∈ U := by
    rw [← hUV]
    exact hz
  have hxV : weakEval (toWeakSpace 𝕜 E x) ∈ V := by
    have h := hx
    rw [← hUV] at h
    exact h
  have hVnhds : V ∈ 𝓝 (weakEval (toWeakSpace 𝕜 E x)) := hV.mem_nhds hxV
  rw [nhds_pi] at hVnhds
  rw [Filter.mem_pi'] at hVnhds
  obtain ⟨I, t, ht, hpi⟩ := hVnhds
  have hball : ∀ f ∈ I, ∃ ε > 0, Metric.ball (f x) ε ⊆ t f := by
    intro f hf
    have htf : t f ∈ 𝓝 (f x) := by
      have h := ht f
      rwa [weakEval_toWeakSpace] at h
    exact Metric.mem_nhds_iff.mp htf
  choose ε hεpos hεball using hball
  obtain ⟨v, hv0, hvker⟩ := exists_ne_zero_forall_dual_apply_eq_zero hInf I
  refine ⟨v, hv0, fun c => hmemU ?_⟩
  have hmem : weakEval (toWeakSpace 𝕜 E (x + c • v)) ∈ Set.pi (↑I) t := by
    rw [Set.mem_pi]
    intro f hf
    have hfx : weakEval (toWeakSpace 𝕜 E (x + c • v)) f = f x := by
      rw [weakEval_toWeakSpace]
      simp [hvker f hf]
    rw [hfx]
    exact hεball f hf (Metric.mem_ball_self (hεpos f hf))
  exact hpi hmem

/-- Every nonempty weakly open set in an infinite-dimensional normed space is
unbounded in norm. -/
theorem exists_norm_gt_of_isOpen (hInf : ¬ FiniteDimensional 𝕜 E)
    {U : Set (WeakSpace 𝕜 E)} (hU : IsOpen U) (hne : U.Nonempty) (R : ℝ) :
    ∃ y ∈ U, R < ‖(toWeakSpace 𝕜 E).symm y‖ := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨x, rfl⟩ := (toWeakSpace 𝕜 E).surjective y₀
  obtain ⟨v, hv0, hline⟩ := exists_line_subset_of_isOpen hInf hU hy₀
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set T : ℝ := (|R| + ‖x‖ + 1) / ‖v‖ with hT
  have hTpos : 0 < T := div_pos (by linarith [norm_nonneg x, abs_nonneg R]) hvnorm
  refine ⟨toWeakSpace 𝕜 E (x + (T : 𝕜) • v), hline (T : 𝕜), ?_⟩
  simp only [LinearEquiv.symm_apply_apply]
  have h1 : ‖(T : 𝕜) • v‖ = T * ‖v‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hTpos]
  have hle : ‖x + (T : 𝕜) • v - x‖ ≤ ‖x + (T : 𝕜) • v‖ + ‖x‖ := norm_sub_le _ _
  rw [add_sub_cancel_left] at hle
  have hTmul : T * ‖v‖ = |R| + ‖x‖ + 1 := by
    rw [hT]; field_simp
  linarith [le_abs_self R]

/-- The open unit ball is not weakly open in infinite dimensions. -/
theorem not_isOpen_image_ball (hInf : ¬ FiniteDimensional 𝕜 E) :
    ¬ IsOpen ((toWeakSpace 𝕜 E) '' Metric.ball (0 : E) 1) := by
  intro h
  have hne : ((toWeakSpace 𝕜 E) '' Metric.ball (0 : E) 1).Nonempty :=
    ⟨toWeakSpace 𝕜 E 0, ⟨0, Metric.mem_ball_self zero_lt_one, rfl⟩⟩
  obtain ⟨y, hyU, hyR⟩ := exists_norm_gt_of_isOpen hInf h hne 2
  obtain ⟨z, hz, hzy⟩ := hyU
  have hz1 : ‖z‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hz
  have hsymm : (toWeakSpace 𝕜 E).symm y = z := by
    rw [← hzy]
    exact (toWeakSpace 𝕜 E).symm_apply_apply z
  rw [hsymm] at hyR
  linarith

/-- The unit sphere is not weakly open in infinite dimensions. -/
theorem not_isOpen_image_sphere (hInf : ¬ FiniteDimensional 𝕜 E) :
    ¬ IsOpen ((toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1) := by
  intro h
  have hne : ((toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨v, hv0⟩ := exists_ne_zero_of_not_finiteDimensional hInf
    refine ⟨toWeakSpace 𝕜 E (((‖v‖⁻¹ : ℝ) : 𝕜) • v),
      ⟨(((‖v‖⁻¹ : ℝ) : 𝕜) • v), ?_, rfl⟩⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv0)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  obtain ⟨y, hyU, hyR⟩ := exists_norm_gt_of_isOpen hInf h hne 2
  obtain ⟨z, hz, hzy⟩ := hyU
  have hz1 : ‖z‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact hz
  have hsymm : (toWeakSpace 𝕜 E).symm y = z := by
    rw [← hzy]
    exact (toWeakSpace 𝕜 E).symm_apply_apply z
  rw [hsymm, hz1] at hyR
  norm_num at hyR

/-- In an infinite-dimensional normed space, the weak closure of the unit
sphere is the closed unit ball. -/
theorem closure_image_sphere_eq_image_closedBall (hInf : ¬ FiniteDimensional 𝕜 E) :
    closure ((toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1)
      = (toWeakSpace 𝕜 E) '' Metric.closedBall (0 : E) 1 := by
  apply le_antisymm
  · calc closure ((toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1)
        ⊆ closure ((toWeakSpace 𝕜 E) '' Metric.closedBall (0 : E) 1) :=
          closure_mono (Set.image_mono Metric.sphere_subset_closedBall)
      _ = (toWeakSpace 𝕜 E) '' Metric.closedBall (0 : E) 1 := by
          let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
          let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
          rw [← Convex.toWeakSpace_closure 𝕜 (convex_closedBall (0 : E) 1),
            isClosed_closedBall.closure_eq]
  · rintro y ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [_root_.mem_closure_iff]
    intro U hU hxU
    obtain ⟨V, hV, hUV⟩ := isEmbedding_weakEval.isInducing.isOpen_iff.mp hU
    have hmemU {z : E} (hz : weakEval (toWeakSpace 𝕜 E z) ∈ V) :
        toWeakSpace 𝕜 E z ∈ U := by
      rw [← hUV]
      exact hz
    have hxV : weakEval (toWeakSpace 𝕜 E x) ∈ V := by
      have h := hxU
      rw [← hUV] at h
      exact h
    have hVnhds : V ∈ 𝓝 (weakEval (toWeakSpace 𝕜 E x)) := hV.mem_nhds hxV
    rw [nhds_pi] at hVnhds
    rw [Filter.mem_pi'] at hVnhds
    obtain ⟨I, t, ht, hpi⟩ := hVnhds
    have hball : ∀ f ∈ I, ∃ ε > 0, Metric.ball (f x) ε ⊆ t f := by
      intro f hf
      have htf : t f ∈ 𝓝 (f x) := by
        have h := ht f
        rwa [weakEval_toWeakSpace] at h
      exact Metric.mem_nhds_iff.mp htf
    choose ε hεpos hεball using hball
    obtain ⟨v, hv0, hvker⟩ := exists_ne_zero_forall_dual_apply_eq_zero hInf I
    by_cases hnorm : ‖x‖ = 1
    · refine ⟨toWeakSpace 𝕜 E x, hxU, ?_⟩
      exact ⟨x, by rw [Metric.mem_sphere, dist_zero_right]; exact hnorm, rfl⟩
    · have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx hnorm
      have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      set T : ℝ := (‖x‖ + 2) / ‖v‖ with hT
      have hTpos : 0 < T := div_pos (by linarith [norm_nonneg x]) hvnorm
      have hcont : Continuous fun s : ℝ => ‖x + (s : 𝕜) • v‖ := by
        apply Continuous.norm
        apply Continuous.add continuous_const
        exact (RCLike.continuous_ofReal (K := 𝕜)).smul continuous_const
      have hφT : 2 ≤ (fun s : ℝ => ‖x + (s : 𝕜) • v‖) T := by
        have h1 : ‖(T : 𝕜) • v‖ = T * ‖v‖ := by
          rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hTpos]
        have hle : ‖x + (T : 𝕜) • v - x‖ ≤ ‖x + (T : 𝕜) • v‖ + ‖x‖ := norm_sub_le _ _
        rw [add_sub_cancel_left] at hle
        rw [h1] at hle
        have hTmul : T * ‖v‖ = ‖x‖ + 2 := by
          rw [hT]; field_simp
        linarith
      have h1mem : (1 : ℝ) ∈ Set.Icc ‖x‖ ((fun s : ℝ => ‖x + (s : 𝕜) • v‖) T) :=
        ⟨hlt.le, one_le_two.trans hφT⟩
      obtain ⟨s, _, hseq⟩ := intermediate_value_Icc hTpos.le hcont.continuousOn
        (show (1 : ℝ) ∈ Set.Icc ((fun s : ℝ => ‖x + (s : 𝕜) • v‖) 0)
          ((fun s : ℝ => ‖x + (s : 𝕜) • v‖) T) by simpa using h1mem)
      refine ⟨toWeakSpace 𝕜 E (x + (s : 𝕜) • v), hmemU ?_, ?_⟩
      · have hmem : weakEval (toWeakSpace 𝕜 E (x + (s : 𝕜) • v)) ∈ Set.pi (↑I) t := by
          rw [Set.mem_pi]
          intro f hf
          have hfx : weakEval (toWeakSpace 𝕜 E (x + (s : 𝕜) • v)) f = f x := by
            rw [weakEval_toWeakSpace]
            simp [hvker f hf]
          rw [hfx]
          exact hεball f hf (Metric.mem_ball_self (hεpos f hf))
        exact hpi hmem
      · refine ⟨x + (s : 𝕜) • v, ?_, rfl⟩
        rw [Metric.mem_sphere, dist_zero_right]
        exact hseq

/-- The unit sphere is not weakly closed in infinite dimensions: its weak
closure is the whole closed unit ball. -/
theorem not_isClosed_image_sphere (hInf : ¬ FiniteDimensional 𝕜 E) :
    ¬ IsClosed ((toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1) := by
  intro h
  have hcl := closure_image_sphere_eq_image_closedBall (𝕜 := 𝕜) (E := E) hInf
  rw [h.closure_eq] at hcl
  have h0 : toWeakSpace 𝕜 E (0 : E) ∈ (toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1 := by
    rw [hcl]
    exact ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨z, hz, hzz⟩ := h0
  have hz0 : z = 0 := (toWeakSpace 𝕜 E).injective hzz
  subst hz0
  rw [Metric.mem_sphere, dist_zero_right] at hz
  simp at hz

/-- The unit sphere is not weakly compact in infinite dimensions. -/
theorem not_isCompact_image_sphere (hInf : ¬ FiniteDimensional 𝕜 E) :
    ¬ IsCompact ((toWeakSpace 𝕜 E) '' Metric.sphere (0 : E) 1) :=
  fun h => not_isClosed_image_sphere hInf h.isClosed

/-- In finite dimensions the identity map from the norm topology to the weak
topology is an open map: the weak topology agrees with the norm topology. -/
theorem isOpenMap_toWeakSpaceCLM_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    IsOpenMap (toWeakSpaceCLM 𝕜 E) := by
  have hfd : FiniteDimensional 𝕜 (WeakSpace 𝕜 E) := (toWeakSpace 𝕜 E).finiteDimensional
  have hcont : Continuous (toWeakSpace 𝕜 E).symm :=
    LinearMap.continuous_of_finiteDimensional (toWeakSpace 𝕜 E).symm.toLinearMap
  let e : E ≃L[𝕜] WeakSpace 𝕜 E :=
    { toWeakSpace 𝕜 E with
      continuous_toFun := (toWeakSpaceCLM 𝕜 E).cont
      continuous_invFun := hcont }
  exact e.toHomeomorph.isOpenMap

/-- In infinite dimensions the identity map from the norm topology to the weak
topology is not an open map: the open unit ball is norm-open but not
weakly open. -/
theorem not_isOpenMap_toWeakSpaceCLM_of_infiniteDimensional
    (hInf : ¬ FiniteDimensional 𝕜 E) :
    ¬ IsOpenMap (toWeakSpaceCLM 𝕜 E) := by
  intro h
  apply not_isOpen_image_ball hInf
  have himg := h (Metric.ball (0 : E) 1) Metric.isOpen_ball
  have hEq : (toWeakSpaceCLM 𝕜 E) '' Metric.ball (0 : E) 1
      = (toWeakSpace 𝕜 E) '' Metric.ball (0 : E) 1 :=
    Set.image_congr fun x _ => toWeakSpaceCLM_eq_toWeakSpace 𝕜 E x
  rwa [hEq] at himg

end MathlibExt.Analysis.Normed.Module.WeakTopologyInfiniteDimensional

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Normalize
import MathlibExt.Topology.ScottishBook46

/-!
# Tests for unicoherence of the unit sphere

The first test applies the theorem to the real square-summable sequence space, with the whole
sphere and a singleton as the two cover members. The second applies it, in every real
infinite-dimensional Banach space, to the two closed half-spheres that a nonzero continuous linear
functional `f` cuts out: their intersection, the unit sphere of the kernel of `f`, is connected.
-/

open Set Metric
open MathlibExt.Topology.ScottishBook46Wanted

example : IsConnected
    (sphere (0 : lp (fun _ : ℕ ↦ ℝ) 2) 1 ∩ {lp.single 2 (0 : ℕ) (1 : ℝ)}) := by
  let E := lp (fun _ : ℕ ↦ ℝ) 2
  let S := sphere (0 : E) 1
  let x : E := lp.single 2 (0 : ℕ) (1 : ℝ)
  change IsConnected (S ∩ {x})
  have hinf : ¬ Module.Finite ℝ E := by
    intro h
    let b : HilbertBasis ℕ ℝ E := default
    exact h.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent
  have hrank : 1 < Module.rank ℝ E :=
    Cardinal.one_lt_aleph0.trans_le
      (le_of_not_gt fun hlt ↦ hinf (Module.rank_lt_aleph0_iff.mp hlt))
  have hx : x ∈ S := by
    change x ∈ sphere (0 : E) 1
    rw [mem_sphere_zero_iff_norm]
    rw [show x = lp.single 2 (0 : ℕ) (1 : ℝ) from rfl, lp.norm_single (by norm_num), norm_one]
  have hsub : {x} ⊆ S := singleton_subset_iff.mpr hx
  exact sphere_in_banach_space_is_unicoherent E hinf S {x} Subset.rfl hsub
    (union_eq_left.mpr hsub) isClosed_sphere (isConnected_sphere hrank 0 zero_le_one)
    isClosed_singleton isConnected_singleton

/-- A closed half-sphere `{x ∈ S | 0 ≤ f x}` of a nonzero continuous linear functional `f` is
connected: `NormedSpace.normalize` maps the punctured half-space `{v | v ≠ 0 ∧ 0 ≤ f v}`, which is
star-convex about any `u` with `0 < f u`, onto it. -/
private theorem isConnected_sphere_inter_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E →L[ℝ] ℝ} (hf : f ≠ 0) :
    IsConnected (sphere (0 : E) 1 ∩ {x | 0 ≤ f x}) := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    refine hf (ContinuousLinearMap.ext fun w ↦ ?_)
    simpa using not_exists.mp h w
  obtain ⟨u, hu⟩ : ∃ u, 0 < f u := by
    rcases hw.lt_or_gt with h | h
    · exact ⟨-w, by simpa using neg_pos.mpr h⟩
    · exact ⟨w, h⟩
  let P : Set E := {v | v ≠ 0 ∧ 0 ≤ f v}
  have huP : u ∈ P := ⟨fun h ↦ by simp [h] at hu, hu.le⟩
  have hstar : StarConvex ℝ u P := by
    intro y hy a b ha hb hab
    have hfy : f (a • u + b • y) = a * f u + b * f y := by simp
    refine ⟨fun h0 ↦ ?_, ?_⟩
    · rcases ha.lt_or_eq with ha' | ha'
      · have hpos : 0 < a * f u + b * f y :=
          add_pos_of_pos_of_nonneg (mul_pos ha' hu) (mul_nonneg hb hy.2)
        rw [← hfy, h0, map_zero] at hpos
        exact lt_irrefl 0 hpos
      · subst ha'
        rw [zero_add] at hab
        subst hab
        exact hy.1 (by simpa using h0)
    · rw [hfy]
      exact add_nonneg (mul_nonneg ha hu.le) (mul_nonneg hb hy.2)
  have hcont : ContinuousOn (NormedSpace.normalize : E → E) P := fun x hx ↦
    ((continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx.1)).smul
      continuousAt_id).continuousWithinAt
  have himage : NormedSpace.normalize '' P = sphere (0 : E) 1 ∩ {x | 0 ≤ f x} := by
    ext x
    constructor
    · rintro ⟨v, ⟨hv0, hfv⟩, rfl⟩
      refine ⟨mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize_eq_one_iff.mpr hv0), ?_⟩
      change 0 ≤ f (‖v‖⁻¹ • v)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) hfv
    · rintro ⟨hx, hfx⟩
      have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      exact ⟨x, ⟨fun h ↦ by simp [h] at hx1, hfx⟩,
        NormedSpace.normalize_eq_self_of_norm_eq_one hx1⟩
  rw [← himage]
  exact ((hstar.isPathConnected huP).isConnected).image _ hcont

/-- In a real infinite-dimensional Banach space, the closed half-spheres `{x ∈ S | 0 ≤ f x}` and
`{x ∈ S | f x ≤ 0}` of a nonzero continuous linear functional `f` are closed and connected and
cover the unit sphere `S`, so the theorem shows that their intersection, the unit sphere of the
kernel of `f`, is connected. -/
example (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hinf : ¬ Module.Finite ℝ E) (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
    IsConnected (sphere (0 : E) 1 ∩ {x | f x = 0}) := by
  have hB : IsConnected (sphere (0 : E) 1 ∩ {x | f x ≤ 0}) := by
    have h := isConnected_sphere_inter_nonneg (neg_ne_zero.mpr hf)
    have hset : {x : E | 0 ≤ (-f) x} = {x | f x ≤ 0} := by
      ext x
      simp
    rwa [hset] at h
  have hcover : sphere (0 : E) 1 ∩ {x | 0 ≤ f x} ∪ sphere (0 : E) 1 ∩ {x | f x ≤ 0} =
      sphere (0 : E) 1 := by
    rw [← inter_union_distrib_left]
    refine inter_eq_left.mpr fun x _ ↦ ?_
    rcases le_total 0 (f x) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hinter : sphere (0 : E) 1 ∩ {x | 0 ≤ f x} ∩ (sphere (0 : E) 1 ∩ {x | f x ≤ 0}) =
      sphere (0 : E) 1 ∩ {x | f x = 0} := by
    ext x
    constructor
    · rintro ⟨⟨hx, h₁⟩, -, h₂⟩
      exact ⟨hx, le_antisymm h₂ h₁⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨hx, h.ge⟩, hx, h.le⟩
  rw [← hinter]
  exact sphere_in_banach_space_is_unicoherent E hinf _ _ inter_subset_left inter_subset_left
    hcover (isClosed_sphere.inter (isClosed_le continuous_const f.continuous))
    (isConnected_sphere_inter_nonneg hf)
    (isClosed_sphere.inter (isClosed_le f.continuous continuous_const)) hB

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Stereographic picture for doubly-punctured sphere

We show that removing two antipodal points from `𝕊ⁿ` leaves a space
homeomorphic to `ℝⁿ ∖ {0}` via stereographic projection.  The antipode
goes to the origin.
-/

@[expose] public section

open Metric

namespace AlgebraicTopology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Doubly-punctured sphere `≃ₜ` punctured Euclidean space via stereographic projection. -/
noncomputable def spherePuncturedTwoHomeo (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (v w : sphere (0 : E) 1) (hw : (w : E) = -(v : E)) :
    ↥(({v, w}ᶜ : Set (sphere (0 : E) 1))) ≃ₜ
      ↥(({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) := by
  set e := stereographic' n v with he
  have hsrc : e.source = {v}ᶜ := stereographic'_source v
  have hne : v ≠ w := by
    intro h
    have hvv : (v : E) = -(v : E) := by
      rw [← hw]
      exact congrArg Subtype.val h
    have hz : (v : E) = 0 := by
      rw [eq_neg_iff_add_eq_zero, ← two_smul ℝ] at hvv
      exact (smul_eq_zero.mp hvv).resolve_left two_ne_zero
    have hn := norm_eq_of_mem_sphere v
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hwsrc : w ∈ e.source := by
    rw [hsrc, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact hne h.symm
  have hew : e w = 0 := by
    have hw_eq : (w : sphere (0 : E) 1) = -v := Subtype.ext hw
    rw [hw_eq, he, stereographic', OpenPartialHomeomorph.trans_apply,
      stereographic_apply_neg v]
    simp
  have hxsrc : ∀ x : ↥(({v, w}ᶜ : Set (sphere (0 : E) 1))),
      (x.1 : sphere (0 : E) 1) ∈ e.source := by
    intro x
    rw [hsrc, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact x.2 (Set.mem_insert_iff.mpr (Or.inl h))
  refine ⟨⟨fun x => ⟨e x.1, ?_⟩, fun y => ⟨e.symm y.1, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro h
    rw [Set.mem_singleton_iff] at h
    have : (x.1 : sphere (0 : E) 1) = w :=
      e.injOn (hxsrc x) hwsrc (h.trans hew.symm)
    exact x.2 (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr this)))
  · have hyt : y.1 ∈ e.target := by
      rw [stereographic'_target]
      trivial
    have hmemsrc : e.symm y.1 ∈ e.source := e.map_target hyt
    rw [hsrc] at hmemsrc
    intro hc
    rcases Set.mem_insert_iff.mp hc with hv | hw'
    · exact hmemsrc hv
    · rw [Set.mem_singleton_iff] at hw'
      have hy0 : y.1 = 0 := by
        rw [← e.right_inv hyt, hw', hew]
      exact y.2 (Set.mem_singleton_iff.mpr hy0)
  · rintro x
    apply Subtype.ext
    exact e.left_inv (hxsrc x)
  · rintro y
    apply Subtype.ext
    exact e.right_inv (by rw [stereographic'_target]; trivial)
  · apply Continuous.subtype_mk
    exact e.continuousOn_toFun.comp_continuous continuous_subtype_val (fun x => hxsrc x)
  · apply Continuous.subtype_mk
    apply e.continuousOn_invFun.comp_continuous continuous_subtype_val
    intro y
    rw [stereographic'_target]
    trivial

end AlgebraicTopology

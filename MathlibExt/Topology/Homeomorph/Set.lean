/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions

/-!
# Homeomorphisms between intersections

This file provides a flat-subtype form of restricting a homeomorphism between
subspaces to corresponding subsets.
-/

@[expose] public section

universe u v

namespace Homeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict a homeomorphism between subspaces to corresponding subsets, presenting the
resulting source and target as intersections in the ambient spaces. -/
def inter {s t : Set X} {u v : Set Y} (e : t ≃ₜ v)
    (h : ∀ z : t, z.1 ∈ s ↔ (e z).1 ∈ u) :
    (s ∩ t : Set X) ≃ₜ (u ∩ v : Set Y) where
  toFun z := ⟨(e ⟨z.1, z.2.2⟩).1,
    ⟨(h ⟨z.1, z.2.2⟩).1 z.2.1, (e ⟨z.1, z.2.2⟩).2⟩⟩
  invFun z := ⟨(e.symm ⟨z.1, z.2.2⟩).1,
    ⟨(h (e.symm ⟨z.1, z.2.2⟩)).2 (by simpa using z.2.1),
      (e.symm ⟨z.1, z.2.2⟩).2⟩⟩
  left_inv z := by
    apply Subtype.ext
    change (e.symm (e ⟨z.1, z.2.2⟩)).1 = z.1
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z.1, z.2.2⟩)
  right_inv z := by
    apply Subtype.ext
    change (e (e.symm ⟨z.1, z.2.2⟩)).1 = z.1
    exact congrArg Subtype.val (e.apply_symm_apply ⟨z.1, z.2.2⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (e.continuous.comp (continuous_subtype_val.subtype_mk _))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))

@[simp]
theorem inter_apply_coe {s t : Set X} {u v : Set Y} (e : t ≃ₜ v)
    (h : ∀ z : t, z.1 ∈ s ↔ (e z).1 ∈ u) (z : (s ∩ t : Set X)) :
    (e.inter h z : Y) = e ⟨z.1, z.2.2⟩ :=
  rfl

@[simp]
theorem inter_symm_apply_coe {s t : Set X} {u v : Set Y} (e : t ≃ₜ v)
    (h : ∀ z : t, z.1 ∈ s ↔ (e z).1 ∈ u) (z : (u ∩ v : Set Y)) :
    ((e.inter h).symm z : X) = e.symm ⟨z.1, z.2.2⟩ :=
  rfl

end Homeomorph

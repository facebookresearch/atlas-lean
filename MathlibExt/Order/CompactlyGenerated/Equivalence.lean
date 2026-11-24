/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Bounds.OrderIso

@[expose] public section

variable {α : Type*} {β : Type*} [PartialOrder α] [PartialOrder β]

namespace OrderIso

private theorem isCompactElement_map (e : α ≃o β) {a : α}
    (ha : IsCompactElement a) : IsCompactElement (e a) := by
  intro s u hs hdir hlub hle
  let t := e.symm '' s
  have ht_nonempty : t.Nonempty := by
    obtain ⟨x, hx⟩ := hs
    exact ⟨e.symm x, x, hx, rfl⟩
  have ht_directed : DirectedOn (· ≤ ·) t := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x' hx' y' hy'
    exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.symm.monotone hxz, e.symm.monotone hyz⟩
  have ht_lub : IsLUB t (e.symm u) := by
    have : IsLUB s (e (e.symm u)) := by
      rw [e.apply_symm_apply]
      exact hlub
    exact (e.symm.isLUB_image (s := s)).mpr this
  have ha_le : a ≤ e.symm u := by
    rw [← e.le_iff_le]
    rw [e.apply_symm_apply]
    exact hle
  obtain ⟨y, hy_mem, hy_le⟩ := ha t (e.symm u) ht_nonempty ht_directed ht_lub ha_le
  obtain ⟨x, hx_mem, rfl⟩ := hy_mem
  have hle' : e a ≤ x := by
    have : e a ≤ e (e.symm x) := e.le_iff_le.mpr hy_le
    rwa [e.apply_symm_apply] at this
  exact ⟨x, hx_mem, hle'⟩

theorem isCompactElement_iff (e : α ≃o β) (a : α) :
    IsCompactElement (e a) ↔ IsCompactElement a := by
  constructor
  · intro h
    have h' := isCompactElement_map e.symm h
    simpa [e.symm_apply_apply] using h'
  · intro h
    exact isCompactElement_map e h

end OrderIso

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit.lean` and
`P2M/Sol/S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Isomorphisms from tensoring with the unit

In a braided monoidal category, if `M ⊗ N` and `M' ⊗ N'` are both isomorphic
to the unit and `M ≅ M'`, then `N ≅ N'`: the isomorphism is built from the
unitors, the associator, and the braiding.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

/-- In a braided monoidal category, tensoring with the unit is cancellative
up to isomorphism: if `M ⊗ N ≅ 𝟙`, `M' ⊗ N' ≅ 𝟙`, and `M ≅ M'`, then
`N ≅ N'`. -/
theorem CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N M' N' : C} (e : M ≅ M') (h : Nonempty (M ⊗ N ≅ 𝟙_ C))
    (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
    Nonempty (N ≅ N') := by
  obtain ⟨i⟩ := h
  obtain ⟨i'⟩ := h'
  exact ⟨(ρ_ N).symm ≪≫ (Iso.refl N ⊗ᵢ i'.symm) ≪≫ (α_ N M' N').symm ≪≫
    ((β_ N M') ⊗ᵢ Iso.refl N') ≪≫ ((e.symm ⊗ᵢ Iso.refl N) ⊗ᵢ Iso.refl N') ≪≫
    (i ⊗ᵢ Iso.refl N') ≪≫ λ_ N'⟩

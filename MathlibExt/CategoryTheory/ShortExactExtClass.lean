/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g.lean`
and
`P2M/Sol/S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

@[expose] public section

open CategoryTheory Abelian Limits

universe w v u

/-- The extension class of a short exact sequence vanishes if and only if its epimorphism
`S.g` has a section. -/
theorem CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt.{w} C] {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h0
    have hx : (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) = 0 := by
      rw [Ext.mk₀_id_comp, h0]
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) hx
    refine ⟨Ext.homEquiv₀ x₂, ?_⟩
    have : Ext.mk₀ (Ext.homEquiv₀ x₂ ≫ S.g) = Ext.mk₀ (𝟙 S.X₃) := by
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply, hx₂]
    exact Ext.homEquiv₀.symm.injective (by simpa [Ext.mk₀_homEquiv₀_apply] using this)
  · rintro ⟨s, hs⟩
    have h1 : (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) = 0 := by
      rw [hS.comp_extClass, Ext.comp_zero]
    rwa [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hs, Ext.mk₀_id_comp] at h1

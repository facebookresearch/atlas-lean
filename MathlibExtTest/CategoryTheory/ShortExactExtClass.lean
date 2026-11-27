/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.ShortExactExtClass

@[expose] public section

open CategoryTheory Abelian Limits

universe w v u

private theorem exactSource_shortExact {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ :=
  CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g hS

-- Consumer of the backward direction: a section of `S.g` kills the extension class.
example {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    hS.extClass = 0 :=
  (CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g hS).2 ⟨s, hs⟩

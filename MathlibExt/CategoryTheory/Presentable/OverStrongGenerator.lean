/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Generator.Over
import MathlibExt.CategoryTheory.Presentable.OverSource
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Comma.LocallySmall

/-!
# Slice local presentability from actual presentable generators

The original presentable generators retain all their original maps to the
base. Source presentability transfers to each such slice object without
any presentability or size premise on the base. Their small strong-generator
property therefore proves slice local presentability at the same rank.
-/

universe w v u t
open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  [LocallySmall.{w} C] {ι : Type t} [Small.{w} ι]

/-- A native presentable strong generator gives local presentability of every actual slice. -/
theorem over_isCardinalLocallyPresentable_of_generator (G : ι → C) (S : C)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hG : (ObjectProperty.ofObj G).IsStrongGenerator)
    (hP : ∀ i, IsCardinalPresentable (G i) κ) :
    IsCardinalLocallyPresentable (Over S) κ := by
  let _ : HasColimitsOfSize.{w, w} (Over S) :=
    CostructuredArrow.hasColimitsOfSize (G := 𝟭 C) (X := S)
  let _ : LocallySmall.{w} (Over S) := Over.locallySmall S
  let _ : ObjectProperty.Small.{w} (overGenerator G S) := overGenerator_small G S
  refine (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator _ _).mpr
    ⟨overGenerator G S, inferInstance, overGenerator_isStrongGenerator G S hG, ?_⟩
  intro X hX
  change ObjectProperty.ofObj (overGeneratorObj G S) X at hX
  rcases hX with ⟨⟨i, a⟩⟩
  let _ : IsCardinalPresentable (G i) κ := hP i
  exact over_mk_isCardinalPresentable a κ

end CategoryTheory

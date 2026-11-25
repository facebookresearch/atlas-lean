/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.Basic

/-!
# Closure under admissible extensions in an exact category

The property refers to the original ambient admissible rows, with
independent object and morphism universes. Its rowwise quantifier is the
closure interface used by inherited full-subcategory exact structures.
-/

public section

open CategoryTheory Limits

universe uH vH

namespace CategoryTheory.ExactCategory

variable {H : Type uH} [Category.{vH} H] [Preadditive H]
  [HasZeroObject H] [HasBinaryBiproducts H] [ExactCategory H]

/-- The extension-closure condition refers only to actual
admissible exact rows in the original ambient exact category. -/
def ExtensionClosed (P : ObjectProperty H) : Prop :=
  ∀ S : ShortComplex H, ExactCategory.IsAdmissibleExact S → P S.X₁ → P S.X₃ → P S.X₂

private theorem originalExtensionClosureFunctionComputed (P : ObjectProperty H) :
    ExtensionClosed P ↔
      ∀ S : ShortComplex H, ExactCategory.IsAdmissibleExact S → P S.X₁ → P S.X₃ → P S.X₂ := Iff.rfl

/-- Extension closure is exactly its original rowwise R1 quantifier,
with no exposed predicate or added closure outcome. -/
theorem extensionClosed_iff (P : ObjectProperty H) :
    ExtensionClosed P ↔
      ∀ S : ShortComplex H, ExactCategory.IsAdmissibleExact S → P S.X₁ → P S.X₃ → P S.X₂ :=
  originalExtensionClosureFunctionComputed P

end CategoryTheory.ExactCategory

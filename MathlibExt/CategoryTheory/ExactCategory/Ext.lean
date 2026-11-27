/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.ExactCategory.Basic

/-!
# Equality of Quillen exact structures

The admissible-row predicate determines the exact structure: all remaining fields
are propositions. This compares proved predicates, not supplied model equalities.
-/

@[expose] public section

open CategoryTheory Limits
universe u v

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Two exact structures with the same actual admissible rows are equal. -/
theorem ext_admissible (E F : ExactCategory C)
    (h : ∀ S : ShortComplex C, E.IsAdmissibleExact S ↔ F.IsAdmissibleExact S) : E = F := by
  have hp : E.IsAdmissibleExact = F.IsAdmissibleExact := funext fun S => propext (h S)
  cases E
  cases F
  cases hp
  rfl

end CategoryTheory.ExactCategory

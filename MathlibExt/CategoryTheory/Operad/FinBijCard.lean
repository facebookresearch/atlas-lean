/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.SmallFinBijGroupoid

/-- The canonical small finite-bijection object of cardinality `n`. -/
abbrev card (n : ℕ) : SmallFinBijGroupoid :=
  ⟨FintypeCat.Skeleton.mk n⟩

end CategoryTheory.Operad.SmallFinBijGroupoid

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal

/-!
# Finite-set cardinal objects

Defines the cardinal-n object of the small groupoid of finite sets and bijections from Fin n.
This fixes the representative used for degree-indexed constructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Operad.SmallFinBijGroupoid

/-- The canonical small finite-bijection object of cardinality `n`. -/
abbrev card (n : ℕ) : SmallFinBijGroupoid :=
  ⟨FintypeCat.Skeleton.mk n⟩

end CategoryTheory.Operad.SmallFinBijGroupoid

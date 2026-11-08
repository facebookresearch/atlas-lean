/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Place

@[expose] public section

namespace NumberFieldPlaceTest

/-- A finite place has residue norm at least one. -/
example {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    1 ≤ v.residueNorm :=
  v.one_le_residueNorm

/-- Finite and infinite places both land in the unified place type. -/
example {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K)
    (w : NumberField.InfinitePlace K) :
    NumberField.Place K × NumberField.Place K :=
  ⟨NumberField.Place.finitePlace v, NumberField.Place.infinitePlace w⟩

end NumberFieldPlaceTest

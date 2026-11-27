/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.PuiseuxTheorem

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

universe v

-- `exactSource` consumer for the generalized theorem, with the original
-- binders: no `CharZero K` hypothesis.
example {K : Type*} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) :=
  HahnSeries.isAlgClosed_rat

-- Higher-universe consumer: the coefficient field may live in any universe.
example {K : Type v} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) :=
  HahnSeries.isAlgClosed_rat

-- Positive-characteristic consumer: unlike the former characteristic-zero
-- statement, no `CharZero` hypothesis is needed, so the algebraic closure
-- of the field with three elements is allowed.
example : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure (GaloisField 3 1))) :=
  HahnSeries.isAlgClosed_rat

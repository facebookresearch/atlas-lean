/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.PurelyInseparableFrobenius
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.PurelyInseparable.Basic

@[expose] public section

/-- Consumer with the original binders. -/
theorem exactSource {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] [IsPurelyInseparable M E] (p : ℕ)
    [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange =
        (iterateFrobenius E p r).fieldRange :=
  Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
    p hp

/-- The degree conclusion alone, projected from the consumer. -/
example {M E : Type*} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] [IsPurelyInseparable M E] (p : ℕ)
    [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r := by
  obtain ⟨r, hr, -⟩ := exactSource (M := M) p hp
  exact ⟨r, hr⟩

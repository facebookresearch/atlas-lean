/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.SeparableOfFrobeniusFinrank

@[expose] public section

-- Consumer with the original binders.
example {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hdeg : Module.finrank (frobenius F p).fieldRange F = p)
    (y : E) (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) :
    Algebra.IsSeparable E F :=
  Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq p hdeg y hy

-- The witness hypothesis is not automatic: `0` maps into the field of
-- `p`-th powers, so it can never serve as the witness `y`.
example {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    algebraMap F F (0 : F) ∈ (frobenius F p).fieldRange :=
  ⟨0, by simp⟩

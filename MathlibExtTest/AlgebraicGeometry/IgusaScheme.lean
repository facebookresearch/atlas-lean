/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.IgusaScheme

@[expose] public section

open AlgebraicGeometry

/-- Exact-source consumer, with the original binders. -/
private theorem exactSource (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIntegral (ModularCurve.IgusaScheme N ℓ) :=
  ModularCurve.IgusaScheme.isIntegral N ℓ

/-- The structure morphism of the Igusa scheme lands in the spectrum of `Rat.localizedAt ℓ`. -/
noncomputable example (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ModularCurve.IgusaScheme N ℓ ⟶ Spec (CommRingCat.of (Rat.localizedAt ℓ)) :=
  ModularCurve.IgusaScheme.igusaTo N ℓ

/-- Outside any scope, `chartAlg` has Mathlib's standard `Subalgebra` type, and it is the integral
closure of the generated subalgebra with scalars restricted to `Rat.localizedAt ℓ`. -/
example (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (S : Set ↥(ModularCurve.modularFunctionFieldFull N)) :
    (ModularCurve.IgusaScheme.chartAlg N ℓ S :
        Subalgebra ↥(Rat.localizedAt ℓ) ↥(ModularCurve.modularFunctionFieldFull N)) =
      (integralClosure (Algebra.adjoin ↥(Rat.localizedAt ℓ) S)
        ↥(ModularCurve.modularFunctionFieldFull N)).restrictScalars ↥(Rat.localizedAt ℓ) :=
  rfl

/-- The chart algebras combine with Mathlib's `Algebra.adjoin` for the standard instance. -/
example (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (S : Set ↥(ModularCurve.modularFunctionFieldFull N)) :
    Algebra.adjoin ↥(Rat.localizedAt ℓ) S ≤ ModularCurve.IgusaScheme.chartAlg N ℓ S :=
  ModularCurve.IgusaScheme.adjoin_le_chartAlg N ℓ S

/-- Boundary example at level one and the prime two. -/
example : IsIntegral (ModularCurve.IgusaScheme 1 2) :=
  ModularCurve.IgusaScheme.isIntegral 1 2

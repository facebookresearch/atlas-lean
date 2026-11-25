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

/-- Boundary example at level one and the prime two. -/
example : IsIntegral (ModularCurve.IgusaScheme 1 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ModularCurve.IgusaScheme.isIntegral 1 2

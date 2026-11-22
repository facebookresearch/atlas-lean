/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.ZeroOfAlgHom

@[expose] public section

open scoped TensorProduct

universe u

example {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {B : Type u} [CommRing B] [Algebra R B]
    [NoZeroSMulDivisors R B] [IsReduced (TensorProduct R K B)]
    [Module.Finite K (TensorProduct R K B)] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω] (b : B)
    (hb : ∀ φ : B →ₐ[R] Ω, φ b = 0) : b = 0 :=
  Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct K Ω b hb

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.Embedding

@[expose] public section

example (n : ℕ) [NeZero n] (K : Type*) [Field K] [Algebra ℚ K]
    [IsCyclotomicExtension {n} ℚ K]
    (L : Type*) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ n) :
    ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ :=
  IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension n K L ξ hξ

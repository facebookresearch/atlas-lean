/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.PrimeDegree

@[expose] public section

example (K L : Type*) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    IsGalois K L ∧ orderOf σ = Module.finrank K L ∧ Subgroup.zpowers σ = ⊤ :=
  AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hdeg σ hσ

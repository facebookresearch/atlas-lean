/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.AlgHomCount

@[expose] public section

example (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] :
    Nat.card (B →ₐ[K] K) = Module.finrank K B :=
  AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed K B

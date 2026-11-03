/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Module.InvertibleRankOne

@[expose] public section

universe u v

example {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K],
      Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P :=
  Module.Invertible.of_projective_of_forall_finrank_eq_one P h

example : Module.Invertible ℤ ℤ :=
  Module.Invertible.of_projective_of_forall_finrank_eq_one ℤ (fun _K ↦
    Module.finrank_baseChange.trans (Module.finrank_self ℤ))

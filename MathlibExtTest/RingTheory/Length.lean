/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Length

@[expose] public section

universe u v w

example {R : Type u} {M : Type v} {N : Type w} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (K : Submodule R M) (f : M →ₗ[R] N)
    (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N :=
  Module.length_quotient_le_of_ker_le (R := R) (M := M) (N := N) K f h

example :
    ∀ {R M N : Type} [Ring R] [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] (K : Submodule R M) (f : M →ₗ[R] N)
      (_h : LinearMap.ker f ≤ K),
      Module.length R (M ⧸ K) ≤ Module.length R N :=
  @Module.length_quotient_le_of_ker_le

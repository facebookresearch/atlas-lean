/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.FiniteFree

@[expose] public section

universe u v

example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R : Type v) [CommRing R] [Algebra 𝓞 R] [Module.Finite 𝓞 R] [Module.Free 𝓞 R] :
    IsAdicComplete (Ideal.span {(p : R)}) R :=
  IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p R

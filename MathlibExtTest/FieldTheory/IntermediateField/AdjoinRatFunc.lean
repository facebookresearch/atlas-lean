/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.IntermediateField.AdjoinRatFunc

@[expose] public section

universe u v

example (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] (x : L)
    (hx : Transcendental K x) :
    ∃ e : ↥(IntermediateField.adjoin K ({x} : Set L)) ≃ₐ[K] RatFunc K,
      e ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ = RatFunc.X :=
  IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental K L x hx

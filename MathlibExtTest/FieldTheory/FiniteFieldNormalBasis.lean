/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.FieldTheory.Finite.GaloisField
import MathlibExt.FieldTheory.FiniteFieldNormalBasis

open MetaMathlibExt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- The base field as an extension of itself.
example : ∃ β : ZMod 2, LinearIndependent (ZMod 2) (fun σ : ZMod 2 ≃ₐ[ZMod 2] ZMod 2 => σ β) :=
  exists_normalBasis_finiteField (ZMod 2) (ZMod 2)

-- The quadratic extension of the field of two elements.
example : ∃ β : GaloisField 2 2,
    LinearIndependent (ZMod 2) (fun σ : GaloisField 2 2 ≃ₐ[ZMod 2] GaloisField 2 2 => σ β) := by
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  exact exists_normalBasis_finiteField (ZMod 2) (GaloisField 2 2)

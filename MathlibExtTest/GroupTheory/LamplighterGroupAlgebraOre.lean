/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.LamplighterGroupAlgebraOre
import Mathlib.Algebra.Field.ZMod

open MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted
open Multiplicative

-- The shift moves a lamp one site to the right, including across the origin.
example : shift 3 (ofAdd (Finsupp.single (-1) 2)) = ofAdd (Finsupp.single 0 2) := by
  apply toAdd.injective
  change Finsupp.equivMapDomain (Equiv.addRight 1) (Finsupp.single (-1 : ℤ) (2 : ZMod 3)) = _
  rw [Finsupp.equivMapDomain_single]
  rfl

-- The refutation also applies when the coefficient characteristic equals the lamp order.
example : ¬ IsOreRing (MonoidAlgebra (ZMod 2) (Lamplighter 2)) :=
  fun h ↦ lamplighterGroupAlgebraOre_refuted ⟨ZMod 2, inferInstance, 2, Nat.prime_two, h⟩

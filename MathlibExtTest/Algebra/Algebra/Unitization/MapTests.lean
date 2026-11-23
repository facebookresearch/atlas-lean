/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Algebra.Unitization.Map
import Mathlib.GroupTheory.GroupAction.Ring
import Batteries.Tactic.Lint

noncomputable section
set_option autoImplicit false

universe u v w

/-- The actual lift retains the original scalar and applies the coefficient
map in independent algebra carrier universes over an arbitrary scalar ring. -/
example (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    (B : Type w) [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B]
    (f : A →ₙₐ[k] B) (r : k) (a : A) :
    Unitization.mapAlgHom k A f (Unitization.mk (r, a)) = Unitization.mk (r, f a) :=
  Unitization.mapAlgHom_apply k A f (Unitization.mk (r, a))

/-- A genuine nonunital ring map becomes an integer-linear map by its
actual preservation of integer scaling, in the same two original worlds. -/
example {I : Type v} {J : Type w} [NonUnitalRing I] [NonUnitalRing J]
    (f : I →ₙ+* J) (z : ℤ) (a : I) :
    let fZ : I →ₙₐ[ℤ] J :=
      { f with toFun := f, map_smul' n x := map_zsmul f n x }
    Unitization.mapAlgHom ℤ I fZ (Unitization.mk (z, a)) = Unitization.mk (z, f a) := by
  dsimp only
  exact Unitization.mapAlgHom_apply ℤ I _ (Unitization.mk (z, a))

/-- The zero coefficient map kills the original coefficient and retains
the negative external integer, despite failing to preserve the original unit. -/
example :
    Unitization.mapAlgHom ℤ ℤ (0 : ℤ →ₙₐ[ℤ] ℤ) (Unitization.mk (-3, 7)) =
      Unitization.mk (-3, 0) :=
  Unitization.mapAlgHom_apply ℤ ℤ _ _

#print axioms Unitization.mapAlgHom
#print axioms Unitization.mapAlgHom_inr
#print axioms Unitization.mapAlgHom_inl
#print axioms Unitization.mapAlgHom_apply

#lint only unusedArguments in MathlibExt.Algebra.Algebra.Unitization.Map

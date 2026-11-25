/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
import MathlibExt.KTheory.Ring.K1.Local
import MathlibExt.KTheory.Ring.K2.StableSteinbergUniversal
import MathlibExt.KTheory.Ring.K2.AbelianFunctor

/-!
# Focused ring K-theory public API checks

The whole-root integration check retains the same examples. These imports
exercise the public determinant, central-extension and commutativity API without
loading every MathlibExt domain.
-/

noncomputable example (R : Type*) [CommRing R] [IsLocalRing R] :
    AlgebraicKTheory.K1 R ≃+ Additive Rˣ :=
  AlgebraicKTheory.K1.detEquivUnitsOfLocalRing (R := R)

example (R : Type*) [Ring R] :
    (AlgebraicKTheory.StableSteinberg.steinbergExtension (R := R)).IsUniversal :=
  AlgebraicKTheory.StableSteinberg.steinbergExtension_isUniversal R

example (R : Type*) [Ring R] : IsMulCommutative (AlgebraicKTheory.K2 R) := inferInstance

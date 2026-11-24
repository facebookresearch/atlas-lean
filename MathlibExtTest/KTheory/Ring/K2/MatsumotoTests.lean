/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

import MathlibExt.KTheory.Ring.K2.MatsumotoEquivalence

/-!
# Matsumoto public-API regression tests

Consumer checks for Matsumoto's theorem for fields: the comparison sends the
Milnor symbol to the algebraic Steinberg symbol in order, both unconditional
inverse identities hold via the named theorems, the unconditional equivalence
applies with inferred types, and the equivalence is natural under field homs.
This is Weibel, The K-book, Chapter III, Theorem 6.1.

This covers the principal public surface only, not internal Bruhat/Weyl,
permutation, central-extension, or kernel-generation machinery.
-/

open AlgebraicKTheory

open scoped IsMulCommutative

universe u

namespace MathlibExtTest.KTheory.Ring.K2.MatsumotoTests

-- Symbol orientation: Milnor `(a, b)` maps to algebraic `(a, b)` in order.
example (F : Type u) [Field F] (a b : Fˣ) :
    K2.milnorComparison F (MilnorK.k2Symbol F a b) =
      Additive.ofMul (K2.steinbergSymbol a b) :=
  K2.milnorComparison_k2Symbol F a b

-- Milnor-side inverse through the named unconditional theorem.
example (F : Type u) [Field F] (x : MilnorK F 2) :
    (K2.matsumotoReverse F).toIntLinearMap ((K2.milnorComparison F) x) = x := by
  have h := K2.matsumotoReverse_comp_milnorComparison_eq_id_unconditional F
  have hx := DFunLike.congr_fun h x
  simpa using hx

-- K₂-side inverse through the named unconditional theorem.
example (F : Type u) [Field F] (y : Additive (K2 F)) :
    (K2.milnorComparison F).toAddMonoidHom ((K2.matsumotoReverse F) y) = y := by
  have h := K2.milnorComparison_comp_matsumotoReverse_eq_id_unconditional F
  have hy := DFunLike.congr_fun h y
  simpa using hy

-- Application, type inference, and forward-map wiring for the equivalence.
example (F : Type u) [Field F] (x : MilnorK F 2) :
    K2.matsumotoAddEquiv_unconditional F x = K2.milnorComparison F x := rfl

-- Forward naturality under an arbitrary field hom, without a concrete fixture.
example {F K : Type u} [Field F] [Field K] (f : F →+* K) :
    (K2.mapRingHom f).toAdditive.comp
        (K2.matsumotoAddEquiv_unconditional F).toAddMonoidHom =
      (K2.matsumotoAddEquiv_unconditional K).toAddMonoidHom.comp
        (MilnorK.mapAddHom f 2) :=
  K2.matsumotoAddEquiv_mapRingHom f

end MathlibExtTest.KTheory.Ring.K2.MatsumotoTests

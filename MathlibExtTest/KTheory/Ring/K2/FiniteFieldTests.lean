/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.K2.FiniteField

/-! # Finite field K₂ computation examples

The public computation applies to arbitrary finite fields, F₂ and F₃, and to the
existing ordered Steinberg symbols over F₃.
-/

open AlgebraicKTheory
open scoped IsMulCommutative

universe u

namespace MathlibExtTest.KTheory.Ring.K2.FiniteFieldTests

example (F : Type u) [Field F] [Finite F] (x : K2 F) : x = 1 :=
  K2.finiteField_eq_one x

example (x : K2 (ZMod 2)) : x = 1 :=
  K2.finiteField_eq_one x

example (x : K2 (ZMod 3)) : x = 1 :=
  K2.finiteField_eq_one x

example (a b : (ZMod 3)ˣ) : K2.steinbergSymbol a b = 1 :=
  K2.finiteField_eq_one (K2.steinbergSymbol a b)

end MathlibExtTest.KTheory.Ring.K2.FiniteFieldTests

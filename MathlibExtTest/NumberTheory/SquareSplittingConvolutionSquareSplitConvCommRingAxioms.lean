/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitConvCommRingAxioms

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitConvCommRingAxioms

-- Commutativity evaluated at a concrete point.
example (f g h : ArithmeticFunction ℂ) :
    squareSplitConv f g 72 = squareSplitConv g f 72 :=
  DFunLike.congr_fun (squareSplitConv_commRing_axioms f g h).1 72

-- Associativity evaluated at a concrete point.
example (f g h : ArithmeticFunction ℂ) :
    squareSplitConv (squareSplitConv f g) h 6
      = squareSplitConv f (squareSplitConv g h) 6 :=
  DFunLike.congr_fun (squareSplitConv_commRing_axioms f g h).2.1 6

-- Distributivity evaluated at a concrete point.
example (f g h : ArithmeticFunction ℂ) :
    squareSplitConv f (g + h) 4 = (squareSplitConv f g + squareSplitConv f h) 4 :=
  DFunLike.congr_fun (squareSplitConv_commRing_axioms f g h).2.2.1 4

-- The identity law evaluated at a concrete point.
example (f g h : ArithmeticFunction ℂ) : squareSplitConv 1 f 12 = f 12 :=
  DFunLike.congr_fun (squareSplitConv_commRing_axioms f g h).2.2.2 12

-- Right distributivity follows from commutativity and left distributivity.
example (f g h : ArithmeticFunction ℂ) :
    squareSplitConv (g + h) f = squareSplitConv g f + squareSplitConv h f := by
  have e1 := (squareSplitConv_commRing_axioms f (g + h) h).1
  have e2 := (squareSplitConv_commRing_axioms f g h).2.2.1
  have e3 := (squareSplitConv_commRing_axioms f g h).1
  have e4 := (squareSplitConv_commRing_axioms f h h).1
  rw [← e1, e2, e3, e4]

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitConvCommRingAxioms

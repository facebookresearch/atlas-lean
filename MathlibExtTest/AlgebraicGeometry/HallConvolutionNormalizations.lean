/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HallSemiclassicalOperations
import MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics

/-!
# Actual Hall correspondence and semiclassical quotient checks

The first check verifies every geometric product generator and its
added denominator exponent. The second verifies that the literal
(L−1) quotient identifies the actual affine-line product with the
original regular class.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.HallConvolutionNormalizations

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeometricHallStackFunctions HallFamilyStackModels HallConvolutionOperations
open HallSemiclassicalOperations
open HallProjectiveInverseModels

example {X : Over (Spec (.of ℂ))} {H : HallStacks X} {D : ConvolutionModels H}
    (h : ConvolutionDescent D) (a b : Generator H.moduli) (n m : ℕ) :
    convolution h (stageSymbol a n) (stageSymbol b m) =
      stageSymbol (D a b).generator (n+m) := convolution_stageSymbol h a b n m

example {X : Over (Spec (.of ℂ))} {H : HallStacks X} {D : ConvolutionModels H}
    {h : ConvolutionDescent D} {L : ∀ g : Generator H.moduli, LefschetzProduct g}
    {hL : LefschetzDescent L} (C : RegularClosure h hL) (a : Regular H.moduli) :
    (semiclassicalRelations C).mkQ (regularLefschetz C a - a) = 0 := by
  rw [map_sub,semiclassical_lefschetz C a,sub_self]

/-- Toda's P^1 denominator is an actual scalar action on the corrected regular space. -/
example {M : ComplexStack} (J : ProjectiveInverseModel 1)
    (D : ScalarProductModels M J.inverseStack) (h : ScalarDescent D) (a : Regular M) :
    scalarAction h a.val ∈ regularSubmodule M := projectiveInverse_regular 1 J D h a

end MathlibExtTest.AlgebraicGeometry.HallConvolutionNormalizations

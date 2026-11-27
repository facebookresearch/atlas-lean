/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CriticalMilnorFibreModels
import MathlibExt.AlgebraicGeometry.HallBehrendIntegrationModels
import MathlibExt.AlgebraicGeometry.HallZeroObjectModels

/-!
# Critical-fibre and completed-integration boundary checks

For the zero regular function, every nonzero nearby level is
actually empty. A coefficientwise zero regular Hall series maps
to the coefficientwise zero completed target. These tests use
the native point evaluation and actual monoid-algebra coefficients.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.BehrendHallNormalizations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open IntegralChowChernModels ComplexAnalytification CriticalMilnorFibreModels
open HallNumericalGradingModels HallLaurentCompletion HallBehrendIntegrationModels
open GeometricHallStackFunctions HallFamilyStackModels HallConvolutionOperations
open HallSemiclassicalOperations StackBehrendModels StablePairFamilies

example {U : SchemeData} (E : CoordinateEmbedding U) (p : space U.scheme)
    (epsilon : ℝ) (eta : ℂ) (h : eta≠0) :
    IsEmpty (milnorFibre E (0 : Γ(U.scheme.left, ⊤)) p epsilon eta) := by
  refine ⟨fun q => ?_⟩
  apply h
  have he := q.property.2
  simpa [regularValue,ComplexPoints.eval] using he.symm

example {X : Over (Spec (.of ℂ))} {HX : Threefold X} {N : NumericalData X HX}
    {H : HallStacks X} {D : ConvolutionModels H} {h : ConvolutionDescent D}
    {L : ∀ g : Generator H.moduli, LefschetzProduct g} {hL : LefschetzDescent L}
    {C : RegularClosure h hL} {P : NumericalProjectionData N H}
    {W : StackBehrendModel H.families.carrier} (I : NormalizedIntegration C P W)
    (a : RegularHallSeries H P) (ha : ∀ α : Delta N, a.coefficient α=0) (α : Delta N) :
    (completedIntegration I a).coefficient α=0 := by
  have he : regularCoefficient a α=0 := Subtype.ext (ha α)
  simp [completedIntegration,completedIntegrationValue,he]

end MathlibExtTest.AlgebraicGeometry.BehrendHallNormalizations

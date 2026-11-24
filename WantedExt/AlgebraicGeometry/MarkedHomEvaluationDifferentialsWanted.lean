/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials
public import Batteries.Util.ProofWanted

/-!
# Universal marked evaluation and Kodaira–Spencer comparison

Both sides of each comparison are already computed from actual maps:
the Kähler evaluation derivative, the universal product derivative,
the marking pullback identity, the module adjunction counit, and the
native right-derived unit. A producer cannot substitute an arbitrary
tangent isomorphism or an unrelated cohomology evaluation map.

Behrend–Fantechi, alg-geom/9601010v1, §6, Proposition 6.2 and its proof
construct the universal morphism obstruction theory; restriction at
fixed markings gives these native comparison arrows. This leaves
genus and marking count arbitrary. The source-covered ordinary and
derived comparison data are explicit inputs; their general existence
is not requested again.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MarkedHomEvaluation
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes

/-- The actual marked universal-map restriction satisfies the Kähler chain rule. -/
theorem_wanted markedEvaluationTangentChainRule
    {k : Type} [Field k]
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (C V : Over (Spec (.of k))) (n : ℕ) (P : Markings C n)
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas)
    (B : DifferentialData C V P M a) (i : Fin n) :
    B.universalEvaluationTangent i = B.evaluationTangent i

/-- The genuine degree-zero universal deformation arrow has its actual evaluation derivative. -/
theorem_wanted markedEvaluationKodairaSpencer
    {k : Type} [Field k]
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (C V : Over (Spec (.of k))) [IsProper C.hom] [Smooth C.hom] [Smooth V.hom]
    (n : ℕ) (P : Markings C n)
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas)
    (B : DifferentialData C V P M a)
    (Z : PushforwardH0 (fixedProjection C a.U)
      ((Scheme.Modules.pullback (M.family a.U a.point).map).obj (tangent V)))
    (i : Fin n) :
    B.kodairaSpencerH0 ≫ B.derivedEvaluation Z i = B.evaluationTangent i

end MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials

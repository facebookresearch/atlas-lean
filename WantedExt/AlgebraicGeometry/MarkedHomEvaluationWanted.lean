/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedHomEvaluation
public import Batteries.Util.ProofWanted

/-!
# Actual marked evaluation smoothness from the fixed fibre H1 obstruction

Behrend--Fantechi alg-geom/9601010v1 §6, Proposition 6.2 and its
square-zero extension proof, with restriction at the fixed markings.
Graber--Harris--Starr math/0109220v1 §2 supplies the applications to
marked curve deformation and normal-bundle vanishing.
The atlas is an actual étale fixed-Hom chart and the evaluation is the
literal universal map at the actual disjoint markings. Vanishing is
tested on every actual algebraically closed geometric parameter point.
This covers arbitrary source genus and smooth target dimension; no
degree-one/P^n restriction or free evaluation operator is used.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.MarkedHomEvaluation

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.FourierMukai

theorem_wanted markedHomEvaluationSmooth
    {k : Type} [Field k] [IsAlgClosed k] [HasDerivedPushforwards.{0}]
    (C V : Over (Spec (.of k))) [IsProper C.hom] [Smooth C.hom] [Smooth V.hom]
    (dimension : topologicalKrullDim C.left = 1)
    (n : ℕ) (P : Markings C n)
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas)
    [LocallyOfFinitePresentation (evaluationProduct C V P M a).left]
    (vanishing : IsUnobstructed C V P M a) :
    Smooth (evaluationProduct C V P M a).left

end MathlibExt.AlgebraicGeometry.MarkedHomEvaluation

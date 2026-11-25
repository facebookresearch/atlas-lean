/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MarkedHomEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Normalized universal marked evaluation differentials

The parameter tangent arrow is the dual of the literal Kähler differential
of each marked evaluation. Its second presentation restricts the already
computed universal-map tangent along the actual marking. Restriction of
relative sections is the native pullback/pushforward counit, with the
section identity fixed by `pullbackComp`, `pullbackCongr` and `pullbackId`.

The degree-zero derived restriction uses the actual right-derived unit.
Its comparison with the universal Kodaira–Spencer arrow is a separate
native bridge; none of these maps is an independently supplied tangent
equivalence. The source curve, marking count and smooth target dimension
are unrestricted by genus-zero or projective-space specializations.

Reference: Behrend–Fantechi, alg-geom/9601010v1, §6, Proposition 6.2
(the fixed-source morphism obstruction theory); §4, Proposition 4.1.
The marked restriction is the functorial relative version of that
construction. Kähler and module adjunction primitives are completed
source integration, not additional requested existence results.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MarkedHomEvaluation
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
open MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
open MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers

attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k]

/-- The actual section identity fixes the pullback of every parameter module. -/
def markingPullbackBaseIso (C T : Over (Spec (.of k))) {n : ℕ}
    (P : Markings C n) (i : Fin n) (N : T.left.Modules) :
    (Scheme.Modules.pullback (parameterMark (T := T) P i)).obj
        ((Scheme.Modules.pullback (fixedProjection C T)).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp (parameterMark (T := T) P i)
      (fixedProjection C T)).app N ≪≫
    (Scheme.Modules.pullbackCongr (parameterMark_projection (T := T) P i)).app N ≪≫
      (Scheme.Modules.pullbackId T.left).app N

variable (C V : Over (Spec (.of k))) {n : ℕ} (P : Markings C n)
    (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas)

/-- Actual restriction of relative sections, defined by the native counit. -/
def moduleEvaluation (N : (fixedCurve C a.U).left.Modules) (i : Fin n) :
    (Scheme.Modules.pushforward (fixedProjection C a.U)).obj N ⟶
      (Scheme.Modules.pullback (parameterMark (T := a.U) P i)).obj N :=
  (markingPullbackBaseIso C a.U P i
    ((Scheme.Modules.pushforward (fixedProjection C a.U)).obj N)).inv ≫
      (Scheme.Modules.pullback (parameterMark (T := a.U) P i)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (fixedProjection C a.U)).counit.app N)

/-- Restriction lands in the actual pulled tangent sheaf of the target point. -/
def homModuleEvaluation (i : Fin n) :
    (Scheme.Modules.pushforward (fixedProjection C a.U)).obj
        ((Scheme.Modules.pullback (M.family a.U a.point).map).obj (tangent V)) ⟶
      (Scheme.Modules.pullback (MarkedHomEvaluation.evaluation C V P M a i)).obj (tangent V) :=
  moduleEvaluation C V P M a _ i ≫
    (Scheme.Modules.pullbackComp (parameterMark (T := a.U) P i)
      (M.family a.U a.point).map).hom.app (tangent V)

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- All derivative data are pinned on local functions and actual dual pairings. -/
structure DifferentialData where
  universal : FixedHomDifferentialData C V M a
  evaluationDifferential : ∀ i : Fin n,
    PullbackDifferential V (evaluationOver C V P M a i)
  evaluationPrecomposition : ∀ i : Fin n,
    DualPrecomposition (evaluationDifferential i).map
  evaluationDual : ∀ i : Fin n,
    DualPullback (MarkedHomEvaluation.evaluation C V P M a i) (forms k V 1)

variable {C V P M a}

/-- The literal evaluation tangent map is the dual of its normalized Kähler derivative. -/
def DifferentialData.evaluationTangent (B : DifferentialData C V P M a) (i : Fin n) :
    tangent a.U ⟶
      (Scheme.Modules.pullback (MarkedHomEvaluation.evaluation C V P M a i)).obj (tangent V) :=
  (B.evaluationPrecomposition i).map ≫ (B.evaluationDual i).comparison.inv

/-- Restrict the same universal-map parameter tangent to the actual marked section. -/
def DifferentialData.universalEvaluationTangent
    (B : DifferentialData C V P M a) (i : Fin n) :
    tangent a.U ⟶
      (Scheme.Modules.pullback (MarkedHomEvaluation.evaluation C V P M a i)).obj (tangent V) :=
  (markingPullbackBaseIso C a.U P i (tangent a.U)).inv ≫
    (Scheme.Modules.pullback (parameterMark (T := a.U) P i)).map
      (parameterTangent C V a.U (M.family a.U a.point)
        B.universal.parameter B.universal.differential B.universal.precomposition
        B.universal.dualParameter B.universal.dualTarget) ≫
      (Scheme.Modules.pullbackComp (parameterMark (T := a.U) P i)
        (M.family a.U a.point).map).hom.app (tangent V)

/-- The map on parameter tangent is induced by the computed derived Kodaira–Spencer arrow. -/
def DifferentialData.kodairaSpencerH0 (B : DifferentialData C V P M a) :
    tangent a.U ⟶
      (DerivedCategory.homologyFunctor a.U.left.Modules 0).obj
        (fixedDeformation C V a.U (M.family a.U a.point)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso a.U.left.Modules 0).inv.app
      (tangent a.U) ≫
    (DerivedCategory.homologyFunctor a.U.left.Modules 0).map B.universal.kodairaSpencer

/-- The degree-zero module comparison is the actual right-derived unit on a single complex. -/
def pushforwardH0Map {X Y : Scheme.{0}} (p : X ⟶ Y) (N : X.Modules) :
    (Scheme.Modules.pushforward p).obj N ⟶
      (DerivedCategory.homologyFunctor Y.Modules 0).obj
        ((derivedPushforward p).obj ((DerivedCategory.singleFunctor X.Modules 0).obj N)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).inv.app
      ((Scheme.Modules.pushforward p).obj N) ≫
    (DerivedCategory.homologyFunctor Y.Modules 0).map
      (DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pushforward p) (.up ℤ) 0).inv.app N) ≫
        (derivedPushforwardUnit p).app ((CochainComplex.singleFunctor X.Modules 0).obj N))

/-- An identification of $p_*N$ with the degree-zero cohomology of $Rp_*N$, for a morphism of
schemes $p : X \to Y$ and a sheaf of $\mathcal{O}_X$-modules $N$, given derived direct images
(`HasDerivedPushforwards`): an isomorphism from $p_*N$ to $H^0(Rp_*N)$, with $N$ placed in degree
$0$, whose forward map is the canonical map `pushforwardH0Map p N` induced by the unit
$p_* \to Rp_*$ of the right derived functor. -/
structure PushforwardH0 {X Y : Scheme.{0}} (p : X ⟶ Y) (N : X.Modules) where
  comparison : (Scheme.Modules.pushforward p).obj N ≅
    (DerivedCategory.homologyFunctor Y.Modules 0).obj
      ((derivedPushforward p).obj ((DerivedCategory.singleFunctor X.Modules 0).obj N))
  normalized : comparison.hom = pushforwardH0Map p N

/-- The derived target bundle is identified by the fixed pullback counit. -/
def DifferentialData.fixedSourceIso (B : DifferentialData C V P M a) :
    (derivedPushforward (fixedProjection C a.U)).obj
        ((DerivedCategory.singleFunctor (fixedCurve C a.U).left.Modules 0).obj
          ((Scheme.Modules.pullback (M.family a.U a.point).map).obj (tangent V))) ≅
      fixedDeformation C V a.U (M.family a.U a.point) :=
  (derivedPushforward (fixedProjection C a.U)).mapIso
    (singlePullbackIso (M.family a.U a.point).map (tangent V) 0 B.universal.targetBundle).symm

/-- Degree-zero derived evaluation uses the fixed bundle comparison and native restriction. -/
def DifferentialData.derivedEvaluation (B : DifferentialData C V P M a)
    (Z : PushforwardH0 (fixedProjection C a.U)
      ((Scheme.Modules.pullback (M.family a.U a.point).map).obj (tangent V))) (i : Fin n) :
    (DerivedCategory.homologyFunctor a.U.left.Modules 0).obj
        (fixedDeformation C V a.U (M.family a.U a.point)) ⟶
      (Scheme.Modules.pullback (MarkedHomEvaluation.evaluation C V P M a i)).obj (tangent V) :=
  ((DerivedCategory.homologyFunctor a.U.left.Modules 0).mapIso B.fixedSourceIso).inv ≫
    Z.comparison.inv ≫ homModuleEvaluation C V P M a i

end MathlibExt.AlgebraicGeometry.MarkedHomEvaluationDifferentials

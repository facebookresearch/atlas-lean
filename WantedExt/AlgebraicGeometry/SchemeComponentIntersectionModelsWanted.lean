/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SchemeComponentIntersectionModels

/-!
# Component-cycle construction and coherent degree requests

The outputs contain the complete native component carrier, reduced closed
subschemes, finite original local-ring lengths and native coherent degree
presentations. Provider proofs remain separate from these interfaces.
Source: Yuan--Zhang, arXiv:2105.13587v9, Lemma 4.2.2 and Appendix A.6.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SchemeComponentIntersectionModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings
open MathlibExt.AlgebraicGeometry.SchemeComponentIntersectionModels
open MathlibExt.AlgebraicGeometry.ModelIntersectionDegrees

public def_wanted components (X : Scheme.{0}) [IsNoetherian X] : ComponentSources X

variable [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPullbacks.{0}]
  [MathlibExt.AlgebraicGeometry.FourierMukai.HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

public def_wanted intersectionSources (K : Type) [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom]
    (d : ℕ) (dimension : IsPureRelativeDimension X.hom d)
    (L : Fin d → X.left.Modules)
    (lines : ∀ i, MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.IsLineBundle (L i)) :
    ComponentIntersectionSources X d L

/-- The coherent intersection degree uses the whole nonreduced fundamental cycle. -/
public theorem_wanted totalDegree (K : Type) [Field K] (X : Over (Spec (.of K)))
    (d : ℕ) (L : Fin d → X.left.Modules) (D : DegreeData X d L)
    (S : ComponentIntersectionSources X d L) :
    componentTotalDegree S = mixedDegree D

end WantedExt.AlgebraicGeometry.SchemeComponentIntersectionModels

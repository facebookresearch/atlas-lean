/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Identity of positive refinement

An identity pole-chart refinement induces the identity on the completed coefficient ring.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1;
Beauville--Laszlo descent.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicCompletionRefinements AnalyticProObjectSites
open MeromorphicCoefficientCompletion

/-- The identity refinement induces the identity of completed rings: for a prime $p$, a field $E$, a
map $d : D \to X$ of $E$-spaces with a puncture `U` and a pole chart `Q` at `U`, a refinement $r$ of
`Q` by itself whose map of chart spaces is the identity, and a coefficient refinement `R` for $r$,
the induced map of the completion of the chart's coefficient ring along the divisor (`positiveMap`)
is the identity. -/
public theorem positiveRefinement_identity (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] {X D : ESpace p E}
    (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (r : PoleRefinement p E d U Q Q) (hr : r.map = 𝟙 Q.space)
    (R : CoefficientRefinement p E d U Q Q r) :
    positiveMap p E d U Q Q r R.powers R.finite = RingHom.id _ := by
  apply RingHom.ext
  intro a
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [positiveMap_finite]
  change Ideal.quotientMap (chartIdeal p E d U Q ^ n) (sectionMap p E r.map)
    (R.powers n) (AdicCompletion.evalₐ (chartIdeal p E d U Q) n a) =
      AdicCompletion.evalₐ (chartIdeal p E d U Q) n a
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (chartIdeal p E d U Q) n a)
  rw [← hb, Ideal.quotientMap_mk]
  simp [hr, sectionMap]
  rfl

end WantedExt.AlgebraicGeometry.MeromorphicTorsorCompletion

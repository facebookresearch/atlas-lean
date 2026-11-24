/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Full analytic pro-object site integration

The constructions preserve all native presentation projections, original
Tate coefficients and full natural-transformation arrows. The represented
affinoids form a comparison boundary inside this formal pro-object site.
The requested comparison does not redefine pro-objects by completed rings.

References: Scholze arXiv:1205.3463v2, Definitions 3.1/3.9 and Lemma 3.10;
BMS18 arXiv:1602.03148v3, Section 5.1 (including transfinite coverings).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticProObjectSites

open CategoryTheory
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

public def_wanted actualProObjectPoints (p : ℕ) [Fact p.Prime]
    (G : AnalyticAdicSpace p) (h : IsLocallyNoetherian p G) : PointRealization p G

public theorem_wanted etaleInclusionContinuous (p : ℕ) [Fact p.Prime]
    (G : AnalyticAdicSpace p) (h : IsLocallyNoetherian p G) (R : PointRealization p G) :
    (etaleEmbedding p G).IsContinuous
      (MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites.analyticEtaleTopology p G)
      (bmsTopology p G R)

/-- Every full pro-object is locally represented with the original
complete-ring and point-limit normalization. -/
public def_wanted representedBoundaryCover (p : ℕ) [Fact p.Prime]
    (G : AnalyticAdicSpace p) (h : IsLocallyNoetherian p G) (R : PointRealization p G)
    (U : ProEtaleSite p G) :
    Σ' (I : Type 1) (B : I → RepresentedBoundary p G R) (f : ∀ i, (B i).formal ⟶ U),
      (∀ i, IsBMSCoverMap p G R (f i)) ∧
      (∀ x : R.functor.obj U, ∃ i, x ∈ Set.range (R.functor.map (f i)))

public def_wanted representedBoundaryGeometry (p : ℕ) [Fact p.Prime]
    (G : AnalyticAdicSpace p) (h : IsLocallyNoetherian p G) (R : PointRealization p G) :
    RepresentedBoundary.GeometryComparison p G R

/-- The comparison theorem concerns the concrete restriction functor on
all objects and all pro-morphisms of this source-normalized boundary. -/
public theorem_wanted representedBoundarySheafComparison (p : ℕ) [Fact p.Prime]
    (G : AnalyticAdicSpace p) (h : IsLocallyNoetherian p G) (R : PointRealization p G) :
    ((RepresentedBoundary.inclusion p G R).sheafPushforwardContinuous (ModuleCat.{1} ℤ)
      (RepresentedBoundary.boundaryTopology p G R) (bmsTopology p G R)).IsEquivalence

end WantedExt.AlgebraicGeometry.AnalyticProObjectSites

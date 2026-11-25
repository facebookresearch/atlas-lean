/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffinoidTorsorAlgebraizationModels
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Original all-test torsor algebraization and native fpqc pullback requests

The source algebraization retains the whole original analytic torsor
presheaf and every action/map on actual Gamma spectrum tests. Its source
is an actual strongly noetherian whole affinoid chart. Native completion
and fpqc restriction are computed separately from this source output.

Source: Fargues--Scholze arXiv:2102.13459v4, Section III.3 and VI.1;
Stacks Project, Tags03AG and04UV; affinoid algebraization.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffinoidTorsorAlgebraization

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticDiamondEtaleSites AnalyticProObjectSites
open AnalyticGroupTorsorSites
open AffinoidTorsorAlgebraizationModels

/-- Algebraize the original native analytic torsors, retaining all tests, actions and equivariant maps. -/
public def_wanted affinoidTorsorAlgebraization (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (X : ESpace p E) (Q : Chart p X.left) [IsIso Q.map]
    (hQ : IsStronglyNoetherian p Q.pair) : Algebraization p E G H X

/-- Restriction along each actual scheme map preserves the native fpqc torsor condition. -/
public theorem_wanted fpqcRestrictionPreservesTorsors
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    {B C : Over (Spec (.of E))} (f : B ⟶ C) : FpqcPreservesTorsors E G f

end WantedExt.AlgebraicGeometry.AffinoidTorsorAlgebraization

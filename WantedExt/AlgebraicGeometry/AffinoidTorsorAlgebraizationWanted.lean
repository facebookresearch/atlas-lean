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

/-- Algebraization of $G$-torsors on an affinoid space: let $p$ be a prime, $E$ a field and $G$ a
reductive group scheme over $E$, and suppose (`H`) that for every $E$-space $V$ (an analytic adic
space with a ring map $E → Γ(V, \mathcal O_V)$) the presheaf
$T ↦ G(\operatorname{Spec} Γ(T, \mathcal O_T))$ is a sheaf on the big étale site of $V$. Let $X$ be
an $E$-space whose affinoid chart `Q` is an isomorphism onto $X$, with a strongly noetherian Tate
ring. Then there is a functor from $G$-torsors on the big étale site of $X$ to fpqc $G$-torsors over
$\operatorname{Spec} Γ(X, \mathcal O_X)$, with natural identifications of their values on every $T$
over $X$, through $\operatorname{Spec} Γ(T, \mathcal O_T)$, compatible with torsor maps and the
actions of $G$ (`Algebraization`). -/
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

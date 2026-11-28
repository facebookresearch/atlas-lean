/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.MeromorphicGroupFactorizationMeromorphicGroupFactorizationUnique
public import MathlibExt.AlgebraicGeometry.MeromorphicGroupFactorizationPuncturedParameterUnit

/-!
# Actual finite-pole G-factorization and coefficient restriction requests

The input is the original meromorphic torsor comparison on actual
Cartier charts. The reductive hypothesis includes native affine,
finite-presentation, smooth and geometrically connected group geometry.
The output point is over A[1/t] and its restriction must be the original
framed punctured comparison. Completion is already a computed map on
that finite-pole ring and its image subring.

These requests do not assign completed coefficients to arbitrary
analytic punctured functions. Unframed torsor algebraization, all
refinement maps and the normalized B_dR-position interface remain
further required operations, as do the equal-characteristic families.

Source: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1;
Beauville--Laszlo, *Un lemme de descente*.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCoefficientCompletion
open FramedMeromorphicGroupModels

/-- Let $p$ be a prime, $E$ a field, $d : D → X$ a morphism of analytic adic spaces over $E$ and
$U$ a puncture of $d$, and assume that $d$ has a Cartier atlas (`CartierAtlas`). Let $Q$ be a pole
chart of $d$ (`PoleChart`) whose parameter $t$ restricts to a unit on the punctured chart of $Q$.
Then the restriction map from the finite-pole coefficient ring $\mathcal{O}(Q)[1/t]$ to the
global sections of the punctured chart is injective. -/
public theorem_wanted meromorphic_restriction_injective
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter)) :
    Function.Injective (puncturedMap p E d U Q h)

/-- Factorization of meromorphic modifications through finite-pole coefficients: let $p$ be a
prime, $E$ a field and $G$ a reductive group scheme over $E$, with given torsor descent data $H$
and pullback compatibility $P$ on analytic adic spaces over $E$. Let $d : D → X$ be a morphism of
such spaces with a puncture $U$, and $Q$ a pole chart of $d$ whose parameter $t$ restricts to a
unit on the punctured chart, such that restriction from $\mathcal{O}(Q)[1/t]$ to the sections of
the punctured chart is injective. For a meromorphic modification $M$ of $G$-bundles on $X$ along
$d$ (`Modification`, `IsMeromorphic`) and integral frames of both of its bundles on $Q$: a point
of $G$ over $\mathcal{O}(Q)[1/t]$ whose restriction to the punctured chart is the comparison
element of $M$ in these frames (`GroupFactorization`). -/
public def_wanted meromorphicGroupFactorization
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E)) G]
    (H : ∀ V : ESpace p E, GroupDescent p E G V)
    (P : PullbackPreservation p E G H)
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (Q : PoleChart p E d U)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (hi : Function.Injective (puncturedMap p E d U Q h))
    (M : Modification p E G H P d U)
    (hM : MeromorphicHeckeModels.IsMeromorphic p E G H P d U M)
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right) :
    GroupFactorization p E G H P d U Q h M left right

end WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization

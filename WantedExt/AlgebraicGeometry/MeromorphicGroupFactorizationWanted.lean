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

/-- The actual Cartier generator restricts to a unit on the actual complement. -/
public theorem_wanted punctured_parameter_unit
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U) :
    IsUnit (sectionMap p E Q.puncture.map Q.parameter)

/-- Finite-pole coefficients embed in the original punctured analytic ring. -/
public theorem_wanted meromorphic_restriction_injective
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter)) :
    Function.Injective (puncturedMap p E d U Q h)

/-- The original meromorphic comparison factors through its actual A[1/t] G-points. -/
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

/-- The actual punctured restriction fixes the meromorphic G-point uniquely. -/
public theorem_wanted meromorphicGroupFactorization_unique
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
    (left : IntegralFrame p E G H d U Q M.left)
    (right : IntegralFrame p E G H d U Q M.right)
    (F N : GroupFactorization p E G H P d U Q h M left right) : F.element = N.element

end WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization

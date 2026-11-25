/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralAnalyticGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# General analytic realization and coherent GAGA interfaces

These are shared construction/proof requests. Paper tasks may bind the
public AnalyticSpace, Morphism, CoherentPullback and GAGA contracts while
contributors finish the providers. Singular and nonreduced finite-type
complex schemes use actual polynomial local quotients, not manifold
replacement spaces. The earlier smooth hypercohomology and Cartan-B
requests remain specializations rather than duplicate general providers.

References: Serre, GAGA, https://doi.org/10.5802/aif.59;
SGA1, Expose XII, Theorem 4.4: coherent GAGA for proper complex schemes.
https://arxiv.org/abs/math/0206203
Existing Axiom/Weil curve functions/Picard and generic exact derived functor
constructions are covered support, not new theorem requests.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralAnalyticGeometryWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeneralAnalyticGeometry
open MathlibExt.AlgebraicGeometry.AnalyticRealization (ComplexScheme)
open MathlibExt.AlgebraicGeometry.PolynomialAnalyticSpaces

def_wanted affine_analytic_map (n : ℕ)
    (I : Ideal (PolynomialRing n)) :
    AffineAnalyticMap n I

def_wanted analytic_realization (X : ComplexScheme)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    AnalyticSpace X

def_wanted analytic_morphism (X Y : ComplexScheme)
    [IsSeparated X.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact X.hom] [QuasiCompact Y.hom]
    (A : AnalyticSpace X) (B : AnalyticSpace Y) (f : X ⟶ Y) : A.Morphism B f

theorem_wanted coherent_pullback (X : ComplexScheme)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (A : AnalyticSpace X) : A.CoherentPullback

theorem_wanted proper_gaga (X : ComplexScheme) [IsProper X.hom]
    (A : AnalyticSpace X) : A.GAGA

end WantedExt.AlgebraicGeometry.GeneralAnalyticGeometryWanted

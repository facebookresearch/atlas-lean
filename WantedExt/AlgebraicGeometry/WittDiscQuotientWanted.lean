/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.WittFramingComparisonModels
public import MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Original Witt-disc torsor quotient and restriction requests

Source: Zhu, arXiv:1407.8519v3, Lemma 1.3, pp. 8--9,
with the perfect residue field and ramified coefficient scope of Section 0.5.
The actual native group sheaf, fpqc torsor groupoid and punctured-frame
category are completed definitions. The output preserves all native
Witt-ring maps, torsor actions and the original punctured frame square.

The quotient is the genuine fpqc positive-loop quotient. Its loop
normalization retains left multiplication by the original loop on every
scheme-valued point, and its field/base-change dictionary uses the actual
framed restriction functors. These are construction/comparison requests,
not assumptions that the source group already satisfies the conclusion.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.WittDiscQuotient

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
open MathlibExt.AlgebraicGeometry.WittFramingComparisonModels

/-- Construct all actual framed restrictions, retaining original actions and frames. -/
public def_wanted framedTorsorRestrictionData
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsAffineHom G.hom]
    [LocallyOfFinitePresentation G.hom] [Smooth G.hom] [GeometricallyConnected G.hom] :
    RestrictionData p k B pi G

/-- Identify the actual loop quotient with genuine punctured-framed G-torsors. -/
public def_wanted discTorsorQuotientComparison
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsAffineHom G.hom]
    [LocallyOfFinitePresentation G.hom] [Smooth G.hom] [GeometricallyConnected G.hom]
    (D : RestrictionData p k B pi G) : TorsorQuotientComparison p k B pi G D

end WantedExt.AlgebraicGeometry.WittDiscQuotient

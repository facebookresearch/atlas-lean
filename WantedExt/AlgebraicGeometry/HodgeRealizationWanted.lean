/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.HodgeRealization

/-!
# Geometric pure Hodge realization

This packet asks for the smooth-proper geometric realization, not for a
Hodge structure chosen on an unrelated vector space. Holomorphic forms,
the exterior derivative, the constant-unit comparison and the filtration
are fixed in the completed core. Abstract mixed Hodge structures are
adapted separately from public TauCeti code.

Sources: Deligne, *Théorie de Hodge II*, §2.2;
Peters--Steenbrink, *Mixed Hodge Structures*, Chapter 2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HodgeRealizationWanted

open CategoryTheory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticRealization HolomorphicDeRham HodgeRealization PerverseSheaves

/-- The actual holomorphic de Rham unit is a quasi-isomorphism. Its degree
zero map is fixed by the constant global function `1`; its higher arrows
are the coordinate exterior derivative. -/
public theorem_wanted holomorphic_poincare
    (X : AnalyticRealization.ComplexScheme) (d : ℕ) [AnalyticManifold X d]
    (D : HolomorphicDeRhamData X d) : QuasiIso D.complexUnit

/-- The normalized Betti--de Rham comparison realizes smooth proper
cohomology as a pure rational Hodge structure of weight its cohomological
degree, with precisely the geometric brutal-cut Hodge filtration. -/
public def_wanted smooth_proper_hodge_realization
    (X : AnalyticRealization.ComplexScheme) (d : ℕ) [IsComplexVariety X]
    [Smooth X.hom] [IsProper X.hom] [AnalyticManifold X d]
    [RegularFunctions X d] (D : HolomorphicDeRhamData X d)
    (R : BettiDeRhamResolution X d D) (n : ℕ) : PureBettiHodgeData R (n : ℤ)

end WantedExt.AlgebraicGeometry.HodgeRealizationWanted

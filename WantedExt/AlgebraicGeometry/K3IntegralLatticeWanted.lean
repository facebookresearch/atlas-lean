/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.K3IntegralLattice

/-!
# The integral K3 cup-lattice comparison

Huybrechts, *Lectures on K3 surfaces*, Chapter1, Definition3.1 and
Proposition3.5. The compact connected analytic surface has actual
H^1(O_an)=0 and a nowhere-vanishing actual holomorphic two-form. Its
cohomology is integral constant-sheaf derived cohomology, and every
pairing value is the actual Yoneda cup product. No rational Hodge
isometry or Torelli implication is asserted or assumed.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.K3IntegralLatticeWanted

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AnalyticRealization
open MathlibExt.AlgebraicGeometry.K3IntegralLattice
open MathlibExt.AlgebraicGeometry.ComplexAnalytification

/-- **Integral cup-product lattice of a K3 surface.** Let $X$ be a proper complex scheme, smooth
of relative dimension 2, with a given complex-manifold structure of dimension 2 on its space of
complex points (`AnalyticManifold`) in which regular functions are holomorphic
(`RegularFunctions`), such that this space is compact and connected,
$H^1(X^{an}, \mathcal{O}_{X^{an}}) = 0$, and $X$ has a nowhere-vanishing holomorphic 2-form. Then:
isomorphisms $H^2(X^{an}, ℤ) ≅ ℤ^{22}$ and $H^4(X^{an}, ℤ) ≅ ℤ$ (constant-sheaf cohomology) under
which the cup product becomes the pairing of the lattice $3U ⊕ E_8(-1) ⊕ E_8(-1)$
(`IntegralCupComparison`). -/
public def_wanted integral_k3_cup_lattice (X : ComplexScheme)
    [AnalyticManifold X 2] [RegularFunctions X 2]
    [IsProper X.hom] [SmoothOfRelativeDimension 2 X.hom]
    [CompactSpace (space X)] [ConnectedSpace (space X)]
    (h1 : IsZero (holomorphicH1 X)) (volume : HolomorphicVolume X) :
    IntegralCupComparison X

end WantedExt.AlgebraicGeometry.K3IntegralLatticeWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.TypeA2FlagCorrespondences

/-!
# Geometric type A2 nil-Hecke realization

Choose compatible complex purities for the actual full-flag and adjacent-
flag incidence spaces, and prove the square-zero and braid relations for
the computed degree-minus-two pullback/proper-trace operators. The longest-
word point-class normalization fixes a geometric scale and excludes zero
operators. The target chooses the compatible family; it does not falsely
assert braid laws for independently rescaled arbitrary purities.

The literal Bott--Samelson gallery and evaluation maps are completed support.
This scope is the rational Betti flag calculus in type A2. General algebraic
flag-scheme construction, Bruhat resolutions in all ranks, and general
Schubert multiplication remain residual scope.

Reference: Bernstein--Gelfand--Gelfand, *Schubert cells and the cohomology of
the spaces G/P*, Russian Math. Surveys 28 (1973), §3.
Public-source generic Gysin/duality, finite Weyl/Bruhat combinatorics and
TauCeti's word-121 moment-value table are already covered and excluded.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.TypeA2NilHeckeWanted

open MathlibExt.AlgebraicGeometry.TypeA2FlagCorrespondences

/-- **Geometric nil-Hecke relations on the flag manifold of $\mathbb{C}^3$.** Let $\mathrm{Fl}$
be the space of complete flags in $\mathbb{C}^3$ (given by Hermitian projectors) and, for
$i = 1, 2$, $Z_i$ the correspondence of pairs of flags that agree except possibly in their
$i$-dimensional subspace, with the given dualizing complexes and proper pullback data
(`DualityInputs`). Then: identifications of the dualizing complexes of $\mathrm{Fl}$, of the $Z_i$
and of the point with $\mathbb{Q}[6]$, $\mathbb{Q}[8]$ and $\mathbb{Q}$, such that the resulting
Demazure operators $\partial_i$ on rational cohomology (pullback along the second projection
$Z_i \to \mathrm{Fl}$, then proper pushforward along the first, lowering the degree by $2$)
satisfy $\partial_i^2 = 0$ and
$\partial_1 \partial_2 \partial_1 = \partial_2 \partial_1 \partial_2$, and
$\partial_1 \partial_2 \partial_1$ sends the class of the standard flag to $1$. -/
public def_wanted geometricNilHecke (U : DualityInputs) : NilHeckePurities U

end WantedExt.AlgebraicGeometry.TypeA2NilHeckeWanted

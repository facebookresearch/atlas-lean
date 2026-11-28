/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogPairs
public import MathlibExt.AlgebraicGeometry.LogPairDiscrepancyCanonicalFrameIndependence
public import MathlibExt.AlgebraicGeometry.LogPairDiscrepancyDiscrepancyAdjointIndependence

/-!
# General canonical and discrepancy proof contracts

These requests use actual normal finite-type schemes, rational differentials,
codimension-one orders, Cartier cocycles and line bundles. The computed
discrepancy is `1 + canonical order - pulled adjoint order`. Source/model
invariance is an explicit proof obligation; adjoint-presentation invariance
is proved in
`MathlibExt.AlgebraicGeometry.LogPairDiscrepancyDiscrepancyAdjointIndependence`.
A klt or discrepancy value is not supplied as an uninterpreted predicate or
field.

References: Hartshorne, *Algebraic Geometry*, II.6; Kollár--Mori,
*Birational Geometry of Algebraic Varieties*, §2.3. Native function fields,
local orders and stalk scalar maps are covered Mathlib support. General
canonical/Cartier gluing and birational normalization are shared dependencies
for these minimal log-pair interfaces, not claims of a completed MMP theory.
The earlier principalization and affine hypersurface requests remain in
their original scope.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

open MathlibExt.AlgebraicGeometry.LogPairs

universe u

/-- Canonical data on a normal variety: for a field $k$ of characteristic zero and a normal variety
$V$ of dimension $n$ over $k$ (integral, Noetherian, separated, locally of finite type and
quasi-compact, with integrally closed local rings), canonical data on $V$ (recording that $k$ is
perfect): a nonzero rational top form together with, at every codimension-one point $p$, a basis of
the top Kähler forms of the local ring at $p$ and its image basis of the rational top forms, such
that the orders of the form in these bases are nonzero at only finitely many points. -/
public def_wanted canonical_data (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) : CanonicalData V

/-- Every proper birational model of a log pair carries the canonical comparison data: for a field
$k$ of characteristic zero and a log pair $P$ over $k$, every proper birational morphism
$f : W \to X$ from a normal variety $W$ of the same dimension to the variety $X$ of $P$ admits
`BirationalData`: $f$ maps the generic point to the generic point, the induced map of function
fields is a $k$-isomorphism, and $W$ has canonical data whose rational top form is the pullback of
that of $P$. -/
public def_wanted model_calculus (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) : HasModelCalculus P

/-- The log discrepancy depends only on the divisorial valuation: for a field $k$ of characteristic
zero and a log pair $P$ over $k$, if prime divisors $p$ and $q$ on two proper birational models of
$P$ induce the same valuation on the function field of the variety of $P$, their log discrepancies
are equal. -/
public theorem_wanted discrepancy_model_independence (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (M N : BirationalModel P)
    (p : PrimePoint M.variety) (q : PrimePoint N.variety)
    (same : ∀ a, valuationOnBase M p a = valuationOnBase N q a) :
    logDiscrepancy M p = logDiscrepancy N q

end WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

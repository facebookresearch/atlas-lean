/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogPairs

/-!
# General canonical and discrepancy proof contracts

These requests use actual normal finite-type schemes, rational differentials,
codimension-one orders, Cartier cocycles and line bundles. The computed
discrepancy is `1 + canonical order - pulled adjoint order`. Source/model
and adjoint-presentation invariance are explicit proof obligations; a klt
or discrepancy value is not supplied as an uninterpreted predicate or field.

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

/-- Canonical local/rational frames with finite divisor support. -/
public def_wanted canonical_data (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) : CanonicalData V

/-- The canonical Weil coefficients do not depend on the chosen local frames. -/
public theorem_wanted canonical_frame_independence (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) (C D : CanonicalData V) (same : C.form = D.form) :
    canonicalDivisor C = canonicalDivisor D

/-- Every actual normal proper birational model admits the normalized calculus. -/
public def_wanted model_calculus (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) : HasModelCalculus P

/-- Equivalent Cartier representations of K+Delta give the same discrepancy. -/
public theorem_wanted discrepancy_adjoint_independence (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (M : BirationalModel P)
    (D : CartierCombination P.variety)
    (h : D.divisor = realCast (canonicalDivisor P.canonical) + P.boundary)
    (p : PrimePoint M.variety) :
    logDiscrepancy M p = logDiscrepancy (M.withAdjoint D h) p

/-- A divisorial valuation has an intrinsic log discrepancy. -/
public theorem_wanted discrepancy_model_independence (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (M N : BirationalModel P)
    (p : PrimePoint M.variety) (q : PrimePoint N.variety)
    (same : ∀ a, valuationOnBase M p a = valuationOnBase N q a) :
    logDiscrepancy M p = logDiscrepancy N q

end WantedExt.AlgebraicGeometry.LogPairDiscrepancyWanted

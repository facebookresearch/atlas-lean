/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GlobalPerfectedPerfModels

/-!
# Hypercomplete arc descent of the actual full Perf(Xperf) categories

The Frobenius source includes primality. Every perfected scheme,
original hypercover level/map, constant coefficient fibre, full
categorical limit and comparison is independently fixed. Descent is
the output, including the source's symmetric fixed Tor-amplitude scope.

Source: Bhatt--Mathew1807.04725v4, Theorem5.16 and its proof.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GlobalPerfectedPerfModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneralArcHypercoverModels FrobeniusPerfectionModels GlobalFpPerfectionModels
open OrdinarySchemeTorModels OrdinaryConstantCoefficientModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels

variable {p : ℕ} {F : FrobeniusSource p} (G : GlobalPerfectionSource F)
  {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)
  {X : FpSchemes p} (H : SimplicialObject (Over X.left))
  [∀ m : ℕ, HasLimit (matchingDiagram H m)]

/-- Theorem5.16: the actual complete categorical comparison is an equivalence for every original arc hypercover. -/
theorem_wanted perfected_perf_arc_hyperdescent (h : IsArcHypercover H) :
  CategoricalWeakEquivalence (perfectedComparison H G M)

/-- The source's [-n,n] full Tor-amplitude categories have the same hypercomplete arc descent. -/
theorem_wanted perfected_tor_perf_arc_hyperdescent (h : IsArcHypercover H)
    (T : OrdinaryTorSystem N) (n : ℕ)
    (I : TorComparison M T (perfectedDiagram H G) (-(n : ℤ)) (n : ℤ)) :
  CategoricalWeakEquivalence I.map

end MathlibExt.AlgebraicGeometry.GlobalPerfectedPerfModels

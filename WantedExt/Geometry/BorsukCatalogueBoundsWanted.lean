/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Catalogue bounds for the first Borsuk failure
-/
module

public import Batteries.Util.ProofWanted

public import MathlibExt.Geometry.Euclidean.BorsukNumber

@[expose] public section

namespace WantedExt.Geometry.BorsukCatalogueBoundsWanted

open Metric

/-- Kahn and Kalai's first explicit failing dimension 1325. This is an unproved claim.
Source: Optimization Problems, constant 28a, [KK1993-ub-1325]. -/
private theorem_wanted kahnKalaiUpperBound : firstBorsukFailureDimension ≤ 1325

/-- Nilli's 1994 improvement to dimension 946. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-improvements]. -/
private theorem_wanted nilliUpperBound : firstBorsukFailureDimension ≤ 946

/-- Raigorodskii's 1997 bound 561. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-improvements]. -/
private theorem_wanted raigorodskiiUpperBound : firstBorsukFailureDimension ≤ 561

/-- Weißbach's 2000 bound 560. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-improvements]. -/
private theorem_wanted weissbachUpperBound : firstBorsukFailureDimension ≤ 560

/-- Hinrichs' 2002 spherical-code bound 323. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-improvements]. -/
private theorem_wanted hinrichsUpperBound : firstBorsukFailureDimension ≤ 323

/-- Pikhurko's 2002 bound 321. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Pik2002-ub-321-322]. -/
private theorem_wanted pikhurkoUpperBound : firstBorsukFailureDimension ≤ 321

/-- Hinrichs and Richter's 2003 bound 298. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-298]. -/
private theorem_wanted hinrichsRichterUpperBound : firstBorsukFailureDimension ≤ 298

/-- Bondarenko's 2014 two-distance bound 65. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-65]. -/
private theorem_wanted bondarenkoUpperBound : firstBorsukFailureDimension ≤ 65

/-- Jenrich and Brouwer's 2014 bound 64. This is an unproved claim.
Source: Optimization Problems, constant 28a, [JB2014-ub-64]. -/
private theorem_wanted jenrichBrouwerUpperBound : firstBorsukFailureDimension ≤ 64

/-- Grinsztajn's 2026 bound 63. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Gri2026]. -/
private theorem_wanted grinsztajnUpperBound : firstBorsukFailureDimension ≤ 63

/-- The classical lower bound 4. This is an unproved claim.
Source: Optimization Problems, constant 28a, Known lower bounds. -/
private theorem_wanted classicalLowerBound : 4 ≤ firstBorsukFailureDimension

/-- Borsuk's partition bound is true in dimensions 1 through 3. This is an unproved claim.
Source: Optimization Problems, constant 28a, [WX2022-lb-nle3]. -/
private theorem_wanted borsukConjectureThroughDimensionThree :
  ∀ n : ℕ, 0 < n → n ≤ 3 → borsukConjectureInDimension n

/-- Known counterexamples make the first failing dimension finite. This is an unproved claim.
Source: Optimization Problems, constant 28a, Description of constant. -/
private theorem_wanted knownFailureDimensionFinite : firstBorsukFailureDimension < ⊤

/-- Pikhurko's counterexample in dimension 321. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Pik2002-ub-321-322]. -/
private theorem_wanted pikhurkoDimension321Failure : 322 < dimensionBorsukNumber 321

/-- Pikhurko's counterexample in dimension 322. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Pik2002-ub-321-322]. -/
private theorem_wanted pikhurkoDimension322Failure : 323 < dimensionBorsukNumber 322

/-- Kahn and Kalai's failure in every dimension above 2014. This is an unproved claim.
Source: Optimization Problems, constant 28a, [KK1993-ub-1325]. -/
private theorem_wanted kahnKalaiFailureAbove2014 :
  ∀ n : ℕ, 2014 < n → (n + 1 : ℕ∞) < dimensionBorsukNumber n

/-- Hinrichs and Richter's failure in every dimension at least 298. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-298]. -/
private theorem_wanted hinrichsRichterFailureFrom298 :
  ∀ n : ℕ, 298 ≤ n → (n + 1 : ℕ∞) < dimensionBorsukNumber n

/-- Borsuk's conjecture eventually fails in every dimension. This is an unproved claim.
Source: Optimization Problems, constant 28a, [KK1993-asymptotic]. -/
private theorem_wanted eventualBorsukFailure :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n + 1 : ℕ∞) < dimensionBorsukNumber n

end WantedExt.Geometry.BorsukCatalogueBoundsWanted

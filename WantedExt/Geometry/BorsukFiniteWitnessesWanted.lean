/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite Borsuk counterexample statements
-/
module

public import Batteries.Util.ProofWanted

public import MathlibExt.Geometry.Euclidean.BorsukNumber

@[expose] public section

namespace WantedExt.Geometry.BorsukFiniteWitnessesWanted

open Metric

/-- Bondarenko's 416-point unit-sphere witness. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-65]. -/
private theorem_wanted bondarenkoUnitSphereCounterexample :
  ∃ s : Set (EuclideanSpace ℝ (Fin 65)),
    s.Finite ∧ s.ncard = 416 ∧ (∀ x ∈ s, ‖x‖ = 1) ∧
      IsTwoDistanceSet s ∧ ¬HasBorsukCover 83 s

/-- Jenrich and Brouwer's 352-point two-distance witness. This is an unproved claim.
Source: Optimization Problems, constant 28a, [JB2014-ub-64]. -/
private theorem_wanted jenrichBrouwerCounterexample :
  ∃ s : Set (EuclideanSpace ℝ (Fin 64)),
    s.Finite ∧ s.ncard = 352 ∧ IsTwoDistanceSet s ∧ ¬HasBorsukCover 70 s

/-- The 321-point witness and all smaller-diameter obstructions. This is an unproved claim.
Source: Grinsztajn (2026), Theorem 1 and Lemma 6. -/
private theorem_wanted grinsztajnCounterexample :
  ∃ s : Set (EuclideanSpace ℝ (Fin 63)),
    s.Finite ∧ s.ncard = 321 ∧
      (∀ t ⊆ s, ediam t < ediam s → t.ncard ≤ 5) ∧
      ¬HasBorsukCover 64 s ∧ (65 : ℕ∞) ≤ setBorsukNumber s

/-- The quoted two-distance Borsuk-number lower bound. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-65]. -/
private theorem_wanted bondarenkoTwoDistanceLowerBound : 84 ≤ twoDistanceBorsukNumber 65

/-- Bondarenko's dimensional lower bound. This is an unproved claim.
Source: Optimization Problems, constant 28a, [Bon2014-ub-65]. -/
private theorem_wanted bondarenkoDimensionalLowerBound : 84 ≤ dimensionBorsukNumber 65

/-- Jenrich and Brouwer's dimensional lower bound. This is an unproved claim.
Source: Optimization Problems, constant 28a, [JB2014-ub-64]. -/
private theorem_wanted jenrichBrouwerDimensionalLowerBound : 71 ≤ dimensionBorsukNumber 64

/-- Grinsztajn's dimensional lower bound. This is an unproved claim.
Source: Grinsztajn (2026), Theorem 1 and Lemma 6. -/
private theorem_wanted grinsztajnDimensionalLowerBound : 65 ≤ dimensionBorsukNumber 63

end WantedExt.Geometry.BorsukFiniteWitnessesWanted

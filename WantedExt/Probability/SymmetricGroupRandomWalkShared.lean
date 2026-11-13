/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Random walks on finite groups (AIM Markov chain mixing times, Problems 5.1 and 5.3)

Shared definitions for the card-shuffling problems of the AimPL list "Markov chain mixing times":
the transition matrix of the random walk on a finite group driven by a step law, the total
variation distance to the uniform distribution after `t` steps from the identity, and the step law
on permutations of `Fin n` given by a uniform pair of positions. Conjecture 5.1 (random-to-random
cutoff) and Problem 5.3 (random transposition cutoff profile) use them.
-/

module

public import MathlibExt.Probability.MarkovMixing
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MathlibExt.Probability.SymmetricGroupRandomWalkShared

open MathlibExt.Probability.MarkovMixing

/-- The transition matrix `P(x, y) = μ(x⁻¹ y)` of the random walk on the group `G` that multiplies
the current state on the right by an independent step of law `μ`. -/
def walkMatrix {G : Type*} [Group G] (μ : G → ℝ) : Matrix G G ℝ :=
  fun x y => μ (x⁻¹ * y)

/-- The total variation distance `‖P^t(1, ·) - U‖_TV` between the law of the walk with step law
`μ` after `t` steps from the identity and the uniform distribution on the finite group `G`. -/
noncomputable def walkDistToUniform {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (μ : G → ℝ) (t : ℕ) : ℝ :=
  tvDist (fun y => (walkMatrix μ ^ t) 1 y) (fun _ => 1 / (Fintype.card G : ℝ))

/-- The law on permutations of `Fin n` of `f (i, j)` for a uniform pair `(i, j) ∈ Fin n × Fin n`:
`σ ↦ #{(i, j) | f (i, j) = σ} / n²`. -/
noncomputable def pairStepLaw {n : ℕ} (f : Fin n × Fin n → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ((Finset.univ.filter fun ij => f ij = σ).card : ℝ) / (n : ℝ) ^ 2

end MathlibExt.Probability.SymmetricGroupRandomWalkShared

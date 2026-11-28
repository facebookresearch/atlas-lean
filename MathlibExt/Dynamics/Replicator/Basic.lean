/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Replicator dynamics and matrix games: basic definitions

A population plays strategies `i : ι` (a finite type) with frequencies `x i`. The fitness of
strategy `i` in state `x` is `f x i`, and the mean fitness is `f̄(x) = ∑ i, x i * f x i`. The
replicator equation (Taylor and Jonker 1978) is `x_i' = x_i (f_i(x) - f̄(x))`. For a symmetric
matrix game with payoff matrix `A` the fitness is `x ↦ A x`, and `meanFitness (fun z => A *ᵥ z) x`
is definitionally `x · A x`.

This file holds only the definitions, so that every library may state results about them:

* `meanFitness`, `IsSolution`, `IsRestPoint`: the replicator equation and its rest points;
* `IsNash`, `IsESS`: symmetric Nash equilibria and evolutionarily stable states of a matrix game.

The theory (simplex invariance, rest points as equalizers, stability of interior ESS) is in
`Domains.Biology.Dynamics.Replicator` and `Domains.Biology.Dynamics.ReplicatorStability`.

## References

* P. D. Taylor and L. B. Jonker, *Evolutionarily stable strategies and game dynamics*,
  Math. Biosci. 40 (1978) 145–156.
* J. Maynard Smith and G. R. Price, *The logic of animal conflict*, Nature 246 (1973) 15–18.
* J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge
  University Press (1998), §6.1 and §7.1–7.2.
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.Replicator

variable {ι : Type*} [Fintype ι]

/-- The mean fitness `f̄(x) = ∑ i, x i * f x i` of the population state `x` for the fitness
function `f`. -/
def meanFitness (f : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * f x i

/-- `x` solves the replicator equation `x_i' = x_i (f_i(x) - f̄(x))` for all times `t ≥ 0`. -/
structure IsSolution (f : (ι → ℝ) → ι → ℝ) (x : ℝ → ι → ℝ) : Prop where
  /-- Each frequency grows at the rate of its excess fitness. -/
  hasDerivAt : ∀ i t, 0 ≤ t →
    HasDerivAt (fun s => x s i) (x t i * (f (x t) i - meanFitness f (x t))) t

/-- `x` is a rest point of the replicator equation: `x_i (f_i(x) - f̄(x)) = 0` for all `i`. -/
def IsRestPoint (f : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : Prop :=
  ∀ i, x i * (f x i - meanFitness f x) = 0

open Matrix in
/-- `p` is a **symmetric Nash equilibrium** of the matrix game `A`: `p` is a mixed strategy and
no mixed strategy `q` earns more against `p` than `p` itself, `q · A p ≤ p · A p`. -/
def IsNash (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧
    ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 → q ⬝ᵥ A *ᵥ p ≤ p ⬝ᵥ A *ᵥ p

open Matrix in
/-- `p` is an **evolutionarily stable state** of the matrix game `A` (Maynard Smith and Price
1973; Hofbauer–Sigmund 1998, (6.3)–(6.4)): `p` is a mixed strategy and for every mixed strategy
`q ≠ p`, either `q · A p < p · A p`, or `q · A p = p · A p` and `q · A q < p · A q`. -/
def IsESS (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  ((∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) ∧ ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 → q ≠ p →
    q ⬝ᵥ A *ᵥ p < p ⬝ᵥ A *ᵥ p ∨ (q ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p ∧ q ⬝ᵥ A *ᵥ q < p ⬝ᵥ A *ᵥ q)

end MathlibExt.Biology.Dynamics.Replicator

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maxwell's bound on equilibrium points of point charges (Eremenko, Question 2)

A. Eremenko, Equilibrium points of Newtonian potentials (My favorite unsolved problems): for the
potential `u(x) = ∑_{k=1}^{n} a_k / ‖x - x_k‖`, `a_k > 0`, of finitely many positive charges in
3-space, an equilibrium point is a point with `grad u(x) = 0`. Question 2: if the set of equilibrium
points is finite, how many points can it contain? Maxwell stated without proof that the number of
equilibrium points is at most `(n - 1)²`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Analysis.MaxwellEquilibriumBoundAMR36Problem0036Wanted

/-!
Source: A. Eremenko, My favorite unsolved problems: Equilibrium points of Newtonian potentials
(Maxwell), Question 2, https://www.math.purdue.edu/~eremenko/dvi/equil2.pdf. UnsolvedMath record
UM-03700036 (`AMR-036-0036`), dataset ulamai/UnsolvedMath v1.8.0.

The equilibrium set (`equilibriumSet`) is the set of points off the charges where the derivative of
`u` vanishes (`u` is smooth there). Charges sit at distinct points. The target is Maxwell's bound
`(n - 1)²` for finite equilibrium sets; the open-ended 'how many points can it contain' is not
formalized. `OpenConjectures/Analysis/NewtonianEquilibriumFiniteness` (Eremenko's Question 1)
encodes the same equilibrium set through the explicit field `∑ a_k (y - x_k)/‖y - x_k‖³`; that entry
is not importable from WantedExt, so the set is defined here through the derivative of `u`.
-/

/-- The Newtonian potential `u(y) = ∑_k a_k / |y - x_k|` of charges `a_k` at points `x_k` of
`ℝ³`. -/
noncomputable def potential {n : ℕ} (a : Fin n → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin 3))
    (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ k, a k / ‖y - x k‖

/-- The equilibrium set of `u`: the points off the charges where the derivative of `u` vanishes
(Eremenko's equilibrium points, `grad u = 0`). -/
def equilibriumSet {n : ℕ} (a : Fin n → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | (∀ k, y ≠ x k) ∧ fderiv ℝ (potential a x) y = 0}

/-- Maxwell's bound (Eremenko, Question 2 on equilibrium points of Newtonian potentials): for `n`
positive charges at distinct points of `ℝ³`, a finite equilibrium set of `u` has at most `(n - 1)²`
points. -/
def maxwellBound : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin 3)), (∀ k, 0 < a k) →
    Function.Injective x → (equilibriumSet a x).Finite → (equilibriumSet a x).ncard ≤ (n - 1) ^ 2

/--
Resolved false (unrefereed, AI-assisted; recorded by the problem list): Arathoon, Ball and Kvalheim
exhibit five positive point charges whose potential has a finite equilibrium set with at least 24
points, while Maxwell's bound allows `(5 - 1)² = 16`. Source: A. Eremenko, My favorite unsolved
problems: Equilibrium points of Newtonian potentials (Maxwell), Question 2,
https://www.math.purdue.edu/~eremenko/dvi/equil2.pdf; resolution: P. Arathoon, G. Ball and M. D.
Kvalheim, The Maxwell Conjecture is False, arXiv:2607.27197 (2026), unrefereed preprint whose
construction was suggested by an LLM; Eremenko's unsolved-problems page records it: 'A
counterexample to Maxwell's conjecture is found, though it holds for 3 points. All AI assisted.',
Theorem 1: for charges 1, 1, 1 at the vertices of an equilateral triangle and q_ε, q_ε at (0, 0, ±ε)
the potential has at least 24 non-degenerate critical points for small ε > 0, and 'a small
perturbation to the charge strengths gives a potential with a finite number k ≥ 24 of critical
points all of which are non-degenerate' (§2: all charges stay positive, so the critical points lie
in the convex hull of the charges); 24 > (5 - 1)² = 16, https://arxiv.org/abs/2607.27197.
-/
public theorem_wanted maxwellBound_refuted : ¬ maxwellBound

end MathlibExt.Analysis.MaxwellEquilibriumBoundAMR36Problem0036Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace MathlibExt.Algebra.Polynomial.ScottishBook79Wanted

/-- Mazur and Orlicz's Problem 79 from the Scottish Book, for the
Euclidean plane: if a polynomial map of the plane to itself is
bijective with polynomial inverse (the two coordinate polynomials
`P` and the coordinate polynomials `Q` of the inverse), must the map
be affine, with nonzero determinant? -/
def ScottishBookProblem79Claim : Prop :=
  ∀ (P Q : Fin 2 → MvPolynomial (Fin 2) ℝ),
    (∀ x : Fin 2 → ℝ,
      (fun i => MvPolynomial.eval
        (fun j => MvPolynomial.eval x (P j)) (Q i)) = x) →
    (∀ y : Fin 2 → ℝ,
      (fun i => MvPolynomial.eval
        (fun j => MvPolynomial.eval y (Q j)) (P i)) = y) →
    ∃ (a : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ),
      Matrix.det a ≠ 0 ∧
      ∀ (x : Fin 2 → ℝ) (i : Fin 2),
        MvPolynomial.eval x (P i) = ∑ j, a i j * x j + c i

/--
Mazur–Orlicz Problem 79 is false: a bijective polynomial map of the
plane with polynomial inverse need not be affine. Source: S. Mazur and
W. Orlicz, Problem 79 of the Scottish Book; typescript Ad 79 records
the negative answer, via triangular polynomial automorphisms: maps
`y₁ = x₁ + k`, `y₂ = x₂ + φ₂(x₁)`, …, `yₙ = xₙ + φₙ(x₁, …, xₙ₋₁)`
with arbitrary polynomials `φ` are polynomial automorphisms with
obvious polynomial inverses, but are not affine when some `φ` is
nonlinear. For the plane, `y₁ = x₁`, `y₂ = x₂ + x₁²` already refutes
affineness.
-/
theorem_wanted mazurOrlicz79_refuted : ¬ ScottishBookProblem79Claim

end MathlibExt.Algebra.Polynomial.ScottishBook79Wanted

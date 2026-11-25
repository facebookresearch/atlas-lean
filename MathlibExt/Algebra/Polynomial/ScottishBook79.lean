/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# A nonlinear polynomial automorphism of the real plane

The quadratic shear fixes the first coordinate, so subtracting its square from the second
coordinate inverts the map. Its restriction to the horizontal axis is a parabola.
-/

@[expose] public section

namespace MathlibExt.Algebra.Polynomial.ScottishBook79Wanted

/-- **Mazur–Orlicz claim on polynomial automorphisms of the plane.** The statement that every
polynomial map of the plane with a polynomial inverse is affine: for all pairs
$P = (P_1, P_2)$ and $Q = (Q_1, Q_2)$ of real polynomials in two variables such that
$Q(P(x)) = x$ for every $x \in \mathbb{R}^2$ and $P(Q(y)) = y$ for every $y \in \mathbb{R}^2$,
there are a real $2 \times 2$ matrix $A$ with $\det A \neq 0$ and a vector $c \in \mathbb{R}^2$
such that $P(x) = Ax + c$ for every $x \in \mathbb{R}^2$.

This is the affirmative answer to Mazur and Orlicz's Problem 79 of the Scottish Book,
restricted to the Euclidean plane. -/
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

open MvPolynomial in
/--
**Mazur–Orlicz Problem 79 has a negative answer.** The claim of Problem 79 of the Scottish Book
for the plane is false: there is a polynomial map $P$ of $\mathbb{R}^2$ to itself with a
polynomial two-sided inverse that is not of the form $x \mapsto Ax + c$ with $A$ an invertible
real $2 \times 2$ matrix and $c \in \mathbb{R}^2$. For example, the map
$(x_1, x_2) \mapsto (x_1, x_2 + x_1^2)$ has the inverse $(y_1, y_2) \mapsto (y_1, y_2 - y_1^2)$.

Source: S. Mazur and
W. Orlicz, Problem 79 of the Scottish Book; typescript Ad 79 records
the negative answer, via triangular polynomial automorphisms: maps
`y₁ = x₁ + k`, `y₂ = x₂ + φ₂(x₁)`, …, `yₙ = xₙ + φₙ(x₁, …, xₙ₋₁)`
with arbitrary polynomials `φ` are polynomial automorphisms with
obvious polynomial inverses, but are not affine when some `φ` is
nonlinear. For the plane, `y₁ = x₁`, `y₂ = x₂ + x₁²` already refutes
affineness.
-/
theorem mazurOrlicz79_refuted : ¬ ScottishBookProblem79Claim := by
  intro claim
  let P : Fin 2 → MvPolynomial (Fin 2) ℝ := ![X 0, X 1 + X 0 ^ 2]
  let Q : Fin 2 → MvPolynomial (Fin 2) ℝ := ![X 0, X 1 - X 0 ^ 2]
  obtain ⟨a, c, _, ha⟩ := claim P Q (by
    intro x
    funext i
    fin_cases i <;> simp [P, Q]) (by
    intro y
    funext i
    fin_cases i <;> simp [P, Q])
  have axis (t : ℝ) : t ^ 2 = a 1 0 * t + c 1 := by
    simpa [P, Fin.sum_univ_two] using ha ![t, 0] 1
  linarith [axis (-1), axis 0, axis 1]

end MathlibExt.Algebra.Polynomial.ScottishBook79Wanted

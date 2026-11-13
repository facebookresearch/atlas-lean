/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Laplacian algebras of polynomials are maximal (Radeschi's question)

F. Morgan and P. Pansu, A List of Open Problems in Differential Geometry (2018), Question 23 (M.
Radeschi, Spherical submetries): is every Laplacian algebra of polynomials maximal?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Algebra.LaplacianAlgebraMaximalAMR67Problem0023Wanted

/-!
Source: F. Morgan and P. Pansu, A List of Open Problems in Differential Geometry (2018), Question 23
(M. Radeschi, Spherical submetries). UnsolvedMath record UM-06800023 (`AMR-067-0023`), dataset
ulamai/UnsolvedMath v1.8.0.

Definitions from Mendes–Radeschi (GAFA 2020; restated in the resolving paper, §1): a Laplacian
algebra is a subalgebra `A ⊆ ℝ[V]` (unital, Mathlib `Subalgebra`) containing `r² = ∑ xᵢ²` and
preserved by the Laplacian `Δ = ∑ ∂²/∂xᵢ²`; `A` is maximal when `A = B(L(A))`, i.e. every polynomial
constant on the common level sets of `A` (`x ∼ y` iff `g x = g y` for all `g ∈ A`) lies in `A`. `V =
ℝⁿ` with coordinates `x₁, …, xₙ` (any Euclidean space after an orthonormal basis).
-/

/-- The distance-squared polynomial `r² = x₁² + ⋯ + xₙ²` on `ℝⁿ`. -/
noncomputable def radiusSq (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.X i ^ 2

/-- The Laplacian `Δ = ∑ ∂²/∂xᵢ²` on `ℝ[x₁, …, xₙ]`. -/
noncomputable def laplacian {n : ℕ} (f : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i f)

/-- A Laplacian algebra: a subalgebra of `ℝ[V]` containing `r²` and preserved by `Δ`. -/
def IsLaplacianAlgebra {n : ℕ} (A : Subalgebra ℝ (MvPolynomial (Fin n) ℝ)) : Prop :=
  radiusSq n ∈ A ∧ ∀ f ∈ A, laplacian f ∈ A

/-- A maximal algebra: every polynomial constant on the common level sets of `A` (the classes of
`x ∼ y ⟺ g x = g y` for all `g ∈ A`) lies in `A`. -/
def IsMaximalAlgebra {n : ℕ} (A : Subalgebra ℝ (MvPolynomial (Fin n) ℝ)) : Prop :=
  ∀ f : MvPolynomial (Fin n) ℝ,
    (∀ x y : Fin n → ℝ, (∀ g ∈ A, MvPolynomial.eval x g = MvPolynomial.eval y g) →
      MvPolynomial.eval x f = MvPolynomial.eval y f) → f ∈ A

/-- Radeschi's question (Morgan–Pansu, Open Problems in Differential Geometry, Question 23),
answered: every Laplacian algebra of real polynomials is maximal. -/
def laplacianAlgebrasMaximal : Prop :=
  ∀ (n : ℕ) (A : Subalgebra ℝ (MvPolynomial (Fin n) ℝ)), IsLaplacianAlgebra A → IsMaximalAlgebra A

/--
Resolved true: Mendes and Radeschi proved that every Laplacian algebra `A ⊆ ℝ[V]` (containing `r²`
and preserved by `Δ`) is maximal, i.e. contains every polynomial constant on its common level sets
(Theorem A), as conjectured in their GAFA paper. Source: F. Morgan and P. Pansu, A List of Open
Problems in Differential Geometry (2018), Question 23 (M. Radeschi, Spherical submetries);
resolution: R. A. E. Mendes and M. Radeschi, Maximality of Laplacian algebras, with applications to
Invariant Theory, Ann. Mat. Pura Appl. (4) 202 (2023), 1011-1031, arXiv:2012.07914, Theorem A: let A
⊆ ℝ[V] be a Laplacian algebra; then A is maximal (Laplacian: contains r² and is preserved by Δ;
maximal: A = B(L(A)), §2 definitions), https://arxiv.org/abs/2012.07914.
-/
public theorem_wanted laplacianAlgebrasMaximal_holds : laplacianAlgebrasMaximal

end MathlibExt.Algebra.LaplacianAlgebraMaximalAMR67Problem0023Wanted

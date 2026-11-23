/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

open scoped BigOperators Topology

namespace MathlibExt.LinearAlgebra.Matrix.JacobiIterationWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
**Convergence of the Jacobi method for strictly diagonally dominant matrices.** Let $A$ be a
real square matrix with rows and columns indexed by a finite type, and let $b$ be a real vector.
Suppose $A$ is strictly diagonally dominant: $\sum_{j \ne i} |A_{ij}| < |A_{ii}|$ for every $i$.
Define the Jacobi sweep $J$ by $J(x)_i = \bigl(b_i - \sum_{j \ne i} A_{ij} x_j\bigr) / A_{ii}$.
Then there is a vector $x^*$ with $A x^* = b$ such that, for every starting vector $x_0$, the
iterates $J^k(x_0)$ converge to $x^*$ as $k \to \infty$.

Sources: Mathlib repository, `docs/undergrad.yaml` (the undergraduate curriculum list),
section "Numerical Analysis" / "Iterative methods" / "Jacobian";
G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins Univ. Press,
2013, §11.2; https://en.wikipedia.org/wiki/Jacobi_method
-/
public theorem_wanted jacobi_iteration_converges
    (A : Matrix n n ℝ) (b : n → ℝ)
    (hA : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) :
    ∃ xStar : n → ℝ, A.mulVec xStar = b ∧ ∀ x₀ : n → ℝ,
      Filter.Tendsto
        (fun k =>
          (fun x : n → ℝ => fun i => (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i)^[k]
            x₀)
        Filter.atTop (𝓝 xStar)

end MathlibExt.LinearAlgebra.Matrix.JacobiIterationWanted

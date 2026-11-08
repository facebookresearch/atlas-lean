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
The Jacobi iteration converges for strictly diagonally dominant systems: if
`∑_{j ≠ i} |A i j| < |A i i|` for every `i`, then `A x = b` has a solution `xStar` and
the Jacobi iterates converge to `xStar` from any starting point. One Jacobi sweep maps `x`
to the vector whose `i`-th entry is `(b i - ∑_{j ≠ i} A i j * x j) / A i i`.

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

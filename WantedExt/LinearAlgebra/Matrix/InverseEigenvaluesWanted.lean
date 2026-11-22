/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- **Eigenvalues of the inverse matrix.** Let $M$ be a square matrix over a field $K$, with rows
and columns indexed by a finite type, whose determinant is a unit of $K$ (so $M$ is invertible),
and let $\mu \in K$ be nonzero. Then a vector $x$ is an eigenvector of $M$ with eigenvalue $\mu$
(that is, $x \ne 0$ and $Mx = \mu x$) if and only if $x$ is an eigenvector of $M^{-1}$ with
eigenvalue $\mu^{-1}$.

Source: https://en.wikipedia.org/wiki/Eigendecomposition_of_a_matrix, statement `inveig-s1`. -/
theorem_wanted inverse_eigenvalues {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (M : Matrix n n K) (hM : IsUnit M.det) {μ : K}
    (hμ : μ ≠ 0) (x : n → K) : Module.End.HasEigenvector (Matrix.toLin' M) μ x ↔
      Module.End.HasEigenvector (Matrix.toLin' M⁻¹) μ⁻¹ x

end

end MetaMathlibExt

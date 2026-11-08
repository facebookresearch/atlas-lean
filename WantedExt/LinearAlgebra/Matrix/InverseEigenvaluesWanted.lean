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

/-- Inverse eigenvalues theorem (stable source:
https://en.wikipedia.org/wiki/Eigendecomposition_of_a_matrix, statement `inveig-s1`):
for an invertible square matrix `M` over a field, a nonzero scalar `μ` has eigenvector
`x` for `M` if and only if `μ⁻¹` has the same eigenvector `x` for `M⁻¹`. -/
theorem_wanted inverse_eigenvalues {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (M : Matrix n n K) (hM : IsUnit M.det) {μ : K}
    (hμ : μ ≠ 0) (x : n → K) : Module.End.HasEigenvector (Matrix.toLin' M) μ x ↔
      Module.End.HasEigenvector (Matrix.toLin' M⁻¹) μ⁻¹ x

end

end MetaMathlibExt

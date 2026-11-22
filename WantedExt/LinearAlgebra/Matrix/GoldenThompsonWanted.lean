/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Golden–Thompson inequality (wanted)

For Hermitian matrices `A` and `B`, `tr e^{A + B} ≤ tr (e^A e^B)` (S. Golden, Phys. Rev. 137
(1965) B1127, for nonnegative definite `A`, `B`; C. J. Thompson, J. Math. Phys. 6 (1965) 1812, for
all Hermitian `A`, `B`; as stated in P. J. Forrester and C. J. Thompson, *The Golden–Thompson
inequality — historical aspects and random matrix applications*, arXiv:1408.2008v1, equation
(1.1)). The commuting case, where equality holds, and the fact that the right side is a
nonnegative real are proved in `MathlibExt.LinearAlgebra.Matrix.GoldenThompson`. The general
proof is deferred.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.GoldenThompsonWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Golden–Thompson inequality.** For Hermitian complex matrices `A` and `B`,
`tr e^{A + B} ≤ tr (e^A e^B)` (P. J. Forrester and C. J. Thompson, *The Golden–Thompson
inequality — historical aspects and random matrix applications*, arXiv:1408.2008v1, equation
(1.1); S. Golden, Phys. Rev. 137 (1965) B1127; C. J. Thompson, J. Math. Phys. 6 (1965) 1812).
The inequality is taken in the partial order of `ℂ`, so it also asserts that the right side is
real, as it is. -/
theorem_wanted golden_thompson {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace

end MathlibExt.LinearAlgebra.Matrix.GoldenThompsonWanted

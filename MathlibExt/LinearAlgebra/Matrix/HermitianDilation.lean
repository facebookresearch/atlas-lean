/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Matrix.Block

/-!
# The Hermitian dilation of a rectangular matrix

For a rectangular matrix `B` of size `d₁ × d₂`, the Hermitian dilation is the
`(d₁ + d₂) × (d₁ + d₂)` block matrix `H(B) = [[0, B], [B*, 0]]`
(J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, Found. Trends Mach. Learn.
8 (2015), arXiv:1501.01571, Definition 2.1.5). It is Hermitian, real-linear in `B`, and its square
is block diagonal, `H(B)² = [[B B*, 0], [0, B* B]]` (display (2.1.27)), so the squared eigenvalues
of `H(B)` are the squared singular values of `B` together with zeros. Conjugating by
`J = [[I, 0], [0, -I]]` sends `H(B)` to `-H(B)`, so the spectrum of `H(B)` is symmetric about `0`.
Through the dilation, concentration inequalities for Hermitian matrices extend to rectangular
ones, for instance the rectangular matrix Bernstein inequality (Tropp, Theorem 6.1.1).

The identity `λmax(H(B)) = ‖B‖` of display (2.1.28) is not formalized here.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.HermitianDilation

variable {m n α : Type*}

/-- **Hermitian dilation.** For `B : Matrix m n α`, the block matrix
`H(B) = [[0, B], [Bᴴ, 0]]` indexed by `m ⊕ n` (Tropp, *An Introduction to Matrix Concentration
Inequalities*, arXiv:1501.01571, Definition 2.1.5, display (2.1.26)). -/
def dilation [Zero α] [Star α] (B : Matrix m n α) : Matrix (m ⊕ n) (m ⊕ n) α :=
  fromBlocks 0 B Bᴴ 0

/-- **The Hermitian dilation is Hermitian** (Tropp, arXiv:1501.01571, Definition 2.1.5). -/
theorem isHermitian_dilation [AddMonoid α] [StarAddMonoid α] (B : Matrix m n α) :
    (dilation B).IsHermitian := by
  simp [dilation, IsHermitian, fromBlocks_conjTranspose]

/-- **The Hermitian dilation is additive** (Tropp, arXiv:1501.01571, §2.1.16:
the dilation is real-linear). -/
theorem dilation_add [AddMonoid α] [StarAddMonoid α] (B C : Matrix m n α) :
    dilation (B + C) = dilation B + dilation C := by
  simp [dilation, fromBlocks_add, conjTranspose_add]

/-- **The Hermitian dilation commutes with real scalars** (Tropp, arXiv:1501.01571, §2.1.16:
the dilation is real-linear). -/
theorem dilation_smul {R : Type*} [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    [Star R] [TrivialStar R] [StarModule R α] (r : R) (B : Matrix m n α) :
    dilation (r • B) = r • dilation B := by
  simp [dilation, fromBlocks_smul, conjTranspose_smul]

/-- **Square of the Hermitian dilation** (Tropp, arXiv:1501.01571, display (2.1.27)):
`H(B)² = [[B Bᴴ, 0], [0, Bᴴ B]]`. -/
theorem dilation_mul_self [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α]
    (B : Matrix m n α) :
    dilation B * dilation B = fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B) := by
  simp [dilation, fromBlocks_multiply]

/-- **The spectrum of the Hermitian dilation is symmetric** (Tropp, arXiv:1501.01571, §2.1.16):
conjugating by the signature matrix `J = [[I, 0], [0, -I]]`, an involution, sends `H(B)` to
`-H(B)`, so `H(B)` and `-H(B)` are similar. -/
theorem signature_mul_dilation_mul_signature [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [Ring α] [StarRing α] (B : Matrix m n α) :
    fromBlocks (1 : Matrix m m α) 0 0 (-1) * dilation B * fromBlocks (1 : Matrix m m α) 0 0 (-1) =
      -dilation B := by
  simp [dilation, fromBlocks_multiply, fromBlocks_neg]

end MathlibExt.LinearAlgebra.Matrix.HermitianDilation

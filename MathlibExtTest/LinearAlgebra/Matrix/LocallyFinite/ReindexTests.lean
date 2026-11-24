/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.Reindex
public import Mathlib.Data.Int.Basic

/-!
# Actual corner image, zero and return clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe um un um' un' uR

namespace Matrix.LocallyFinite.SourceClients.Reindex

/-- The literal even-coordinate injection used by the concrete corner clients. -/
def evenEmbedding : ℕ ↪ ℕ where
  toFun n := 2 * n
  inj' a b h := by
    change 2 * a = 2 * b at h
    omega

/-- The concrete corner injection reads its original doubled coordinate. -/
@[simp]
theorem evenEmbedding_apply (i : ℕ) : evenEmbedding i = 2 * i := rfl

/-- An original image coefficient survives the actual even corner extension. -/
theorem even_corner_diagonal (r : ℤ) (i : ℕ) :
    extend evenEmbedding evenEmbedding (diagonal (fun _ : ℕ => r)) (2 * i) (2 * i) = r := by
  have h := extend_apply_image evenEmbedding evenEmbedding (diagonal (fun _ : ℕ => r)) i i
  simpa [diagonal_apply] using h

/-- An actual odd coordinate outside the image reads zero in the same original corner. -/
theorem odd_corner_zero (A : Matrix.LocallyFinite ℕ ℕ ℤ) :
    extend evenEmbedding evenEmbedding A 1 1 = 0 := by
  apply extend_apply_of_notMem_row_range
  rintro ⟨i, hi⟩
  change 2 * i = 1 at hi
  omega

/-- Independent row and column worlds return the same actual original corner matrix. -/
theorem independent_corner_return {m : Type um} {n : Type un}
    {m' : Type um'} {n' : Type un'} {R : Type uR} [Zero R]
    (e : m ↪ m') (f : n ↪ n') (A : Matrix.LocallyFinite m n R) :
    submatrix e f (extend e f A) = A := submatrix_extend e f A

/-- Both original index inverse maps are retained by the square ring equivalence. -/
theorem original_reindex_return {m : Type um} {n : Type un} {R : Type uR} [Semiring R]
    (e : m ≃ n) (A : Matrix.LocallyFinite m m R) :
    (reindexRingEquiv e).symm (reindexRingEquiv e A) = A :=
  (reindexRingEquiv e).symm_apply_apply A

end Matrix.LocallyFinite.SourceClients.Reindex

end

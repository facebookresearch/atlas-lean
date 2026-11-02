/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank of a bilinear form

This file proves that the rank of the matrix of a bilinear form is independent of the chosen
basis.
-/

@[expose] public section

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem bilinRank_toMatrix_le {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V)
    (B : LinearMap.BilinForm K V) : (toMatrix b₂ B).rank ≤ (toMatrix b₁ B).rank := by
  rw [← toMatrix_mul_basis_toMatrix b₁ b₂ B]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- **The Gram matrices of a bilinear form in two bases have the same rank.** Let $V$ be a vector
space over a field $K$, let $B$ be a bilinear form on $V$, and let $b = (b_i)_{i \in n_1}$ and
$c = (c_j)_{j \in n_2}$ be bases of $V$ indexed by finite types $n_1$ and $n_2$. Then the Gram
matrices $(B(b_i, b_j))_{i, j \in n_1}$ and $(B(c_i, c_j))_{i, j \in n_2}$ have the same rank. -/
theorem rank_toMatrix_eq_rank_toMatrix {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V)
    (B : LinearMap.BilinForm K V) : (toMatrix b₁ B).rank = (toMatrix b₂ B).rank := by
  apply le_antisymm
  · exact bilinRank_toMatrix_le b₂ b₁ B
  · exact bilinRank_toMatrix_le b₁ b₂ B

end LinearMap.BilinForm

namespace MathlibExt.LinearAlgebra.BilinearFormRankWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/--
**Rank of a bilinear form.** Let $V$ be a vector space over a field $K$, let $B$ be a bilinear
form on $V$, and let $b = (b_i)_{i \in n}$ be a basis of $V$ indexed by a finite type $n$. The
rank of $B$ with respect to $b$ is the rank of the Gram matrix $(B(b_i, b_j))_{i, j \in n}$ of $B$
in $b$.

By the basis independence theorem, this number does not depend on the choice of $b$.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.
-/
noncomputable def bilinFormRank {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K V) (B : LinearMap.BilinForm K V) : ℕ :=
  (LinearMap.BilinForm.toMatrix b B).rank

/--
**Rank of a bilinear form via its Gram matrix.** Let $V$ be a vector space over a field $K$, let
$B$ be a bilinear form on $V$, and let $b = (b_i)_{i \in n}$ be a basis of $V$ indexed by a finite
type $n$. Then the rank of $B$ with respect to $b$ equals the rank of the Gram matrix
$(B(b_i, b_j))_{i, j \in n}$. This holds by definition.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.
-/
theorem bilinFormRank_eq_matrix_rank {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K V) (B : LinearMap.BilinForm K V) :
    bilinFormRank b B = (LinearMap.BilinForm.toMatrix b B).rank := rfl

/--
**Basis independence of the rank of a bilinear form.** Let $V$ be a vector space over a field
$K$, let $B$ be a bilinear form on $V$, and let $b = (b_i)_{i \in n_1}$ and
$c = (c_j)_{j \in n_2}$ be bases of $V$ indexed by finite types $n_1$ and $n_2$. Then the rank of
$B$ with respect to $b$ equals the rank of the Gram matrix $(B(c_i, c_j))_{i, j \in n_2}$ of $B$
in $c$.

Proof: The Gram matrix in one basis is the Gram matrix in the other multiplied on both sides by
change-of-basis matrices. Since the rank of a product is at most the rank of each factor, each
rank is at most the other, hence they are equal.

Proves `Wanted` entry `bilinFormRank_basis_independent`.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.
-/
theorem bilinFormRank_basis_independent {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂]
    (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V) (B : LinearMap.BilinForm K V) :
    bilinFormRank b₁ B = (LinearMap.BilinForm.toMatrix b₂ B).rank := by
  rw [bilinFormRank_eq_matrix_rank]
  exact LinearMap.BilinForm.rank_toMatrix_eq_rank_toMatrix b₁ b₂ B

end MathlibExt.LinearAlgebra.BilinearFormRankWanted

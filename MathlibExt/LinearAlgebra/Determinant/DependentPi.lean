/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of dependent componentwise endomorphisms

Mathlib's `LinearMap.det_pi` computes the determinant of a componentwise
endomorphism of `ι → M`, where every component is the same finite free
module.  This file proves the dependent-family version: the modules `M i`
may have different ranks.

## Informal proof

Choose a finite basis `b i` of each component `M i`.  The dependent Pi basis
`Pi.basis b` is indexed by the sigma type of all component basis indices.
In that basis the componentwise endomorphism has matrix

```text
Matrix.blockDiagonal' (fun i => matrix (f i)).
```

Indeed, a basis vector supported in component `j` stays in component `j`, so
every off-diagonal block is zero, while the `j`-th diagonal block is exactly
the matrix of `f j`.

For completeness, the required determinant formula for unequal block sizes
is proved first.  Give the finite outer index an arbitrary linear order and
view `blockDiagonal'` as block triangular.  The block-triangular determinant
theorem expresses its determinant as the product of its square diagonal
blocks.  The fiber of `Sigma.fst` over `i` is canonically equivalent to the
index type of the `i`-th block, so determinant invariance under reindexing
identifies that square block with the original matrix.  Applying this matrix
formula to the dependent Pi basis gives the result.

## Reconstructing a block-diagonal endomorphism

For an arbitrary endomorphism `F` of a finite dependent product, its `(i,j)`
block is the composite

```text
M j --single j--> (∀ i, M i) --F--> (∀ i, M i) --proj i--> M i.
```

Suppose every block with `i ≠ j` is zero.  Decompose an arbitrary vector as
the finite sum `∑ j, Pi.single j (x j)` and apply linearity of `F`.  After
evaluating at coordinate `i`, all terms except `j = i` vanish by the block
hypothesis.  The surviving term is the diagonal block applied to `x i`.
Function and linear-map extensionality therefore identify `F` with the
componentwise endomorphism assembled from its diagonal blocks.  This argument
uses neither matrices nor finite-free hypotheses.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open scoped BigOperators

universe uR uI uM uK

namespace Matrix

variable {R : Type uR} [CommRing R]
variable {ι : Type uI} [Fintype ι]
variable {κ : ι → Type uK} [∀ i, Fintype (κ i)]

/-- The index type of one block is equivalent to the corresponding fiber of
the sigma-type block projection. -/
private noncomputable def sigmaBlockFiberEquiv (i : ι) :
    κ i ≃ {x : Sigma κ // x.1 = i} :=
  Equiv.ofBijective
    (fun j => ⟨⟨i, j⟩, rfl⟩)
    ⟨fun _ _ h => sigma_mk_injective (congrArg Subtype.val h), fun x => by
      rcases x with ⟨⟨j, x⟩, hj⟩
      change j = i at hj
      subst j
      exact ⟨x, rfl⟩⟩

omit [Fintype ι] [∀ i, Fintype (κ i)] in
private theorem toSquareBlock_blockDiagonal'_eq_reindex
    [DecidableEq ι]
    (A : ∀ i, Matrix (κ i) (κ i) R) (i : ι) :
    (Matrix.blockDiagonal' A).toSquareBlock Sigma.fst i =
      Matrix.reindex (sigmaBlockFiberEquiv (κ := κ) i)
        (sigmaBlockFiberEquiv (κ := κ) i) (A i) := by
  ext ⟨⟨j, x⟩, hj⟩ ⟨⟨k, y⟩, hk⟩
  change j = i at hj
  change k = i at hk
  subst j
  subst k
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_eq]
  let e := sigmaBlockFiberEquiv (κ := κ) i
  change A i x y =
    A i (e.symm ⟨⟨i, x⟩, rfl⟩) (e.symm ⟨⟨i, y⟩, rfl⟩)
  have hx : e.symm ⟨⟨i, x⟩, rfl⟩ = x := by
    apply e.symm_apply_eq.mpr
    apply Subtype.ext
    rfl
  have hy : e.symm ⟨⟨i, y⟩, rfl⟩ = y := by
    apply e.symm_apply_eq.mpr
    apply Subtype.ext
    rfl
  rw [hx, hy]

private theorem det_blockDiagonal'_of_linearOrder
    [DecidableEq ι] [∀ i, DecidableEq (κ i)] [LinearOrder ι]
    (A : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' A).det = ∏ i, (A i).det := by
  rw [(Matrix.blockTriangular_blockDiagonal' A).det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  rw [toSquareBlock_blockDiagonal'_eq_reindex,
    Matrix.det_reindex_self]

/-- The determinant of a finite dependent block-diagonal matrix is the
product of the determinants of its blocks. -/
theorem det_blockDiagonal' [DecidableEq ι] [∀ i, DecidableEq (κ i)]
    (A : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' A).det = ∏ i, (A i).det := by
  classical
  let horder : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  exact @det_blockDiagonal'_of_linearOrder R _ ι _ κ _ _ _ horder A

end Matrix

namespace LinearMap

variable {R : Type uR} [CommRing R]
variable {ι : Type uI}
variable {M : ι → Type uM}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The `(i,j)` block of an endomorphism of a dependent product: include the
`j`-th component, apply the endomorphism, then project to component `i`. -/
noncomputable def dependentPiBlock
    (F : (∀ i, M i) →ₗ[R] ∀ i, M i) (i j : ι) : M j →ₗ[R] M i := by
  classical
  exact (LinearMap.proj i).comp (F.comp (LinearMap.single R M j))

/-- A finite dependent-product endomorphism with zero off-diagonal blocks is
the componentwise endomorphism assembled from its diagonal blocks. -/
theorem eq_pi_diagonal_of_dependentPiBlock_eq_zero
    [Finite ι]
    (F : (∀ i, M i) →ₗ[R] ∀ i, M i)
    (hF : ∀ i j : ι, i ≠ j → dependentPiBlock F i j = 0) :
    F = LinearMap.pi fun i => (dependentPiBlock F i i).comp (LinearMap.proj i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  apply LinearMap.ext
  intro x
  funext i
  change F x i = dependentPiBlock F i i (x i)
  calc
    F x i = F (∑ j, Pi.single j (x j)) i := by
      rw [LinearMap.sum_single_apply]
    _ = ∑ j, F (Pi.single j (x j)) i := by
      rw [map_sum, Finset.sum_apply]
    _ = dependentPiBlock F i i (x i) := by
      change (∑ j, dependentPiBlock F i j (x j)) = dependentPiBlock F i i (x i)
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        rw [hF i j hji.symm, LinearMap.zero_apply]
      · simp

variable [Fintype ι]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- Determinant of a componentwise endomorphism of a finite dependent
product.  Unlike `LinearMap.det_pi`, the component modules may have unequal
ranks. -/
theorem det_pi_dependent (f : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).det =
      ∏ i, (f i).det := by
  classical
  let b := fun i => Module.Free.chooseBasis R (M i)
  let B := Pi.basis b
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix (b _)]
  have hmatrix :
      LinearMap.toMatrix B B
          (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        Matrix.blockDiagonal'
          (fun i => LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp only [LinearMap.toMatrix_apply', B, Pi.basis_apply, Pi.basis_repr,
      LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_proj, Function.eval,
      Matrix.blockDiagonal'_apply]
    split_ifs with h
    · subst j
      simp
    · simp [h]
  rw [hmatrix, Matrix.det_blockDiagonal']

end LinearMap

namespace LinearEquiv

variable {R : Type uR} [CommRing R]
variable {ι : Type uI} [Fintype ι]
variable {M : ι → Type uM}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- The determinant of a dependent product of linear equivalences is the
product of their determinants. -/
theorem det_piCongrRight (f : ∀ i, M i ≃ₗ[R] M i) :
    LinearEquiv.det (LinearEquiv.piCongrRight f) =
      ∏ i, LinearEquiv.det (f i) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.coe_prod]
  have hmap : (LinearEquiv.piCongrRight f).toLinearMap =
      LinearMap.pi (fun i => (f i).toLinearMap.comp
        (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro x
    funext i
    rfl
  rw [hmap, LinearMap.det_pi_dependent]
  simp only [LinearEquiv.coe_det]

end LinearEquiv

end

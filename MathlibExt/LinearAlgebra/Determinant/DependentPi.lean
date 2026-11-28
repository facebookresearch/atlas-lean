/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/LinearAlgebra/Determinant.lean` (Mathlib):
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinants of dependent product endomorphisms

Let R be a commutative ring, I finite and M_i finite free R-modules of possibly different
ranks. For componentwise f=(f_i) on ∏iM_i, det(f)=∏i det(f_i). A dependent block-diagonal
matrix likewise has determinant the product of its square block determinants. A finite product
endomorphism with zero off-diagonal blocks equals the componentwise map from its diagonal
blocks.
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

/-- **Index set of a dependent matrix block.**

For a family κ:I→Type and i∈I, sigmaBlockFiberEquiv i identifies κ_i with the fiber
{x∈Σjκ_j:x.1=i}, by a↦(i,a).
-/
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

/-- **Determinant of a dependent block-diagonal matrix.**

Let R be a commutative ring, I finite, all κ_i finite and A_i square matrices on κ_i. Then
det(blockDiagonal′(A_i))=∏i det(A_i), including empty blocks.
-/
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

/-- **Block of a dependent product endomorphism.**

Let R be a commutative ring and M_i R-modules. For F:∏iM_i→∏iM_i, dependentPiBlock F i j is
proj_i∘F∘single_j:M_j→M_i.
-/
noncomputable def dependentPiBlock
    (F : (∀ i, M i) →ₗ[R] ∀ i, M i) (i j : ι) : M j →ₗ[R] M i := by
  classical
  exact (LinearMap.proj i).comp (F.comp (LinearMap.single R M j))

/-- **Zero off-diagonal blocks characterize a componentwise map.**

Let I be finite and M_i R-modules over a commutative ring. If F_ij=proj_i F single_j is zero
for i≠j, then F(x)_i=F_ii(x_i), so F is the componentwise map from its diagonal blocks.
-/
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

/-- **Determinant of a finite dependent componentwise map.**

Let R be a commutative ring, I finite and M_i finite free R-modules of possibly different
ranks. For componentwise f=(f_i) on ∏iM_i, det(f)=∏i det(f_i). The identity is
det_pi_dependent for the linear map x↦(f_i(x_i))_i.

The dependent-family proof is adapted from Mathlib's `LinearMap.det_pi` in
`Mathlib/LinearAlgebra/Determinant.lean`.
-/
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

/-- **Determinant of a dependent product of equivalences.**

Let R be a commutative ring, I finite and M_i finite free R-modules of possibly different
ranks. For componentwise f=(f_i) on ∏iM_i, det(f)=∏i det(f_i). For component linear
equivalences e_i:M_i≃M_i, det(piCongrRight e)=∏i det(e_i).
-/
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

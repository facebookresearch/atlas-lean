/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv.lean`
and
`P2M/Sol/S_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Norms in tensor products with a Galois extension

For a Galois extension `M / F` and any `F`-algebra `R`, the norm of an
element `z : R ⊗[F] M` over `R` is the product of its Galois conjugates.
The proof diagonalizes left multiplication by `z` over `M` by a Vandermonde
matrix built from the embeddings of `M`.
-/

@[expose] public section

universe u v

open scoped TensorProduct
open Matrix

namespace TensorProductNormAux

variable (F M : Type*) [Field F] [Field M] [Algebra F M]
  (R : Type*) [CommRing R] [Algebra F R]

private abbrev S := R ⊗[F] M

private abbrev ψM : M →ₐ[F] R ⊗[F] M := Algebra.TensorProduct.includeRight

private abbrev ψR : R →+* R ⊗[F] M := algebraMap R (R ⊗[F] M)

private theorem ψR_apply (r : R) : ψR F M R r = r ⊗ₜ[F] (1 : M) := rfl

private theorem ψM_apply (m : M) : ψM F M R m = (1 : R) ⊗ₜ[F] m := rfl

private theorem ψM_algebraMap (f : F) :
    ψM F M R (algebraMap F M f) = algebraMap F (R ⊗[F] M) f :=
  AlgHom.commutes _ f

private theorem ψR_algebraMap (f : F) :
    ψR F M R (algebraMap F R f) = algebraMap F (R ⊗[F] M) f :=
  (IsScalarTower.algebraMap_apply F R (R ⊗[F] M) f).symm

private abbrev act (g : M ≃ₐ[F] M) : R ⊗[F] M →ₐ[F] R ⊗[F] M :=
  Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M)

private theorem act_tmul (g : M ≃ₐ[F] M) (r : R) (m : M) :
    act F M R g (r ⊗ₜ[F] m) = r ⊗ₜ[F] g m := rfl

section Matrices

variable {n : ℕ} (b : Module.Basis (Fin n) F M) (e : (M ≃ₐ[F] M) ≃ Fin n)

private noncomputable abbrev A (x : M) : Matrix (Fin n) (Fin n) F := Algebra.leftMulMatrix b x

private noncomputable def P : Matrix (Fin n) (Fin n) M := fun i j => e.symm i (b j)

private theorem P_mul_A (x : M) :
    P F M b e * (A F M b x).map (algebraMap F M) =
      diagonal (fun i => e.symm i x) * P F M b e := by
  ext i k
  rw [Matrix.mul_apply, diagonal_mul]
  have hx : x * b k = ∑ j, (A F M b x) j k • b j := by
    conv_lhs => rw [← b.sum_repr (x * b k)]
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
  have := congrArg (e.symm i) hx
  rw [map_mul, map_sum] at this
  simp only [Algebra.smul_def] at this
  rw [P, this]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, P]
  rw [map_mul, AlgEquiv.commutes, mul_comm]

private theorem det_P_ne_zero : (P F M b e).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  have hli : LinearIndependent M
      fun i : Fin n => ((e.symm i : M ≃ₐ[F] M) : M →ₐ[F] M).toLinearMap := by
    have h := linearIndependent_algHom_toLinearMap F M M
    have hinj : Function.Injective
        fun i : Fin n => ((e.symm i : M ≃ₐ[F] M) : M →ₐ[F] M) := by
      intro i j hij
      apply e.symm.injective
      exact AlgEquiv.ext fun x => (congrArg (fun φ : M →ₐ[F] M => φ x) hij :)
    exact h.comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hc0
  funext i
  refine hli c ?_ i
  apply b.ext
  intro k
  have hk := congrFun hc k
  simp only [vecMul, dotProduct, P] at hk
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    LinearMap.zero_apply, smul_eq_mul]
  simpa [AlgEquiv.coe_toAlgHom] using hk

variable (bR : Module.Basis (Fin n) R (R ⊗[F] M)) (hbR : ∀ i, bR i = 1 ⊗ₜ[F] b i)

include hbR in
private theorem leftMulMatrix_tmul (r : R) (x : M) :
    Algebra.leftMulMatrix bR (r ⊗ₜ[F] x) = r • (A F M b x).map (algebraMap F R) := by
  have hb : bR = Algebra.TensorProduct.basis R b := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [hbR, Algebra.TensorProduct.basis_apply]
  subst hb
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.leftMulMatrix_eq_repr_mul]

include hbR in
private theorem P_mul_L (z : R ⊗[F] M) :
    (P F M b e).map (ψM F M R) * (Algebra.leftMulMatrix bR z).map (ψR F M R)
      = diagonal (fun i => act F M R (e.symm i) z) * (P F M b e).map (ψM F M R) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, Matrix.map_add, Matrix.mul_add, hx, hy, ← Matrix.add_mul]
      · congr 1
        rw [diagonal_add]
        congr 1
        funext i
        simp
      · exact fun a₁ a₂ => map_add _ a₁ a₂
  | tmul r x =>
      rw [leftMulMatrix_tmul F M R b bR hbR r x]
      have hmap : (r • (A F M b x).map (algebraMap F R)).map (ψR F M R)
          = ψR F M R r • ((A F M b x).map (algebraMap F M)).map (ψM F M R) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
        rw [ψM_algebraMap, ψR_algebraMap]
      rw [hmap, Matrix.mul_smul, ← Matrix.map_mul, P_mul_A F M b e x, Matrix.map_mul,
        ← Matrix.smul_mul]
      congr 1
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, diagonal, of_apply, smul_eq_mul]
      split_ifs
      · rw [act_tmul, ψR_apply, ψM_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · rw [map_zero, mul_zero]

include b bR hbR in
private theorem algebraMap_norm_eq_prod (z : R ⊗[F] M) :
    ψR F M R (Algebra.norm R z) = ∏ i, act F M R (e.symm i) z := by
  classical
  have hdet := congrArg Matrix.det (P_mul_L F M R b e bR hbR z)
  rw [det_mul, det_mul, det_diagonal] at hdet
  have hPunit : IsUnit ((P F M b e).map (ψM F M R)).det := by
    have : ((P F M b e).map (ψM F M R)).det =
        (ψM F M R : M →+* R ⊗[F] M) (P F M b e).det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr (det_P_ne_zero F M b e)).map _
  have hL : (Algebra.leftMulMatrix bR z).det = Algebra.norm R z :=
    (Algebra.norm_eq_matrix_det bR z).symm
  have hLS : ((Algebra.leftMulMatrix bR z).map (ψR F M R)).det = ψR F M R (Algebra.norm R z) := by
    rw [← hL, RingHom.map_det]; rfl
  rw [hLS, mul_comm] at hdet
  exact hPunit.mul_right_cancel hdet

end Matrices

private theorem result [FiniteDimensional F M] [IsGalois F M] (z : R ⊗[F] M) :
    algebraMap R (R ⊗[F] M) (Algebra.norm R z) =
      ∏ g : M ≃ₐ[F] M, Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M) z := by
  classical
  set n := Module.finrank F M
  let b : Module.Basis (Fin n) F M := Module.finBasis F M
  have hcard : Fintype.card (M ≃ₐ[F] M) = n := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let e : (M ≃ₐ[F] M) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bR : Module.Basis (Fin n) R (R ⊗[F] M) := Algebra.TensorProduct.basis R b
  have hbR : ∀ i, bR i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h := algebraMap_norm_eq_prod F M R b e bR hbR z
  rw [h, ← Equiv.prod_comp e.symm]

end TensorProductNormAux

namespace Algebra.TensorProduct

/-- For a Galois extension `M / F` and any `F`-algebra `R`, the norm of an
element of `R ⊗[F] M` over `R` is the product of its Galois conjugates. -/
theorem algebraMap_norm_eq_prod_map_algEquiv
    (F M : Type*) [Field F] [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (R : Type*) [CommRing R] [Algebra F R] (z : R ⊗[F] M) :
    algebraMap R (R ⊗[F] M) (Algebra.norm R z) =
      ∏ g : M ≃ₐ[F] M, Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M) z :=
  TensorProductNormAux.result F M R z

end Algebra.TensorProduct

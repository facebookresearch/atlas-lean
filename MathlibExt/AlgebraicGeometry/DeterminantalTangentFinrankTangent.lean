/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeterminantalTangent

import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Projection

/-!
# Dimension of determinantal tangent spaces

This module computes the dimension of the polynomial tangent space at a matrix of rank `r`.

References:
* Harris, *Algebraic Geometry: A First Course*, Example 14.16 (tangent spaces
  to determinantal varieties).
* Bruns–Vetter, *Determinantal Rings*, Chapter 2,
  https://doi.org/10.1007/BFb0080378.
* Covered minor-polynomial identities: TauCetiProject/TauCeti at
  62bbc0596dc3539d488232e4e924a338548ea0a9,
  `TauCeti/RingTheory/MvPolynomial/DeterminantalIdeal.lean`.
* Covered algebraic rank operations: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/LinearAlgebra/Matrix/DeterminantalRank.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeterminantalTangentWanted

open MathlibExt.AlgebraicGeometry.DeterminantalTangent
open MathlibExt.AlgebraicGeometry.AffineTangent

private def dual {k : Type*} (a b : k) : TrivSqZeroExt k k := (a, b)

private def dualMatrix {k M N : Type*} (A B : Matrix M N k) :
    Matrix M N (TrivSqZeroExt k k) := fun i j ↦ dual (A i j) (B i j)

private theorem dualMatrix_mul {k M N L : Type*} [Field k] [Fintype N]
    (A B : Matrix M N k) (C D : Matrix N L k) :
    dualMatrix A B * dualMatrix C D = dualMatrix (A * C) (A * D + B * C) := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · change (∑ t : N, dual (A i t) (B i t) * dual (C t j) (D t j)).fst =
      ∑ t : N, A i t * C t j
    rw [TrivSqZeroExt.fst_sum]
    apply Finset.sum_congr rfl
    intro t _
    rfl
  · change (∑ t : N, dual (A i t) (B i t) * dual (C t j) (D t j)).snd =
      (∑ t : N, A i t * D t j) + ∑ t : N, B i t * C t j
    rw [TrivSqZeroExt.snd_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rfl

private theorem dualMatrix_transform {k M N L P : Type*} [Field k] [Fintype M] [Fintype N]
    (U : Matrix L M k) (V : Matrix N P k) (A B : Matrix M N k) :
    dualMatrix U 0 * dualMatrix A B * dualMatrix V 0 =
      dualMatrix (U * A * V) (U * B * V) := by
  rw [dualMatrix_mul, dualMatrix_mul]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

private theorem dualMatrix_fromBlocks {k M₁ M₂ N₁ N₂ : Type*} [Field k]
    (A E : Matrix M₁ N₁ k) (B F : Matrix M₁ N₂ k)
    (C G : Matrix M₂ N₁ k) (D H : Matrix M₂ N₂ k) :
    dualMatrix (Matrix.fromBlocks A B C D) (Matrix.fromBlocks E F G H) =
      Matrix.fromBlocks (dualMatrix A E) (dualMatrix B F) (dualMatrix C G) (dualMatrix D H) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

private theorem dualMatrix_zero {k M N : Type*} [Field k] :
    dualMatrix (0 : Matrix M N k) 0 = 0 := rfl

private theorem dualMatrix_one {k N : Type*} [Field k] [DecidableEq N] :
    dualMatrix (1 : Matrix N N k) 0 = 1 := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [dualMatrix, Matrix.one_apply, h] <;> rfl

private theorem eval_dual {k σ : Type*} [Field k] [Fintype σ]
    (p v : σ → k) (f : MvPolynomial σ k) :
    MvPolynomial.aeval (fun i ↦ dual (p i) (v i)) f =
      dual (MvPolynomial.eval p f) (differential f p v) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C, MvPolynomial.eval_C, differential_C,
      LinearMap.zero_apply]; rfl
  | add f g hf hg => simp only [map_add, differential_add, LinearMap.add_apply, hf, hg]; rfl
  | mul_X f i hf =>
    simp only [map_mul, MvPolynomial.aeval_X, hf, MvPolynomial.eval_X,
      differential_mul, LinearMap.add_apply, LinearMap.smul_apply, differential_X]
    apply TrivSqZeroExt.ext
    · rfl
    · change MvPolynomial.eval p f * v i + differential f p v * p i =
        MvPolynomial.eval p f * v i + p i * differential f p v
      rw [mul_comm (differential f p v)]

private theorem eval_minor_dual {k : Type*} [Field k] {m n r : ℕ}
    (A B : Matrix (Fin m) (Fin n) k) (rows : Fin (r + 1) ↪ Fin m)
    (cols : Fin (r + 1) ↪ Fin n) :
    MvPolynomial.aeval (fun ij ↦ dual (A ij.1 ij.2) (B ij.1 ij.2))
      (minorPolynomial r rows cols : MvPolynomial (Fin m × Fin n) k) =
      (Matrix.submatrix (fun i j ↦ dual (A i j) (B i j)) rows cols).det := by
  rw [minorPolynomial, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact MvPolynomial.aeval_X _ _

private def minorsZero {R M N : Type*} [CommRing R] (r : ℕ) (A : Matrix M N R) : Prop :=
  ∀ (rows : Fin (r + 1) → M) (cols : Fin (r + 1) → N),
    (A.submatrix rows cols).det = 0

private theorem minorsZero_of_embeddings {R M N : Type*} [CommRing R]
    (r : ℕ) (A : Matrix M N R)
    (h : ∀ (rows : Fin (r + 1) ↪ M) (cols : Fin (r + 1) ↪ N),
      (A.submatrix rows cols).det = 0) : minorsZero r A := by
  classical
  intro rows cols
  by_cases hr : Function.Injective rows
  · by_cases hc : Function.Injective cols
    · exact h ⟨rows, hr⟩ ⟨cols, hc⟩
    · obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hc
      exact Matrix.det_zero_of_column_eq hij (fun t ↦ congrArg (fun c ↦ A (rows t) c) heq)
  · obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hr
    exact Matrix.det_zero_of_row_eq hij (funext fun t ↦ congrArg (fun row ↦ A row (cols t)) heq)

private theorem minorsZero_of_rank {k M N : Type*} [Field k] [Fintype N]
    (r : ℕ) (A : Matrix M N k) (hA : Matrix.rank A ≤ r) : minorsZero r A := by
  intro rows cols
  by_contra h
  have hminor := Matrix.rank_of_det_ne_zero h
  have hle := Matrix.rank_submatrix_le A rows cols
  simp only [Fintype.card_fin] at hminor
  omega

private theorem minorsZero_mul_left {R L M N : Type*} [CommRing R] [Fintype M]
    (r : ℕ) (U : Matrix L M R) (A : Matrix M N R) (hA : minorsZero r A) :
    minorsZero r (U * A) := by
  classical
  intro rows cols
  have he : (U * A).submatrix rows cols =
      fun i ↦ ∑ t : M, U (rows i) t • (fun j ↦ A t (cols j)) := by
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  rw [he]
  change Matrix.detRowAlternating.toMultilinearMap
    (fun i ↦ ∑ t : M, U (rows i) t • (fun j ↦ A t (cols j))) = 0
  rw [MultilinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro t _
  rw [MultilinearMap.map_smul_univ]
  change (∏ i, U (rows i) (t i)) • (A.submatrix t cols).det = 0
  rw [hA t cols, smul_zero]

private theorem minorsZero_transpose {R M N : Type*} [CommRing R]
    (r : ℕ) (A : Matrix M N R) (hA : minorsZero r A) : minorsZero r A.transpose := by
  intro rows cols
  simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using hA cols rows

private theorem minorsZero_mul_right {R L M N : Type*} [CommRing R] [Fintype N]
    (r : ℕ) (A : Matrix M N R) (U : Matrix N L R) (hA : minorsZero r A) :
    minorsZero r (A * U) := by
  have h := minorsZero_transpose r _
    (minorsZero_mul_left r U.transpose A.transpose (minorsZero_transpose r A hA))
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h

private theorem inverse_transform {k M N L P : Type*} [Field k]
    [Fintype M] [Fintype N] [Fintype L] [Fintype P] [DecidableEq M] [DecidableEq N]
    (U : Matrix L M k) (Ui : Matrix M L k) (V : Matrix N P k) (Vi : Matrix P N k)
    (hU : Ui * U = 1) (hV : V * Vi = 1) (B : Matrix M N k) :
    Ui * (U * B * V) * Vi = B := by
  calc
    _ = (Ui * U) * B * (V * Vi) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]

private theorem minorsZero_transform {k M N L P : Type*} [Field k]
    [Fintype M] [Fintype N] [Fintype L] [Fintype P] [DecidableEq M] [DecidableEq N]
    (r : ℕ) (U : Matrix L M k) (Ui : Matrix M L k) (V : Matrix N P k) (Vi : Matrix P N k)
    (hU : Ui * U = 1) (hV : V * Vi = 1) (A B : Matrix M N k) :
    minorsZero r (dualMatrix A B) ↔ minorsZero r (dualMatrix (U * A * V) (U * B * V)) := by
  constructor
  · intro h
    rw [← dualMatrix_transform]
    exact minorsZero_mul_right r _ _ (minorsZero_mul_left r _ _ h)
  · intro h
    have hh := minorsZero_mul_right r _ (dualMatrix Vi 0)
      (minorsZero_mul_left r (dualMatrix Ui 0) _ h)
    rw [dualMatrix_transform, inverse_transform U Ui V Vi hU hV,
      inverse_transform U Ui V Vi hU hV] at hh
    exact hh

private theorem minorsZero_small {R M N : Type*} [CommRing R] [Fintype M]
    (r : ℕ) (A : Matrix M N R) (hr : Fintype.card M ≤ r) : minorsZero r A := by
  apply minorsZero_of_embeddings
  intro rows cols
  have h := Fintype.card_le_of_embedding rows
  simp only [Fintype.card_fin] at h
  omega

private theorem minorsZero_det {R M N T : Type*} [CommRing R] [Fintype T] [DecidableEq T]
    (r : ℕ) (A : Matrix M N R) (hA : minorsZero r A) (e : T ≃ Fin (r + 1))
    (rows : T → M) (cols : T → N) : (A.submatrix rows cols).det = 0 := by
  rw [← Matrix.det_submatrix_equiv_self e.symm (A.submatrix rows cols)]
  exact hA (rows ∘ e.symm) (cols ∘ e.symm)

private theorem minorsZero_normal {k : Type*} [Field k] (r a b : ℕ)
    (B : Matrix (Fin r ⊕ Fin a) (Fin r ⊕ Fin b) k) :
    minorsZero r (dualMatrix (Matrix.fromBlocks 1 0 0 0) B) ↔ B.toBlocks₂₂ = 0 := by
  constructor
  · intro h
    let C : Matrix (Fin r ⊕ Fin a) (Fin r ⊕ Fin a) k :=
      Matrix.fromBlocks B.toBlocks₁₁ 0 B.toBlocks₂₁ 0
    let D : Matrix (Fin r ⊕ Fin b) (Fin r ⊕ Fin b) k :=
      Matrix.fromBlocks 0 B.toBlocks₁₂ 0 0
    have he : dualMatrix (1 : Matrix (Fin r ⊕ Fin a) (Fin r ⊕ Fin a) k) (-C) *
        dualMatrix (Matrix.fromBlocks 1 0 0 0) B *
        dualMatrix (1 : Matrix (Fin r ⊕ Fin b) (Fin r ⊕ Fin b) k) (-D) =
        dualMatrix (Matrix.fromBlocks 1 0 0 0) (Matrix.fromBlocks 0 0 0 B.toBlocks₂₂) := by
      rw [dualMatrix_mul, dualMatrix_mul]
      simp only [Matrix.one_mul, Matrix.mul_one]
      congr 1
      rw [← Matrix.fromBlocks_toBlocks B]
      simp [C, D, Matrix.fromBlocks_multiply, Matrix.mul_neg,
        Matrix.fromBlocks_add, Matrix.fromBlocks_neg]
    have hz := minorsZero_mul_right r _ (dualMatrix 1 (-D))
      (minorsZero_mul_left r (dualMatrix 1 (-C)) _ h)
    rw [he] at hz
    apply Matrix.ext
    intro i j
    have hh := minorsZero_det r _ hz finSumFinEquiv
      (Sum.elim Sum.inl (fun _ : Fin 1 ↦ Sum.inr i))
      (Sum.elim Sum.inl (fun _ : Fin 1 ↦ Sum.inr j))
    have hm : (dualMatrix (Matrix.fromBlocks 1 0 0 0)
        (Matrix.fromBlocks 0 0 0 B.toBlocks₂₂)).submatrix
        (Sum.elim Sum.inl (fun _ : Fin 1 ↦ Sum.inr i))
        (Sum.elim Sum.inl (fun _ : Fin 1 ↦ Sum.inr j)) =
        Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (TrivSqZeroExt k k)) 0 0
          (fun _ _ : Fin 1 ↦ dual 0 (B.toBlocks₂₂ i j)) := by
      rw [dualMatrix_fromBlocks, dualMatrix_one, dualMatrix_zero]
      apply Matrix.ext
      intro x y
      cases x <;> cases y <;> rfl
    rw [hm] at hh
    have hd := Matrix.det_fromBlocks_zero₂₁
      (1 : Matrix (Fin r) (Fin r) (TrivSqZeroExt k k))
      (0 : Matrix (Fin r) (Fin 1) (TrivSqZeroExt k k))
      (fun _ _ : Fin 1 ↦ dual 0 (B.toBlocks₂₂ i j))
    have hh' := hd.symm.trans hh
    rw [Matrix.det_one, one_mul] at hh'
    have helem := (Matrix.det_fin_one (fun _ _ : Fin 1 ↦ dual 0 (B.toBlocks₂₂ i j))).symm.trans hh'
    exact congrArg TrivSqZeroExt.snd helem
  · intro h
    let U := Matrix.fromRows (1 : Matrix (Fin r) (Fin r) k) (0 : Matrix (Fin a) (Fin r) k)
    let V := Matrix.fromCols (1 : Matrix (Fin r) (Fin r) k) (0 : Matrix (Fin r) (Fin b) k)
    let E := Matrix.fromRows B.toBlocks₁₁ B.toBlocks₂₁
    let F := Matrix.fromCols (0 : Matrix (Fin r) (Fin r) k) B.toBlocks₁₂
    have he : dualMatrix U E * dualMatrix V F =
        dualMatrix (Matrix.fromBlocks 1 0 0 0) B := by
      rw [dualMatrix_mul]
      congr 1
      · simp only [U, V, Matrix.fromRows_mul_fromCols, Matrix.one_mul, Matrix.mul_zero,
          Matrix.zero_mul]
      · rw [← Matrix.fromBlocks_toBlocks B, h]
        simp only [U, V, E, F, Matrix.fromRows_mul_fromCols, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_zero, Matrix.zero_mul, Matrix.fromBlocks_add, add_zero, zero_add]
    rw [← he]
    exact minorsZero_mul_left r _ _ (minorsZero_small r _ (by simp))

private theorem mem_tangent_dual {k : Type*} [Field k] {m n r : ℕ}
    (A B : Matrix (Fin m) (Fin n) k) (hA : Matrix.rank A ≤ r) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent r A ↔
      minorsZero r (dualMatrix A B) := by
  have hz := minorsZero_of_rank r A hA
  rw [tangent, minorIdeal, tangentIdeal_span]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h
      apply minorsZero_of_embeddings
      intro rows cols
      have hd := h _ ⟨(rows, cols), rfl⟩
      have he := eval_dual (fun ij ↦ A ij.1 ij.2) (fun ij ↦ B ij.1 ij.2)
        (minorPolynomial r rows cols)
      rw [eval_minor_dual] at he
      change ((dualMatrix A B).submatrix rows cols).det = _ at he
      rw [he]
      apply TrivSqZeroExt.ext
      · simpa [dual] using hz rows cols
      · exact hd
    · intro h f hf
      obtain ⟨⟨rows, cols⟩, rfl⟩ := hf
      have he := eval_dual (fun ij ↦ A ij.1 ij.2) (fun ij ↦ B ij.1 ij.2)
        (minorPolynomial r rows cols)
      rw [eval_minor_dual] at he
      have hh := congrArg TrivSqZeroExt.snd (he.symm.trans (h rows cols))
      exact hh
  · rintro f ⟨⟨rows, cols⟩, rfl⟩
    simpa using hz rows cols

private theorem rank_normal_form {k : Type*} [Field k] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) k) :
    ∃ (a b : ℕ)
      (U : Matrix (Fin A.rank ⊕ Fin a) (Fin m) k)
      (Ui : Matrix (Fin m) (Fin A.rank ⊕ Fin a) k)
      (V : Matrix (Fin n) (Fin A.rank ⊕ Fin b) k)
      (Vi : Matrix (Fin A.rank ⊕ Fin b) (Fin n) k),
      U * Ui = 1 ∧ Ui * U = 1 ∧ V * Vi = 1 ∧ Vi * V = 1 ∧
      U * A * V = Matrix.fromBlocks 1 0 0 0 ∧ A.rank + a = m ∧ A.rank + b = n := by
  let f := A.mulVecLin
  let I := LinearMap.range f
  let K := LinearMap.ker f
  obtain ⟨P, hP⟩ := Submodule.exists_isCompl K
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl I
  let eP : P ≃ₗ[k] I := (K.quotientEquivOfIsCompl P hP).symm ≪≫ₗ f.quotKerEquivRange
  have heP (x : P) : (eP x : Fin m → k) = f x := by
    simp only [eP, LinearEquiv.trans_apply, Submodule.quotientEquivOfIsCompl_symm_apply]
    exact f.quotKerEquivRange_apply_mk x
  let bI := Module.finBasis k I
  let bK := Module.finBasis k K
  let bQ := Module.finBasis k Q
  let bV := ((bI.map eP.symm).prod bK).map (P.prodEquivOfIsCompl K hP.symm)
  let bW := (bI.prod bQ).map (I.prodEquivOfIsCompl Q hQ)
  let U := bW.toMatrix (Pi.basisFun k (Fin m))
  let Ui := (Pi.basisFun k (Fin m)).toMatrix bW
  let V := (Pi.basisFun k (Fin n)).toMatrix bV
  let Vi := bV.toMatrix (Pi.basisFun k (Fin n))
  have hinl (j : Fin (Module.finrank k I)) : f (bV (Sum.inl j)) = bW (Sum.inl j) := by
    simp only [bV, bW, Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inl,
      Function.comp_apply, LinearMap.inl_apply, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_zero, add_zero]
    simpa only [LinearEquiv.apply_symm_apply] using (heP (eP.symm (bI j))).symm
  have hinr (j : Fin (Module.finrank k K)) : f (bV (Sum.inr j)) = 0 := by
    simp only [bV, Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr,
      Function.comp_apply, LinearMap.inr_apply, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_zero, zero_add]
    exact (bK j).property
  have hn : LinearMap.toMatrix bV bW f = Matrix.fromBlocks 1 0 0 0 := by
    apply Matrix.ext
    intro i j
    cases j with
    | inl j =>
      rw [LinearMap.toMatrix_apply, hinl]
      cases i <;> simp [Matrix.fromBlocks, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    | inr j =>
      rw [LinearMap.toMatrix_apply, hinr, map_zero]
      cases i <;> rfl
  refine ⟨Module.finrank k Q, Module.finrank k K, U, Ui, V, Vi,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    ?_, ?_, ?_⟩
  · change bW.toMatrix (Pi.basisFun k (Fin m)) * A *
      (Pi.basisFun k (Fin n)).toMatrix bV = _
    have hstd : LinearMap.toMatrix (Pi.basisFun k (Fin n)) (Pi.basisFun k (Fin m)) f = A := by
      change LinearMap.toMatrix (Pi.basisFun k (Fin n)) (Pi.basisFun k (Fin m)) A.mulVecLin = A
      rw [← Matrix.toLin'_apply', ← Matrix.toLin_eq_toLin']
      exact LinearMap.toMatrix_toLin _ _ A
    calc
      _ = bW.toMatrix (Pi.basisFun k (Fin m)) *
          LinearMap.toMatrix (Pi.basisFun k (Fin n)) (Pi.basisFun k (Fin m)) f *
          (Pi.basisFun k (Fin n)).toMatrix bV :=
        congrArg (fun M ↦ bW.toMatrix (Pi.basisFun k (Fin m)) * M *
          (Pi.basisFun k (Fin n)).toMatrix bV) hstd.symm
      _ = LinearMap.toMatrix bV bW f :=
        basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix _ _ _ _ _
      _ = _ := hn
  · have hd := (I.prodEquivOfIsCompl Q hQ).finrank_eq
    simpa only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin, I, f, Matrix.rank]
      using hd
  · simpa only [Module.finrank_pi, Fintype.card_fin, K, f, Matrix.rank] using
      f.finrank_range_add_finrank_ker

private def normalMap {k : Type*} [Field k] {m n r a b : ℕ}
    (U : Matrix (Fin r ⊕ Fin a) (Fin m) k)
    (V : Matrix (Fin n) (Fin r ⊕ Fin b) k) :
    ((Fin m × Fin n) → k) →ₗ[k] Matrix (Fin a) (Fin b) k where
  toFun v := (U * Matrix.of (fun i j ↦ v (i, j)) * V).toBlocks₂₂
  map_add' x y := by
    change (U * (Matrix.of (fun i j ↦ x (i, j)) +
      Matrix.of (fun i j ↦ y (i, j))) * V).toBlocks₂₂ = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' c x := by
    change (U * (c • Matrix.of (fun i j ↦ x (i, j))) * V).toBlocks₂₂ = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

private theorem normalMap_surjective {k : Type*} [Field k] {m n r a b : ℕ}
    (U : Matrix (Fin r ⊕ Fin a) (Fin m) k)
    (Ui : Matrix (Fin m) (Fin r ⊕ Fin a) k)
    (V : Matrix (Fin n) (Fin r ⊕ Fin b) k)
    (Vi : Matrix (Fin r ⊕ Fin b) (Fin n) k)
    (hU : U * Ui = 1) (hV : Vi * V = 1) : Function.Surjective (normalMap U V) := by
  intro D
  let C : Matrix (Fin r ⊕ Fin a) (Fin r ⊕ Fin b) k := Matrix.fromBlocks 0 0 0 D
  let B := Ui * C * Vi
  refine ⟨fun ij ↦ B ij.1 ij.2, ?_⟩
  change (U * (Ui * C * Vi) * V).toBlocks₂₂ = D
  rw [inverse_transform Ui U Vi V hU hV]
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

/-- The rank-exactly-`r` stratum has the expected tangent dimension. -/
theorem finrank_tangent {k : Type*} [Field k] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) k)
    (hA : Matrix.rank A = r) (hrm : r < m) (hrn : r < n) :
    Module.finrank k (tangent r A) = r * (m + n - r) := by
  subst r
  obtain ⟨a, b, U, Ui, V, Vi, hU, hUi, hV, hVi, hn, ha, hb⟩ := rank_normal_form A
  have hker : LinearMap.ker (normalMap U V) = tangent A.rank A := by
    ext v
    rw [LinearMap.mem_ker]
    have hm := mem_tangent_dual A (Matrix.of fun i j ↦ v (i, j)) le_rfl
    change v ∈ tangent A.rank A ↔
      minorsZero A.rank (dualMatrix A (Matrix.of fun i j ↦ v (i, j))) at hm
    rw [minorsZero_transform A.rank U Ui V Vi hUi hV, hn, minorsZero_normal] at hm
    exact hm.symm
  have hdim : a * b + Module.finrank k (tangent A.rank A) = m * n := by
    have hd := (normalMap U V).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (normalMap_surjective U Ui V Vi hU hVi),
      hker, finrank_top] at hd
    simpa only [Module.finrank_matrix, Module.finrank_pi, Fintype.card_prod,
      Fintype.card_fin, CommSemiring.finrank_self, mul_one] using hd
  have hsum : m + n - A.rank = A.rank + a + b := by omega
  have hprod : a * b + A.rank * (m + n - A.rank) = m * n := by
    calc
      _ = (A.rank + a) * (A.rank + b) := by rw [hsum]; ring
      _ = m * n := congrArg₂ (· * ·) ha hb
  omega

end WantedExt.AlgebraicGeometry.DeterminantalTangentWanted

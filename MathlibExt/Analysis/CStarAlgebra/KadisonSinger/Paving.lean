/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

universe u v

open scoped Matrix.Norms.L2Operator in
/-- **Finite-support Marcus–Spielman–Srivastava bound.** The proposition that the following holds
for every natural number $m$ and every finite index set $D$. Let $s_1, \dots, s_m$ be positive
integers, let $p_{i,a} \ge 0$ be reals and $v_{i,a} \in \mathbb{C}^D$ be vectors for
$1 \le i \le m$ and $1 \le a \le s_i$, and let $\eta \ge 0$ be real. Suppose that
$\sum_a p_{i,a} = 1$ for each $i$, that $\sum_i \sum_a p_{i,a} v_{i,a} v_{i,a}^* = \mathrm{Id}_D$,
and that $\sum_a p_{i,a} \|v_{i,a}\|^2 \le \eta$ for each $i$, where $\|v_{i,a}\|$ is the
Euclidean norm. Then there are choices $a_i \in \{1, \dots, s_i\}$ for $i = 1, \dots, m$ such
that $\left\|\sum_i v_{i,a_i} v_{i,a_i}^*\right\| \le (1 + \sqrt{\eta})^2$, where the norm of a
matrix is the operator norm.

In probabilistic terms, $p_{i,a}$ is the probability that an independent random vector $v_i$
takes the value $v_{i,a}$, and the conclusion is that some choice of values meets the bound. -/
public def FiniteMSSBound : Prop :=
  ∀ (m : ℕ) (d : Type u) [Fintype d] [DecidableEq d] (s : Fin m → ℕ),
    (∀ i, 0 < s i) →
    ∀ (p : (i : Fin m) → Fin (s i) → ℝ)
      (v : (i : Fin m) → Fin (s i) → d → ℂ) (η : ℝ),
      0 ≤ η →
      (∀ i a, 0 ≤ p i a) →
      (∀ i, ∑ a, p i a = 1) →
      (∑ i, ∑ a, (p i a : ℂ) • Matrix.vecMulVec (v i a) (star (v i a)) = 1) →
      (∀ i, ∑ a, p i a * ∑ k, ‖v i a k‖ ^ 2 ≤ η) →
      ∃ ω : (i : Fin m) → Fin (s i),
        ‖∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i)))‖ ≤
          (1 + Real.sqrt η) ^ 2

private noncomputable def ksLiftVector {r d : ℕ} (a : Fin r) (u : Fin d → ℂ) :
    Fin r × Fin d → ℂ :=
  fun x ↦ if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0

private def ksMatrixEntryLM {m n : Type} (x : m) (y : n) : Matrix m n ℂ →ₗ[ℂ] ℂ :=
  (LinearMap.proj y : (n → ℂ) →ₗ[ℂ] ℂ).comp
    (LinearMap.proj x : Matrix m n ℂ →ₗ[ℂ] (n → ℂ))

private lemma ksSum_lift_outer {r d : ℕ} (hr : 0 < r) (u : Fin d → ℂ)
    (x y : Fin r × Fin d) :
    ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) *
      (ksLiftVector a u x * star (ksLiftVector a u y))) =
      if x.1 = y.1 then u x.2 * star (u y.2) else 0 := by
  have hcoef : ((r : ℂ)⁻¹ * (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) = 1 := by
    calc
      (r : ℂ)⁻¹ * (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) =
          (r : ℂ)⁻¹ * ((Real.sqrt r * Real.sqrt r : ℝ) : ℂ) := by
        push_cast
        ring
      _ = (r : ℂ)⁻¹ * (r : ℂ) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
        norm_num
      _ = 1 := by simp [hr.ne']
  by_cases hxy : x.1 = y.1
  · simp only [ksLiftVector]
    rw [show y.1 = x.1 from hxy.symm]
    have hsum :
        (∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) *
          ((if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0) *
            star (if x.1 = a then (Real.sqrt r : ℂ) * u y.2 else 0)))) =
          (((r : ℝ)⁻¹ : ℂ) *
            (((Real.sqrt r : ℂ) * u x.2) * star ((Real.sqrt r : ℂ) * u y.2))) := by
      let f : Fin r → ℂ := fun a ↦ (((r : ℝ)⁻¹ : ℂ) *
        ((if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0) *
          star (if x.1 = a then (Real.sqrt r : ℂ) * u y.2 else 0)))
      change (∑ a, f a) = _
      calc
        (∑ a, f a) = f x.1 := by
          apply Finset.sum_eq_single_of_mem x.1 (Finset.mem_univ _)
          intro a ha hax
          have hxa : x.1 ≠ a := Ne.symm hax
          simp [f, hxa]
        _ = _ := by simp [f]
    rw [hsum]
    simp only [map_mul, RCLike.star_def, Complex.conj_ofReal]
    calc
      (↑r)⁻¹ * ((↑√↑r * u x.2) * (↑√↑r * (starRingEnd ℂ) (u y.2))) =
          (((↑r)⁻¹ * ↑√↑r * ↑√↑r) * (u x.2 * (starRingEnd ℂ) (u y.2))) := by
        ring
      _ = u x.2 * (starRingEnd ℂ) (u y.2) := by rw [hcoef, one_mul]
  · simp only [hxy, ↓reduceIte, ksLiftVector]
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hxa : x.1 = a
    · have hya : y.1 ≠ a := fun h ↦ hxy (hxa.trans h.symm)
      simp [hxa, hya]
    · simp [hxa]

private lemma ksLift_covariance_sum {m d r : ℕ} (hr : 0 < r)
    (u : Fin m → Fin d → ℂ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1) :
    ((∑ i, ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) •
      Matrix.vecMulVec (ksLiftVector a (u i)) (star (ksLiftVector a (u i))))) :
        Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) = 1 := by
  apply funext
  intro x
  apply funext
  intro y
  change ksMatrixEntryLM x y
      (∑ i, ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) •
        Matrix.vecMulVec (ksLiftVector a (u i)) (star (ksLiftVector a (u i))))) =
    ksMatrixEntryLM x y (1 : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ)
  simp only [map_sum, map_smul]
  change (∑ i, ∑ a : Fin r, (((r : ℝ)⁻¹ : ℂ) *
    (ksLiftVector a (u i) x * star (ksLiftVector a (u i) y)))) =
      (1 : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) x y
  rw [Matrix.one_apply]
  simp_rw [ksSum_lift_outer hr]
  have hf := congrArg (ksMatrixEntryLM x.2 y.2) hframe
  simp only [map_sum] at hf
  change (∑ i, u i x.2 * star (u i y.2)) =
    (1 : Matrix (Fin d) (Fin d) ℂ) x.2 y.2 at hf
  rw [Matrix.one_apply] at hf
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ↓reduceIte]
    simpa [Prod.ext_iff, hxy] using hf
  · simp [Prod.ext_iff, hxy]

private lemma ksLift_norm_sq {r d : ℕ} (a : Fin r) (u : Fin d → ℂ) :
    ∑ x : Fin r × Fin d, ‖ksLiftVector a u x‖ ^ 2 =
      r * ∑ k, ‖u k‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  let f : Fin r → ℝ := fun b ↦ ∑ k, ‖ksLiftVector a u (b, k)‖ ^ 2
  change (∑ b, f b) = _
  calc
    (∑ b, f b) = f a := by
      apply Finset.sum_eq_single_of_mem a (Finset.mem_univ _)
      intro b hb hba
      simp [f, ksLiftVector, hba]
    _ = r * ∑ k, ‖u k‖ ^ 2 := by
      simp only [f, ksLiftVector, ite_true, norm_mul, Complex.norm_real]
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      simp_rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]
      rw [Finset.mul_sum]

private noncomputable def ksPavingProj {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i ↦ if c i = j then 1 else 0)

private lemma ksFiltered_columns {n r : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (c : Fin n → Fin r) (j : Fin r) :
    ((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
      Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) :
        Matrix (Fin n) (Fin n) ℂ) =
      S * ksPavingProj c j * Matrix.conjTranspose S := by
  apply funext
  intro a
  apply funext
  intro b
  change ksMatrixEntryLM a b
      (∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) =
    ksMatrixEntryLM a b (S * ksPavingProj c j * Matrix.conjTranspose S)
  simp only [map_sum, ksMatrixEntryLM]
  change (∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), S a i * star (S b i)) =
    (S * ksPavingProj c j * Matrix.conjTranspose S) a b
  have hinner (i : Fin n) :
      (S * ksPavingProj c j) a i = S a i * (if c i = j then 1 else 0) := by
    simp [ksPavingProj]
  rw [Matrix.mul_apply]
  simp_rw [hinner]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : c i = j <;> simp [hc]

private lemma ksAll_columns {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) :
      Matrix (Fin n) (Fin n) ℂ) = S * Matrix.conjTranspose S := by
  apply funext
  intro a
  apply funext
  intro b
  change ksMatrixEntryLM a b
      (∑ i, Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) =
    ksMatrixEntryLM a b (S * Matrix.conjTranspose S)
  simp only [map_sum, ksMatrixEntryLM]
  change (∑ i, S a i * star (S b i)) = (S * Matrix.conjTranspose S) a b
  rw [Matrix.mul_apply]
  simp

private lemma ksColumn_norm_sq {n : ℕ} (S B : Matrix (Fin n) (Fin n) ℂ)
    (hSB : Matrix.conjTranspose S * S = B) (i : Fin n) :
    ((∑ k, ‖S k i‖ ^ 2 : ℝ) : ℂ) = B i i := by
  have hi := congrFun (congrFun hSB i) i
  simpa [Matrix.mul_apply, RCLike.star_def, RCLike.conj_mul] using hi

private lemma ksPavingProj_star {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    Matrix.conjTranspose (ksPavingProj c j) = ksPavingProj c j := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [ksPavingProj, Matrix.conjTranspose_apply]
  · simp [ksPavingProj, Matrix.conjTranspose_apply, hab, Ne.symm hab]

private lemma ksPavingProj_sq {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    ksPavingProj c j * ksPavingProj c j = ksPavingProj c j := by
  rw [show ksPavingProj c j = Matrix.diagonal (fun i ↦ if c i = j then 1 else 0) by rfl]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : c i = j <;> simp [hc]

private lemma ksPavingProj_mul_of_refines {n r s : ℕ}
    (c : Fin n → Fin r) (j : Fin r) (d : Fin n → Fin s) (k : Fin s)
    (h : ∀ i, c i = j → d i = k) :
    ksPavingProj c j * ksPavingProj d k = ksPavingProj c j := by
  simp only [ksPavingProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : c i = j
  · simp [hc, h i hc]
  · simp [hc]

private lemma ksPavingProj_mul_of_refines' {n r s : ℕ}
    (c : Fin n → Fin r) (j : Fin r) (d : Fin n → Fin s) (k : Fin s)
    (h : ∀ i, c i = j → d i = k) :
    ksPavingProj d k * ksPavingProj c j = ksPavingProj c j := by
  simp only [ksPavingProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hc : c i = j
  · simp [hc, h i hc]
  · simp [hc]

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

private noncomputable def ksBlockEmbedding {r d : ℕ}
    (j : Fin r) : Matrix (Fin r × Fin d) (Fin d) ℂ :=
  fun x a => if x = (j, a) then 1 else 0

private def ksBlock {r d : ℕ}
    (M : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (j : Fin r) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => M (j, a) (j, b)

private noncomputable def ksMatrixCLM {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  (Matrix.toEuclideanLin (m := m) (n := n) (𝕜 := ℂ)).trans LinearMap.toContinuousLinearMap A

private noncomputable def ksOperatorNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  ‖ksMatrixCLM A‖

private lemma ksOperatorNorm_mul {l m n : Type} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix n l ℂ) :
    ksOperatorNorm (A * B) ≤ ksOperatorNorm A * ksOperatorNorm B := by
  unfold ksOperatorNorm ksMatrixCLM
  have h := ((Matrix.toEuclideanLin (n := n) (m := m) (𝕜 := ℂ)).trans
    LinearMap.toContinuousLinearMap A).opNorm_comp_le
      ((Matrix.toEuclideanLin (n := l) (m := n) (𝕜 := ℂ)).trans
        LinearMap.toContinuousLinearMap B)
  convert! h
  ext1 x
  exact congr(WithLp.toLp 2 ($(Matrix.toLin'_mul A B) x))

private lemma ksOperatorNorm_conjTranspose {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    ksOperatorNorm (Matrix.conjTranspose A) = ksOperatorNorm A := by
  unfold ksOperatorNorm ksMatrixCLM
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    Matrix.toLin_conjTranspose, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

private lemma ksBlockEmbedding_star_mul_self {r d : ℕ} (j : Fin r) :
    Matrix.conjTranspose
        (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ) * ksBlockEmbedding j =
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext a b
  simp [ksBlockEmbedding, Matrix.mul_apply, Matrix.one_apply, eq_comm]

private lemma ksBlockEmbedding_norm_le {r d : ℕ} [Nonempty (Fin d)] (j : Fin r) :
    ‖(ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)‖ ≤ 1 := by
  have hsq : ‖(ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)‖ *
      ‖(ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ksBlockEmbedding_star_mul_self, norm_one]
  nlinarith [norm_nonneg (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ)]

private lemma ksBlockCompression_eq {r d : ℕ}
    (M : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (j : Fin r) :
    Matrix.conjTranspose (ksBlockEmbedding j) * M * ksBlockEmbedding j =
      ksBlock M j := by
  ext a b
  change (∑ x : Fin r × Fin d, (∑ y : Fin r × Fin d,
    star (ksBlockEmbedding j y a) * M y x) * ksBlockEmbedding j x b) = _
  simp [ksBlockEmbedding, ksBlock]

private lemma ksBlock_norm_le {r d : ℕ} [Nonempty (Fin d)]
    (M : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (j : Fin r) :
    ksOperatorNorm (ksBlock M j) ≤ ksOperatorNorm M := by
  rw [← ksBlockCompression_eq M j]
  rw [Matrix.mul_assoc]
  have hE : ksOperatorNorm
      (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ) ≤ 1 := by
    unfold ksOperatorNorm ksMatrixCLM
    rw [← Matrix.l2_opNorm_def]
    exact ksBlockEmbedding_norm_le j
  have hM_nonneg : 0 ≤ ksOperatorNorm M := by
    exact norm_nonneg _
  have hE_nonneg : 0 ≤ ksOperatorNorm
      (ksBlockEmbedding j : Matrix (Fin r × Fin d) (Fin d) ℂ) := by
    exact norm_nonneg _
  calc
    ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j) *
        (M * ksBlockEmbedding j)) ≤
        ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j)) *
          ksOperatorNorm (M * ksBlockEmbedding j) := by
      exact ksOperatorNorm_mul (Matrix.conjTranspose (ksBlockEmbedding j))
        (M * ksBlockEmbedding j)
    _ ≤ ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j)) *
        (ksOperatorNorm M * ksOperatorNorm (ksBlockEmbedding j)) :=
      mul_le_mul_of_nonneg_left
        (ksOperatorNorm_mul M (ksBlockEmbedding j))
        (by exact norm_nonneg (ksMatrixCLM (Matrix.conjTranspose (ksBlockEmbedding j))))
    _ = ksOperatorNorm (ksBlockEmbedding j) *
        (ksOperatorNorm M * ksOperatorNorm (ksBlockEmbedding j)) := by
      rw [show ksOperatorNorm (Matrix.conjTranspose (ksBlockEmbedding j)) =
          ksOperatorNorm (ksBlockEmbedding j) by
        exact ksOperatorNorm_conjTranspose (ksBlockEmbedding j)]
    _ = (ksOperatorNorm (ksBlockEmbedding j) * ksOperatorNorm M) *
        ksOperatorNorm (ksBlockEmbedding j) := by ring
    _ ≤ ksOperatorNorm M * ksOperatorNorm (ksBlockEmbedding j) :=
      mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hE hM_nonneg)
        hE_nonneg
    _ ≤ ksOperatorNorm M * 1 :=
      mul_le_mul_of_nonneg_left hE hM_nonneg
    _ = ksOperatorNorm M := mul_one _

private lemma ksPavingProj_norm_le {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    ‖ksPavingProj c j‖ ≤ 1 := by
  have hsq : ‖ksPavingProj c j‖ * ‖ksPavingProj c j‖ = ‖ksPavingProj c j‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ksPavingProj_star, ksPavingProj_sq]
  nlinarith [norm_nonneg (ksPavingProj c j)]

private lemma ksRefine_order_bound {n r s : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (a : ℝ)
    (c : Fin n → Fin r) (j : Fin r) (d : Fin n → Fin s) (k : Fin s)
    (h : ∀ i, c i = j → d i = k)
    (hbound : ksPavingProj d k * B * ksPavingProj d k ≤ a • ksPavingProj d k) :
    ksPavingProj c j * B * ksPavingProj c j ≤ a • ksPavingProj c j := by
  let Q := ksPavingProj c j
  let P := ksPavingProj d k
  have hQP : Q * P = Q := ksPavingProj_mul_of_refines c j d k h
  have hPQ : P * Q = Q := ksPavingProj_mul_of_refines' c j d k h
  have hQself : IsSelfAdjoint Q :=
    (show Q.IsHermitian from ksPavingProj_star c j).isSelfAdjoint
  have hc := hQself.conjugate_le_conjugate hbound
  calc
    Q * B * Q = Q * (P * B * P) * Q := by
      rw [show Q * (P * B * P) * Q = (Q * P) * B * (P * Q) by noncomm_ring]
      rw [hQP, hPQ]
    _ ≤ Q * (a • P) * Q := hc
    _ = a • Q := by
      rw [show Q * (a • P) * Q = a • (Q * P * Q) by
        simp only [mul_smul_comm, smul_mul_assoc]]
      rw [hQP, ksPavingProj_sq]

private lemma ksCompression_le_smul_projection {n r : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hB0 : 0 ≤ B)
    (c : Fin n → Fin r) (j : Fin r) (a : ℝ)
    (hnorm : ‖ksPavingProj c j * B * ksPavingProj c j‖ ≤ a) :
    ksPavingProj c j * B * ksPavingProj c j ≤ a • ksPavingProj c j := by
  let Q := ksPavingProj c j
  let X := Q * B * Q
  have hQstar : Matrix.conjTranspose Q = Q := ksPavingProj_star c j
  have hQsq : Q * Q = Q := ksPavingProj_sq c j
  have hQself : IsSelfAdjoint Q :=
    (show Q.IsHermitian from hQstar).isSelfAdjoint
  have hX0 : 0 ≤ X := by
    have hx := star_left_conjugate_nonneg hB0 Q
    simpa only [X, Matrix.star_eq_conjTranspose, hQstar] using hx
  have hXleNorm : X ≤ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖X‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self X (IsSelfAdjoint.of_nonneg hX0)
  have hmap : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖X‖ ≤
      (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) a := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right hnorm
      (show 0 ≤ (1 : Matrix (Fin n) (Fin n) ℂ) from zero_le_one)
  have hc := hQself.conjugate_le_conjugate (hXleNorm.trans hmap)
  change X ≤ a • Q
  calc
    X = Q * X * Q := by
      symm
      calc
        Q * X * Q = (Q * Q) * B * (Q * Q) := by
          simp only [X]
          noncomm_ring
        _ = X := by rw [hQsq]
    _ ≤ Q * (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) a * Q := hc
    _ = a • Q := by simp [Algebra.algebraMap_eq_smul_one, hQsq]

private lemma ksMSS_outcome_for_frame
    (hMSS : FiniteMSSBound.{0}) {m d r : ℕ} (hr : 0 < r)
    (u : Fin m → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
    (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
    ∃ c : Fin m → Fin r,
      ‖∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
        (star (ksLiftVector (c i) (u i)))‖ ≤
          (1 + Real.sqrt (r * δ)) ^ 2 := by
  apply hMSS m (Fin r × Fin d) (fun _ ↦ r) (fun _ ↦ hr)
    (fun _ _ ↦ (r : ℝ)⁻¹) (fun i a ↦ ksLiftVector a (u i)) (r * δ)
  · positivity
  · intro i a
    positivity
  · intro i
    simp [hr.ne']
  · simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      ksLift_covariance_sum hr u hframe
  · intro i
    calc
      ∑ a : Fin r, (r : ℝ)⁻¹ * ∑ x, ‖ksLiftVector a (u i) x‖ ^ 2 =
          r * ∑ k, ‖u i k‖ ^ 2 := by
        simp_rw [ksLift_norm_sq]
        simp [hr.ne']
      _ ≤ r * δ := mul_le_mul_of_nonneg_left (hu i) (Nat.cast_nonneg r)

private def ksColorGram {m d r : ℕ} (u : Fin m → Fin d → ℂ)
    (c : Fin m → Fin r) (j : Fin r) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), Matrix.vecMulVec (u i) (star (u i))

private lemma ksBlock_outcome_eq {m d r : ℕ} (u : Fin m → Fin d → ℂ)
    (c : Fin m → Fin r) (j : Fin r) :
    ksBlock (∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
      (star (ksLiftVector (c i) (u i)))) j = (r : ℂ) • ksColorGram u c j := by
  apply funext
  intro a
  apply funext
  intro b
  change ksMatrixEntryLM (j, a) (j, b)
      (∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
        (star (ksLiftVector (c i) (u i)))) =
    ksMatrixEntryLM a b ((r : ℂ) • ksColorGram u c j)
  simp only [ksColorGram, map_sum, map_smul, ksMatrixEntryLM, smul_eq_mul]
  change (∑ i, ksLiftVector (c i) (u i) (j, a) *
      star (ksLiftVector (c i) (u i) (j, b))) =
    (r : ℂ) * ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
      u i a * star (u i b)
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : c i = j
  · subst j
    simp only [ksLiftVector, ite_true, map_mul, RCLike.star_def, Complex.conj_ofReal]
    calc
      ↑√↑r * u i a * (↑√↑r * (starRingEnd ℂ) (u i b)) =
          ((↑√↑r * ↑√↑r) * (u i a * (starRingEnd ℂ) (u i b))) := by ring
      _ = (r : ℂ) * (u i a * (starRingEnd ℂ) (u i b)) := by
        norm_cast
        rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
        norm_num
  · have hjc : j ≠ c i := Ne.symm hc
    simp [ksLiftVector, hc, hjc]

private lemma ksMSS_rescale {r : ℕ} (hr : 0 < r) {δ : ℝ} :
    (1 + Real.sqrt (r * δ)) ^ 2 / r =
      (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := by
  rw [Real.sqrt_mul (Nat.cast_nonneg r)]
  have hspos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hr)
  have hsne : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt hspos
  have hs2 : Real.sqrt (r : ℝ) ^ 2 = r := Real.sq_sqrt (Nat.cast_nonneg r)
  field_simp [hsne]
  nlinarith

private theorem ksExists_fin_frame_partition
    (hMSS : FiniteMSSBound.{0}) {m d r : ℕ} (hr : 0 < r)
    (u : Fin m → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
    (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
    ∃ c : Fin m → Fin r, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
          (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := by
  cases d with
  | zero =>
      let c : Fin m → Fin r := fun _ ↦ ⟨0, hr⟩
      refine ⟨c, ?_⟩
      intro j
      have hzero :
          ((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
            Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin 0) (Fin 0) ℂ) = 0 :=
        Subsingleton.elim _ _
      rw [hzero, norm_zero]
      positivity
  | succ d =>
      obtain ⟨c, hc⟩ := ksMSS_outcome_for_frame hMSS hr u δ hδ hframe hu
      refine ⟨c, ?_⟩
      intro j
      let M : Matrix (Fin r × Fin (d + 1)) (Fin r × Fin (d + 1)) ℂ :=
        ∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
          (star (ksLiftVector (c i) (u i)))
      have hfull : ksOperatorNorm M ≤ (1 + Real.sqrt (r * δ)) ^ 2 := by
        unfold ksOperatorNorm ksMatrixCLM
        rw [← Matrix.l2_opNorm_def]
        exact hc
      have hblock : ksOperatorNorm (ksBlock M j) ≤
          (1 + Real.sqrt (r * δ)) ^ 2 :=
        (ksBlock_norm_le M j).trans hfull
      have hblock_eq : ksBlock M j = (r : ℂ) • ksColorGram u c j := by
        exact ksBlock_outcome_eq u c j
      rw [hblock_eq] at hblock
      have hscale : ksOperatorNorm ((r : ℂ) • ksColorGram u c j) =
          r * ‖ksColorGram u c j‖ := by
        unfold ksOperatorNorm ksMatrixCLM
        rw [← Matrix.l2_opNorm_def, norm_smul]
        simp
      rw [hscale] at hblock
      change ‖ksColorGram u c j‖ ≤ (1 / Real.sqrt r + Real.sqrt δ) ^ 2
      calc
        ‖ksColorGram u c j‖ ≤ (1 + Real.sqrt (r * δ)) ^ 2 / r :=
          (le_div_iff₀ (Nat.cast_pos.2 hr)).2 (by simpa [mul_comm] using hblock)
        _ = (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := ksMSS_rescale hr

/-- **Partitioning a Parseval frame with the finite MSS bound.** Assume the finite-support
Marcus–Spielman–Srivastava bound holds. Let $I$ be a finite index set, let $d$ and $r$ be natural
numbers with $r > 0$, let $\delta \ge 0$ be real, and let $u_i \in \mathbb{C}^d$ for $i \in I$
be vectors with $\sum_{i \in I} u_i u_i^* = \mathrm{Id}_d$ and $\|u_i\|^2 \le \delta$ for every
$i$. Then there is a map $c : I \to \{1, \dots, r\}$ such that for every $j$,
$\left\|\sum_{i \in I,\ c(i) = j} u_i u_i^*\right\| \le (1/\sqrt{r} + \sqrt{\delta})^2$, where
$\|u_i\|$ is the Euclidean norm of $u_i$ and the norm of a matrix is the operator norm. -/
public theorem exists_frame_partition_of_finiteMSS
    (hMSS : FiniteMSSBound.{0}) {I : Type v} [Fintype I] {d r : ℕ}
    (hr : 0 < r) (u : I → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
    (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
    ∃ c : I → Fin r, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
          (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let v : Fin (Fintype.card I) → Fin d → ℂ := fun i ↦ u (e.symm i)
  have hv_frame : ∑ i, Matrix.vecMulVec (v i) (star (v i)) = 1 := by
    exact (e.symm.sum_comp (fun i ↦ Matrix.vecMulVec (u i) (star (u i)))).trans hframe
  have hv_norm : ∀ i, ∑ k, ‖v i k‖ ^ 2 ≤ δ := by
    intro i
    exact hu (e.symm i)
  obtain ⟨c, hc⟩ := ksExists_fin_frame_partition hMSS hr v δ hδ hv_frame hv_norm
  let c' : I → Fin r := fun i ↦ c (e i)
  refine ⟨c', ?_⟩
  intro j
  have hsum :
      ((∑ i ∈ Finset.univ.filter (fun i ↦ c' i = j),
        Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (v i) (star (v i)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    simpa [c', v] using e.sum_comp (fun i ↦
      if c i = j then Matrix.vecMulVec (v i) (star (v i)) else 0)
  rw [hsum]
  exact hc j

private theorem ksPositive_half_paving
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hdiag : ∀ i, B i i = (((1 / 2 : ℝ) : ℂ))) :
    ∃ c : Fin n → Fin r, ∀ j,
      ‖ksPavingProj c j * B * ksPavingProj c j‖ ≤
        (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 := by
  let S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt B
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt (1 - B)
  let u : Fin n ⊕ Fin n → Fin n → ℂ :=
    Sum.elim (fun i k ↦ S k i) (fun i k ↦ T k i)
  have hSstar : Matrix.conjTranspose S = S :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).isHermitian.eq
  have hTstar : Matrix.conjTranspose T = T :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 - B))).isHermitian.eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB0
  have hTT : T * T = 1 - B :=
    CFC.sqrt_mul_sqrt_self (1 - B) (sub_nonneg.mpr hB1)
  have hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) +
      ∑ i, Matrix.vecMulVec (fun k ↦ T k i) (star (fun k ↦ T k i)) = 1
    rw [ksAll_columns, ksAll_columns, hSstar, hTstar, hSS, hTT]
    noncomm_ring
  have hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    intro i
    cases i with
    | inl i =>
        change ∑ k, ‖S k i‖ ^ 2 ≤ (1 / 2 : ℝ)
        have hcol := ksColumn_norm_sq S B (by simpa [hSstar] using hSS) i
        have heq : (∑ k, ‖S k i‖ ^ 2 : ℝ) = 1 / 2 := by
          apply Complex.ofReal_injective
          exact hcol.trans (hdiag i)
        exact heq.le
    | inr i =>
        change ∑ k, ‖T k i‖ ^ 2 ≤ (1 / 2 : ℝ)
        have hcol := ksColumn_norm_sq T (1 - B) (by simpa [hTstar] using hTT) i
        have hcomp : (1 - B) i i = (((1 / 2 : ℝ) : ℂ)) := by
          simp [hdiag i]
          norm_num
        have heq : (∑ k, ‖T k i‖ ^ 2 : ℝ) = 1 / 2 := by
          apply Complex.ofReal_injective
          exact hcol.trans hcomp
        exact heq.le
  obtain ⟨cSum, hcSum⟩ :=
    exists_frame_partition_of_finiteMSS hMSS hr u (1 / 2) (by norm_num) hframe hu
  let c : Fin n → Fin r := fun i ↦ cSum (Sum.inl i)
  refine ⟨c, ?_⟩
  intro j
  let L : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i ↦ cSum (Sum.inl i) = j),
      Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))
  let R : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i ↦ cSum (Sum.inr i) = j),
      Matrix.vecMulVec (fun k ↦ T k i) (star (fun k ↦ T k i))
  let G : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i ↦ cSum i = j),
      Matrix.vecMulVec (u i) (star (u i))
  have hG : G = L + R := by
    simp only [G, L, R, Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    rfl
  have hL0 : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro i hi
    exact (Matrix.posSemidef_vecMulVec_self_star _).nonneg
  have hR0 : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro i hi
    exact (Matrix.posSemidef_vecMulVec_self_star _).nonneg
  have hLG : L ≤ G := by
    rw [hG]
    exact le_add_of_nonneg_right hR0
  have hLnorm : ‖L‖ ≤ (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 :=
    (CStarAlgebra.norm_le_norm_of_le_of_nonneg hLG hL0).trans (hcSum j)
  have hL : L = S * ksPavingProj c j * Matrix.conjTranspose S := by
    exact ksFiltered_columns S c j
  let Q := ksPavingProj c j
  let X := S * Q
  have hQstar : Matrix.conjTranspose Q = Q := ksPavingProj_star c j
  have hQsq : Q * Q = Q := ksPavingProj_sq c j
  have hleft : S * Q * Matrix.conjTranspose S = X * star X := by
    rw [hSstar]
    simp only [X, star_mul, Matrix.star_eq_conjTranspose, hQstar, hSstar]
    calc
      S * Q * S = S * (Q * S) := Matrix.mul_assoc S Q S
      _ = S * ((Q * Q) * S) := by rw [hQsq]
      _ = (S * Q) * (Q * S) := by simp only [Matrix.mul_assoc]
  have hright : Q * B * Q = star X * X := by
    simp only [X, star_mul, Matrix.star_eq_conjTranspose, hQstar, hSstar]
    rw [← hSS]
    simp [Matrix.mul_assoc]
  change ‖Q * B * Q‖ ≤ _
  calc
    ‖Q * B * Q‖ = ‖star X * X‖ := congrArg norm hright
    _ = ‖X‖ * ‖X‖ := CStarRing.norm_star_mul_self
    _ = ‖X * star X‖ := CStarRing.norm_self_mul_star.symm
    _ = ‖S * Q * Matrix.conjTranspose S‖ := congrArg norm hleft.symm
    _ = ‖L‖ := congrArg norm hL.symm
    _ ≤ _ := hLnorm

private theorem ksPositive_half_paving_order
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hdiag : ∀ i, B i i = (((1 / 2 : ℝ) : ℂ))) :
    ∃ c : Fin n → Fin r, ∀ j,
      ksPavingProj c j * B * ksPavingProj c j ≤
        (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 • ksPavingProj c j := by
  obtain ⟨c, hc⟩ := ksPositive_half_paving hMSS hr B hB0 hB1 hdiag
  refine ⟨c, ?_⟩
  intro j
  exact ksCompression_le_smul_projection B hB0 c j _ (hc j)

private theorem ksHermitian_paving_of_mss
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
    ∃ c : Fin n → Fin (r * r), ∀ j,
      ‖ksPavingProj c j * A * ksPavingProj c j‖ ≤
        2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 := by
  have hAself : IsSelfAdjoint A := hA.isSelfAdjoint
  have hmap : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖A‖ ≤
      (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right hnormA
      (show 0 ≤ (1 : Matrix (Fin n) (Fin n) ℂ) from zero_le_one)
  have hAle : A ≤ 1 := by
    calc
      A ≤ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖A‖ :=
        IsSelfAdjoint.le_algebraMap_norm_self A hAself
      _ ≤ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := hmap
      _ = 1 := by simp
  have hnegOneLe : -(1 : Matrix (Fin n) (Fin n) ℂ) ≤ A := by
    calc
      -(1 : Matrix (Fin n) (Fin n) ℂ) =
          -(algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := by simp
      _ ≤ -(algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖A‖ := neg_le_neg hmap
      _ ≤ A := IsSelfAdjoint.neg_algebraMap_norm_le_self A hAself
  let Bp : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (1 + A)
  let Bm : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (1 - A)
  have hBp0 : 0 ≤ Bp := by
    have hsum : 0 ≤ (1 : Matrix (Fin n) (Fin n) ℂ) + A := by
      have hs := add_le_add_left hnegOneLe 1
      simpa [add_comm] using hs
    exact smul_nonneg (by norm_num) hsum
  have hBp1 : Bp ≤ 1 := by
    have hs : (1 : Matrix (Fin n) (Fin n) ℂ) + A ≤ 1 + 1 :=
      by simpa [add_comm] using add_le_add_left hAle 1
    change (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + A) ≤ 1
    calc
      (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + A) ≤
          (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) :=
        smul_le_smul_of_nonneg_left hs (by norm_num)
      _ = 1 := by module
  have hBm0 : 0 ≤ Bm := by
    exact smul_nonneg (by norm_num) (sub_nonneg.mpr hAle)
  have hBm1 : Bm ≤ 1 := by
    have hnegA : -A ≤ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      simpa using neg_le_neg hnegOneLe
    have hs : (1 : Matrix (Fin n) (Fin n) ℂ) - A ≤ 1 + 1 := by
      simpa [sub_eq_add_neg] using add_le_add_left hnegA 1
    change (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) - A) ≤ 1
    calc
      (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) - A) ≤
          (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) :=
        smul_le_smul_of_nonneg_left hs (by norm_num)
      _ = 1 := by module
  have hBpdiag : ∀ i, Bp i i = (((1 / 2 : ℝ) : ℂ)) := by
    intro i
    simp [Bp, hdiagA i]
  have hBmdiag : ∀ i, Bm i i = (((1 / 2 : ℝ) : ℂ)) := by
    intro i
    simp [Bm, hdiagA i]
  obtain ⟨cp, hcp⟩ := ksPositive_half_paving_order hMSS hr Bp hBp0 hBp1 hBpdiag
  obtain ⟨cm, hcm⟩ := ksPositive_half_paving_order hMSS hr Bm hBm0 hBm1 hBmdiag
  let c : Fin n → Fin (r * r) := fun i ↦ finProdFinEquiv (cp i, cm i)
  refine ⟨c, ?_⟩
  intro j
  let p : Fin r × Fin r := finProdFinEquiv.symm j
  have hp : ∀ i, c i = j → cp i = p.1 := by
    intro i hi
    have hpairs : (cp i, cm i) = p := by
      simpa [c, p] using congrArg finProdFinEquiv.symm hi
    exact congrArg Prod.fst hpairs
  have hm : ∀ i, c i = j → cm i = p.2 := by
    intro i hi
    have hpairs : (cp i, cm i) = p := by
      simpa [c, p] using congrArg finProdFinEquiv.symm hi
    exact congrArg Prod.snd hpairs
  let α : ℝ := (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2
  let β : ℝ := 2 * α - 1
  have hpBound : ksPavingProj c j * Bp * ksPavingProj c j ≤ α • ksPavingProj c j :=
    ksRefine_order_bound Bp α c j cp p.1 hp (hcp p.1)
  have hmBound : ksPavingProj c j * Bm * ksPavingProj c j ≤ α • ksPavingProj c j :=
    ksRefine_order_bound Bm α c j cm p.2 hm (hcm p.2)
  let Q := ksPavingProj c j
  let X := Q * A * Q
  have hQsq : Q * Q = Q := ksPavingProj_sq c j
  have hplusId : (2 : ℝ) • Bp = 1 + A := by
    simp [Bp, smul_smul]
  have hminusId : (2 : ℝ) • Bm = 1 - A := by
    simp [Bm, smul_smul]
  have hXplus : X = (2 : ℝ) • (Q * Bp * Q) - Q := by
    symm
    calc
      (2 : ℝ) • (Q * Bp * Q) - Q = Q * ((2 : ℝ) • Bp) * Q - Q := by
        simp only [mul_smul_comm, smul_mul_assoc]
      _ = Q * (1 + A) * Q - Q := by rw [hplusId]
      _ = X := by simp [X, mul_add, add_mul, hQsq]
  have hXminus : -X = (2 : ℝ) • (Q * Bm * Q) - Q := by
    calc
      -X = Q * (1 - A) * Q - Q := by simp [X, mul_sub, sub_mul, hQsq]
      _ = Q * ((2 : ℝ) • Bm) * Q - Q := by rw [hminusId]
      _ = (2 : ℝ) • (Q * Bm * Q) - Q := by
        simp only [mul_smul_comm, smul_mul_assoc]
  have hupper : X ≤ β • Q := by
    rw [hXplus]
    calc
      (2 : ℝ) • (Q * Bp * Q) - Q ≤ (2 : ℝ) • (α • Q) - Q :=
        sub_le_sub_right (smul_le_smul_of_nonneg_left hpBound (by norm_num)) Q
      _ = β • Q := by
        simp [β, smul_smul]
        module
  have hnegUpper : -X ≤ β • Q := by
    rw [hXminus]
    calc
      (2 : ℝ) • (Q * Bm * Q) - Q ≤ (2 : ℝ) • (α • Q) - Q :=
        sub_le_sub_right (smul_le_smul_of_nonneg_left hmBound (by norm_num)) Q
      _ = β • Q := by
        simp [β, smul_smul]
        module
  have hbeta : 0 ≤ β := by
    have hx : 0 ≤ 1 / Real.sqrt (r : ℝ) := by positivity
    have hy : 0 ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
    have hy2 : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    dsimp [β, α]
    nlinarith [mul_nonneg hx hy]
  have hQnorm : ‖Q‖ ≤ 1 := ksPavingProj_norm_le c j
  have hendpoint : ‖β • Q‖ ≤ β := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta]
    nlinarith [norm_nonneg Q]
  have hXself : IsSelfAdjoint X := by
    have hXherm := Matrix.isHermitian_conjTranspose_mul_mul Q hA
    rw [ksPavingProj_star c j] at hXherm
    exact hXherm.isSelfAdjoint
  change ‖X‖ ≤ β
  calc
    ‖X‖ ≤ max ‖-(β • Q)‖ ‖β • Q‖ :=
      IsSelfAdjoint.norm_le_max_of_le_of_le (neg_le.mpr hnegUpper) hupper hXself
    _ = ‖β • Q‖ := by simp
    _ ≤ β := hendpoint

/-- **Anderson paving from the finite MSS bound.** Assume the finite-support
Marcus–Spielman–Srivastava bound holds. Let $n$ and $r$ be natural numbers with $r > 0$, and let
$A$ be a Hermitian complex $n \times n$ matrix with zero diagonal and operator norm
$\|A\| \le 1$. Then there is a coloring $c$ of the indices $\{1, \dots, n\}$ with $r^2$ colors
such that for every color $j$, writing $P_j$ for the diagonal matrix with entry $1$ at the
indices of color $j$ and $0$ elsewhere,
$\|P_j A P_j\| \le 2\left(1/\sqrt{r} + \sqrt{1/2}\right)^2 - 1$, where $\|\cdot\|$ is the
operator norm. -/
public theorem andersonPaving_of_finiteMSS
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
    ∃ c : Fin n → Fin (r * r), ∀ j,
      ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
          2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 := by
  simpa only [ksPavingProj] using
    ksHermitian_paving_of_mss hMSS hr A hA hdiagA hnormA

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger

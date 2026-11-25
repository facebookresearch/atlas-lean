/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.LowRankRecovery

import Mathlib.Analysis.InnerProductSpace.Trace
import MathlibExt.Analysis.InnerProductSpace.EckartYoungFrobenius
import MathlibExt.LinearAlgebra.Matrix.RankAddGeneral

/-!
# Exact recovery of low-rank matrices by nuclear norm minimization

The theorem `nuclearNorm_lt_of_isRestrictedIsometry_five_mul` gives exact recovery of matrices
of rank at most `r` by nuclear norm minimization under an order-`5r` restricted isometry
with distortion below `1/10`.
-/

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.LowRankRecovery
open scoped Matrix.Norms.Frobenius

namespace MathlibExt.LinearAlgebra.NuclearNormRecoveryWanted

open EckartYoungFrobenius InnerProductSpace Module
open scoped BigOperators

variable {m n : ℕ}

local notation "E[" d "]" => EuclideanSpace ℝ (Fin d)
local notation "M[" a "," b "]" => Matrix (Fin a) (Fin b) ℝ
local notation "lin" => Matrix.toEuclideanLin
local notation "σ" => singularSeq
local notation "v" => rightSingularBasis
local notation "⟪" x ", " y "⟫" => inner ℝ x y

private theorem rank_eq_finrank_range (A : M[m,n]) :
    A.rank = finrank ℝ (lin A).range := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

private theorem nuclearNorm_eq_sum_range (A : M[m,n]) {k : ℕ} (hk : A.rank ≤ k) :
    nuclearNorm A = ∑ i ∈ Finset.range k, σ A i := by
  rw [nuclearNorm, Finsupp.sum]
  have hs : (σ A).support = Finset.range A.rank := by
    rw [singularSeq, LinearMap.support_singularValues, rank_eq_finrank_range]
  exact Finset.sum_subset (hs ▸ Finset.range_mono hk)
    (fun _ _ hj => Finsupp.notMem_support_iff.mp hj)

private theorem singular_inner (A : M[m,n]) (i : Fin n) (x : E[n]) :
    ⟪lin A (v A i), lin A x⟫ = (σ A i) ^ 2 * ⟪v A i, x⟫ := by
  rw [← LinearMap.adjoint_inner_left, ← LinearMap.comp_apply,
    singularSeq, (lin A).sq_singularValues_fin finrank_euclideanSpace_fin]
  conv_lhs => rw [rightSingularBasis, LinearMap.IsSymmetric.apply_eigenvectorBasis]
  simp [rightSingularBasis, real_inner_smul_left]

private theorem norm_singular_image (A : M[m,n]) (i : Fin n) :
    ‖lin A (v A i)‖ = σ A i := by
  apply le_antisymm <;> apply le_of_sq_le_sq
  · rw [← real_inner_self_eq_norm_sq, singular_inner, real_inner_self_eq_norm_sq]
    simp [OrthonormalBasis.norm_eq_one]
  · exact (lin A).singularValues_nonneg i
  · rw [← real_inner_self_eq_norm_sq, singular_inner, real_inner_self_eq_norm_sq]
    simp [OrthonormalBasis.norm_eq_one]
  · exact norm_nonneg _

/-- Multiply the action on each right singular vector by its weight. -/
private noncomputable def weighted (A : M[m,n]) (w : Fin n → ℝ) : E[n] →ₗ[ℝ] E[m] :=
  (v A).toBasis.constr ℝ (fun i => w i • lin A (v A i))

private theorem weighted_basis (A : M[m,n]) (w : Fin n → ℝ) (i : Fin n) :
    weighted A w (v A i) = w i • lin A (v A i) :=
  (v A).toBasis.constr_basis ℝ _ i

private theorem weighted_apply (A : M[m,n]) (w : Fin n → ℝ) (x : E[n]) :
    weighted A w x = ∑ i, (⟪v A i, x⟫ * w i) • lin A (v A i) := by
  conv_lhs => rw [← (v A).sum_repr x, map_sum]
  simp only [map_smul, OrthonormalBasis.repr_apply_apply, weighted_basis, smul_smul]

private theorem weighted_range_le (A : M[m,n]) (w : Fin n → ℝ) :
    (weighted A w).range ≤ (lin A).range := by
  rintro _ ⟨x, rfl⟩
  rw [weighted_apply]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

private theorem le_weighted_ker (A : M[m,n]) (w : Fin n → ℝ) :
    (lin A).ker ≤ (weighted A w).ker := by
  intro x hx
  rw [LinearMap.mem_ker, weighted_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := singular_inner A i x
  rw [LinearMap.mem_ker.mp hx, inner_zero_right, zero_eq_mul] at hi
  rcases hi with hi | hi
  · have hz : σ A i = 0 := sq_eq_zero_iff.mp hi
    have hin : lin A (v A i) = 0 := norm_eq_zero.mp ((norm_singular_image A i).trans hz)
    rw [hin, smul_zero]
  · rw [hi, zero_mul, zero_smul]

/-- The trace pairing, computed in any orthonormal basis of the domain. -/
private noncomputable def pairing (L T : E[n] →ₗ[ℝ] E[m]) : ℝ :=
  LinearMap.trace ℝ _ (L.adjoint ∘ₗ T)

private theorem pairing_eq_sum {ι : Type*} [Fintype ι] (L T : E[n] →ₗ[ℝ] E[m])
    (b : OrthonormalBasis ι ℝ E[n]) :
    pairing L T = ∑ i, ⟪L (b i), T (b i)⟫ := by
  simp [pairing, LinearMap.trace_eq_sum_inner _ b, LinearMap.adjoint_inner_right]

private theorem pairing_add_left (L K T : E[n] →ₗ[ℝ] E[m]) :
    pairing (L + K) T = pairing L T + pairing K T := by
  simp only [pairing_eq_sum _ _ (EuclideanSpace.basisFun (Fin n) ℝ), LinearMap.add_apply,
    inner_add_left, Finset.sum_add_distrib]

private theorem pairing_add_right (L T S : E[n] →ₗ[ℝ] E[m]) :
    pairing L (T + S) = pairing L T + pairing L S := by
  simp only [pairing_eq_sum _ _ (EuclideanSpace.basisFun (Fin n) ℝ), LinearMap.add_apply,
    inner_add_right, Finset.sum_add_distrib]

private theorem pairing_eq_zero_of_range_le_orthogonal (L T : E[n] →ₗ[ℝ] E[m])
    (h : T.range ≤ L.rangeᗮ) : pairing L T = 0 := by
  rw [pairing_eq_sum _ _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  exact Finset.sum_eq_zero fun i _ =>
    (L.range.mem_orthogonal _).mp (h (LinearMap.mem_range_self _ _)) _
      (LinearMap.mem_range_self _ _)

private theorem pairing_le_nuclearNorm (A : M[m,n]) (L : E[n] →ₗ[ℝ] E[m])
    (hL : ∀ x, ‖L x‖ ≤ ‖x‖) : pairing L (lin A) ≤ nuclearNorm A := by
  rw [pairing_eq_sum _ _ (v A), nuclearNorm_eq_sum_range A (by simpa using A.rank_le_card_width),
    ← Fin.sum_univ_eq_sum_range (σ A) n]
  refine Finset.sum_le_sum fun i _ => (real_inner_le_norm _ _).trans ?_
  rw [norm_singular_image]
  exact mul_le_of_le_one_left ((lin A).singularValues_nonneg i)
    ((hL _).trans_eq ((v A).norm_eq_one i))

private theorem weighted_norm_sq (A : M[m,n]) (w : Fin n → ℝ) (x : E[n]) :
    ‖weighted A w x‖ ^ 2 = ∑ i, (⟪v A i, x⟫ * w i * σ A i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, weighted_apply]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, singular_inner,
    OrthonormalBasis.inner_eq_ite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_eq_single i]
  · simp
    ring
  · intro j h
    simp [h]

/-- Normalize the nonzero images of the right singular vectors to attain the trace bound. -/
private theorem exists_pairing_eq_nuclearNorm (A : M[m,n]) :
    ∃ L : E[n] →ₗ[ℝ] E[m], (∀ x, ‖L x‖ ≤ ‖x‖) ∧ (lin A).ker ≤ L.ker ∧
      L.range ≤ (lin A).range ∧ pairing L (lin A) = nuclearNorm A := by
  let w : Fin n → ℝ := fun i => (σ A i)⁻¹
  refine ⟨weighted A w, ?_, le_weighted_ker A w, weighted_range_le A w, ?_⟩
  · intro x
    apply le_of_sq_le_sq _ (norm_nonneg x)
    rw [weighted_norm_sq, ← (v A).sum_sq_norm_inner_right]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    by_cases hi : σ A i = 0
    · simpa [hi] using (sq_nonneg ⟪v A i, x⟫)
    · simp [w, hi]
  · rw [pairing_eq_sum _ _ (v A), nuclearNorm_eq_sum_range A (by simpa using A.rank_le_card_width),
      ← Fin.sum_univ_eq_sum_range (σ A) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weighted_basis, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_singular_image]
    by_cases hi : σ A i = 0
    · simp [hi]
    · simp [w, pow_two, hi]

private theorem frobenius_sq_eq_pairing (A : M[m,n]) : ‖A‖ ^ 2 = pairing (lin A) (lin A) := by
  rw [pairing_eq_sum _ _ (EuclideanSpace.basisFun (Fin n) ℝ), ← frobSq_eq_norm_sq, frobSq,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply]


/-- Orthogonal row and column spaces allow the two maximizing contractions to be added. -/
private theorem exists_pairing_eq_nuclearNorm_add (A C : M[m,n])
    (hRange : (lin C).range ≤ (lin A).rangeᗮ) (hKer : (lin A).kerᗮ ≤ (lin C).ker) :
    ∃ L : E[n] →ₗ[ℝ] E[m], (∀ x, ‖L x‖ ≤ ‖x‖) ∧
      pairing L (lin A + lin C) = nuclearNorm A + nuclearNorm C := by
  obtain ⟨L, hL, hLker, hLrange, hLA⟩ := exists_pairing_eq_nuclearNorm A
  obtain ⟨K, hK, hKker, hKrange, hKC⟩ := exists_pairing_eq_nuclearNorm C
  have hOrth : K.range ≤ L.rangeᗮ :=
    hKrange.trans (hRange.trans (Submodule.orthogonal_le hLrange))
  refine ⟨L + K, ?_, ?_⟩
  · intro x
    let U := (lin A).ker
    let x₁ := Uᗮ.starProjection x
    let x₂ := U.starProjection x
    have hx₁ : x₁ ∈ Uᗮ := Submodule.starProjection_apply_mem _ _
    have hx₂ : x₂ ∈ U := Submodule.starProjection_apply_mem _ _
    have hx : x₂ + x₁ = x := Submodule.starProjection_add_starProjection_orthogonal x
    have hL₂ : L x₂ = 0 := LinearMap.mem_ker.mp (hLker hx₂)
    have hK₁ : K x₁ = 0 := LinearMap.mem_ker.mp (hKker (hKer hx₁))
    have hOut : ⟪L x₁, K x₂⟫ = 0 :=
      (L.range.mem_orthogonal _).mp (hOrth (LinearMap.mem_range_self _ _)) _
        (LinearMap.mem_range_self _ _)
    have hIn : ⟪x₂, x₁⟫ = 0 := (U.mem_orthogonal _).mp hx₁ _ hx₂
    have hSum : (L + K) x = L x₁ + K x₂ := by
      simp [← hx, map_add, hL₂, hK₁, add_comm]
    apply le_of_sq_le_sq _ (norm_nonneg x)
    have hInSq : ‖x‖ ^ 2 = ‖x₂‖ ^ 2 + ‖x₁‖ ^ 2 := by
      rw [← hx, norm_add_sq_real, hIn, mul_zero, add_zero]
    rw [hSum, norm_add_sq_real, hOut, mul_zero, add_zero, hInSq]
    have h₁ := pow_le_pow_left₀ (norm_nonneg _) (hL x₁) 2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (hK x₂) 2
    linarith
  · have hLC : (lin C).range ≤ L.rangeᗮ := hRange.trans (Submodule.orthogonal_le hLrange)
    have hKA : (lin A).range ≤ K.rangeᗮ :=
      (lin A).range.le_orthogonal_orthogonal.trans
        (Submodule.orthogonal_le (hKrange.trans hRange))
    rw [pairing_add_right, pairing_add_left, pairing_add_left, hLA, hKC,
      pairing_eq_zero_of_range_le_orthogonal K _ hKA,
      pairing_eq_zero_of_range_le_orthogonal L _ hLC, add_zero, zero_add]

private theorem neg_pairing_le_nuclearNorm (B : M[m,n]) (L : E[n] →ₗ[ℝ] E[m])
    (hL : ∀ x, ‖L x‖ ≤ ‖x‖) : -pairing L (lin B) ≤ nuclearNorm B := by
  have h := pairing_le_nuclearNorm B (-L) (fun x => by simpa using hL x)
  simpa only [pairing_eq_sum _ _ (v B), LinearMap.neg_apply, inner_neg_left,
    Finset.sum_neg_distrib] using h

/-- Split a perturbation using the kernel and range projections of the reference matrix. -/
private theorem exists_orthogonal_split (A H : M[m,n]) :
    ∃ B C : M[m,n], H = B + C ∧ B.rank ≤ 2 * A.rank ∧
      (lin C).range ≤ (lin A).rangeᗮ ∧ (lin A).kerᗮ ≤ (lin C).ker ∧
      ∀ x ∈ (lin A).ker, lin B x ∈ (lin A).range := by
  let U := (lin A).range
  let V := (lin A).ker
  let P := U.starProjection.toLinearMap
  let P' := Uᗮ.starProjection.toLinearMap
  let Q := V.starProjection.toLinearMap
  let Q' := Vᗮ.starProjection.toLinearMap
  let B₁ := P ∘ₗ lin H
  let B₂ := P' ∘ₗ lin H ∘ₗ Q'
  let C := P' ∘ₗ lin H ∘ₗ Q
  refine ⟨Matrix.toEuclideanLin.symm B₁ + Matrix.toEuclideanLin.symm B₂,
    Matrix.toEuclideanLin.symm C, ?_, ?_, ?_, ?_, ?_⟩
  · apply Matrix.toEuclideanLin.injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    ext1 x
    change lin H x = U.starProjection (lin H x) +
      Uᗮ.starProjection (lin H (Vᗮ.starProjection x)) +
      Uᗮ.starProjection (lin H (V.starProjection x))
    rw [add_assoc, ← map_add, ← map_add, add_comm (Vᗮ.starProjection x),
      Submodule.starProjection_add_starProjection_orthogonal,
      Submodule.starProjection_add_starProjection_orthogonal]
  · have h₁ : (Matrix.toEuclideanLin.symm B₁ : M[m,n]).rank ≤ A.rank := by
      rw [rank_eq_finrank_range, LinearEquiv.apply_symm_apply, rank_eq_finrank_range]
      apply Submodule.finrank_mono
      rintro _ ⟨x, rfl⟩
      exact U.starProjection_apply_mem _
    have h₂ : (Matrix.toEuclideanLin.symm B₂ : M[m,n]).rank ≤ A.rank := by
      rw [rank_eq_finrank_range, LinearEquiv.apply_symm_apply, rank_eq_finrank_range]
      change finrank ℝ (P'.comp ((lin H).comp Q')).range ≤ finrank ℝ U
      calc
        _ ≤ finrank ℝ ((lin H).comp Q').range := by
          rw [LinearMap.range_comp]
          exact Submodule.finrank_map_le _ _
        _ ≤ finrank ℝ Q'.range := by
          rw [LinearMap.range_comp]
          exact Submodule.finrank_map_le _ _
        _ = finrank ℝ U := by
          change finrank ℝ Vᗮ.starProjection.range = _
          rw [Submodule.range_starProjection, LinearMap.orthogonal_ker,
            LinearMap.finrank_range_adjoint]
    exact (Matrix.rank_add_le _ _).trans (by omega)
  · rw [LinearEquiv.apply_symm_apply]
    rintro _ ⟨x, rfl⟩
    exact Uᗮ.starProjection_apply_mem _
  · rw [LinearEquiv.apply_symm_apply]
    intro x hx
    have hQ : Q x = 0 := (V.starProjection_apply_eq_zero_iff).mpr hx
    simp [C, LinearMap.mem_ker, hQ]
  · intro x hx
    have hQ' : Q' x = 0 := by
      change Vᗮ.starProjection x = 0
      rw [Submodule.starProjection_orthogonal_val, (V.starProjection_eq_self_iff).mpr hx,
        sub_self]
    have hb₂ : B₂ x = 0 := by simp [B₂, hQ']
    simp only [map_add, LinearEquiv.apply_symm_apply, LinearMap.add_apply, hb₂, add_zero]
    exact U.starProjection_apply_mem (lin H x)

/-- Selecting right singular vectors preserves the orthogonality of the split. -/
private theorem norm_le_norm_add_weighted (A B C : M[m,n])
    (hRange : (lin C).range ≤ (lin A).rangeᗮ) (hKer : (lin A).kerᗮ ≤ (lin C).ker)
    (hB : ∀ x ∈ (lin A).ker, lin B x ∈ (lin A).range) (w : Fin n → ℝ) :
    ‖B‖ ≤ ‖B + Matrix.toEuclideanLin.symm (weighted C w)‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  simp only [frobenius_sq_eq_pairing, pairing_eq_sum _ _ (v C), real_inner_self_eq_norm_sq,
    map_add, LinearEquiv.apply_symm_apply, LinearMap.add_apply, weighted_basis]
  refine Finset.sum_le_sum fun i _ => ?_
  have hInner : ⟪lin B (v C i), lin C (v C i)⟫ = 0 := by
    by_cases hi : σ C i = 0
    · rw [norm_eq_zero.mp ((norm_singular_image C i).trans hi), inner_zero_right]
    · have hiKer : v C i ∈ (lin C).kerᗮ := by
        apply ((lin C).ker.mem_orthogonal' _).mpr
        intro x hx
        have h := singular_inner C i x
        rw [LinearMap.mem_ker.mp hx, inner_zero_right] at h
        exact (zero_eq_mul.mp h).resolve_left (pow_ne_zero _ hi)
      have hiA : v C i ∈ (lin A).ker := by
        simpa using Submodule.orthogonal_le hKer hiKer
      exact ((lin A).range.mem_orthogonal _).mp (hRange (LinearMap.mem_range_self _ _)) _
        (hB _ hiA)
  rw [norm_add_sq_real, real_inner_smul_right, hInner, mul_zero, mul_zero, add_zero]
  exact le_add_of_nonneg_right (sq_nonneg _)


/-- Keep the singular components whose zero-based indices lie in `s`. -/
private noncomputable def singularBlock (A : M[m,n]) (s : Finset ℕ) : M[m,n] :=
  Matrix.toEuclideanLin.symm (weighted A fun i => if i.val ∈ s then 1 else 0)

private theorem singularBlock_basis (A : M[m,n]) (s : Finset ℕ) (i : Fin n) :
    lin (singularBlock A s) (v A i) = if i.val ∈ s then lin A (v A i) else 0 := by
  rw [singularBlock, LinearEquiv.apply_symm_apply, weighted_basis]
  split_ifs <;> simp

private theorem singularBlock_rank_le (A : M[m,n]) (s : Finset ℕ) :
    (singularBlock A s).rank ≤ s.card := by
  let selected := Finset.univ.filter fun i : Fin n => i.val ∈ s
  let component (i : Fin n) : M[m,n] := Matrix.toEuclideanLin.symm
    (rankOne ℝ (lin A (v A i)) (v A i)).toLinearMap
  have hsum : singularBlock A s = ∑ i ∈ selected, component i := by
    apply Matrix.toEuclideanLin.injective
    ext1 x
    simp only [singularBlock, LinearEquiv.apply_symm_apply, weighted_apply, map_sum,
      LinearMap.sum_apply, selected, Finset.sum_filter, component]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hsum]
  refine (Matrix.rank_sum_le_card _ _ ?_).trans ?_
  · intro i _
    dsimp only [component]
    rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
    exact Matrix.rank_vecMulVec_le _ _
  · refine Finset.card_le_card_of_injOn Fin.val ?_ Fin.val_injective.injOn
    intro i hi
    exact (Finset.mem_filter.mp hi).2

private theorem singularBlock_norm_sq (A : M[m,n]) (s : Finset ℕ) :
    ‖singularBlock A s‖ ^ 2 = ∑ i ∈ s, (σ A i) ^ 2 := by
  simp only [frobenius_sq_eq_pairing, pairing_eq_sum _ _ (v A), real_inner_self_eq_norm_sq,
    singularBlock_basis]
  calc
    _ = ∑ i : Fin n, if i.val ∈ s then (σ A i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp [norm_singular_image]
    _ = ∑ i ∈ (Finset.range n).filter (· ∈ s), (σ A i) ^ 2 := by
      rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
    _ = _ := by
      refine Finset.sum_subset (fun i hi => (Finset.mem_filter.mp hi).2) fun i hi hnot => ?_
      have hn : n ≤ i := by
        simpa [Finset.mem_filter, Finset.mem_range, hi] using hnot
      change ((lin A).singularValues i) ^ 2 = 0
      rw [(lin A).singularValues_of_finrank_le (by simpa using hn), zero_pow (by decide)]

private theorem singularBlock_split (A : M[m,n]) {a b : ℕ} (hab : a ≤ b) :
    singularBlock A (Finset.Ico a n) =
      singularBlock A (Finset.Ico a b) + singularBlock A (Finset.Ico b n) := by
  apply Matrix.toEuclideanLin.injective
  apply (v A).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, map_add, LinearMap.add_apply, singularBlock_basis,
    Finset.mem_Ico]
  have hi := i.isLt
  split_ifs <;> first | omega | simp

private theorem singularBlock_zero_start (A : M[m,n]) :
    singularBlock A (Finset.Ico 0 n) = A := by
  apply Matrix.toEuclideanLin.injective
  apply (v A).toBasis.ext
  intro i
  simp [singularBlock_basis, i.isLt]

private theorem singularBlock_eq_zero (A : M[m,n]) {a : ℕ} (ha : n ≤ a) :
    singularBlock A (Finset.Ico a n) = 0 := by
  apply Matrix.toEuclideanLin.injective
  apply (v A).toBasis.ext
  intro i
  simp [singularBlock_basis, Finset.Ico_eq_empty_of_le ha]

private theorem nuclearNorm_eq_sum_Ico (A : M[m,n]) :
    nuclearNorm A = ∑ i ∈ Finset.Ico 0 n, σ A i := by
  rw [Nat.Ico_zero_eq_range]
  exact nuclearNorm_eq_sum_range A (by simpa using A.rank_le_card_width)

private theorem norm_le_nuclearNorm (A : M[m,n]) : ‖A‖ ≤ nuclearNorm A := by
  apply le_of_sq_le_sq _ (nuclearNorm_nonneg A)
  rw [← singularBlock_zero_start A, singularBlock_norm_sq]
  rw [singularBlock_zero_start, nuclearNorm_eq_sum_Ico]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => (lin A).singularValues_nonneg i

private theorem nuclearNorm_le_sqrt_mul_norm (A : M[m,n]) {k : ℕ} (hk : A.rank ≤ k) :
    nuclearNorm A ≤ √(k : ℝ) * ‖A‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  have hs : (σ A).support ⊆ Finset.range k := by
    rw [singularSeq, LinearMap.support_singularValues, ← rank_eq_finrank_range]
    exact Finset.range_mono hk
  have hnorm : ‖A‖ ^ 2 = ∑ i ∈ Finset.range k, (σ A i) ^ 2 := by
    rw [← frobSq_eq_norm_sq, frobSq_eq_sum_sq_singularSeq, Finsupp.sum]
    exact Finset.sum_subset hs fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi]; norm_num
  rw [nuclearNorm_eq_sum_range A hk, mul_pow, Real.sq_sqrt (by positivity), hnorm]
  simpa [mul_comm] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k) (fun _ => (1 : ℝ)) (σ A)


/-- The Frobenius norm of a block is bounded by the preceding block's singular-value sum,
divided by the square root of the block size. -/
private theorem norm_block_le_previous (C : M[m,n]) {k a : ℕ} (hk : 0 < k) (ha : k ≤ a) :
    ‖singularBlock C (Finset.Ico a (a + k))‖ ≤
      (∑ i ∈ Finset.Ico (a - k) a, σ C i) / √(k : ℝ) := by
  have hs : 0 < √(k : ℝ) := by positivity
  have hblock : ‖singularBlock C (Finset.Ico a (a + k))‖ ≤ √(k : ℝ) * σ C a := by
    apply le_of_sq_le_sq _ (mul_nonneg hs.le ((lin C).singularValues_nonneg _))
    rw [singularBlock_norm_sq, mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ∑ _i ∈ Finset.Ico a (a + k), (σ C a) ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact pow_le_pow_left₀ ((lin C).singularValues_nonneg _)
          ((lin C).singularValues_antitone (Finset.mem_Ico.mp hi).1) 2
      _ = _ := by simp [singularSeq]
  refine hblock.trans ((le_div_iff₀ hs).2 ?_)
  calc
    √(k : ℝ) * σ C a * √(k : ℝ) = (k : ℝ) * σ C a := by
      rw [show √(k : ℝ) * σ C a * √(k : ℝ) = (√(k : ℝ)) ^ 2 * σ C a by ring,
        Real.sq_sqrt (by positivity)]
    _ = ∑ _i ∈ Finset.Ico (a - k) a, σ C a := by
      simp [show a - (a - k) = k by omega]
    _ ≤ _ := Finset.sum_le_sum fun i hi =>
      (lin C).singularValues_antitone (Finset.mem_Ico.mp hi).2.le

/-- Peel off consecutive blocks, charging each one's norm to the preceding block. -/
private theorem norm_map_tail_le {p k : ℕ} (𝒜 : M[m,n] →ₗ[ℝ] E[p]) (C : M[m,n])
    (hk : 0 < k) {b : ℝ} (hb : 0 ≤ b) (hupper : ∀ Y : M[m,n], Y.rank ≤ k → ‖𝒜 Y‖ ≤ b * ‖Y‖)
    (a : ℕ) (ha : k ≤ a) :
    ‖𝒜 (singularBlock C (Finset.Ico a n))‖ ≤
      (b / √(k : ℝ)) * ∑ i ∈ Finset.Ico (a - k) n, σ C i := by
  by_cases h : n ≤ a
  · rw [singularBlock_eq_zero C h, map_zero, norm_zero]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => (lin C).singularValues_nonneg i)
  rw [singularBlock_split C (Nat.le_add_right a k), map_add]
  have hRank : (singularBlock C (Finset.Ico a (a + k))).rank ≤ k := by
    simpa using singularBlock_rank_le C (Finset.Ico a (a + k))
  have hTail := norm_map_tail_le 𝒜 C hk hb hupper (a + k) (by omega)
  rw [Nat.add_sub_cancel] at hTail
  calc
    _ ≤ ‖𝒜 (singularBlock C (Finset.Ico a (a + k)))‖ +
        ‖𝒜 (singularBlock C (Finset.Ico (a + k) n))‖ := norm_add_le _ _
    _ ≤ b * ((∑ i ∈ Finset.Ico (a - k) a, σ C i) / √(k : ℝ)) +
        (b / √(k : ℝ)) * ∑ i ∈ Finset.Ico a n, σ C i :=
      add_le_add ((hupper _ hRank).trans
        (mul_le_mul_of_nonneg_left (norm_block_le_previous C hk ha) hb)) hTail
    _ = (b / √(k : ℝ)) * ((∑ i ∈ Finset.Ico (a - k) a, σ C i) +
          ∑ i ∈ Finset.Ico a n, σ C i) := by ring
    _ = _ := by rw [Finset.sum_Ico_consecutive (σ C) (Nat.sub_le a k) (by omega)]
termination_by n - a
decreasing_by omega

/-- **Exact recovery by nuclear norm minimization under restricted isometry.** Let `r ≥ 1` and let
`𝒜` be a linear map from real `m × n` matrices to `ℝ^p` that is a restricted isometry of order
`5 r` with a constant `δ < 1/10` (that is, `δ_{5r}(𝒜) < 1/10`). Let `X₀` have rank at most `r`.
Then `X₀` is the unique minimizer of the nuclear norm over `{X : 𝒜(X) = 𝒜(X₀)}`: every other
matrix `X` with `𝒜(X) = 𝒜(X₀)` has `‖X₀‖_* < ‖X‖_*`.

Source: B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear
matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), arXiv:0706.4138,
Theorem 3.3 ("`X_* = X₀`", with `X_*` the nuclear-norm minimizer (3.1) and `X₀` of rank `r`;
rank at most `r` follows, since `δ_{5r'} ≤ δ_{5r}` for `r' ≤ r` and the case `X₀ = 0` is
immediate). -/
theorem nuclearNorm_lt_of_isRestrictedIsometry_five_mul {m n p : ℕ}
    {𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)} {r : ℕ} (hr : 1 ≤ r)
    {δ : ℝ} (hRIP : IsRestrictedIsometry 𝒜 (5 * r) δ) (hδ : δ < 1 / 10)
    {X₀ : Matrix (Fin m) (Fin n) ℝ} (hX₀ : X₀.rank ≤ r) (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : 𝒜 X = 𝒜 X₀) (hne : X ≠ X₀) :
    nuclearNorm X₀ < nuclearNorm X := by
  by_contra! hle
  let H := X - X₀
  have hH : 𝒜 H = 0 := by simp [H, hX]
  obtain ⟨B, C, hSplit, hRank, hRange, hKer, hB⟩ := exists_orthogonal_split X₀ H
  -- Optimality would force the orthogonal part to have the smaller nuclear norm.
  obtain ⟨L, hL, hPair⟩ := exists_pairing_eq_nuclearNorm_add X₀ C hRange hKer
  have hXEq : X = (X₀ + C) + B := by
    calc
      X = X₀ + H := by simp [H]
      _ = _ := by rw [hSplit]; abel
  have hEval : pairing L (lin X) = nuclearNorm X₀ + nuclearNorm C + pairing L (lin B) := by
    conv_lhs => rw [hXEq]
    rw [map_add, map_add, pairing_add_right, hPair]
  have hPairX := pairing_le_nuclearNorm X L hL
  have hPairB := neg_pairing_le_nuclearNorm B L hL
  rw [hEval] at hPairX
  have hCB : nuclearNorm C ≤ nuclearNorm B := by linarith
  have hBpos : 0 < ‖B‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hCzero : C = 0 := by
      have hc : nuclearNorm C ≤ 0 := by simpa [he, nuclearNorm] using hCB
      exact norm_eq_zero.mp (le_antisymm ((norm_le_nuclearNorm C).trans hc) (norm_nonneg _))
    exact hne (sub_eq_zero.mp (by simpa [H, he, hCzero] using hSplit))
  have hRankB : B.rank ≤ 2 * r := hRank.trans (Nat.mul_le_mul_left _ hX₀)
  -- The first block can be added to B while staying within the restricted isometry order.
  let D := singularBlock C (Finset.Ico 0 (3 * r))
  let T := singularBlock C (Finset.Ico (3 * r) n)
  have hCT : C = D + T :=
    (singularBlock_zero_start C).symm.trans (singularBlock_split C (Nat.zero_le _))
  have hDT : 𝒜 (B + D) = -𝒜 T := by
    rw [hSplit, hCT, ← add_assoc, map_add] at hH
    exact eq_neg_of_add_eq_zero_left hH
  have hRankD : D.rank ≤ 3 * r := by
    simpa [D] using singularBlock_rank_le C (Finset.Ico 0 (3 * r))
  have hRankBD : (B + D).rank ≤ 5 * r :=
    (Matrix.rank_add_le _ _).trans (by omega)
  have hBD : ‖B‖ ≤ ‖B + D‖ := norm_le_norm_add_weighted X₀ B C hRange hKer hB _
  have hLower : (9 / 10 : ℝ) * ‖B‖ < ‖𝒜 (B + D)‖ :=
    (mul_lt_mul_of_pos_right (by linarith : (9 / 10 : ℝ) < 1 - δ) hBpos).trans_le
      ((mul_le_mul_of_nonneg_left hBD (by linarith)).trans (hRIP _ hRankBD).1)
  have hk : 0 < 3 * r := by omega
  have hs : 0 < √((3 * r : ℕ) : ℝ) := by positivity
  have hUpper (Y : M[m,n]) (hY : Y.rank ≤ 3 * r) : ‖𝒜 Y‖ ≤ (11 / 10 : ℝ) * ‖Y‖ :=
    (hRIP Y (hY.trans (by omega))).2.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hTail := norm_map_tail_le 𝒜 C hk (by norm_num) hUpper (3 * r) le_rfl
  rw [Nat.sub_self, ← nuclearNorm_eq_sum_Ico] at hTail
  have hRatio : √((2 * r : ℕ) : ℝ) ≤ (9 / 11 : ℝ) * √((3 * r : ℕ) : ℝ) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hr' : 0 ≤ (r : ℝ) := by positivity
    push_cast
    nlinarith
  have hCoeff : (11 / 10 : ℝ) / √((3 * r : ℕ) : ℝ) * √((2 * r : ℕ) : ℝ) ≤ 9 / 10 :=
    (mul_le_mul_of_nonneg_left hRatio (by positivity)).trans_eq (by field_simp [hs.ne'])
  apply hLower.not_ge
  calc
    ‖𝒜 (B + D)‖ = ‖𝒜 T‖ := by rw [hDT, norm_neg]
    _ ≤ (11 / 10 : ℝ) / √((3 * r : ℕ) : ℝ) * nuclearNorm C := hTail
    _ ≤ (11 / 10 : ℝ) / √((3 * r : ℕ) : ℝ) * (√((2 * r : ℕ) : ℝ) * ‖B‖) :=
      mul_le_mul_of_nonneg_left (hCB.trans (nuclearNorm_le_sqrt_mul_norm B hRankB))
        (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)

end MathlibExt.LinearAlgebra.NuclearNormRecoveryWanted

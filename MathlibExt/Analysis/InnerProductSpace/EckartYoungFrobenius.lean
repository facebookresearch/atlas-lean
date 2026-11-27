/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import MathlibExt.LinearAlgebra.Matrix.RankAddGeneral

/-!
# Eckart–Young in the Frobenius norm

For a real matrix `A` with singular values `σ₀ ≥ σ₁ ≥ ⋯` (Mathlib's
`LinearMap.singularValues` of `Matrix.toEuclideanLin A`), the best rank-`k`
approximation in the Frobenius norm is the truncated singular value
decomposition `truncSVD A k`, and the minimal squared error is the tail sum
`∑_{i ≥ k} σᵢ²` (C. Eckart and G. Young, "The approximation of one matrix by
another of lower rank", Psychometrika 1 (1936), 211–218).

Two forms are given: with Mathlib's scoped Frobenius norm (`truncSVD` and
`sum_sq_singularValues_le_frobenius_sub_sq`; this core implementation is
shared with principal component analysis, which imports it from here), and
with the elementary squared Frobenius norm `frobSq A = ∑ i j, (A i j)²`
(`singularTailSq_le_frobSq_sub`, `isLeast_frobSq_sub`, and the two-sided
whitening form `isLeast_frobSq_whitened` used by weighted rank tests).

## Main results

* `Matrix.EckartYoungFrobenius.truncSVD`, `rank_truncSVD_le`,
  `frobenius_sub_truncSVD_sq`: the truncated SVD and its exact error.
* `Matrix.EckartYoungFrobenius.sum_sq_singularValues_le_frobenius_sub_sq`:
  the lower bound for every rank-`≤ k` approximant.
* `Matrix.EckartYoungFrobenius.isLeast_frobSq_sub`: the singular tail is the
  minimum squared Frobenius error.
* `Matrix.EckartYoungFrobenius.isLeast_frobSq_whitened`: the whitened form.
-/


@[expose] public section

namespace Matrix.EckartYoungFrobenius

open scoped Matrix.Norms.Frobenius

variable {m n : ℕ}

/-- Right singular vectors of `A`: an orthonormal eigenbasis of `Aᵀ A`, ordered so that the
`i`-th vector has eigenvalue `σᵢ²` with `σ₀ ≥ σ₁ ≥ ⋯` the singular values. -/
noncomputable def rightSingularBasis (A : Matrix (Fin m) (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis
    finrank_euclideanSpace_fin

/-- The rank-`k` truncated singular value decomposition `A Vₖ Vₖᵀ = ∑_{i<k} σᵢ uᵢ vᵢᵀ`,
where `Vₖ` collects the first `k` right singular vectors. -/
noncomputable def truncSVD (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  A * ∑ i : Fin n with i.val < k,
    vecMulVec ⇑(rightSingularBasis A i) ⇑(rightSingularBasis A i)

/-- A sum of matrices of rank at most one has rank at most the number of summands. -/
private theorem rank_sum_bound {a b : ℕ} {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Fin a) (Fin b) ℝ) (h : ∀ i ∈ s, (M i).rank ≤ 1) :
    (∑ i ∈ s, M i).rank ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    exact (Matrix.rank_add_le _ _).trans
      (by have := h i (Finset.mem_insert_self i s)
          have := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
          omega)

/-- The squared Frobenius norm is the sum of the squared entries. -/
private theorem frobenius_sq_entries {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    ‖M‖ ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The squared Frobenius norm is `∑ⱼ ‖M uⱼ‖²` over any orthonormal basis `u`. -/
private theorem frobenius_sq_basis {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (u : OrthonormalBasis (Fin b) ℝ (EuclideanSpace ℝ (Fin b))) :
    ‖M‖ ^ 2 = ∑ j, ‖Matrix.toEuclideanLin M (u j)‖ ^ 2 := by
  classical
  let T := Matrix.toEuclideanLin M
  have ht (v : OrthonormalBasis (Fin b) ℝ (EuclideanSpace ℝ (Fin b))) :
      (T.adjoint ∘ₗ T).trace ℝ _ = ∑ j, ‖T (v j)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ v]
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [← ht u, ht (EuclideanSpace.basisFun (Fin b) ℝ), frobenius_sq_entries]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp [T, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply]

/-- The outer product `u vᵀ` maps `x` to `⟪v, x⟫ u`. -/
private theorem outer_action {b : ℕ} (u v x : EuclideanSpace ℝ (Fin b)) :
    Matrix.toEuclideanLin (vecMulVec ⇑u ⇑v) x = (inner ℝ v x) • u := by
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
    PiLp.inner_apply, Finset.mul_sum, mul_assoc, mul_comm]

/-- The truncated SVD agrees with `A` on the first `k` right singular vectors and kills the
others. -/
private theorem trunc_action {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (k : ℕ) (j : Fin b) :
    Matrix.toEuclideanLin (truncSVD A k) (rightSingularBasis A j) =
      if j.val < k then Matrix.toEuclideanLin A (rightSingularBasis A j) else 0 := by
  classical
  have hp :
      Matrix.toEuclideanLin (∑ i : Fin b with i.val < k,
        vecMulVec ⇑(rightSingularBasis A i) ⇑(rightSingularBasis A i))
        (rightSingularBasis A j) =
          if j.val < k then rightSingularBasis A j else 0 := by
    simp only [map_sum, LinearMap.sum_apply, outer_action,
      OrthonormalBasis.inner_eq_ite, ite_smul, one_smul, zero_smul]
    simp
  simp only [truncSVD, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply]
  rw [hp]
  split_ifs <;> simp

/-- `‖A vⱼ‖² = σⱼ²` for the right singular vectors. -/
private theorem singular_energy {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (j : Fin b) :
    ‖Matrix.toEuclideanLin A (rightSingularBasis A j)‖ ^ 2 =
      (Matrix.toEuclideanLin A).singularValues j ^ 2 := by
  rw [(Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin]
  rw [← real_inner_self_eq_norm_sq,
    ← LinearMap.adjoint_inner_left (Matrix.toEuclideanLin A)]
  change inner ℝ (((Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A)
    (rightSingularBasis A j)) (rightSingularBasis A j) = _
  rw [rightSingularBasis, LinearMap.IsSymmetric.apply_eigenvectorBasis]
  simp [inner_smul_left]

/-- A tail sum over `Fin b` as a sum over `Finset.Ico k b`. -/
private theorem fin_tail_sum (b k : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin b with k ≤ i.val, f i.val) = ∑ i ∈ Finset.Ico k b, f i := by
  classical
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro j hj
    refine ⟨⟨j, (Finset.mem_Ico.mp hj).2⟩, ?_, rfl⟩
    simp [(Finset.mem_Ico.mp hj).1]
  · intro i _
    rfl

/-- `∑ⱼ ‖T wⱼ‖²` through the adjoint and the standard basis. -/
private theorem energy_adjoint {a b r : ℕ}
    (T : EuclideanSpace ℝ (Fin b) →ₗ[ℝ] EuclideanSpace ℝ (Fin a))
    (w : Fin r → EuclideanSpace ℝ (Fin b)) :
    (∑ j, ‖T (w j)‖ ^ 2) =
      ∑ i, ∑ j, (inner ℝ (w j) (T.adjoint (EuclideanSpace.basisFun (Fin a) ℝ i))) ^ 2 := by
  calc
    _ = ∑ j, ∑ i, (inner ℝ (w j)
        (T.adjoint (EuclideanSpace.basisFun (Fin a) ℝ i))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← (EuclideanSpace.basisFun (Fin a) ℝ).sum_sq_inner_right]
      apply Finset.sum_congr rfl
      intro i _
      rw [← T.adjoint_inner_left, real_inner_comm]
    _ = _ := Finset.sum_comm

/-- Bessel: `∑ⱼ ‖M wⱼ‖² ≤ ‖M‖²` for an orthonormal family `w`. -/
private theorem orthonormal_energy_le {a b r : ℕ} (M : Matrix (Fin a) (Fin b) ℝ)
    (w : Fin r → EuclideanSpace ℝ (Fin b)) (hw : Orthonormal ℝ w) :
    (∑ j, ‖Matrix.toEuclideanLin M (w j)‖ ^ 2) ≤ ‖M‖ ^ 2 := by
  rw [energy_adjoint]
  calc
    _ ≤ ∑ i, ‖(Matrix.toEuclideanLin M).adjoint
        (EuclideanSpace.basisFun (Fin a) ℝ i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa using hw.sum_inner_products_le
        ((Matrix.toEuclideanLin M).adjoint (EuclideanSpace.basisFun (Fin a) ℝ i))
    _ = ∑ j, ‖Matrix.toEuclideanLin M (EuclideanSpace.basisFun (Fin b) ℝ j)‖ ^ 2 := by
      conv_rhs => rw [energy_adjoint]
      simp only [OrthonormalBasis.sum_sq_inner_right]
    _ = ‖M‖ ^ 2 := (frobenius_sq_basis M (EuclideanSpace.basisFun (Fin b) ℝ)).symm

/-- `‖A x‖² = ∑ᵢ σᵢ² ⟪vᵢ, x⟫²` in the right singular basis. -/
private theorem spectral_energy {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (x : EuclideanSpace ℝ (Fin b)) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 =
      ∑ i : Fin b, (Matrix.toEuclideanLin A).singularValues i ^ 2 *
        (inner ℝ (rightSingularBasis A i) x) ^ 2 := by
  let T := Matrix.toEuclideanLin A
  let v := rightSingularBasis A
  have h : (T.adjoint ∘ₗ T) x =
      ∑ i, (inner ℝ (v i) x) • (T.adjoint ∘ₗ T) (v i) := by
    simpa only [map_sum, map_smul] using
      congrArg (T.adjoint ∘ₗ T) (v.sum_repr' x).symm
  have hn : ‖T x‖ ^ 2 = inner ℝ ((T.adjoint ∘ₗ T) x) x := by
    rw [LinearMap.comp_apply, T.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [hn, h, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_left]
  change _ * inner ℝ ((T.adjoint ∘ₗ T)
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin i)) x = _
  rw [LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_left,
    ← T.sq_singularValues_fin finrank_euclideanSpace_fin]
  simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id_eq]
  change inner ℝ (v i) x * (T.singularValues i ^ 2 * inner ℝ (v i) x) =
    T.singularValues i ^ 2 * (inner ℝ (v i) x) ^ 2
  ring

/-- For decreasing nonnegative `d` and weights `cᵢ ∈ [0, 1]` of total at least `b - k`,
`∑_{i ≥ k} dᵢ ≤ ∑ dᵢ cᵢ`. -/
private theorem weighted_tail_le {b : ℕ} (k : ℕ) (hk : k < b)
    (d c : Fin b → ℝ) (hd : Antitone d) (hd0 : ∀ i, 0 ≤ d i)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hc : (b - k : ℕ) ≤ ∑ i, c i) :
    (∑ i : Fin b with k ≤ i.val, d i) ≤ ∑ i, d i * c i := by
  classical
  let t : ℝ := d ⟨k, hk⟩
  have hcount : (∑ i : Fin b, if k ≤ i.val then (1 : ℝ) else 0) = (b - k : ℕ) := by
    rw [← Finset.sum_filter]
    exact (fin_tail_sum b k (fun _ => 1)).trans (by simp)
  have hi (i : Fin b) :
      t * (c i - if k ≤ i.val then 1 else 0) ≤
        d i * c i - if k ≤ i.val then d i else 0 := by
    by_cases h : k ≤ i.val
    · have horder : d i ≤ t := hd h
      have := mul_le_mul_of_nonpos_right horder (sub_nonpos.mpr (hc1 i))
      simp only [ite_eq_left h]
      nlinarith
    · have horder : t ≤ d i := hd (show i ≤ ⟨k, hk⟩ from Nat.le_of_lt (Nat.lt_of_not_ge h))
      simpa [h] using mul_le_mul_of_nonneg_right horder (hc0 i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [hcount, ← Finset.sum_filter] at hs
  have ht : 0 ≤ t := hd0 ⟨k, hk⟩
  have := mul_nonneg ht (sub_nonneg.mpr hc)
  linarith

/-- The truncated SVD has rank at most `k`. -/
theorem rank_truncSVD_le (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : (truncSVD A k).rank ≤ k := by
  classical
  unfold truncSVD
  refine (Matrix.rank_mul_le_right _ _).trans ((rank_sum_bound _ _ ?_).trans ?_)
  · intro i _
    exact Matrix.rank_vecMulVec_le _ _
  · calc
      (Finset.univ.filter fun i : Fin n => i.val < k).card ≤ (Finset.range k).card :=
        Finset.card_le_card_of_injOn Fin.val
          (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
          (fun i _ j _ hij => Fin.ext hij)
      _ = k := Finset.card_range k

/-- The squared Frobenius error of the truncated SVD is the sum of the discarded squared
singular values. -/
theorem frobenius_sub_truncSVD_sq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    ‖A - truncSVD A k‖ ^ 2 =
      ∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2 := by
  classical
  rw [frobenius_sq_basis _ (rightSingularBasis A)]
  have he (j : Fin n) :
      ‖Matrix.toEuclideanLin (A - truncSVD A k) (rightSingularBasis A j)‖ ^ 2 =
        if k ≤ j.val then (Matrix.toEuclideanLin A).singularValues j ^ 2 else 0 := by
    simp only [map_sub, LinearMap.sub_apply, trunc_action]
    by_cases h : j.val < k
    · simp [h, not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h, singular_energy]
  simp_rw [he]
  rw [← Finset.sum_filter]
  exact fin_tail_sum n k (fun i => (Matrix.toEuclideanLin A).singularValues i ^ 2)

/-- **Eckart–Young (Frobenius norm).** Every matrix of rank at most `k` has squared Frobenius
distance from `A` at least the sum of the discarded squared singular values. -/
theorem sum_sq_singularValues_le_frobenius_sub_sq (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank ≤ k) :
    ∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2 ≤ ‖A - B‖ ^ 2 := by
  classical
  by_cases hk : n ≤ k
  · rw [Finset.Ico_eq_empty_of_le hk, Finset.sum_empty]
    positivity
  have hkn : k < n := Nat.lt_of_not_ge hk
  let W := (Matrix.toEuclideanLin B).ker
  let w := stdOrthonormalBasis ℝ W
  let z : Fin (Module.finrank ℝ W) → EuclideanSpace ℝ (Fin n) := fun j => w j
  have hz : Orthonormal ℝ z := w.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hBz (j : Fin (Module.finrank ℝ W)) : Matrix.toEuclideanLin B (z j) = 0 :=
    (w j).property
  have hbound : (∑ j, ‖Matrix.toEuclideanLin A (z j)‖ ^ 2) ≤ ‖A - B‖ ^ 2 := by
    convert orthonormal_energy_le (A - B) z hz using 1
    apply Finset.sum_congr rfl
    intro j _
    simp [map_sub, LinearMap.sub_apply, hBz]
  let c : Fin n → ℝ := fun i => ∑ j, (inner ℝ (rightSingularBasis A i) (z j)) ^ 2
  have hc0 (i : Fin n) : 0 ≤ c i :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc1 (i : Fin n) : c i ≤ 1 := by
    simpa [c, real_inner_comm] using hz.sum_inner_products_le (rightSingularBasis A i)
  have hcsum : (∑ i, c i) = (Module.finrank ℝ W : ℝ) := by
    dsimp [c]
    rw [Finset.sum_comm]
    simp only [OrthonormalBasis.sum_sq_inner_right]
    have hn (j : Fin (Module.finrank ℝ W)) : ‖z j‖ = 1 := w.norm_eq_one j
    simp [hn]
  have hrank : Module.finrank ℝ (Matrix.toEuclideanLin B).range = B.rank := by
    exact (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).symm
  have hdim : n - k ≤ Module.finrank ℝ W := by
    have hn := (Matrix.toEuclideanLin B).finrank_range_add_finrank_ker
    rw [hrank, finrank_euclideanSpace_fin] at hn
    dsimp [W]
    omega
  have hc : (n - k : ℕ) ≤ ∑ i, c i := by
    rw [hcsum]
    exact_mod_cast hdim
  have hs : (∑ j, ‖Matrix.toEuclideanLin A (z j)‖ ^ 2) =
      ∑ i : Fin n, (Matrix.toEuclideanLin A).singularValues i ^ 2 * c i := by
    simp_rw [spectral_energy]
    rw [Finset.sum_comm]
    simp only [c, Finset.mul_sum]
  have hord : Antitone (fun i : Fin n => (Matrix.toEuclideanLin A).singularValues i ^ 2) := by
    intro i j hij
    change (Matrix.toEuclideanLin A).singularValues j ^ 2 ≤
      (Matrix.toEuclideanLin A).singularValues i ^ 2
    rw [(Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin,
      (Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin]
    exact (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues_antitone
      finrank_euclideanSpace_fin hij
  rw [← fin_tail_sum n k (fun i => (Matrix.toEuclideanLin A).singularValues i ^ 2)]
  exact (weighted_tail_le k hkn _ c hord (fun _ => sq_nonneg _) hc0 hc1 hc).trans
    (hs ▸ hbound)

/-- **Eckart–Young, best-approximation form.** The truncated SVD is a best rank-`k` approximation
of `A` in the Frobenius norm: the least squared distance from `A` to a matrix of rank at most `k`
is `∑_{k ≤ i < n} σᵢ²`, attained by `truncSVD A k`. -/
theorem isLeast_frobenius_sub_sq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsLeast {r | ∃ B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k ∧ r = ‖A - B‖ ^ 2}
      (∑ i ∈ Finset.Ico k n, (Matrix.toEuclideanLin A).singularValues i ^ 2) := by
  refine ⟨⟨truncSVD A k, rank_truncSVD_le A k, (frobenius_sub_truncSVD_sq A k).symm⟩, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  exact sum_sq_singularValues_le_frobenius_sub_sq A B hB

/-- The squared Frobenius norm of a finite real matrix. -/
def frobSq (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The squared Frobenius norm is the square of Mathlib's Frobenius norm. -/
theorem frobSq_eq_norm_sq (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = ‖A‖ ^ 2 := by
  rw [frobSq, frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- The singular values of a real matrix, as a finitely supported sequence
(zero-indexed, nonincreasing). -/
noncomputable def singularSeq (A : Matrix (Fin m) (Fin n) ℝ) : ℕ →₀ ℝ :=
  (Matrix.toEuclideanLin A).singularValues

/-- The sum of squared singular values beyond the `k`-th. -/
noncomputable def singularTailSq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ :=
  (singularSeq A).sum fun j s => if k ≤ j then s ^ 2 else 0

theorem singularTailSq_eq_sum_Ico (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularTailSq A k =
      ∑ j ∈ Finset.Ico k n, ((Matrix.toEuclideanLin A).singularValues j) ^ 2 := by
  classical
  have hle : Module.finrank ℝ (Matrix.toEuclideanLin A).range ≤ n := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin A)
    rw [finrank_euclideanSpace_fin] at h
    omega
  have hsupp : (Matrix.toEuclideanLin A).singularValues.support ⊆ Finset.range n := by
    rw [LinearMap.support_singularValues]
    exact Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le hx hle)
  have h1 : singularTailSq A k =
      ∑ j ∈ Finset.range n,
        (if k ≤ j then ((Matrix.toEuclideanLin A).singularValues j) ^ 2 else 0) := by
    rw [singularTailSq, singularSeq, Finsupp.sum]
    refine Finset.sum_subset hsupp fun j _ hj => ?_
    by_cases hkj : k ≤ j
    · rw [ite_eq_left hkj, Finsupp.notMem_support_iff.mp hj]
      norm_num
    · rw [ite_eq_right hkj]
  have hfilter : (Finset.range n).filter (fun j => k ≤ j) = Finset.Ico k n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h1, ← Finset.sum_filter, hfilter]

/-- **Eckart–Young, Frobenius lower bound.** Every matrix of rank at most `k`
approximates `A` with squared Frobenius error at least the singular tail. -/
theorem singularTailSq_le_frobSq_sub (A G : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hG : G.rank ≤ k) :
    singularTailSq A k ≤ frobSq (A - G) := by
  rw [singularTailSq_eq_sum_Ico, frobSq_eq_norm_sq]
  exact sum_sq_singularValues_le_frobenius_sub_sq A G hG

/-- **Eckart–Young, attainment.** For a real `m × n` matrix `A` and `k : ℕ`, some real
`m × n` matrix `G` of rank at most `k` (a truncated singular value decomposition of `A`) has
`frobSq (A - G) = singularTailSq A k = ∑_{j ≥ k} σ_j(A) ^ 2`, where `σ_0(A) ≥ σ_1(A) ≥ ⋯` are
the singular values of `A`. -/
theorem exists_rank_le_frobSq_sub_eq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧ frobSq (A - G) = singularTailSq A k :=
  ⟨truncSVD A k, rank_truncSVD_le A k, by
    rw [frobSq_eq_norm_sq, frobenius_sub_truncSVD_sq, singularTailSq_eq_sum_Ico]⟩

/-- **Eckart–Young, the tail is the minimum squared Frobenius error.** For a real `m × n`
matrix `A` and `k : ℕ`, the least value of `frobSq (A - G)`, the squared Frobenius norm of
`A - G`, over real `m × n` matrices `G` of rank at most `k` is
`singularTailSq A k = ∑_{j ≥ k} σ_j(A) ^ 2`, where `σ_0(A) ≥ σ_1(A) ≥ ⋯` are the singular values
of `A`. -/
theorem isLeast_frobSq_sub (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsLeast {x : ℝ | ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧ x = frobSq (A - G)}
      (singularTailSq A k) := by
  obtain ⟨G, hG, hEq⟩ := exists_rank_le_frobSq_sub_eq A k
  refine ⟨⟨G, hG, hEq.symm⟩, ?_⟩
  rintro _ ⟨G', hG', rfl⟩
  exact singularTailSq_le_frobSq_sub A G' hG'

/-- Rank-zero case: the squared Frobenius norm is the sum of all squared singular
values. -/
theorem frobSq_eq_sum_sq_singularSeq (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = (singularSeq A).sum fun _ s => s ^ 2 := by
  have h0 : truncSVD A 0 = 0 := by
    rw [truncSVD]
    simp
  conv_lhs => rw [frobSq_eq_norm_sq, ← sub_zero A, ← h0, frobenius_sub_truncSVD_sq A 0,
    ← singularTailSq_eq_sum_Ico A 0, singularTailSq]
  exact Finsupp.sum_congr fun j _ => by rw [ite_eq_left (Nat.zero_le j)]

/-- **Whitening form.** For invertible `P` and `Q`, optimizing the weighted
squared error `‖P (A - G) Q‖_F²` over `G` of rank at most `k` has minimum the
singular tail of the whitened matrix `P * A * Q`. -/
theorem isLeast_frobSq_whitened (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    IsLeast {x : ℝ | ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧
        x = frobSq (P * (A - G) * Q)} (singularTailSq (P * A * Q) k) := by
  classical
  have hrank : ∀ G : Matrix (Fin m) (Fin n) ℝ, (P * G * Q).rank = G.rank := fun G => by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det Q (P * G) hQ,
      Matrix.rank_mul_eq_right_of_isUnit_det P G hP]
  have hset : {x : ℝ | ∃ G : Matrix (Fin m) (Fin n) ℝ, G.rank ≤ k ∧
        x = frobSq (P * (A - G) * Q)} =
      {x : ℝ | ∃ G' : Matrix (Fin m) (Fin n) ℝ, G'.rank ≤ k ∧
        x = frobSq (P * A * Q - G')} := by
    ext x
    constructor
    · rintro ⟨G, hG, rfl⟩
      refine ⟨P * G * Q, by rwa [hrank G], ?_⟩
      rw [Matrix.mul_sub, Matrix.sub_mul]
    · rintro ⟨G', hG', rfl⟩
      refine ⟨P⁻¹ * G' * Q⁻¹, ?_, ?_⟩
      · have h1 : (P⁻¹ * G' * Q⁻¹).rank = G'.rank := by
          rw [Matrix.rank_mul_eq_left_of_isUnit_det Q⁻¹ (P⁻¹ * G')
              (Matrix.isUnit_nonsing_inv_det _ hQ),
            Matrix.rank_mul_eq_right_of_isUnit_det P⁻¹ G'
              (Matrix.isUnit_nonsing_inv_det _ hP)]
        rwa [h1]
      · have key : P * (A - P⁻¹ * G' * Q⁻¹) * Q = P * A * Q - G' := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          congr 1
          calc P * (P⁻¹ * G' * Q⁻¹) * Q = (P * P⁻¹) * G' * (Q⁻¹ * Q) := by
                simp only [Matrix.mul_assoc]
            _ = G' := by
                rw [Matrix.mul_nonsing_inv _ hP, Matrix.nonsing_inv_mul _ hQ,
                  Matrix.one_mul, Matrix.mul_one]
        rw [key]
  rw [hset]
  exact isLeast_frobSq_sub (P * A * Q) k

end Matrix.EckartYoungFrobenius

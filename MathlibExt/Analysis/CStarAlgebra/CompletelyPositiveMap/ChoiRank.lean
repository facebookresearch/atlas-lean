/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Kraus
import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.ChoiTheorem
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Choi rank of completely positive maps

This module defines the Choi rank of a completely positive map
`φ : Matrix n n ℂ →CP Matrix m m ℂ` as the rank of its Choi matrix.

The repository uses the input × output Choi convention

`J(Φ) ((i,a),(j,b)) = Φ (Matrix.single i j 1) a b`,

indexed by `n × m`. The Choi rank is `rank (J(Φ))`.

## Tags

choi, choi rank, completely positive map
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator CStarAlgebra MatrixOrder ComplexOrder

namespace CompletelyPositiveMap

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Choi rank.** For finite decidable index types `n` and `m` and a completely positive map `φ :
Matrix n n ℂ →CP Matrix m m ℂ`, its Choi rank is the complex rank of `J(φ)`, with input-output index
order `n × m`. -/
noncomputable def choiRank (φ : Matrix n n ℂ →CP Matrix m m ℂ) : ℕ :=
  (choiMatrix φ).rank

/-- **Choi rank of the empty Kraus family.** For finite decidable matrix index types `n` and `m`, any
family `K : Fin 0 → Matrix m n ℂ` defines the zero completely positive map, whose Choi rank is zero. -/
@[simp]
theorem choiRank_kraus_fin_zero (K : Fin 0 → Matrix m n ℂ) :
    choiRank (kraus K) = 0 := by
  simp [choiRank, choiMatrix_kraus]

variable {r : Type*} [Fintype r]

/-- Private rectangular matrix whose columns are the vectorized Kraus operators.

For `K : r → Matrix m n ℂ`, the matrix `krausVecMatrix K : Matrix (n × m) r ℂ`
has entry `(krausVecMatrix K) x i = Matrix.vec (K i) x`. -/
private noncomputable def krausVecMatrix (K : r → Matrix m n ℂ) :
    Matrix (n × m) r ℂ :=
  Matrix.of fun x i => Matrix.vec (K i) x

/-- Private factorization of the Choi matrix of a finite Kraus family as `W * Wᴴ`,
where `W` is the rectangular matrix whose columns are the vectorized Kraus
operators. Proved directly entrywise from `choiMatrix_kraus`. -/
private theorem choiMatrix_kraus_eq_vecMatrix_mul_conjTranspose (K : r → Matrix m n ℂ) :
    choiMatrix (kraus K) = (krausVecMatrix K) * (krausVecMatrix K)ᴴ := by
  rw [choiMatrix_kraus]
  ext x y
  simp only [krausVecMatrix, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Matrix.vec, Matrix.of_apply, Matrix.conjTranspose_apply, Pi.star_apply]

/-- **Choi-rank bound by Kraus-family size.** For finite decidable matrix index types `n,m`, a finite
index type `r`, and `K : r → Matrix m n ℂ`, the completely positive map `X ↦ ∑ i, Kᵢ X Kᵢᴴ` has Choi
rank at most `|r|`. -/
theorem choiRank_kraus_le_card (K : r → Matrix m n ℂ) :
    choiRank (kraus K) ≤ Fintype.card r := by
  rw [choiRank, choiMatrix_kraus_eq_vecMatrix_mul_conjTranspose K]
  calc
    ((krausVecMatrix K) * (krausVecMatrix K)ᴴ).rank ≤ (krausVecMatrix K).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card r :=
      Matrix.rank_le_card_width _

private theorem choiMatrix_kraus_eq_choiMatrix_kraus_support (K : r → Matrix m n ℂ) :
    choiMatrix (kraus K) =
      choiMatrix (kraus (fun (i : {i // K i ≠ 0}) => K i.val)) := by
  classical
  rw [choiMatrix_kraus, choiMatrix_kraus]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : r => K i ≠ 0)
      (fun i => Matrix.vecMulVec (Matrix.vec (K i)) (star (Matrix.vec (K i))))
  have h0 : ∑ _i : {i : r // ¬ (K i ≠ 0)},
      Matrix.vecMulVec (Matrix.vec (K _i.val)) (star (Matrix.vec (K _i.val))) = 0 := by
    apply Fintype.sum_eq_zero
    intro ⟨i, hi⟩
    have hKi : K i = 0 := by
      by_contra h
      exact hi h
    simp [hKi]
  rw [← hsplit, h0, add_zero]

/-- **Choi-rank bound by nonzero Kraus operators.** For finite decidable matrix index types `n,m` and a
finite family `K : r → Matrix m n ℂ`, the Choi rank of `kraus K` is at most the number of indices
`i` with `Kᵢ ≠ 0`. -/
theorem choiRank_kraus_le_natCard_support (K : r → Matrix m n ℂ) :
    choiRank (kraus K) ≤ Nat.card {i // K i ≠ 0} := by
  classical
  have h_eq : choiMatrix (kraus K) =
      choiMatrix (kraus (fun (i : {i // K i ≠ 0}) => K i.val)) :=
    choiMatrix_kraus_eq_choiMatrix_kraus_support K
  calc
    choiRank (kraus K) = (choiMatrix (kraus K)).rank := rfl
    _ = (choiMatrix (kraus (fun (i : {i // K i ≠ 0}) => K i.val))).rank := by
      rw [h_eq]
    _ = choiRank (kraus (fun (i : {i // K i ≠ 0}) => K i.val)) := rfl
    _ ≤ Fintype.card {i // K i ≠ 0} :=
      choiRank_kraus_le_card _
    _ = Nat.card {i // K i ≠ 0} :=
      Nat.card_eq_fintype_card.symm

end CompletelyPositiveMap

section PSDRankFactorization

variable {q : Type*} [Fintype q]

private lemma matrix_mul_conjTranspose_eq_sum_outer (W : Matrix q q ℂ) :
    W * Wᴴ = ∑ j : q, Matrix.vecMulVec (W.col j) (star (W.col j)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.col_apply,
    Matrix.conjTranspose_apply, Pi.star_apply]

-- Private exact rank-sized PSD factorization for complex matrices.
-- For `M : Matrix q q ℂ` PSD, `M = ∑_{i : Fin rank} vecMulVec (v i) (star (v i))`.
-- Uses the Hermitian spectral theorem, `eigenvectorUnitary`, `rank_eq_card_non_zero_eigs`,
-- `eigenvalues_nonneg`, `Real.sqrt`, and `Fintype.equivFinOfCardEq`.
-- Classical is local so the type has no unused `DecidableEq q`.
private theorem posSemidef_exists_rank_sized_vecMulVec_factorization
    (M : Matrix q q ℂ) (hM : M.PosSemidef) :
    ∃ (v : Fin M.rank → q → ℂ), M = ∑ i, Matrix.vecMulVec (v i) (star (v i)) := by
  classical
  let hA := hM.1
  let eig : q → ℝ := hA.eigenvalues
  have hEigNonneg : ∀ i, 0 ≤ eig i := fun i => hM.eigenvalues_nonneg i
  let sqrtEig : q → ℝ := fun i => Real.sqrt (eig i)
  have hSqrtSq : ∀ i, sqrtEig i * sqrtEig i = eig i := fun i =>
    Real.mul_self_sqrt (hEigNonneg i)
  have hSqrtEqZero : ∀ i, sqrtEig i = 0 ↔ eig i = 0 := fun i =>
    Real.sqrt_eq_zero (hEigNonneg i)
  let Umat : Matrix q q ℂ := (hA.eigenvectorUnitary : Matrix q q ℂ)
  let Dsqrt : Matrix q q ℂ := Matrix.diagonal (fun j => Complex.ofReal (sqrtEig j))
  let W : Matrix q q ℂ := Umat * Dsqrt
  have hWEntry : ∀ a j, W a j = Umat a j * Complex.ofReal (sqrtEig j) := by
    intro a j
    simp [W, Dsqrt, Matrix.mul_diagonal]
  have hDsqrtMul : Dsqrt * Dsqrt = Matrix.diagonal (fun i => Complex.ofReal (eig i)) := by
    calc
      Dsqrt * Dsqrt =
          Matrix.diagonal (fun i => Complex.ofReal (sqrtEig i) * Complex.ofReal (sqrtEig i)) := by
        rw [Matrix.diagonal_mul_diagonal]
      _ = Matrix.diagonal (fun i => Complex.ofReal (sqrtEig i * sqrtEig i)) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Complex.ofReal_mul]
        · simp [hij]
      _ = Matrix.diagonal (fun i => Complex.ofReal (eig i)) := by
        congr
        funext i
        rw [hSqrtSq]
  have hDsqrtStar : Dsqrtᴴ = Dsqrt := by
    calc
      Dsqrtᴴ = Matrix.diagonal (star (fun j => Complex.ofReal (sqrtEig j) : q → ℂ)) := by
        rw [Matrix.diagonal_conjTranspose]
      _ = Matrix.diagonal (fun j => Complex.ofReal (sqrtEig j)) := by
        congr
        funext j
        simp [Complex.conj_ofReal]
  have hWConj : Wᴴ = Dsqrt * star Umat := by
    calc
      Wᴴ = (Umat * Dsqrt)ᴴ := rfl
      _ = Dsqrtᴴ * Umatᴴ := by rw [Matrix.conjTranspose_mul]
      _ = Dsqrt * Umatᴴ := by rw [hDsqrtStar]
      _ = Dsqrt * star Umat := by rw [Matrix.star_eq_conjTranspose]
  have hSpec : M =
      Umat * Matrix.diagonal (fun i => Complex.ofReal (eig i)) * star Umat := by
    have hST := hA.spectral_theorem
    have hRCLike : (RCLike.ofReal ∘ eig : q → ℂ) = fun i => Complex.ofReal (eig i) := rfl
    rw [hRCLike] at hST
    rw [Unitary.conjStarAlgAut_apply] at hST
    exact hST
  have hMWW : M = W * Wᴴ := by
    calc
      M = Umat * Matrix.diagonal (fun i => Complex.ofReal (eig i)) * star Umat := hSpec
      _ = Umat * (Dsqrt * Dsqrt) * star Umat := by rw [← hDsqrtMul]
      _ = (Umat * (Dsqrt * Dsqrt)) * star Umat := rfl
      _ = ((Umat * Dsqrt) * Dsqrt) * star Umat := by rw [Matrix.mul_assoc Umat Dsqrt Dsqrt]
      _ = (Umat * Dsqrt) * (Dsqrt * star Umat) := by
        rw [Matrix.mul_assoc (Umat * Dsqrt) Dsqrt (star Umat)]
      _ = W * (Dsqrt * star Umat) := rfl
      _ = W * Wᴴ := by rw [← hWConj]
  have hSumOuter : M = ∑ j : q, Matrix.vecMulVec (W.col j) (star (W.col j)) := by
    rw [hMWW, matrix_mul_conjTranspose_eq_sum_outer W]
  let P : q → Prop := fun i => hA.eigenvalues i ≠ 0
  let s := {i : q // P i}
  let f : q → Matrix q q ℂ := fun j => Matrix.vecMulVec (W.col j) (star (W.col j))
  have hZeroCompl : ∑ i : {j // ¬ P j}, f i.val = 0 := by
    apply Fintype.sum_eq_zero
    intro ⟨j, hj⟩
    have hj0 : hA.eigenvalues j = 0 := by
      by_contra hne
      exact hj hne
    have hj0' : eig j = 0 := hj0
    have hSqrt0 : sqrtEig j = 0 := (hSqrtEqZero j).mpr hj0'
    have hCol0 : W.col j = 0 := by
      ext a
      calc
        W.col j a = W a j := rfl
        _ = Umat a j * Complex.ofReal (sqrtEig j) := hWEntry a j
        _ = Umat a j * Complex.ofReal 0 := by rw [hSqrt0]
        _ = 0 := by simp
    simp [f, hCol0]
  have hSumS : M = ∑ i : s, f i.val := by
    calc
      M = ∑ j : q, f j := hSumOuter
      _ = (∑ i : s, f i.val) + ∑ i : {j // ¬ P j}, f i.val := by
        rw [← Fintype.sum_subtype_add_sum_subtype P f]
      _ = (∑ i : s, f i.val) + 0 := by rw [hZeroCompl]
      _ = ∑ i : s, f i.val := by rw [add_zero]
  have hRankEq : M.rank = Fintype.card s := by
    convert hA.rank_eq_card_non_zero_eigs using 1
  let e : s ≃ Fin M.rank :=
    Fintype.equivFinOfCardEq hRankEq.symm
  let g : s → Matrix q q ℂ := fun i => f i.val
  have hSumG : M = ∑ i : s, g i := hSumS
  let v : Fin M.rank → q → ℂ := fun k => W.col (e.symm k).val
  have hV : ∀ k : Fin M.rank, Matrix.vecMulVec (v k) (star (v k)) = g (e.symm k) := by
    intro k
    rfl
  refine ⟨v, ?_⟩
  calc
    M = ∑ i : s, g i := hSumG
    _ = ∑ k : Fin M.rank, g (e.symm k) := by
      rw [← Equiv.sum_comp e.symm g]
    _ = ∑ k : Fin M.rank, Matrix.vecMulVec (v k) (star (v k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hV]

end PSDRankFactorization

namespace CompletelyPositiveMap

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Kraus representation of minimal size.** Every completely positive map `φ : Matrix n n ℂ →CP Matrix
m m ℂ`, for finite decidable `n,m`, has a Kraus family `K : Fin (choiRank φ) → Matrix m n ℂ` with `φ
= kraus K`. Choi rank zero gives an empty family; empty input or output types are allowed. -/
theorem exists_kraus_choiRank (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ (K : Fin (choiRank φ) → Matrix m n ℂ), φ = kraus K := by
  classical
  have hPSD : (choiMatrix φ).PosSemidef := choiMatrix_posSemidef φ
  obtain ⟨v, hv⟩ :=
    posSemidef_exists_rank_sized_vecMulVec_factorization (choiMatrix φ) hPSD
  let K : Fin (choiRank φ) → Matrix m n ℂ := fun r a i => v r (i, a)
  have hVec : ∀ r, Matrix.vec (K r) = v r := by
    intro r
    ext ⟨i, a⟩
    rfl
  have hChoi : choiMatrix (kraus K) = choiMatrix φ := by
    calc
      choiMatrix (kraus K) =
          ∑ r, Matrix.vecMulVec (Matrix.vec (K r)) (star (Matrix.vec (K r))) :=
        choiMatrix_kraus K
      _ = ∑ r, Matrix.vecMulVec (v r) (star (v r)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hVec]
      _ = choiMatrix φ := hv.symm
  refine ⟨K, ?_⟩
  have hLin : (kraus K).toLinearMap = φ.toLinearMap := by
    apply LinearMap.choiMatrix_injective
    calc
      LinearMap.choiMatrix (kraus K).toLinearMap = choiMatrix (kraus K) := rfl
      _ = choiMatrix φ := hChoi
      _ = LinearMap.choiMatrix φ.toLinearMap := rfl
  apply DFunLike.ext
  intro X
  calc
    φ X = φ.toLinearMap X := rfl
    _ = (kraus K).toLinearMap X := by rw [← hLin]
    _ = kraus K X := rfl

variable {r : Type*} [Fintype r]

/-- **Choi rank as the dimension of the Kraus span.** For finite decidable matrix index types `n,m` and
a finite family `K : r → Matrix m n ℂ`, the Choi rank of `kraus K` equals the complex dimension of
the span of the vectorized matrices `vec(Kᵢ)`. -/
theorem choiRank_kraus_eq_finrank_span_vec (K : r → Matrix m n ℂ) :
    choiRank (kraus K) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => Matrix.vec (K i)))) := by
  have h_eq : choiMatrix (kraus K) = (krausVecMatrix K) * (krausVecMatrix K)ᴴ :=
    choiMatrix_kraus_eq_vecMatrix_mul_conjTranspose K
  have h_col : ∀ i, (krausVecMatrix K).col i = Matrix.vec (K i) := by
    intro i
    ext x
    simp only [krausVecMatrix, Matrix.of_apply, Matrix.col_apply]
  have h_fun : (krausVecMatrix K).col = fun i => Matrix.vec (K i) :=
    funext h_col
  have h_range : Set.range (krausVecMatrix K).col =
      Set.range (fun i => Matrix.vec (K i)) := by
    rw [h_fun]
  calc
    choiRank (kraus K) = (choiMatrix (kraus K)).rank := rfl
    _ = ((krausVecMatrix K) * (krausVecMatrix K)ᴴ).rank := by rw [h_eq]
    _ = (krausVecMatrix K).rank := by rw [Matrix.rank_self_mul_conjTranspose]
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (krausVecMatrix K).col)) := by
      rw [Matrix.rank_eq_finrank_span_cols]
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => Matrix.vec (K i)))) := by
      rw [h_range]

/-- **Independence of Kraus operators and Choi rank.** For finite decidable matrix index types `n,m` and
a finite family `K : r → Matrix m n ℂ`, the vectorized operators `vec(Kᵢ)` are complex-linearly
independent exactly when the Choi rank of `kraus K` equals `|r|`. -/
theorem linearIndependent_vec_iff_choiRank_kraus_eq_card (K : r → Matrix m n ℂ) :
    LinearIndependent ℂ (fun i => Matrix.vec (K i)) ↔
      choiRank (kraus K) = Fintype.card r := by
  have h_span : choiRank (kraus K) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => Matrix.vec (K i)))) :=
    choiRank_kraus_eq_finrank_span_vec K
  calc
    LinearIndependent ℂ (fun i => Matrix.vec (K i))
        ↔ Fintype.card r =
          Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => Matrix.vec (K i)))) :=
      linearIndependent_iff_card_eq_finrank_span
    _ ↔ Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => Matrix.vec (K i)))) =
          Fintype.card r :=
      eq_comm
    _ ↔ choiRank (kraus K) = Fintype.card r := by
      rw [h_span]

/-- **Independent minimal Kraus family.** For finite decidable `n,m`, every completely positive map `φ :
Matrix n n ℂ →CP Matrix m m ℂ` has a representation `φ = kraus K` indexed by `Fin (choiRank φ)`
whose vectorized matrices are complex-linearly independent. Rank zero and empty matrix index types
are included. -/
theorem exists_kraus_choiRank_linearIndependent
    (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ (K : Fin (choiRank φ) → Matrix m n ℂ),
      φ = kraus K ∧ LinearIndependent ℂ (fun i => Matrix.vec (K i)) := by
  classical
  obtain ⟨K, hK⟩ := exists_kraus_choiRank φ
  have h_choiRank_eq : choiRank φ = choiRank (kraus K) :=
    congrArg choiRank hK
  have h_card : Fintype.card (Fin (choiRank φ)) = choiRank φ := by
    simp
  have h_rank : choiRank (kraus K) = Fintype.card (Fin (choiRank φ)) := by
    rw [← h_choiRank_eq, h_card]
  have h_li : LinearIndependent ℂ (fun i => Matrix.vec (K i)) := by
    rw [linearIndependent_vec_iff_choiRank_kraus_eq_card K]
    exact h_rank
  exact ⟨K, hK, h_li⟩

end CompletelyPositiveMap

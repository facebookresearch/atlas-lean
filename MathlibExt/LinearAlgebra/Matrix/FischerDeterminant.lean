/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Topology.Algebra.Group.Matrix
import MathlibExt.LinearAlgebra.Matrix.MinkowskiDeterminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fischer's determinant inequality for positive semidefinite block matrices

For a positive semidefinite block matrix `M = [[A, B], [Bᴴ, D]]` with
real entries, Fischer's inequality states that
`det M ≤ det A * det D`.

This is a companion to the self-adjoint / positivity material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(self-adjoint operators, positivity iff the spectrum is nonnegative):
in finite dimension the spectrum is the list of eigenvalues, and the
proof below goes through the spectrum (eigenvalue lower bounds and
concavity-free conjugation by the positive square root). It is not one
of the 72 v1 targets. It is distinct from the Hadamard / AM–GM
determinant bounds for positive semidefinite matrices in base
MathlibExt (`MathlibExt/LinearAlgebra/Matrix/PosSemidefDeterminant.lean`)
and from Minkowski's determinant inequality
(`MathlibExt/LinearAlgebra/Matrix/MinkowskiDeterminant.lean`):
Fischer's inequality is the block-matrix inequality, and its proof
needs the Schur complement `D - Bᴴ * A⁻¹ * B` together with
monotonicity of the determinant on the positive semidefinite cone,
which is obtained from the unchanged complex monotonicity theorem
`Matrix.PosSemidef.det_le_det_add` in `MinkowskiDeterminant.lean`
by real-to-complex scalar extension and finite-index reindexing.

The proof is the classical one: if `A` is positive definite, then
`det M = det A * det (D - Bᴴ * A⁻¹ * B)` by the block determinant
formula, the Schur complement is positive semidefinite, and
`det (D - Bᴴ * A⁻¹ * B) ≤ det D` by the reused determinant
monotonicity theorem. The equality proof retains the square-root
conjugation and eigenvalue argument needed to force `B = 0`. The
general case follows by approximating `A` with the positive definite
matrices `ε • 1 + A` and letting `ε → 0⁺`. The equality case is
characterized as well: for `A` and `D` positive definite and `M`
positive semidefinite, equality holds iff `B = 0` (the hypothesis
that `M` is positive semidefinite is essential: for `A = D = 1` and
`B = √2 • 1` on `ℂ²`, `det M = 1 = det A * det D` although `B ≠ 0`).

## Main declarations

* `Matrix.one_le_det_of_posSemidef_sub_one` : if `W - 1` is positive
  semidefinite then `1 ≤ det W`.
* `Matrix.det_le_det_of_posSemidef_le` : monotonicity of the
  determinant on the positive semidefinite cone.
* `Matrix.fischer_det_fromBlocks_le` : Fischer's inequality.
* `Matrix.fischer_det_fromBlocks_eq_iff` : the equality case.
-/

@[expose] public section

namespace Matrix

open Finset
open scoped Topology MatrixOrder ComplexOrder

/-- A product of reals, each at least `1`, is at least `1`. -/
private lemma one_le_prod_of_one_le {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : 1 ≤ f a := h a (Finset.mem_insert_self a s)
    have h2 : 1 ≤ ∏ i ∈ s, f i := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ f a * ∏ i ∈ s, f i :=
        mul_le_mul h1 h2 zero_le_one (by linarith [h1])

/-- If a product of reals, each at least `1`, equals `1`, then each
factor equals `1`. -/
private lemma eq_one_of_prod_eq_one {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {s : Finset ι}
    (h : ∀ i ∈ s, 1 ≤ f i) (hprod : ∏ i ∈ s, f i = 1) {i : ι} (hi : i ∈ s) :
    f i = 1 := by
  induction s using Finset.induction with
  | empty => simp at hi
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha] at hprod
    have h1 : 1 ≤ f a := h a (Finset.mem_insert_self a s)
    have hrest : ∀ j ∈ s, 1 ≤ f j := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h2 : 1 ≤ ∏ j ∈ s, f j := one_le_prod_of_one_le hrest
    have hfa : f a = 1 := by
      apply le_antisymm _ h1
      calc f a = f a * 1 := (mul_one _).symm
        _ ≤ f a * ∏ j ∈ s, f j :=
          mul_le_mul_of_nonneg_left h2 (by linarith [h1])
        _ = 1 := hprod
    have hprod' : ∏ j ∈ s, f j = 1 := by
      have : f a * ∏ j ∈ s, f j = 1 := hprod
      rw [hfa, one_mul] at this
      exact this
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hfa
    · exact ih hrest hprod' hi'

/-- Every eigenvalue of a Hermitian matrix `W` with `W - 1` positive
semidefinite is at least `1`: evaluate the quadratic form of `W - 1`
at a unit eigenvector. -/
private theorem eigenvalues_ge_one_of_posSemidef_sub_one {n : Type*} [Fintype n]
    [DecidableEq n] {W : Matrix n n ℝ} (hW : W.IsHermitian)
    (h : (W - 1).PosSemidef) (i : n) :
    1 ≤ hW.eigenvalues i := by
  have heig := hW.eigenvalues_eq i
  rw [heig]
  have hsplit : W *ᵥ ⇑(hW.eigenvectorBasis i) =
      (W - 1) *ᵥ ⇑(hW.eigenvectorBasis i) + ⇑(hW.eigenvectorBasis i) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [hsplit, dotProduct_add]
  have hnn : 0 ≤ star ⇑(hW.eigenvectorBasis i) ⬝ᵥ
      (W - 1) *ᵥ ⇑(hW.eigenvectorBasis i) := h.dotProduct_mulVec_nonneg _
  have hone : star ⇑(hW.eigenvectorBasis i) ⬝ᵥ ⇑(hW.eigenvectorBasis i) = 1 := by
    have h2 : inner ℝ (hW.eigenvectorBasis i) (hW.eigenvectorBasis i) = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      have hnorm := hW.eigenvectorBasis.orthonormal.norm_eq_one i
      rw [hnorm]
      norm_num
    rw [PiLp.inner_apply] at h2
    simp only [RCLike.inner_apply] at h2
    simpa [dotProduct] using h2
  rw [hone]
  have hre : ∀ x : ℝ, RCLike.re x = x := fun _ => rfl
  simp only [hre]
  linarith [hnn]

/-- If `W - 1` is positive semidefinite, then `1 ≤ det W`, since every
eigenvalue of `W` is at least `1`. -/
theorem one_le_det_of_posSemidef_sub_one {n : Type*} [Fintype n] [DecidableEq n]
    {W : Matrix n n ℝ} (hW : W.IsHermitian) (h : (W - 1).PosSemidef) :
    1 ≤ W.det := by
  have hdet : W.det = ∏ i, hW.eigenvalues i := by
    simpa using hW.det_eq_prod_eigenvalues
  rw [hdet]
  exact one_le_prod_of_one_le fun i _ =>
    eigenvalues_ge_one_of_posSemidef_sub_one hW h i

private theorem complexify_posSemidef {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) :
    (Complex.ofRealHom.mapMatrix M).PosSemidef := by
  let T := CFC.sqrt M
  let φ : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ := Complex.ofRealHom.mapMatrix
  have hTT : T * T = M := CFC.sqrt_mul_sqrt_self M (ha := hM.nonneg)
  have hT : Tᴴ = T := by
    rw [← Matrix.star_eq_conjTranspose]
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
  have hφT : (φ T)ᴴ = φ T := by
    change (T.map Complex.ofReal)ᴴ = T.map Complex.ofReal
    rw [← Matrix.conjTranspose_map Complex.ofReal (fun x => by simp), hT]
  have hgram : φ M = (φ T)ᴴ * φ T := by
    rw [hφT, ← map_mul, hTT]
  rw [hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self (φ T)


/-- **Monotonicity of the determinant on the positive semidefinite
cone**: if `S` and `D - S` are positive semidefinite, then
`det S ≤ det D`. -/
theorem det_le_det_of_posSemidef_le {n : Type*} [Fintype n] [DecidableEq n]
    {S D : Matrix n n ℝ} (hS : S.PosSemidef) (hSD : (D - S).PosSemidef) :
    S.det ≤ D.det := by
  let e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let φ : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ →+*
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ := Complex.ofRealHom.mapMatrix
  have hS' : (φ (S.submatrix e e)).PosSemidef := complexify_posSemidef (hS.submatrix e)
  have hSD' : (φ ((D - S).submatrix e e)).PosSemidef :=
    complexify_posSemidef (hSD.submatrix e)
  have h := hSD'.det_le_det_add hS'
  have hsum : φ ((D - S).submatrix e e) + φ (S.submatrix e e) = φ (D.submatrix e e) := by
    rw [← map_add]
    congr 1
    ext i j
    simp [Matrix.submatrix]
  rw [hsum] at h
  have hdet (M : Matrix n n ℝ) : (φ (M.submatrix e e)).det.re = M.det := by
    rw [← Complex.ofRealHom.map_det]
    change (M.submatrix e e).det = M.det
    exact Matrix.det_submatrix_equiv_self e M
  rwa [hdet, hdet] at h


/-- **Fischer's inequality, positive definite case**: the block
determinant formula plus determinant monotonicity. -/
private theorem fischer_det_fromBlocks_le_of_posDef {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {D : Matrix n n ℝ} (hA : A.PosDef)
    (hM : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det ≤ A.det * D.det := by
  let _ := hA.isUnit.invertible
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hInv : ⅟A = A⁻¹ :=
    invOf_eq_right_inv (Matrix.mul_nonsing_inv A hAdet)
  have hSchur : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B D hA).mp hM
  have hdet : (Matrix.fromBlocks A B Bᴴ D).det =
      A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [Matrix.det_fromBlocks₁₁, hInv]
  have hle : (D - Bᴴ * A⁻¹ * B).det ≤ D.det := by
    refine det_le_det_of_posSemidef_le hSchur ?_
    have hpsd : (Bᴴ * A⁻¹ * B).PosSemidef :=
      (hA.inv.posSemidef).conjTranspose_mul_mul_same B
    have hsub : D - (D - Bᴴ * A⁻¹ * B) = Bᴴ * A⁻¹ * B := sub_sub_cancel D _
    rwa [hsub]
  rw [hdet]
  exact mul_le_mul_of_nonneg_left hle hA.posSemidef.det_nonneg

/-- **Fischer's determinant inequality**: for a positive semidefinite
block matrix `[[A, B], [Bᴴ, D]]` with real entries,
`det [[A, B], [Bᴴ, D]] ≤ det A * det D`. -/
theorem fischer_det_fromBlocks_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {D : Matrix n n ℝ} (hM : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det ≤ A.det * D.det := by
  have hA : A.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact ((Matrix.isHermitian_fromBlocks_iff).mp hM.isHermitian).1
    · intro x
      have h := hM.dotProduct_mulVec_nonneg (Sum.elim x 0)
      simpa [Matrix.fromBlocks_mulVec] using h
  by_cases hApos : A.PosDef
  · exact fischer_det_fromBlocks_le_of_posDef hApos hM
  · -- Singular case: perturb `A` to `ε • 1 + A` and let `ε → 0⁺`.
    have hpert : ∀ ε : ℝ, 0 < ε →
        (Matrix.fromBlocks (ε • 1 + A) B Bᴴ D).det ≤ (ε • 1 + A).det * D.det := by
      intro ε hε
      have hAε : (ε • 1 + A).PosDef :=
        (Matrix.PosDef.one.smul hε).add_posSemidef hA
      have hN : (Matrix.fromBlocks (ε • (1 : Matrix m m ℝ)) 0 0 (0 : Matrix n n ℝ)).PosSemidef := by
        have hε1 : (ε • (1 : Matrix m m ℝ)) = Matrix.diagonal (fun _ => ε) := by
          ext i j
          by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
        have h0 : (0 : Matrix n n ℝ) = Matrix.diagonal (fun _ => (0 : ℝ)) := by
          ext i j
          simp [Matrix.diagonal]
        rw [hε1, h0, Matrix.fromBlocks_diagonal]
        exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by cases i <;> simp [hε.le])
      have hMε : (Matrix.fromBlocks (ε • 1 + A) B Bᴴ D).PosSemidef := by
        have hsum : Matrix.fromBlocks (ε • 1 + A) B Bᴴ D =
            Matrix.fromBlocks A B Bᴴ D + Matrix.fromBlocks (ε • 1) 0 0 0 := by
          rw [Matrix.fromBlocks_add]
          ext i j
          cases i <;> cases j <;> simp [Matrix.fromBlocks, add_comm]
        rw [hsum]
        exact hM.add hN
      exact fischer_det_fromBlocks_le_of_posDef hAε hMε
    have hcont : Continuous (fun ε : ℝ =>
        (Matrix.fromBlocks (ε • 1 + A) B Bᴴ D).det - (ε • 1 + A).det * D.det) := by
      apply Continuous.sub
      · exact Continuous.matrix_det (by fun_prop)
      · exact (Continuous.matrix_det (by fun_prop)).mul continuous_const
    have htend : Filter.Tendsto (fun ε : ℝ =>
        (Matrix.fromBlocks (ε • 1 + A) B Bᴴ D).det - (ε • 1 + A).det * D.det)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Matrix.fromBlocks A B Bᴴ D).det - A.det * D.det)) := by
      have h := hcont.tendsto (0 : ℝ)
      simpa using h.mono_left nhdsWithin_le_nhds
    have hle0 : (Matrix.fromBlocks A B Bᴴ D).det - A.det * D.det ≤ 0 := by
      apply le_of_tendsto_of_tendsto htend tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      have h := hpert ε hε'
      linarith
    linarith

/-- **Equality case of Fischer's inequality**: for `A` and `D`
positive definite and `[[A, B], [Bᴴ, D]]` positive semidefinite,
`det [[A, B], [Bᴴ, D]] = det A * det D` iff `B = 0`. -/
theorem fischer_det_fromBlocks_eq_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A : Matrix m m ℝ} {B : Matrix m n ℝ}
    {D : Matrix n n ℝ} (hA : A.PosDef) (hD : D.PosDef)
    (hM : (Matrix.fromBlocks A B Bᴴ D).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).det = A.det * D.det ↔ B = 0 := by
  constructor
  · intro heq
    let _ := hA.isUnit.invertible
    have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
    have hInv : ⅟A = A⁻¹ :=
      invOf_eq_right_inv (Matrix.mul_nonsing_inv A hAdet)
    have hSchur : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
      (Matrix.PosDef.fromBlocks₁₁ B D hA).mp hM
    have hdet : (Matrix.fromBlocks A B Bᴴ D).det =
        A.det * (D - Bᴴ * A⁻¹ * B).det := by
      rw [Matrix.det_fromBlocks₁₁, hInv]
    have hSdet : (D - Bᴴ * A⁻¹ * B).det = D.det := by
      rw [hdet] at heq
      exact mul_left_cancel₀ hA.det_pos.ne' heq
    have hSpos : (D - Bᴴ * A⁻¹ * B).PosDef :=
      hSchur.posDef_iff_det_ne_zero.mpr (by rw [hSdet]; exact hD.det_pos.ne')
    -- Conjugate `D` by the inverse square root of the Schur complement.
    set T := CFC.sqrt (D - Bᴴ * A⁻¹ * B) with hTdef
    have hT_herm : Tᴴ = T := by
      rw [← Matrix.star_eq_conjTranspose]
      exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (D - Bᴴ * A⁻¹ * B))
    have hTT : T * T = D - Bᴴ * A⁻¹ * B :=
      CFC.sqrt_mul_sqrt_self (D - Bᴴ * A⁻¹ * B) (ha := hSpos.posSemidef.nonneg)
    have hT_psd : T.PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (D - Bᴴ * A⁻¹ * B))
    have hTdet_unit : IsUnit T.det := by
      have hSunit : IsUnit (D - Bᴴ * A⁻¹ * B).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp hSpos.isUnit
      rw [← hTT, Matrix.det_mul] at hSunit
      exact isUnit_of_mul_isUnit_left hSunit
    have hTTinv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hTdet_unit
    have hTinvT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hTdet_unit
    have hTinv_herm : (T⁻¹)ᴴ = T⁻¹ := hT_psd.isHermitian.inv
    set W := T⁻¹ * D * T⁻¹ with hWdef
    have hDpsd : D.PosSemidef := hD.posSemidef
    have hW_herm : W.IsHermitian := by
      show (T⁻¹ * D * T⁻¹)ᴴ = T⁻¹ * D * T⁻¹
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hTinv_herm, hDpsd.isHermitian,
        Matrix.mul_assoc]
    have hWm1 : (W - 1).PosSemidef := by
      have hsub : W - 1 = T⁻¹ * (D - (D - Bᴴ * A⁻¹ * B)) * T⁻¹ := by
        rw [hWdef]
        have hcan : T⁻¹ * (D - Bᴴ * A⁻¹ * B) * T⁻¹ = 1 := by
          rw [← hTT]
          have hassoc : T⁻¹ * (T * T) * T⁻¹ = (T⁻¹ * T) * (T * T⁻¹) := by
            noncomm_ring
          rw [hassoc, hTinvT, hTTinv, mul_one]
        calc T⁻¹ * D * T⁻¹ - 1
            = T⁻¹ * D * T⁻¹ - T⁻¹ * (D - Bᴴ * A⁻¹ * B) * T⁻¹ := by rw [hcan]
          _ = T⁻¹ * (D - (D - Bᴴ * A⁻¹ * B)) * T⁻¹ := by noncomm_ring
      rw [hsub]
      have hDS : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef := by
        have hsub2 : D - (D - Bᴴ * A⁻¹ * B) = Bᴴ * A⁻¹ * B := sub_sub_cancel D _
        rw [hsub2]
        exact (hA.inv.posSemidef).conjTranspose_mul_mul_same B
      have h := hDS.conjTranspose_mul_mul_same T⁻¹
      rwa [hTinv_herm] at h
    -- `det W = 1` and every eigenvalue of `W` is at least `1`, so every
    -- eigenvalue equals `1`, hence `trace W = n` and `W = 1`.
    have hdetW : W.det = 1 := by
      have hDW : D = T * W * T := by
        rw [hWdef]
        have hassoc : T * (T⁻¹ * D * T⁻¹) * T = (T * T⁻¹) * D * (T⁻¹ * T) := by
          noncomm_ring
        rw [hassoc, hTTinv, hTinvT, one_mul, mul_one]
      have hdetD : D.det = (D - Bᴴ * A⁻¹ * B).det * W.det := by
        calc D.det = (T * W * T).det := by rw [hDW]
          _ = T.det * W.det * T.det := by
            rw [Matrix.det_mul (T * W) T, Matrix.det_mul T W]
          _ = T.det * T.det * W.det := by ring
          _ = (T * T).det * W.det := by rw [Matrix.det_mul T T]
          _ = (D - Bᴴ * A⁻¹ * B).det * W.det := by rw [hTT]
      have h1 : (D - Bᴴ * A⁻¹ * B).det * 1 =
          (D - Bᴴ * A⁻¹ * B).det * W.det := by
        rw [mul_one]
        exact hSdet.trans hdetD
      exact (mul_left_cancel₀ hSpos.det_pos.ne' h1).symm
    have heig1 : ∀ i, hW_herm.eigenvalues i = 1 := by
      intro i
      have hprod : ∏ j, hW_herm.eigenvalues j = 1 := by
        have hdet := hW_herm.det_eq_prod_eigenvalues
        rw [hdetW] at hdet
        exact hdet.symm
      have hall : ∀ j, hW_herm.eigenvalues j = 1 := fun j =>
        eq_one_of_prod_eq_one
          (fun j _ => eigenvalues_ge_one_of_posSemidef_sub_one hW_herm hWm1 j) hprod
          (Finset.mem_univ j)
      exact hall i
    have htrace : W.trace = (Fintype.card n : ℝ) := by
      rw [hW_herm.trace_eq_sum_eigenvalues]
      simp [heig1]
    have hW1 : W - 1 = 0 := by
      have htr : (W - 1).trace = 0 := by
        simp [Matrix.trace_sub, htrace, Matrix.trace_one]
      exact hWm1.trace_eq_zero_iff.mp htr
    have hWD : W = 1 := sub_eq_zero.mp hW1
    -- Hence the Schur complement equals `D`, so `Bᴴ * A⁻¹ * B = 0`.
    have hDS : D = D - Bᴴ * A⁻¹ * B := by
      have hDW : D = T * W * T := by
        rw [hWdef]
        have hassoc : T * (T⁻¹ * D * T⁻¹) * T = (T * T⁻¹) * D * (T⁻¹ * T) := by
          noncomm_ring
        rw [hassoc, hTTinv, hTinvT, one_mul, mul_one]
      calc D = T * W * T := hDW
        _ = T * 1 * T := by rw [hWD]
        _ = T * T := by rw [mul_one]
        _ = D - Bᴴ * A⁻¹ * B := hTT
    have hX : Bᴴ * A⁻¹ * B = 0 := by
      have h1 : Bᴴ * A⁻¹ * B = D - (D - Bᴴ * A⁻¹ * B) := (sub_sub_cancel D _).symm
      rw [h1, ← hDS, sub_self]
    -- Hence `B = 0`: write `Bᴴ * A⁻¹ * B = (√(A⁻¹) * B)ᴴ * (√(A⁻¹) * B)`.
    set U := CFC.sqrt (A⁻¹) * B with hUdef
    have hsqrt_sq : CFC.sqrt (A⁻¹) * CFC.sqrt (A⁻¹) = A⁻¹ :=
      CFC.sqrt_mul_sqrt_self (A⁻¹) (ha := hA.inv.posSemidef.nonneg)
    have hU0 : U = 0 := by
      have hUU : Uᴴ * U = Bᴴ * A⁻¹ * B := by
        have hsqrt_herm : (CFC.sqrt (A⁻¹))ᴴ = CFC.sqrt (A⁻¹) := by
          rw [← Matrix.star_eq_conjTranspose]
          exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (A⁻¹))
        rw [hUdef, Matrix.conjTranspose_mul, hsqrt_herm]
        have hassoc : Bᴴ * CFC.sqrt (A⁻¹) * (CFC.sqrt (A⁻¹) * B) =
            Bᴴ * (CFC.sqrt (A⁻¹) * CFC.sqrt (A⁻¹)) * B := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc,
            ← Matrix.mul_assoc (CFC.sqrt (A⁻¹)) (CFC.sqrt (A⁻¹)) B]
        rw [hassoc, hsqrt_sq]
      have hzero : Uᴴ * U = 0 := by rw [hUU, hX]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    have hUnit : IsUnit (CFC.sqrt (A⁻¹)).det := by
      have hdet : (CFC.sqrt (A⁻¹)).det ≠ 0 := by
        have hsq : (CFC.sqrt (A⁻¹)).det ^ 2 = (A⁻¹).det := by
          calc (CFC.sqrt (A⁻¹)).det ^ 2
              = (CFC.sqrt (A⁻¹)).det * (CFC.sqrt (A⁻¹)).det := sq _
            _ = (CFC.sqrt (A⁻¹) * CFC.sqrt (A⁻¹)).det := (Matrix.det_mul _ _).symm
            _ = (A⁻¹).det := by rw [hsqrt_sq]
        exact (pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
          (by rw [hsq]; exact hA.inv.det_pos.ne')
      exact isUnit_iff_ne_zero.mpr hdet
    have hB : B = (CFC.sqrt (A⁻¹))⁻¹ * U := by
      rw [hUdef]
      have hassoc : (CFC.sqrt (A⁻¹))⁻¹ * (CFC.sqrt (A⁻¹) * B) =
          ((CFC.sqrt (A⁻¹))⁻¹ * CFC.sqrt (A⁻¹)) * B := by
        rw [Matrix.mul_assoc]
      rw [hassoc, Matrix.nonsing_inv_mul _ hUnit]
      exact (Matrix.one_mul B).symm
    rw [hB, hU0, Matrix.mul_zero]
  · intro hB0
    subst hB0
    simp

end Matrix

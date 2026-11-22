/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ComplementBundle

/-!
# Genuine local matrix complement-bundle coordinates

The complete inherited functions and topology are retained.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Filter
open TopologicalSpace Topology
open Matrix
open scoped InnerProductSpace
open CategoryTheory.Spectra

/-!
## Genuine matrix reflections for local complement-bundle coordinates

These raw maps use the inherited real matrix topology. Their two-sided Gram
equations and finite-coordinate formulas are proved directly. No cell or
cofibrancy law is assumed.
-/

namespace CategoryTheory.Spectra.OrthogonalComplementBundle

/-- The real coordinate dot product agrees with the genuine Euclidean inner product. -/
theorem euclidean_dot_inner {k : ℕ} (w x : Euclidean k) :
    w.ofLp ⬝ᵥ x.ofLp = ⟪w, x⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]
  rfl

/-- The raw finite rank-one matrix used in the reflection formula. -/
def vectorOuter {k : ℕ} (w : Euclidean k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.vecMulVec w.ofLp w.ofLp

/-- The rank-one matrix has its actual Euclidean norm as its multiplication scalar. -/
theorem vectorOuter_square {k : ℕ} (w : Euclidean k) :
    vectorOuter w * vectorOuter w = (‖w‖ ^ 2) • vectorOuter w := by
  rw [vectorOuter, Matrix.vecMulVec_mul_vecMulVec,
    euclidean_dot_inner, real_inner_self_eq_norm_sq]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply]
  ring

/-- The total raw reflection matrix, with the identity value at the zero vector. -/
def reflectionMatrix {k : ℕ} (w : Euclidean k) : Matrix (Fin k) (Fin k) ℝ :=
  1 - (2 / ‖w‖ ^ 2) • vectorOuter w

/-- The matrix reflection is symmetric in the inherited coordinate dictionary. -/
theorem reflectionMatrix_transpose {k : ℕ} (w : Euclidean k) :
    (reflectionMatrix w).transpose = reflectionMatrix w := by
  simp only [reflectionMatrix, vectorOuter, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

/-- Zero has the genuine identity reflection matrix. -/
theorem reflectionMatrix_zero (k : ℕ) :
    reflectionMatrix (0 : Euclidean k) = 1 := by
  simp [reflectionMatrix]

/-- Each raw reflection matrix is involutive, including the zero-vector branch. -/
theorem reflectionMatrix_square {k : ℕ} (w : Euclidean k) :
    reflectionMatrix w * reflectionMatrix w = 1 := by
  by_cases hw : w = 0
  · rw [hw, reflectionMatrix_zero, Matrix.one_mul]
  have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  let c : ℝ := 2 / ‖w‖ ^ 2
  have hc : c * c * ‖w‖ ^ 2 = c + c := by
    dsimp [c]
    field_simp
    ring
  change (1 - c • vectorOuter w) * (1 - c • vectorOuter w) = 1
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.one_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, vectorOuter_square, smul_smul, hc]
  rw [add_smul]
  abel

/-- The raw reflection is an actual original two-sided orthogonal matrix hom. -/
def reflectionFrame {k : ℕ} (w : Euclidean k) :
    CategoryTheory.Spectra.OrthogonalMatrixHom k k :=
  ⟨reflectionMatrix w, by
    constructor
    · rw [reflectionMatrix_transpose, reflectionMatrix_square]
    · rw [reflectionMatrix_transpose, reflectionMatrix_square]⟩

/-- The genuine linear map of the original reflection matrix. -/
abbrev reflectedVector {k : ℕ} (w : Euclidean k) : Euclidean k →ₗ[ℝ] Euclidean k :=
  matrixLinear (reflectionMatrix w)

/-- The full raw finite reflection function has the actual inner-product formula. -/
theorem reflectedVector_apply {k : ℕ} (w x : Euclidean k) :
    reflectedVector w x = x - (2 * ⟪w, x⟫_ℝ / ‖w‖ ^ 2) • w := by
  apply WithLp.ofLp_injective
  rw [matrixLinear_ofLp]
  change (1 - (2 / ‖w‖ ^ 2) • Matrix.vecMulVec w.ofLp w.ofLp) *ᵥ x.ofLp = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, euclidean_dot_inner]
  simp only [op_smul_eq_smul, WithLp.ofLp_sub, WithLp.ofLp_smul]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply]
  change x.ofLp i - (2 / ‖w‖ ^ 2) * (⟪w, x⟫_ℝ * w.ofLp i) =
    x.ofLp i - (2 * ⟪w, x⟫_ℝ / ‖w‖ ^ 2) * w.ofLp i
  ring

/-- Reflections preserve the actual Euclidean norm, not a replacement discrete topology. -/
theorem reflectedVector_norm {k : ℕ} (w x : Euclidean k) :
    ‖reflectedVector w x‖ = ‖x‖ :=
  matrixLinear_norm (reflectionMatrix w) (reflectionFrame w).property.1 x

/-- A reflection fixes every vector genuinely perpendicular to its defining vector. -/
theorem reflectedVector_perpendicular {k : ℕ} (w x : Euclidean k)
    (h : ⟪w, x⟫_ℝ = 0) : reflectedVector w x = x := by
  rw [reflectedVector_apply, h]
  simp

/-- The actual reflection sends its defining vector to its negative. -/
theorem reflectedVector_self {k : ℕ} (w : Euclidean k) :
    reflectedVector w w = -w := by
  by_cases hw : w = 0
  · rw [hw, reflectedVector_apply]
    simp
  have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  rw [reflectedVector_apply, real_inner_self_eq_norm_sq]
  have hc : 2 * ‖w‖ ^ 2 / ‖w‖ ^ 2 = (2 : ℝ) := by field_simp
  rw [hc, two_smul]
  abel

/-- The complete finite reflection function is its own inverse. -/
theorem reflectedVector_involutive {k : ℕ} (w x : Euclidean k) :
    reflectedVector w (reflectedVector w x) = x := by
  rw [← matrixLinear_mul, reflectionMatrix_square, matrixLinear_one]

/-- Equal-norm vectors are exchanged by their genuine difference reflection. -/
theorem reflectedVector_exchange {k : ℕ} (v w : Euclidean k) (h : ‖v‖ = ‖w‖) :
    reflectedVector (v - w) v = w := by
  have h₁ : reflectedVector (v - w) (v - w) = -(v - w) := reflectedVector_self _
  have hz : ⟪v - w, v + w⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm w v, h]
    ring
  have h₂ : reflectedVector (v - w) (v + w) = v + w :=
    reflectedVector_perpendicular _ _ hz
  suffices reflectedVector (v - w) v + reflectedVector (v - w) v = w + w by
    apply smul_right_injective (Euclidean k) (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [two_smul] using this
  convert congrArg₂ (fun x y : Euclidean k => x + y) h₂ h₁ using 1
  · rw [map_add, map_sub]
    abel
  · abel

/-- Each nonzero vector has a genuine continuous raw reflection formula in a neighborhood. -/
theorem reflectionMatrix_continuousAt {k : ℕ} {w : Euclidean k} (hw : w ≠ 0) :
    ContinuousAt (fun x : Euclidean k => reflectionMatrix x) w := by
  have hc : ContinuousAt (fun x : Euclidean k => (2 : ℝ) / ‖x‖ ^ 2) w :=
    continuousAt_const.div (continuous_norm.continuousAt.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hw))
  have he (i : Fin k) : Continuous (fun x : Euclidean k => x.ofLp i) :=
    (continuous_apply i).comp (EuclideanSpace.equiv (Fin k) ℝ).continuous
  have ho : Continuous (fun x : Euclidean k => vectorOuter x) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (he i).mul (he j)
  exact continuousAt_const.sub (hc.smul ho.continuousAt)

/-- Changing the sign of the defining vector retains the full reflection matrix. -/
theorem reflectionMatrix_neg {k : ℕ} (w : Euclidean k) :
    reflectionMatrix (-w) = reflectionMatrix w := by
  ext i j
  simp [reflectionMatrix, vectorOuter, Matrix.vecMulVec_apply]

/-- Doubling the defining vector retains the actual reflection matrix. -/
theorem reflectionMatrix_two_smul {k : ℕ} (w : Euclidean k) :
    reflectionMatrix ((2 : ℝ) • w) = reflectionMatrix w := by
  by_cases hw : w = 0
  · rw [hw, smul_zero, reflectionMatrix_zero]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  ext i j
  simp only [reflectionMatrix, vectorOuter, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, WithLp.ofLp_smul, Pi.smul_apply, norm_smul]
  norm_num
  field_simp

/-- Two genuine original reflections rotate the first defining vector to the second. -/
def rotationFrame {k : ℕ} (e v : Euclidean k) :
    CategoryTheory.Spectra.OrthogonalMatrixHom k k :=
  CategoryTheory.Spectra.OrthogonalMatrixHom.comp (reflectionFrame e) (reflectionFrame (v + e))

/-- The full original rotation matrix retains late-first composition. -/
theorem rotationFrame_val {k : ℕ} (e v : Euclidean k) :
    (rotationFrame e v).val = reflectionMatrix (v + e) * reflectionMatrix e := rfl

/-- The complete finite rotation function is the two-reflection composite. -/
theorem rotationFrame_apply {k : ℕ} (e v x : Euclidean k) :
    matrixLinear (rotationFrame e v).val x =
      reflectedVector (v + e) (reflectedVector e x) :=
  matrixLinear_mul _ _ x

/-- The rotation exchanges equal-norm vectors, including the antipodal set branch. -/
theorem rotationFrame_exchange {k : ℕ} (e v : Euclidean k) (h : ‖e‖ = ‖v‖) :
    matrixLinear (rotationFrame e v).val e = v := by
  rw [rotationFrame_apply, reflectedVector_self]
  have hx := reflectedVector_exchange (-e) v (by simpa only [norm_neg] using h)
  have hd : -e - v = -(v + e) := by abel
  rw [hd] at hx
  change matrixLinear (reflectionMatrix (-(v + e))) (-e) = v at hx
  rw [reflectionMatrix_neg] at hx
  exact hx

/-- The rotation preserves every previously fixed orthogonal coordinate. -/
theorem rotationFrame_perpendicular {k : ℕ} (e v x : Euclidean k)
    (he : ⟪e, x⟫_ℝ = 0) (hv : ⟪v, x⟫_ℝ = 0) :
    matrixLinear (rotationFrame e v).val x = x := by
  rw [rotationFrame_apply, reflectedVector_perpendicular e x he]
  apply reflectedVector_perpendicular
  rw [inner_add_left, hv, he, add_zero]

/-- The paired reflection is the original identity when both defining vectors agree. -/
theorem rotationFrame_self {k : ℕ} (e : Euclidean k) :
    rotationFrame e e = CategoryTheory.Spectra.OrthogonalMatrixHom.id k := by
  apply Subtype.ext
  change reflectionMatrix (e + e) * reflectionMatrix e = 1
  rw [← two_smul ℝ e, reflectionMatrix_two_smul, reflectionMatrix_square]

/-- The full finite pair of reflections is continuous where both denominators are nonzero. -/
theorem rotationFrame_continuousAt {k : ℕ} {e v : Euclidean k}
    (he : e ≠ 0) (hv : v + e ≠ 0) :
    ContinuousAt (fun p : Euclidean k × Euclidean k => (rotationFrame p.1 p.2).val) (e, v) := by
  have hf : ContinuousAt
      (fun p : Euclidean k × Euclidean k => reflectionMatrix p.1) (e, v) :=
    ContinuousAt.comp' (f := fun p : Euclidean k × Euclidean k => p.1)
      (g := fun x : Euclidean k => reflectionMatrix x) (x := (e, v))
      (reflectionMatrix_continuousAt he) continuous_fst.continuousAt
  have hs : ContinuousAt
      (fun p : Euclidean k × Euclidean k => reflectionMatrix (p.2 + p.1)) (e, v) :=
    ContinuousAt.comp' (f := fun p : Euclidean k × Euclidean k => p.2 + p.1)
      (g := fun x : Euclidean k => reflectionMatrix x) (x := (e, v))
      (reflectionMatrix_continuousAt hv)
      (continuous_snd.continuousAt.add continuous_fst.continuousAt)
  have hm : Continuous (fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ =>
      p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
  change ContinuousAt (fun p : Euclidean k × Euclidean k =>
    reflectionMatrix (p.2 + p.1) * reflectionMatrix p.1) (e, v)
  exact ContinuousAt.comp'
    (f := fun p : Euclidean k × Euclidean k =>
      (reflectionMatrix (p.2 + p.1), reflectionMatrix p.1))
    (g := fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ => p.1 * p.2)
    (x := (e, v)) hm.continuousAt (hs.prodMk hf)

/-- An actual one-sided embedding column in the original Euclidean coordinates. -/
def embeddingColumn {n k : ℕ} (A : EmbeddingMatrix n k) (j : Fin n) : Euclidean k :=
  WithLp.toLp 2 (fun i : Fin k => A.val i j)

/-- The inherited column is the actual source matrix applied to the original basis vector. -/
theorem embeddingColumn_eq_matrixLinear_basis {n k : ℕ} (A : EmbeddingMatrix n k) (j : Fin n) :
    embeddingColumn A j = matrixLinear A.val (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  apply WithLp.ofLp_injective
  rw [matrixLinear_ofLp, EuclideanSpace.basisFun_apply]
  change (fun i : Fin k => A.val i j) = A.val *ᵥ Pi.single j 1
  rw [Matrix.mulVec_single_one]
  rfl

/-- The columns retain the actual inherited orthonormal Gram equation. -/
theorem embeddingColumn_inner {n k : ℕ} (A : EmbeddingMatrix n k) (i j : Fin n) :
    ⟪embeddingColumn A i, embeddingColumn A j⟫_ℝ = if i = j then 1 else 0 := by
  rw [embeddingColumn_eq_matrixLinear_basis, embeddingColumn_eq_matrixLinear_basis]
  exact (orthonormal_iff_ite.mp (embeddingMatrix_columns_orthonormal A)) i j

/-- Each genuine embedding column has unit Euclidean norm. -/
theorem embeddingColumn_norm {n k : ℕ} (A : EmbeddingMatrix n k) (j : Fin n) :
    ‖embeddingColumn A j‖ = 1 := by
  rw [embeddingColumn_eq_matrixLinear_basis]
  exact (embeddingMatrix_columns_orthonormal A).norm_eq_one j

/-- A one-sided embedding column is nonzero in the actual finite Euclidean space. -/
theorem embeddingColumn_ne_zero {n k : ℕ} (A : EmbeddingMatrix n k) (j : Fin n) :
    embeddingColumn A j ≠ 0 := by
  intro h
  have hn := embeddingColumn_norm A j
  rw [h, norm_zero] at hn
  norm_num at hn

/-- The actual finite embedding columns vary continuously in the inherited matrix topology. -/
theorem embeddingColumn_continuous {n k : ℕ} (j : Fin n) :
    Continuous (fun A : EmbeddingMatrix n k => embeddingColumn A j) := by
  have hc : Continuous (fun A : EmbeddingMatrix n k => fun i : Fin k => A.val i j) := by
    apply continuous_pi
    intro i
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp hc

/-- Successive actual paired reflections align the columns without a continuous global choice. -/
def frameTransportAux {n k : ℕ} (A₀ A : EmbeddingMatrix n k) :
    ℕ → CategoryTheory.Spectra.OrthogonalMatrixHom k k
  | 0 => CategoryTheory.Spectra.OrthogonalMatrixHom.id k
  | m + 1 => if hm : m < n then
      CategoryTheory.Spectra.OrthogonalMatrixHom.comp (frameTransportAux A₀ A m)
        (rotationFrame
          (matrixLinear (frameTransportAux A₀ A m).val (embeddingColumn A₀ ⟨m, hm⟩))
          (embeddingColumn A ⟨m, hm⟩))
    else frameTransportAux A₀ A m

/-- The full original matrix function of one finite transport step. -/
theorem frameTransportAux_succ_apply {n k : ℕ} (A₀ A : EmbeddingMatrix n k)
    (m : ℕ) (hm : m < n) (x : Euclidean k) :
    matrixLinear (frameTransportAux A₀ A (m + 1)).val x =
      matrixLinear (rotationFrame
        (matrixLinear (frameTransportAux A₀ A m).val (embeddingColumn A₀ ⟨m, hm⟩))
        (embeddingColumn A ⟨m, hm⟩)).val
        (matrixLinear (frameTransportAux A₀ A m).val x) := by
  rw [frameTransportAux, dite_eq_left hm]
  exact matrixLinear_mul _ _ x

/-- Every completed finite transport step retains all already aligned actual columns. -/
theorem frameTransportAux_columns {n k : ℕ} (A₀ A : EmbeddingMatrix n k) (m : ℕ) :
    ∀ i : Fin n, i.val < m →
      matrixLinear (frameTransportAux A₀ A m).val (embeddingColumn A₀ i) = embeddingColumn A i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi
    by_cases hm : m < n
    · let j : Fin n := ⟨m, hm⟩
      rw [frameTransportAux_succ_apply A₀ A m hm]
      by_cases hip : i.val < m
      · rw [ih i hip]
        apply rotationFrame_perpendicular
        · rw [← ih i hip, matrixLinear_inner _ (frameTransportAux A₀ A m).property.1,
            embeddingColumn_inner]
          exact ite_eq_right (by
            intro hji
            have hv := congrArg Fin.val hji
            change m = i.val at hv
            omega)
        · rw [embeddingColumn_inner]
          exact ite_eq_right (by
            intro hji
            have hv := congrArg Fin.val hji
            change m = i.val at hv
            omega)
      · have hij : i = j := Fin.ext (by simp only [j]; omega)
        rw [hij]
        apply rotationFrame_exchange
        rw [matrixLinear_norm _ (frameTransportAux A₀ A m).property.1,
          embeddingColumn_norm, embeddingColumn_norm]
    · rw [frameTransportAux, dite_eq_right hm]
      exact ih i (by omega)

/-- The chosen reference embedding has the genuine identity transport at every step. -/
theorem frameTransportAux_self {n k : ℕ} (A : EmbeddingMatrix n k) (m : ℕ) :
    frameTransportAux A A m = CategoryTheory.Spectra.OrthogonalMatrixHom.id k := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : m < n
    · rw [frameTransportAux, dite_eq_left hm, ih]
      change CategoryTheory.Spectra.OrthogonalMatrixHom.comp
        (CategoryTheory.Spectra.OrthogonalMatrixHom.id k)
        (rotationFrame (matrixLinear (1 : Matrix (Fin k) (Fin k) ℝ)
          (embeddingColumn A ⟨m, hm⟩)) (embeddingColumn A ⟨m, hm⟩)) = _
      rw [matrixLinear_one, rotationFrame_self]
      apply Subtype.ext
      exact Matrix.one_mul 1
    · rw [frameTransportAux, dite_eq_right hm, ih]

/-- The actual total finite orthogonal transport between inherited Stiefel embeddings. -/
def frameTransport {n k : ℕ} (A₀ A : EmbeddingMatrix n k) :
    CategoryTheory.Spectra.OrthogonalMatrixHom k k := frameTransportAux A₀ A n

/-- The finite transport sends the entire one-sided embedding matrix to the target matrix. -/
theorem frameTransport_matrix {n k : ℕ} (A₀ A : EmbeddingMatrix n k) :
    (frameTransport A₀ A).val * A₀.val = A.val := by
  ext i j
  have h := frameTransportAux_columns A₀ A n j j.isLt
  have hi := congrArg (fun x : Euclidean k => x.ofLp i) h
  rw [matrixLinear_ofLp] at hi
  exact hi

/-- The genuine matrix action is jointly continuous in the matrix and finite vector. -/
theorem matrixLinear_joint_continuous (m k : ℕ) :
    Continuous (fun p : Matrix (Fin k) (Fin m) ℝ × Euclidean m => matrixLinear p.1 p.2) := by
  have hm : Continuous
      (fun p : Matrix (Fin k) (Fin m) ℝ × Euclidean m => p.1 *ᵥ p.2.ofLp) :=
    continuous_fst.matrix_mulVec
    ((EuclideanSpace.equiv (Fin m) ℝ).continuous.comp continuous_snd)
  exact (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp hm

/-- The actual non-antipodal denominators of the first finite transport steps. -/
def frameTransportRegular {n k : ℕ} (A₀ A : EmbeddingMatrix n k) (m : ℕ) : Prop :=
  ∀ j : Fin n, j.val < m → embeddingColumn A j +
    matrixLinear (frameTransportAux A₀ A j.val).val (embeddingColumn A₀ j) ≠ 0

/-- A genuine regular transport prefix remains regular on every shorter prefix. -/
theorem frameTransportRegular_mono {n k : ℕ} (A₀ A : EmbeddingMatrix n k)
    {m l : ℕ} (h : m ≤ l) (hr : frameTransportRegular A₀ A l) :
    frameTransportRegular A₀ A m := fun j hj => hr j (lt_of_lt_of_le hj h)

/-- No denominator is imposed on the zero-step transport. -/
theorem frameTransportRegular_zero {n k : ℕ} (A₀ A : EmbeddingMatrix n k) :
    frameTransportRegular A₀ A 0 := by
  intro j hj
  omega

/-- Each actual finite regularity condition adds exactly its next nonzero denominator. -/
theorem frameTransportRegular_succ_iff {n k : ℕ} (A₀ A : EmbeddingMatrix n k)
    (m : ℕ) (hm : m < n) :
    frameTransportRegular A₀ A (m + 1) ↔ frameTransportRegular A₀ A m ∧
      embeddingColumn A ⟨m, hm⟩ +
        matrixLinear (frameTransportAux A₀ A m).val (embeddingColumn A₀ ⟨m, hm⟩) ≠ 0 := by
  constructor
  · intro h
    exact ⟨frameTransportRegular_mono A₀ A (Nat.le_succ m) h,
      h ⟨m, hm⟩ (Nat.lt_succ_self m)⟩
  · rintro ⟨h, hnext⟩ j hj
    by_cases hip : j.val < m
    · exact h j hip
    · have hij : j = ⟨m, hm⟩ := Fin.ext (by change j.val = m; omega)
      rw [hij]
      exact hnext

/-- The reference embedding lies in every genuine regularity domain. -/
theorem frameTransportRegular_self {n k : ℕ} (A : EmbeddingMatrix n k) (m : ℕ) :
    frameTransportRegular A A m := by
  intro j hj
  rw [frameTransportAux_self]
  change embeddingColumn A j + matrixLinear (1 : Matrix (Fin k) (Fin k) ℝ)
    (embeddingColumn A j) ≠ 0
  rw [matrixLinear_one, ← two_smul ℝ]
  exact smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (embeddingColumn_ne_zero A j)

/-- Each whole finite transport matrix is continuous at every genuinely regular point. -/
theorem frameTransportAux_continuousAt {n k : ℕ} (A₀ : EmbeddingMatrix n k) (m : ℕ)
    (A : EmbeddingMatrix n k) (hA : frameTransportRegular A₀ A m) :
    ContinuousAt (fun B : EmbeddingMatrix n k => (frameTransportAux A₀ B m).val) A := by
  induction m with
  | zero => exact continuousAt_const
  | succ m ih =>
    by_cases hm : m < n
    · have hp := (frameTransportRegular_succ_iff A₀ A m hm).mp hA
      have hq := ih hp.1
      let j : Fin n := ⟨m, hm⟩
      let ef : EmbeddingMatrix n k → Euclidean k := fun B =>
        matrixLinear (frameTransportAux A₀ B m).val (embeddingColumn A₀ j)
      let vf : EmbeddingMatrix n k → Euclidean k := fun B => embeddingColumn B j
      have he : ContinuousAt ef A :=
        ContinuousAt.comp'
          (f := fun B : EmbeddingMatrix n k =>
            ((frameTransportAux A₀ B m).val, embeddingColumn A₀ j))
          (g := fun p : Matrix (Fin k) (Fin k) ℝ × Euclidean k => matrixLinear p.1 p.2)
          (x := A) (matrixLinear_joint_continuous k k).continuousAt
          (hq.prodMk continuousAt_const)
      have hv : ContinuousAt vf A := (embeddingColumn_continuous j).continuousAt
      have hen : ef A ≠ 0 := by
        intro hzero
        have hn := matrixLinear_norm (frameTransportAux A₀ A m).val
          (frameTransportAux A₀ A m).property.1 (embeddingColumn A₀ j)
        change ‖ef A‖ = ‖embeddingColumn A₀ j‖ at hn
        rw [hzero, norm_zero, embeddingColumn_norm] at hn
        norm_num at hn
      have hsum : vf A + ef A ≠ 0 := hp.2
      have hr : ContinuousAt
          (fun B : EmbeddingMatrix n k => (rotationFrame (ef B) (vf B)).val) A :=
        ContinuousAt.comp' (f := fun B : EmbeddingMatrix n k => (ef B, vf B))
          (g := fun p : Euclidean k × Euclidean k => (rotationFrame p.1 p.2).val)
          (x := A) (rotationFrame_continuousAt hen hsum) (he.prodMk hv)
      have hmul : Continuous
          (fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ => p.1 * p.2) :=
        continuous_fst.matrix_mul continuous_snd
      have ht : ContinuousAt (fun B : EmbeddingMatrix n k =>
          (rotationFrame (ef B) (vf B)).val * (frameTransportAux A₀ B m).val) A :=
        ContinuousAt.comp'
          (f := fun B : EmbeddingMatrix n k =>
            ((rotationFrame (ef B) (vf B)).val, (frameTransportAux A₀ B m).val))
          (g := fun p : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ => p.1 * p.2)
          (x := A) hmul.continuousAt (hr.prodMk hq)
      convert ht using 1
      funext B
      rw [frameTransportAux, dite_eq_left hm]
      rfl
    · have hp : frameTransportRegular A₀ A m :=
        frameTransportRegular_mono A₀ A (Nat.le_succ m) hA
      convert ih hp using 1
      funext B
      rw [frameTransportAux, dite_eq_right hm]

/-- The actual regular matrix-transport domain is open in the inherited Stiefel topology. -/
theorem frameTransportRegular_isOpen {n k : ℕ} (A₀ : EmbeddingMatrix n k) (m : ℕ) :
    IsOpen {A : EmbeddingMatrix n k | frameTransportRegular A₀ A m} := by
  induction m with
  | zero =>
    have hu : {A : EmbeddingMatrix n k | frameTransportRegular A₀ A 0} = Set.univ := by
      ext A
      exact iff_true_intro (frameTransportRegular_zero A₀ A)
    rw [hu]
    exact isOpen_univ
  | succ m ih =>
    by_cases hm : m < n
    · apply isOpen_iff_mem_nhds.mpr
      intro A hA
      have hp := (frameTransportRegular_succ_iff A₀ A m hm).mp hA
      let j : Fin n := ⟨m, hm⟩
      let ef : EmbeddingMatrix n k → Euclidean k := fun B =>
        matrixLinear (frameTransportAux A₀ B m).val (embeddingColumn A₀ j)
      let vf : EmbeddingMatrix n k → Euclidean k := fun B => embeddingColumn B j
      have hq := frameTransportAux_continuousAt A₀ m A hp.1
      have he : ContinuousAt ef A :=
        ContinuousAt.comp'
          (f := fun B : EmbeddingMatrix n k =>
            ((frameTransportAux A₀ B m).val, embeddingColumn A₀ j))
          (g := fun p : Matrix (Fin k) (Fin k) ℝ × Euclidean k => matrixLinear p.1 p.2)
          (x := A) (matrixLinear_joint_continuous k k).continuousAt
          (hq.prodMk continuousAt_const)
      have hv : ContinuousAt vf A := (embeddingColumn_continuous j).continuousAt
      have hs : ContinuousAt (fun B : EmbeddingMatrix n k => vf B + ef B) A := hv.add he
      have hn : {z : Euclidean k | z ≠ 0} ∈ 𝓝 (vf A + ef A) :=
        isClosed_singleton.isOpen_compl.mem_nhds hp.2
      have hbefore := ih.mem_nhds hp.1
      have hnext := hs.preimage_mem_nhds hn
      apply Filter.mem_of_superset (Filter.inter_mem hbefore hnext)
      intro B hB
      exact (frameTransportRegular_succ_iff A₀ B m hm).mpr ⟨hB.1, hB.2⟩
    · have heq : {A : EmbeddingMatrix n k | frameTransportRegular A₀ A (m + 1)} =
          {A : EmbeddingMatrix n k | frameTransportRegular A₀ A m} := by
        ext A
        constructor
        · exact frameTransportRegular_mono A₀ A (Nat.le_succ m)
        · intro h j hj
          exact h j (by omega)
      rw [heq]
      exact ih

/-- The actual open domain of the whole finite frame transport. -/
def frameTransportDomain {n k : ℕ} (A₀ : EmbeddingMatrix n k) : Set (EmbeddingMatrix n k) :=
  {A | frameTransportRegular A₀ A n}

/-- Every reference frame has an open inherited Stiefel neighborhood for transport. -/
theorem frameTransportDomain_isOpen {n k : ℕ} (A₀ : EmbeddingMatrix n k) :
    IsOpen (frameTransportDomain A₀) := frameTransportRegular_isOpen A₀ n

/-- The reference frame is contained in its actual open transport neighborhood. -/
theorem frameTransportDomain_self {n k : ℕ} (A₀ : EmbeddingMatrix n k) :
    A₀ ∈ frameTransportDomain A₀ := frameTransportRegular_self A₀ n

/-- The complete finite transport matrix is continuous throughout its actual open domain. -/
theorem frameTransport_continuousOn {n k : ℕ} (A₀ : EmbeddingMatrix n k) :
    ContinuousOn (fun A : EmbeddingMatrix n k => (frameTransport A₀ A).val)
      (frameTransportDomain A₀) := fun A hA =>
  (frameTransportAux_continuousAt A₀ n A hA).continuousWithinAt

/-- The genuine full frame over a variable base obtained from a fixed reference frame. -/
def localChartFrame (n k a : ℕ) (g : Frame n k a) (A : EmbeddingMatrix n k) : Frame n k a :=
  targetFrame (n := n) (k := k) (l := k) (a := a)
    (frameTransport (frameBase (n := n) (k := k) (a := a) g) A) g

/-- The complete variable frame retains exactly its inherited one-sided base. -/
theorem localChartFrame_base (n k a : ℕ) (g : Frame n k a) (A : EmbeddingMatrix n k) :
    frameBase (localChartFrame n k a g A) = A := by
  apply embeddingMatrix_ext
  change finalPart (targetFrame _ g) = A.val
  rw [targetFrame_finalPart]
  exact frameTransport_matrix (frameBase (n := n) (k := k) (a := a) g) A

/-- The entire finite coordinate function on the actual complement-bundle total space. -/
def localBundleCoordinates (n k a : ℕ) (g : Frame n k a) (p : ComplementBundle n k) :
    EmbeddingMatrix n k × Euclidean a :=
  (bundleBase p, recover n k a (localChartFrame n k a g (bundleBase p), p))

/-- The full inverse coordinate function uses the genuine original coefficient-first frame. -/
def localBundleVector (n k a : ℕ) (g : Frame n k a)
    (q : EmbeddingMatrix n k × Euclidean a) : ComplementBundle n k :=
  rawMap n k a (localChartFrame n k a g q.1, q.2)

/-- The full inverse coordinate function has the original prescribed matrix base. -/
theorem localBundleVector_base (n k a : ℕ) (g : Frame n k a)
    (q : EmbeddingMatrix n k × Euclidean a) :
    bundleBase (localBundleVector n k a g q) = q.1 := by
  rw [localBundleVector, rawMap_base, localChartFrame_base]

/-- Every entire finite coordinate pair is reconstructed without any completion choice. -/
theorem localBundleCoordinates_vector (n k a : ℕ) (g : Frame n k a)
    (q : EmbeddingMatrix n k × Euclidean a) :
    localBundleCoordinates n k a g (localBundleVector n k a g q) = q := by
  change (bundleBase (localBundleVector n k a g q),
    recover n k a (localChartFrame n k a g (bundleBase (localBundleVector n k a g q)),
      localBundleVector n k a g q)) = q
  rw [localBundleVector_base]
  change (q.1, recover n k a
    (localChartFrame n k a g q.1, rawMap n k a (localChartFrame n k a g q.1, q.2))) = q
  rw [recover_rawMap]

/-- The genuine inverse coordinates reconstruct every total-space point
in the inherited topology. -/
theorem localBundleVector_coordinates (n k a : ℕ) (g : Frame n k a)
    (p : ComplementBundle n k) :
    localBundleVector n k a g (localBundleCoordinates n k a g p) = p := by
  apply rawMap_recover
  exact congrArg Subtype.val (localChartFrame_base n k a g (bundleBase p))

/-- The full bundle coordinate map retains the actual Euclidean fiber norm. -/
theorem localBundleCoordinates_norm (n k a : ℕ) (g : Frame n k a)
    (p : ComplementBundle n k) :
    ‖(localBundleCoordinates n k a g p).2‖ = ‖bundleVector p‖ := by
  have h := congrArg (fun q : ComplementBundle n k => ‖bundleVector q‖)
    (localBundleVector_coordinates n k a g p)
  change ‖bundleVector (rawMap n k a
    (localChartFrame n k a g (bundleBase p), (localBundleCoordinates n k a g p).2))‖ = _ at h
  rw [rawMap_norm] at h
  exact h

/-- The actual inherited open Stiefel base of the fixed-reference frame chart. -/
abbrev BundleChartBase (n k a : ℕ) (g : Frame n k a) :=
  {A : EmbeddingMatrix n k //
    A ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)}

/-- The inherited restriction of the complement bundle to its actual open chart base. -/
abbrev BundleChartSpace (n k a : ℕ) (g : Frame n k a) :=
  {p : ComplementBundle n k //
    bundleBase p ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)}

/-- The whole reference-frame family is continuous on the actual inherited open chart base. -/
theorem localChartFrame_continuous (n k a : ℕ) (g : Frame n k a) :
    Continuous (fun A : BundleChartBase n k a g => localChartFrame n k a g A.val) := by
  have hq : Continuous (fun A : BundleChartBase n k a g =>
      (frameTransport (frameBase (n := n) (k := k) (a := a) g) A.val).val) := by
    apply continuous_iff_continuousAt.mpr
    intro A
    exact ContinuousAt.comp' (f := fun B : BundleChartBase n k a g => B.val)
      (g := fun B : EmbeddingMatrix n k =>
        (frameTransport (frameBase (n := n) (k := k) (a := a) g) B).val)
      (x := A)
      (frameTransportAux_continuousAt (frameBase (n := n) (k := k) (a := a) g) n A.val A.property)
      continuous_subtype_val.continuousAt
  apply Continuous.subtype_mk
  exact hq.matrix_mul continuous_const

/-- The full continuous local bundle coordinate function, with the actual restricted base. -/
def bundleChartTo (n k a : ℕ) (g : Frame n k a) (p : BundleChartSpace n k a g) :
    BundleChartBase n k a g × Euclidean a :=
  (⟨bundleBase p.val, p.property⟩,
    recover n k a (localChartFrame n k a g (bundleBase p.val), p.val))

/-- The full local inverse coordinate function into the actual inherited total-space restriction. -/
def bundleChartFrom (n k a : ℕ) (g : Frame n k a)
    (q : BundleChartBase n k a g × Euclidean a) : BundleChartSpace n k a g :=
  ⟨localBundleVector n k a g (q.1.val, q.2), by
    rw [localBundleVector_base]
    exact q.1.property⟩

/-- The complete local inverse function reconstructs each entire bundle-chart point. -/
theorem bundleChartFrom_to (n k a : ℕ) (g : Frame n k a) (p : BundleChartSpace n k a g) :
    bundleChartFrom n k a g (bundleChartTo n k a g p) = p := by
  apply Subtype.ext
  exact localBundleVector_coordinates n k a g p.val

/-- The complete local coordinate function reconstructs every base/coefficient pair. -/
theorem bundleChartTo_from (n k a : ℕ) (g : Frame n k a)
    (q : BundleChartBase n k a g × Euclidean a) :
    bundleChartTo n k a g (bundleChartFrom n k a g q) = q := by
  apply Prod.ext
  · apply Subtype.ext
    exact localBundleVector_base n k a g (q.1.val, q.2)
  · change (localBundleCoordinates n k a g (localBundleVector n k a g (q.1.val, q.2))).2 = q.2
    exact congrArg (fun p : EmbeddingMatrix n k × Euclidean a => p.2)
      (localBundleCoordinates_vector n k a g (q.1.val, q.2))

/-- The entire local finite coordinate function is continuous in the actual total-space topology. -/
theorem bundleChartTo_continuous (n k a : ℕ) (g : Frame n k a) :
    Continuous (bundleChartTo n k a g) := by
  have hb : Continuous (fun p : BundleChartSpace n k a g =>
      (⟨bundleBase p.val, p.property⟩ : BundleChartBase n k a g)) := by
    apply Continuous.subtype_mk
    exact continuous_bundleBase.comp continuous_subtype_val
  have hg := (localChartFrame_continuous n k a g).comp hb
  exact hb.prodMk ((recover_continuous n k a).comp (hg.prodMk continuous_subtype_val))

/-- The whole local inverse function is continuous
for the original inherited matrix/vector topology. -/
theorem bundleChartFrom_continuous (n k a : ℕ) (g : Frame n k a) :
    Continuous (bundleChartFrom n k a g) := by
  apply Continuous.subtype_mk
  exact (rawMap_continuous n k a).comp
    (((localChartFrame_continuous n k a g).comp continuous_fst).prodMk continuous_snd)

/-- The genuine local complement-bundle homeomorphism with its complete two finite functions. -/
def bundleChartHomeomorph (n k a : ℕ) (g : Frame n k a) :
    BundleChartSpace n k a g ≃ₜ BundleChartBase n k a g × Euclidean a where
  toFun := bundleChartTo n k a g
  invFun := bundleChartFrom n k a g
  left_inv := bundleChartFrom_to n k a g
  right_inv := bundleChartTo_from n k a g
  continuous_toFun := bundleChartTo_continuous n k a g
  continuous_invFun := bundleChartFrom_continuous n k a g

/-- The entire local homeomorphism retains the actual norm
needed for disk and sphere restrictions. -/
theorem bundleChartHomeomorph_norm (n k a : ℕ) (g : Frame n k a)
    (p : BundleChartSpace n k a g) :
    ‖(bundleChartHomeomorph n k a g p).2‖ = ‖bundleVector p.val‖ :=
  localBundleCoordinates_norm n k a g p.val

/-- Every actual Stiefel embedding has a genuine local chart in the residual coefficient grade. -/
theorem exists_bundleChart_reference (n k : ℕ) (A : EmbeddingMatrix n k) :
    ∃ g : Frame n k (k - n), frameBase (n := n) (k := k) (a := k - n) g = A ∧
      A ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := k - n) g) := by
  obtain ⟨g, hg⟩ := exists_frame_completion n k (k - n)
    (Nat.sub_add_cancel (embeddingMatrix_dimension A)) A
  have hb : frameBase (n := n) (k := k) (a := k - n) g = A := Subtype.ext hg
  refine ⟨g, hb, ?_⟩
  rw [← hb]
  exact frameTransportDomain_self (frameBase (n := n) (k := k) (a := k - n) g)

/-- The inherited local total space restricted by any genuine fiber norm condition. -/
abbrev BundleChartNormSpace (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop) :=
  {p : BundleChartSpace n k a g // P (‖bundleVector p.val‖)}

/-- The full local coefficient function restricted to its actual norm fiber. -/
def bundleNormChartTo (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop)
    (p : BundleChartNormSpace n k a g P) :
    BundleChartBase n k a g × {x : Euclidean a // P (‖x‖)} :=
  ((bundleChartTo n k a g p.val).1, ⟨(bundleChartTo n k a g p.val).2, by
    change P (‖(bundleChartHomeomorph n k a g p.val).2‖)
    rw [bundleChartHomeomorph_norm]
    exact p.property⟩)

/-- The complete norm-restricted inverse uses the actual original finite frame function. -/
def bundleNormChartFrom (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop)
    (q : BundleChartBase n k a g × {x : Euclidean a // P (‖x‖)}) :
    BundleChartNormSpace n k a g P :=
  ⟨bundleChartFrom n k a g (q.1, q.2.val), by
    change P (‖bundleVector (rawMap n k a (localChartFrame n k a g q.1.val, q.2.val))‖)
    rw [rawMap_norm]
    exact q.2.property⟩

/-- The norm-restricted inverse reconstructs the entire actual local total-space point. -/
theorem bundleNormChartFrom_to (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop)
    (p : BundleChartNormSpace n k a g P) :
    bundleNormChartFrom n k a g P (bundleNormChartTo n k a g P p) = p := by
  apply Subtype.ext
  exact bundleChartFrom_to n k a g p.val

/-- Every whole local base/coefficient pair is recovered with its actual norm condition. -/
theorem bundleNormChartTo_from (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop)
    (q : BundleChartBase n k a g × {x : Euclidean a // P (‖x‖)}) :
    bundleNormChartTo n k a g P (bundleNormChartFrom n k a g P q) = q := by
  have h := bundleChartTo_from n k a g (q.1, q.2.val)
  apply Prod.ext
  · change (bundleChartTo n k a g (bundleChartFrom n k a g (q.1, q.2.val))).1 = q.1
    exact congrArg (fun p : BundleChartBase n k a g × Euclidean a => p.1) h
  · apply Subtype.ext
    change (bundleChartTo n k a g (bundleChartFrom n k a g (q.1, q.2.val))).2 = q.2.val
    exact congrArg (fun p : BundleChartBase n k a g × Euclidean a => p.2) h

/-- The whole norm-restricted coefficient function is continuous for the inherited subspaces. -/
theorem bundleNormChartTo_continuous (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop) :
    Continuous (bundleNormChartTo n k a g P) := by
  have hc : Continuous (fun p : BundleChartNormSpace n k a g P =>
      bundleChartTo n k a g p.val) :=
    (bundleChartTo_continuous n k a g).comp continuous_subtype_val
  apply Continuous.prodMk
  · exact continuous_fst.comp hc
  · apply Continuous.subtype_mk
    exact continuous_snd.comp hc

/-- The complete inverse on each actual norm fiber is continuous in the inherited topology. -/
theorem bundleNormChartFrom_continuous (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop) :
    Continuous (bundleNormChartFrom n k a g P) := by
  apply Continuous.subtype_mk
  exact (bundleChartFrom_continuous n k a g).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- The actual norm-fiber restriction of the complete local complement-bundle homeomorphism. -/
def bundleNormChartHomeomorph (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop) :
    BundleChartNormSpace n k a g P ≃ₜ
      BundleChartBase n k a g × {x : Euclidean a // P (‖x‖)} where
  toFun := bundleNormChartTo n k a g P
  invFun := bundleNormChartFrom n k a g P
  left_inv := bundleNormChartFrom_to n k a g P
  right_inv := bundleNormChartTo_from n k a g P
  continuous_toFun := bundleNormChartTo_continuous n k a g P
  continuous_invFun := bundleNormChartFrom_continuous n k a g P

/-- The actual norm-first local total space, including the original disk and sphere bundles. -/
abbrev BundleNormFirstChartSpace (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop) :=
  {p : {q : ComplementBundle n k // P (‖bundleVector q‖)} //
    bundleBase p.val ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)}

/-- Swapping the actual base/norm subtype order preserves both inherited topologies. -/
def bundleChartNormSwapHomeomorph (n k a : ℕ) (g : Frame n k a) (P : ℝ → Prop) :
    BundleNormFirstChartSpace n k a g P ≃ₜ BundleChartNormSpace n k a g P where
  toFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  invFun p := ⟨⟨p.val.val, p.property⟩, p.val.property⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The entire actual disk bundle is locally the original base times a unit coefficient disk. -/
def diskBundleChartHomeomorph (n k a : ℕ) (g : Frame n k a) :
    {p : DiskBundle n k //
      bundleBase p.val ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)} ≃ₜ
      BundleChartBase n k a g × {x : Euclidean a // ‖x‖ ≤ 1} :=
  (bundleChartNormSwapHomeomorph n k a g (fun r => r ≤ 1)).trans
    (bundleNormChartHomeomorph n k a g (fun r => r ≤ 1))

/-- The entire actual sphere bundle is locally the original base
times the unit coefficient sphere. -/
def sphereBundleChartHomeomorph (n k a : ℕ) (g : Frame n k a) :
    {p : SphereBundle n k //
      bundleBase p.val ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)} ≃ₜ
      BundleChartBase n k a g × {x : Euclidean a // ‖x‖ = 1} :=
  (bundleChartNormSwapHomeomorph n k a g (fun r => r = 1)).trans
    (bundleNormChartHomeomorph n k a g (fun r => r = 1))

/-- The original sphere-to-disk function retains the actual open chart domain. -/
def sphereDiskChartInclusion (n k a : ℕ) (g : Frame n k a)
    (p : {q : SphereBundle n k //
      bundleBase q.val ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)}) :
    {q : DiskBundle n k //
      bundleBase q.val ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)} :=
  ⟨sphereToDisk n k p.val, p.property⟩

/-- The complete unit coefficient sphere-to-disk function has the same finite vector. -/
def coefficientSphereToDisk (a : ℕ) (x : {v : Euclidean a // ‖v‖ = 1}) :
    {v : Euclidean a // ‖v‖ ≤ 1} := ⟨x.val, le_of_eq x.property⟩

/-- The actual entire disk/sphere bundle charts intertwine the original boundary inclusion. -/
theorem sphereDiskChart_square (n k a : ℕ) (g : Frame n k a)
    (p : {q : SphereBundle n k //
      bundleBase q.val ∈ frameTransportDomain (frameBase (n := n) (k := k) (a := a) g)}) :
    diskBundleChartHomeomorph n k a g (sphereDiskChartInclusion n k a g p) =
      ((sphereBundleChartHomeomorph n k a g p).1,
        coefficientSphereToDisk a (sphereBundleChartHomeomorph n k a g p).2) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl


end CategoryTheory.Spectra.OrthogonalComplementBundle

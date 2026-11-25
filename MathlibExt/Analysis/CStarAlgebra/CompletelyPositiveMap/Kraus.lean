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

public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Basic
public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Choi
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra Kronecker ComplexOrder

namespace CompletelyPositiveMap

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Single-Kraus linear map.** Let `n` be a finite index type and `m` any index type. A complex
rectangular matrix `K : Matrix m n ℂ` defines the complex-linear map `X ↦ K X Kᴴ` from `Matrix n n
ℂ` to `Matrix m m ℂ`. -/
noncomputable def singleKrausLinearMap (K : Matrix m n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun X := K * X * Kᴴ
  map_add' X Y := by
    calc
      K * (X + Y) * Kᴴ = (K * (X + Y)) * Kᴴ := rfl
      _ = (K * X + K * Y) * Kᴴ := by rw [Matrix.mul_add]
      _ = K * X * Kᴴ + K * Y * Kᴴ := by rw [Matrix.add_mul]
  map_smul' c X := by
    calc
      K * (c • X) * Kᴴ = (K * (c • X)) * Kᴴ := rfl
      _ = (c • (K * X)) * Kᴴ := by rw [Matrix.mul_smul]
      _ = c • ((K * X) * Kᴴ) := by rw [Matrix.smul_mul]
      _ = c • (K * X * Kᴴ) := rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
@[simp]
theorem singleKrausLinearMap_apply (K : Matrix m n ℂ) (X : Matrix n n ℂ) :
    singleKrausLinearMap K X = K * X * Kᴴ :=
  rfl

-- Private helpers for the amplification argument.
-- These are intentionally private; the public API is `singleKraus` itself.

-- Minimal private local wrapper for `Matrix.comp` as a `StarAlgEquiv` over `ℂ`,
-- specialized to the rectangular Kraus setting. Built from `Matrix.compAlgEquiv`,
-- `Matrix.conjTranspose_comp'` (hence `Matrix.conjTranspose_comp`) and
-- `StarAlgEquiv.ofAlgEquiv`.
private noncomputable def compStarAlgEquivLocal (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] :
    Matrix I I (Matrix J J ℂ) ≃⋆ₐ[ℂ] Matrix (I × J) (I × J) ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.compAlgEquiv I J ℂ ℂ) fun M =>
    (Matrix.conjTranspose_comp' (M := M)).symm

private noncomputable def flatEquivInput (k : ℕ) :
    CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ) ≃⋆ₐ[ℂ] Matrix (Fin k × n) (Fin k × n) ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin k) (A := Matrix n n ℂ)).symm.trans
    (compStarAlgEquivLocal (Fin k) n)

private noncomputable def flatEquivOutput (k : ℕ) :
    CStarMatrix (Fin k) (Fin k) (Matrix m m ℂ) ≃⋆ₐ[ℂ] Matrix (Fin k × m) (Fin k × m) ℂ :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin k) (A := Matrix m m ℂ)).symm.trans
    (compStarAlgEquivLocal (Fin k) m)

private noncomputable def krausAmplification (k : ℕ) (K : Matrix m n ℂ) :
    Matrix (Fin k × m) (Fin k × n) ℂ :=
  (1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ K

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private lemma krausAmplification_apply (k : ℕ) (K : Matrix m n ℂ)
    (i₁ : Fin k) (a : m) (j₁ : Fin k) (b : n) :
    krausAmplification (m := m) (n := n) k K (i₁, a) (j₁, b) =
      if i₁ = j₁ then K a b else 0 := by
  unfold krausAmplification
  rw [Matrix.kronecker_apply, Matrix.one_apply]
  by_cases h : i₁ = j₁
  · simp [h]
  · simp [h]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private lemma krausAmplification_conjTranspose_apply (k : ℕ) (K : Matrix m n ℂ)
    (j₁ : Fin k) (b : n) (i₁ : Fin k) (a : m) :
    (krausAmplification k K)ᴴ (j₁, b) (i₁, a) =
      if j₁ = i₁ then star (K a b) else 0 := by
  rw [Matrix.conjTranspose_apply, krausAmplification_apply]
  by_cases h : i₁ = j₁
  · simp [h]
  · simp [h, Ne.symm h]

-- Positivity transport through a star-algebra equivalence:
-- a nonneg element maps to a nonneg element because
-- `0 ≤ a ↔ ∃ b, a = star b * b`.
omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private lemma starAlgEquiv_map_nonneg {A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) : 0 ≤ e a := by
  obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [hb, map_mul, map_star]
  exact star_mul_self_nonneg _

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private lemma starAlgEquiv_symm_map_nonneg {A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [PartialOrder A] [PartialOrder B] [StarOrderedRing A] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {b : B} (hb : 0 ≤ b) : 0 ≤ e.symm b :=
  starAlgEquiv_map_nonneg e.symm hb

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
private lemma krausAmplification_mul_comp (k : ℕ) (K : Matrix m n ℂ)
    (M : Matrix (Fin k) (Fin k) (Matrix n n ℂ)) (i₁ : Fin k) (a : m) (j₁' : Fin k) (q : n) :
    (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) (j₁', q) =
      ∑ p : n, K a p * M i₁ j₁' p q := by
  calc
    (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) (j₁', q)
        = ∑ x : Fin k × n,
            krausAmplification k K (i₁, a) x * Matrix.comp (Fin k) (Fin k) n n ℂ M x (j₁', q) := by
          rw [Matrix.mul_apply]
    _ = (∑ i₁' : Fin k, ∑ p : n,
          krausAmplification k K (i₁, a) (i₁', p) *
            Matrix.comp (Fin k) (Fin k) n n ℂ M (i₁', p) (j₁', q)) := by
          rw [Fintype.sum_prod_type]
    _ = (∑ i₁' : Fin k, ∑ p : n,
          (if i₁ = i₁' then K a p else 0) * M i₁' j₁' p q) := by
          apply Finset.sum_congr rfl
          intro i₁' _
          apply Finset.sum_congr rfl
          intro p _
          rw [krausAmplification_apply, Matrix.comp_apply]
    _ = (∑ p : n, K a p * M i₁ j₁' p q) := by
          have h_collapse : ∀ i₁' : Fin k, i₁' ≠ i₁ →
              (∑ p : n, (if i₁ = i₁' then K a p else 0) * M i₁' j₁' p q) = 0 := by
            intro i₁' hi
            have h_eq : (fun p : n => (if i₁ = i₁' then K a p else 0) * M i₁' j₁' p q) =
                fun _ : n => (0 : ℂ) := by
              funext p
              simp [ite_eq_right (Ne.symm hi)]
            rw [h_eq, Finset.sum_const_zero]
          calc
            (∑ i₁' : Fin k, ∑ p : n, (if i₁ = i₁' then K a p else 0) * M i₁' j₁' p q)
                = (∑ p : n, K a p * M i₁ j₁' p q) := by
              rw [Finset.sum_eq_single i₁
                (fun i₁' _ hi => h_collapse i₁' hi)
                (by simp)]
              simp

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
private lemma aux_double_sum_eq (K : Matrix m n ℂ) (Mij : Matrix n n ℂ) (a : m) (b : m) :
    (∑ q : n, (∑ p : n, K a p * Mij p q) * star (K b q)) =
      (∑ p : n, ∑ q : n, K a p * Mij p q * star (K b q)) := by
  have h_ac :
      (∑ q : n, (∑ p : n, K a p * Mij p q) * star (K b q)) =
        (∑ q : n, ∑ p : n, K a p * Mij p q * star (K b q)) := by
    apply Finset.sum_congr rfl
    intro q _
    calc
      (∑ p : n, K a p * Mij p q) * star (K b q)
          = (∑ p ∈ Finset.univ, K a p * Mij p q) * star (K b q) := rfl
      _ = ∑ p ∈ Finset.univ, K a p * Mij p q * star (K b q) :=
          Finset.sum_mul Finset.univ (fun p => K a p * Mij p q) (star (K b q))
      _ = ∑ p : n, K a p * Mij p q * star (K b q) := rfl
  have h_cb :
      (∑ q : n, ∑ p : n, K a p * Mij p q * star (K b q)) =
        (∑ p : n, ∑ q : n, K a p * Mij p q * star (K b q)) :=
    Finset.sum_comm (f := fun q p => K a p * Mij p q * star (K b q))
  exact h_ac.trans h_cb

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
private lemma comp_map_kraus_eq_mul (k : ℕ) (K : Matrix m n ℂ)
    (M : Matrix (Fin k) (Fin k) (Matrix n n ℂ)) :
    Matrix.comp (Fin k) (Fin k) m m ℂ (M.map fun X => K * X * Kᴴ) =
      krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M * (krausAmplification k K)ᴴ := by
  ext ⟨i₁, a⟩ ⟨j₁, b⟩
  simp only [Matrix.comp_apply, Matrix.map_apply]
  have h_left : (K * M i₁ j₁ * Kᴴ) a b =
      (∑ p : n, ∑ q : n, K a p * M i₁ j₁ p q * star (K b q)) := by
    have h_a : (K * M i₁ j₁ * Kᴴ) a b =
        ∑ q : n, (K * M i₁ j₁) a q * (Kᴴ) q b := by
      rw [Matrix.mul_apply]
    have h_b : (∑ q : n, (K * M i₁ j₁) a q * (Kᴴ) q b) =
        ∑ q : n, (∑ p : n, K a p * M i₁ j₁ p q) * (Kᴴ) q b := by
      simp only [Matrix.mul_apply]
    have h_c : (∑ q : n, (∑ p : n, K a p * M i₁ j₁ p q) * (Kᴴ) q b) =
        ∑ q : n, (∑ p : n, K a p * M i₁ j₁ p q) * star (K b q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Matrix.conjTranspose_apply]
    have h_d : (∑ q : n, (∑ p : n, K a p * M i₁ j₁ p q) * star (K b q)) =
        (∑ p : n, ∑ q : n, K a p * M i₁ j₁ p q * star (K b q)) :=
      aux_double_sum_eq K (M i₁ j₁) a b
    exact h_a.trans (h_b.trans (h_c.trans h_d))
  rw [h_left]
  have h_mul : (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M *
      (krausAmplification k K)ᴴ) (i₁, a) (j₁, b) =
      (∑ p : n, ∑ q : n, K a p * M i₁ j₁ p q * star (K b q)) := by
    have h1 : (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M *
        (krausAmplification k K)ᴴ) (i₁, a) (j₁, b) =
        ∑ x : Fin k × n,
          (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) x *
            (krausAmplification k K)ᴴ x (j₁, b) := by
      rw [Matrix.mul_apply]
    have h2 : (∑ x : Fin k × n,
        (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) x *
          (krausAmplification k K)ᴴ x (j₁, b)) =
        ∑ j₁' : Fin k, ∑ q : n,
          (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) (j₁', q) *
            (krausAmplification k K)ᴴ (j₁', q) (j₁, b) := by
      rw [Fintype.sum_prod_type]
    have h3 : (∑ j₁' : Fin k, ∑ q : n,
        (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) (j₁', q) *
          (krausAmplification k K)ᴴ (j₁', q) (j₁, b)) =
        ∑ j₁' : Fin k, ∑ q : n,
          (∑ p : n, K a p * M i₁ j₁' p q) *
            (if j₁' = j₁ then star (K b q) else 0) := by
      apply Finset.sum_congr rfl
      intro j₁' _
      apply Finset.sum_congr rfl
      intro q _
      rw [krausAmplification_mul_comp, krausAmplification_conjTranspose_apply]
    have h4 : (∑ j₁' : Fin k, ∑ q : n,
        (∑ p : n, K a p * M i₁ j₁' p q) *
          (if j₁' = j₁ then star (K b q) else 0)) =
        ∑ j₁' : Fin k, ∑ q : n,
          if j₁' = j₁ then (∑ p : n, K a p * M i₁ j₁' p q) * star (K b q) else 0 := by
      apply Finset.sum_congr rfl
      intro j₁' _
      apply Finset.sum_congr rfl
      intro q _
      by_cases hj : j₁' = j₁
      · simp [hj]
      · simp [hj]
    have h_collapse : ∀ j₁' : Fin k, j₁' ≠ j₁ →
        (∑ q : n, if j₁' = j₁ then (∑ p : n, K a p * M i₁ j₁' p q) * star (K b q) else 0) =
          0 := by
      intro j₁' hj
      have h_eq :
          (fun q : n =>
            if j₁' = j₁ then (∑ p : n, K a p * M i₁ j₁' p q) * star (K b q) else 0) =
          fun _ : n => (0 : ℂ) := by
        funext q
        simp [ite_eq_right hj]
      rw [h_eq, Finset.sum_const_zero]
    have h5 : (∑ j₁' : Fin k, ∑ q : n,
        if j₁' = j₁ then (∑ p : n, K a p * M i₁ j₁' p q) * star (K b q) else 0) =
        (∑ q : n, (∑ p : n, K a p * M i₁ j₁ p q) * star (K b q)) := by
      rw [Finset.sum_eq_single j₁
        (fun j₁' _ hj => h_collapse j₁' hj)
        (by simp)]
      simp
    calc
      (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M *
            (krausAmplification k K)ᴴ) (i₁, a) (j₁, b)
          = ∑ x : Fin k × n,
              (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) x *
                (krausAmplification k K)ᴴ x (j₁, b) := h1
      _ = ∑ j₁' : Fin k, ∑ q : n,
              (krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ M) (i₁, a) (j₁', q) *
                (krausAmplification k K)ᴴ (j₁', q) (j₁, b) := h2
      _ = ∑ j₁' : Fin k, ∑ q : n,
              (∑ p : n, K a p * M i₁ j₁' p q) *
                (if j₁' = j₁ then star (K b q) else 0) := h3
      _ = ∑ j₁' : Fin k, ∑ q : n,
              if j₁' = j₁ then (∑ p : n, K a p * M i₁ j₁' p q) * star (K b q) else 0 := h4
      _ = (∑ q : n, (∑ p : n, K a p * M i₁ j₁ p q) * star (K b q)) := h5
      _ = (∑ p : n, ∑ q : n, K a p * M i₁ j₁ p q * star (K b q)) :=
            aux_double_sum_eq K (M i₁ j₁) a b
  exact h_mul.symm

private lemma flatEquivInput_eq_comp (k : ℕ)
    (M : CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)) :
    flatEquivInput k M = Matrix.comp (Fin k) (Fin k) n n ℂ (CStarMatrix.ofMatrix.symm M) :=
  rfl

private lemma flatEquivOutput_eq_comp (k : ℕ)
    (M : CStarMatrix (Fin k) (Fin k) (Matrix m m ℂ)) :
    flatEquivOutput k M = Matrix.comp (Fin k) (Fin k) m m ℂ (CStarMatrix.ofMatrix.symm M) :=
  rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
private lemma ofMatrix_symm_map_singleKraus (k : ℕ) (K : Matrix m n ℂ)
    (M : CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)) :
    CStarMatrix.ofMatrix.symm (M.map (singleKrausLinearMap K)) =
      (CStarMatrix.ofMatrix.symm M).map fun X => K * X * Kᴴ := by
  ext i j a b
  simp [CStarMatrix.map_apply, CStarMatrix.ofMatrix_symm_apply, singleKrausLinearMap_apply]

private lemma flatEquivOutput_map_eq (k : ℕ) (K : Matrix m n ℂ)
    (M : CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)) :
    flatEquivOutput k (M.map (singleKrausLinearMap K)) =
      krausAmplification k K * flatEquivInput k M * (krausAmplification k K)ᴴ := by
  calc
    flatEquivOutput k (M.map (singleKrausLinearMap K))
        = Matrix.comp (Fin k) (Fin k) m m ℂ
            (CStarMatrix.ofMatrix.symm (M.map (singleKrausLinearMap K))) :=
      flatEquivOutput_eq_comp k _
    _ = Matrix.comp (Fin k) (Fin k) m m ℂ
            ((CStarMatrix.ofMatrix.symm M).map fun X => K * X * Kᴴ) := by
      rw [ofMatrix_symm_map_singleKraus]
    _ = krausAmplification k K * Matrix.comp (Fin k) (Fin k) n n ℂ (CStarMatrix.ofMatrix.symm M) *
          (krausAmplification k K)ᴴ := by
      exact comp_map_kraus_eq_mul k K (CStarMatrix.ofMatrix.symm M)
    _ = krausAmplification k K * flatEquivInput k M * (krausAmplification k K)ᴴ := by
      rw [flatEquivInput_eq_comp]

/-- **Single-Kraus completely positive map.** Let `n,m` be finite index types with decidable equality. A
complex rectangular matrix `K : Matrix m n ℂ` defines the completely positive map `X ↦ K X Kᴴ` from
`Matrix n n ℂ` to `Matrix m m ℂ`. -/
noncomputable def singleKraus (K : Matrix m n ℂ) : Matrix n n ℂ →CP Matrix m m ℂ where
  toLinearMap := singleKrausLinearMap K
  map_cstarMatrix_nonneg' k M hM := by
    have h_flat_nonneg : 0 ≤ flatEquivInput k M :=
      starAlgEquiv_map_nonneg (flatEquivInput k) hM
    have h_psd : (flatEquivInput k M).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp h_flat_nonneg)
    have h_ampl_psd :
        PosSemidef (krausAmplification k K * flatEquivInput k M * (krausAmplification k K)ᴴ) :=
      h_psd.mul_mul_conjTranspose_same (krausAmplification k K)
    have h_ampl_nonneg :
        0 ≤ krausAmplification k K * flatEquivInput k M * (krausAmplification k K)ᴴ :=
      Matrix.nonneg_iff_posSemidef.mpr h_ampl_psd
    have h_eq :
        flatEquivOutput k (M.map (singleKrausLinearMap K)) =
          krausAmplification k K * flatEquivInput k M * (krausAmplification k K)ᴴ :=
      flatEquivOutput_map_eq k K M
    have h_out_nonneg : 0 ≤ flatEquivOutput k (M.map (singleKrausLinearMap K)) := by
      rw [h_eq]
      exact h_ampl_nonneg
    exact starAlgEquiv_symm_map_nonneg (flatEquivOutput k) h_out_nonneg

@[simp]
theorem singleKraus_apply (K : Matrix m n ℂ) (X : Matrix n n ℂ) :
    singleKraus (m := m) (n := n) K X = K * X * Kᴴ :=
  rfl

variable {r : Type*} [Fintype r]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- **Finite-family Kraus linear map.** Let `n` be a finite index type and `m` any index type. For a
finite index type `r` and `K : r → Matrix m n ℂ`, this is the complex-linear map `Matrix n n ℂ →
Matrix m m ℂ` given by `X ↦ ∑ i, Kᵢ X Kᵢᴴ`; an empty family gives zero. -/
noncomputable def krausLinearMap (K : r → Matrix m n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ :=
  ∑ i, singleKrausLinearMap (K i)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
@[simp]
theorem krausLinearMap_apply (K : r → Matrix m n ℂ) (X : Matrix n n ℂ) :
    krausLinearMap K X = ∑ i, K i * X * (K i)ᴴ := by
  classical
  calc
    krausLinearMap K X = (∑ i, singleKrausLinearMap (K i)) X := rfl
    _ = ∑ i, singleKrausLinearMap (K i) X := by
      rw [LinearMap.sum_apply]
    _ = ∑ i, K i * X * (K i)ᴴ := by
      simp [singleKrausLinearMap_apply]

/-- **Finite-family completely positive map.** Let `n,m` be finite index types with decidable equality.
For a finite index type `r` and `K : r → Matrix m n ℂ`, the map `Matrix n n ℂ → Matrix m m ℂ` given
by `X ↦ ∑ i, Kᵢ X Kᵢᴴ` is completely positive. The empty family gives zero. -/
noncomputable def kraus (K : r → Matrix m n ℂ) :
    Matrix n n ℂ →CP Matrix m m ℂ :=
  sum fun i => singleKraus (K i)

@[simp]
theorem toLinearMap_kraus (K : r → Matrix m n ℂ) :
    (kraus K).toLinearMap = krausLinearMap K :=
  rfl

@[simp]
theorem kraus_apply (K : r → Matrix m n ℂ) (X : Matrix n n ℂ) :
    kraus K X = ∑ i, K i * X * (K i)ᴴ := by
  classical
  calc
    kraus K X = ∑ i, singleKraus (K i) X := by
      simp [kraus, sum_apply]
    _ = ∑ i, K i * X * (K i)ᴴ := by
      simp

-- Minimal Fin 0 / Fin 1 regressions compatible with factorization.

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
@[simp]
theorem krausLinearMap_fin_zero (K : Fin 0 → Matrix m n ℂ) :
    krausLinearMap K = 0 := by
  ext X
  simp [krausLinearMap]

@[simp]
theorem kraus_fin_zero_apply (K : Fin 0 → Matrix m n ℂ) (X : Matrix n n ℂ) :
    kraus K X = 0 := by
  simp [kraus_apply]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem krausLinearMap_fin_one (K : Fin 1 → Matrix m n ℂ) :
    krausLinearMap K = singleKrausLinearMap (K 0) := by
  classical
  ext X : 1
  calc
    krausLinearMap K X = ∑ i : Fin 1, K i * X * (K i)ᴴ := by
      simp [krausLinearMap_apply]
    _ = K 0 * X * (K 0)ᴴ := by
      rw [Fin.sum_univ_one]
    _ = singleKrausLinearMap (K 0) X := rfl

theorem kraus_fin_one (K : Fin 1 → Matrix m n ℂ) :
    kraus K = singleKraus (K 0) := by
  classical
  apply DFunLike.ext
  intro X
  calc
    kraus K X = ∑ i : Fin 1, K i * X * (K i)ᴴ := by
      simp [kraus_apply]
    _ = K 0 * X * (K 0)ᴴ := by
      rw [Fin.sum_univ_one]
    _ = singleKraus (K 0) X := rfl

variable {s : Type*} [Fintype s]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem krausLinearMap_reindexEquiv (e : r ≃ s) (K : r → Matrix m n ℂ) :
    krausLinearMap (K ∘ e.symm) = krausLinearMap K := by
  classical
  apply LinearMap.ext
  intro X
  calc
    krausLinearMap (K ∘ e.symm) X = ∑ j : s, K (e.symm j) * X * (K (e.symm j))ᴴ := by
      simp [krausLinearMap_apply, Function.comp]
    _ = ∑ i : r, K i * X * (K i)ᴴ := by
      -- Sum over `s` of `f (e.symm)` equals sum over `r` of `f`.
      exact Equiv.sum_comp e.symm (fun i => K i * X * (K i)ᴴ)
    _ = krausLinearMap K X := by
      simp [krausLinearMap_apply]

theorem kraus_reindexEquiv (e : r ≃ s) (K : r → Matrix m n ℂ) :
    kraus (K ∘ e.symm) = kraus K := by
  have h_toLinearMap : (kraus (K ∘ e.symm)).toLinearMap = (kraus K).toLinearMap := by
    rw [toLinearMap_kraus, toLinearMap_kraus, krausLinearMap_reindexEquiv]
  apply DFunLike.ext
  intro X
  calc
    kraus (K ∘ e.symm) X = (kraus (K ∘ e.symm)).toLinearMap X := rfl
    _ = (kraus K).toLinearMap X := by rw [h_toLinearMap]
    _ = kraus K X := rfl

section Composition

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- **Kraus family for composition.** For a finite matrix index type `l` and arbitrary index types
`n,m,r,s`, families `K : r → Matrix l n ℂ` and `L : s → Matrix m l ℂ` define a family on `r × s` by
`(i,j) ↦ Lⱼ Kᵢ`. Its matrices have output index `m` and input index `n`; the product order
corresponds to applying the map of `K` before the map of `L`. -/
noncomputable def krausCompFamily (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ) :
    r × s → Matrix m n ℂ :=
  fun p => L p.2 * K p.1

omit [Fintype m] [Fintype r] [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
private lemma krausCompFamily_term (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ)
    (ir : r) (js : s) (X : Matrix n n ℂ) :
    (L js * K ir) * X * (L js * K ir)ᴴ =
      L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
private lemma krausCompFamily_sum_mul (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ)
    (X : Matrix n n ℂ) :
    (krausLinearMap L) ((krausLinearMap K) X) =
      ∑ js : s, L js * (∑ ir : r, K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
  simp only [krausLinearMap_apply]

omit [Fintype m] [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
private lemma sum_matrix_mul_sum (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ)
    (X : Matrix n n ℂ) (js : s) :
    L js * (∑ ir : r, K ir * X * (K ir)ᴴ) * (L js)ᴴ =
      ∑ ir : r, L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
  calc
    L js * (∑ ir : r, K ir * X * (K ir)ᴴ) * (L js)ᴴ
        = (L js * (∑ ir : r, K ir * X * (K ir)ᴴ)) * (L js)ᴴ := rfl
    _ = (∑ ir : r, L js * (K ir * X * (K ir)ᴴ)) * (L js)ᴴ := by
        rw [Matrix.mul_sum]
    _ = ∑ ir : r, L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
        rw [Matrix.sum_mul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
private lemma sum_prod_comm_swap (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ)
    (X : Matrix n n ℂ) :
    (∑ ir : r, ∑ js : s, L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ) =
      (∑ js : s, ∑ ir : r, L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ) :=
  Finset.sum_comm

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq l] in
theorem krausLinearMap_krausCompFamily (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ) :
    krausLinearMap (krausCompFamily K L) = (krausLinearMap L).comp (krausLinearMap K) := by
  classical
  apply LinearMap.ext
  intro X
  let f : r × s → Matrix m m ℂ := fun p => L p.2 * (K p.1 * X * (K p.1)ᴴ) * (L p.2)ᴴ
  calc
    krausLinearMap (krausCompFamily K L) X
        = ∑ p : r × s, (L p.2 * K p.1) * X * (L p.2 * K p.1)ᴴ := by
          simp [krausLinearMap_apply, krausCompFamily]
    _ = ∑ p : r × s, f p := by
          apply Finset.sum_congr rfl
          intro p _
          simp only [f]
          exact krausCompFamily_term K L p.1 p.2 X
    _ = ∑ ir : r, ∑ js : s, L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
          rw [Fintype.sum_prod_type (f := f)]
    _ = ∑ js : s, ∑ ir : r, L js * (K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
          exact sum_prod_comm_swap K L X
    _ = ∑ js : s, L js * (∑ ir : r, K ir * X * (K ir)ᴴ) * (L js)ᴴ := by
          apply Finset.sum_congr rfl
          intro js _
          rw [← sum_matrix_mul_sum K L X js]
    _ = (krausLinearMap L) ((krausLinearMap K) X) := by
          rw [← krausCompFamily_sum_mul K L X]
    _ = ((krausLinearMap L).comp (krausLinearMap K)) X := rfl

theorem kraus_krausCompFamily (K : r → Matrix l n ℂ) (L : s → Matrix m l ℂ) :
    kraus (krausCompFamily K L) = CompletelyPositiveMap.comp (kraus L) (kraus K) := by
  have h_toLinearMap :
      (kraus (krausCompFamily K L)).toLinearMap =
        (CompletelyPositiveMap.comp (kraus L) (kraus K)).toLinearMap := by
    rw [toLinearMap_kraus, krausLinearMap_krausCompFamily, toLinearMap_comp, toLinearMap_kraus,
      toLinearMap_kraus]
  apply DFunLike.ext
  intro X
  calc
    kraus (krausCompFamily K L) X = (kraus (krausCompFamily K L)).toLinearMap X := rfl
    _ = (CompletelyPositiveMap.comp (kraus L) (kraus K)).toLinearMap X := by rw [h_toLinearMap]
    _ = CompletelyPositiveMap.comp (kraus L) (kraus K) X := rfl

end Composition

section ChoiFormulas

omit [Fintype m] [DecidableEq m] in
/-- Private entry formula: `(K * single i j 1 * Kᴴ) a b = K a i * star (K b j)`. -/
private lemma singleKraus_choi_entry (K : Matrix m n ℂ) (i j : n) (a b : m) :
    (K * Matrix.single i j (1 : ℂ) * Kᴴ) a b = K a i * star (K b j) := by
  classical
  -- First multiplication: `(K * single i j 1) a q = if q = j then K a i else 0`.
  have h_Ksingle : ∀ q : n, (K * Matrix.single i j (1 : ℂ)) a q =
      if q = j then K a i else 0 := by
    intro q
    rw [Matrix.mul_apply]
    by_cases hq : q = j
    · have h_eq : ∀ p : n, K a p * Matrix.single i j (1 : ℂ) p q =
          if p = i then K a p else (0 : ℂ) := by
        intro p
        rw [Matrix.single_apply]
        by_cases hp : p = i
        · simp [hp, hq]
        · simp [hp, Ne.symm hp, hq]
      simp_rw [h_eq]
      rw [Finset.sum_eq_single i
        (fun p _ hp => by simp [hp])
        (by simp)]
      simp [hq]
    · have h_eq : ∀ p : n, K a p * Matrix.single i j (1 : ℂ) p q = (0 : ℂ) := by
        intro p
        have hj : j ≠ q := Ne.symm hq
        rw [Matrix.single_apply]
        simp [hj]
      simp_rw [h_eq]
      rw [Finset.sum_const_zero]
      simp [hq]
  -- Second multiplication collapses to `q = j`.
  calc
    (K * Matrix.single i j (1 : ℂ) * Kᴴ) a b
        = ∑ q : n, (K * Matrix.single i j (1 : ℂ)) a q * Kᴴ q b := by
          rw [Matrix.mul_apply]
    _ = ∑ q : n, (if q = j then K a i else 0) * Kᴴ q b := by
          apply Finset.sum_congr rfl
          intro q _
          rw [h_Ksingle]
    _ = ∑ q : n, if q = j then K a i * Kᴴ q b else 0 := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hq : q = j
          · simp [hq]
          · simp [hq]
    _ = K a i * Kᴴ j b := by
          rw [Finset.sum_eq_single j
            (fun q _ hq => by simp [hq])
            (by simp)]
          simp
    _ = K a i * star (K b j) := by
          rw [Matrix.conjTranspose_apply]

omit [Fintype m] [DecidableEq m] in
/-- **Choi matrix of a single-Kraus linear map.** Let `n` be finite with decidable equality and let `m`
be any index type. For `K : Matrix m n ℂ`, the Choi matrix of the complex-linear map `X ↦ K X Kᴴ` is
the outer product `vec(K) vec(K)ᴴ`, indexed by `n × m`. -/
theorem choiMatrix_singleKrausLinearMap (K : Matrix m n ℂ) :
    LinearMap.choiMatrix (singleKrausLinearMap K) =
      Matrix.vecMulVec (Matrix.vec K) (star (Matrix.vec K)) := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  calc
    LinearMap.choiMatrix (singleKrausLinearMap K) (i, a) (j, b)
        = (singleKrausLinearMap K (Matrix.single i j (1 : ℂ))) a b := by
          simp [LinearMap.choiMatrix_apply]
    _ = (K * Matrix.single i j (1 : ℂ) * Kᴴ) a b := rfl
    _ = K a i * star (K b j) := singleKraus_choi_entry K i j a b
    _ = Matrix.vec K (i, a) * star (Matrix.vec K) (j, b) := rfl
    _ = (Matrix.vecMulVec (Matrix.vec K) (star (Matrix.vec K))) (i, a) (j, b) := by
          simp [Matrix.vecMulVec]

omit [Fintype m] [DecidableEq m] in
/-- **Choi matrix of a finite Kraus linear map.** Let `n` be finite with decidable equality and let `m`
be any index type. For a finite family `K : r → Matrix m n ℂ`, the Choi matrix of the complex-linear
map `X ↦ ∑ i, Kᵢ X Kᵢᴴ` is `∑ i, vec(Kᵢ) vec(Kᵢ)ᴴ`, indexed by `n × m`. -/
theorem choiMatrix_krausLinearMap (K : r → Matrix m n ℂ) :
    LinearMap.choiMatrix (krausLinearMap K) =
      ∑ i : r, Matrix.vecMulVec (Matrix.vec (K i)) (star (Matrix.vec (K i))) := by
  classical
  have h_eq : krausLinearMap K = ∑ i : r, singleKrausLinearMap (K i) := rfl
  calc
    LinearMap.choiMatrix (krausLinearMap K)
        = LinearMap.choiMatrixHom (krausLinearMap K) := rfl
    _ = LinearMap.choiMatrixHom (∑ i : r, singleKrausLinearMap (K i)) := by
          rw [h_eq]
    _ = ∑ i : r, LinearMap.choiMatrixHom (singleKrausLinearMap (K i)) := by
          rw [map_sum]
    _ = ∑ i : r, LinearMap.choiMatrix (singleKrausLinearMap (K i)) := rfl
    _ = ∑ i : r, Matrix.vecMulVec (Matrix.vec (K i)) (star (Matrix.vec (K i))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact choiMatrix_singleKrausLinearMap (K i)

/-- **Choi matrix of a single-Kraus CP map.** Let `n,m` be finite index types with decidable equality.
For `K : Matrix m n ℂ`, the Choi matrix of `X ↦ K X Kᴴ` is the outer product `vec(K) vec(K)ᴴ`,
indexed by `n × m`. -/
theorem choiMatrix_singleKraus (K : Matrix m n ℂ) :
    CompletelyPositiveMap.choiMatrix (singleKraus K) =
      Matrix.vecMulVec (Matrix.vec K) (star (Matrix.vec K)) := by
  classical
  calc
    CompletelyPositiveMap.choiMatrix (singleKraus K)
        = LinearMap.choiMatrix (singleKraus K).toLinearMap := rfl
    _ = LinearMap.choiMatrix (singleKrausLinearMap K) := rfl
    _ = Matrix.vecMulVec (Matrix.vec K) (star (Matrix.vec K)) :=
          choiMatrix_singleKrausLinearMap K

/-- **Choi matrix of a finite Kraus CP map.** Let `n,m` be finite index types with decidable equality.
For a finite family `K : r → Matrix m n ℂ`, the Choi matrix of `X ↦ ∑ i, Kᵢ X Kᵢᴴ` is `∑ i, vec(Kᵢ)
vec(Kᵢ)ᴴ`, indexed by `n × m`. -/
theorem choiMatrix_kraus (K : r → Matrix m n ℂ) :
    CompletelyPositiveMap.choiMatrix (kraus K) =
      ∑ i : r, Matrix.vecMulVec (Matrix.vec (K i)) (star (Matrix.vec (K i))) := by
  classical
  calc
    CompletelyPositiveMap.choiMatrix (kraus K)
        = LinearMap.choiMatrix (kraus K).toLinearMap := rfl
    _ = LinearMap.choiMatrix (krausLinearMap K) := by
          rw [toLinearMap_kraus]
    _ = ∑ i : r, Matrix.vecMulVec (Matrix.vec (K i)) (star (Matrix.vec (K i))) :=
          choiMatrix_krausLinearMap K

end ChoiFormulas

end CompletelyPositiveMap

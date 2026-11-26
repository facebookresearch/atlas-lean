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

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.Matrix
import MathlibExt.LinearAlgebra.Matrix.UnitaryBetween
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

open scoped Matrix.Norms.L2Operator ComplexStarModule ComplexOrder
open Matrix

/-!
# Operator-norm contractions are averages of two unitaries

Let I be a finite index type and X an I×I complex matrix with Euclidean L² operator norm
‖X‖≤1. There exist unitary matrices W,Z with X=(W+Z)/2. The norm is the operator norm on
Euclidean ℂ^I.
-/

private theorem exists_eq_average_two_unitaries_of_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.IsHermitian) (hPnorm : ‖P‖ ≤ 1) :
    ∃ W Z : Matrix n n ℂ,
      W ∈ unitaryGroup n ℂ ∧ Z ∈ unitaryGroup n ℂ ∧
        P = ((2 : ℂ)⁻¹) • (W + Z) := by
  -- Provide the C* order instances for matrices
  let _po : PartialOrder (Matrix n n ℂ) :=
    CStarAlgebra.spectralOrder (Matrix n n ℂ)
  let _sor : StarOrderedRing (Matrix n n ℂ) :=
    CStarAlgebra.spectralOrderedRing (Matrix n n ℂ)
  have hSelf : IsSelfAdjoint P := hP.isSelfAdjoint
  let a : selfAdjoint (Matrix n n ℂ) := ⟨P, hSelf⟩
  have ha_norm : ‖a‖ ≤ 1 := by
    have h_eq : ‖a‖ = ‖(a : Matrix n n ℂ)‖ := rfl
    calc ‖a‖ = ‖(a : Matrix n n ℂ)‖ := h_eq
      _ = ‖P‖ := rfl
      _ ≤ 1 := hPnorm
  let u : unitary (Matrix n n ℂ) :=
    selfAdjoint.unitarySelfAddISMul a ha_norm
  let W : Matrix n n ℂ := (u : Matrix n n ℂ)
  let Z : Matrix n n ℂ := star W
  have hW_mem : W ∈ unitaryGroup n ℂ := by
    have h : W ∈ unitary (Matrix n n ℂ) := u.prop
    exact h
  have hZ_mem : Z ∈ unitaryGroup n ℂ := by
    have hW_unitary : W ∈ unitary (Matrix n n ℂ) := u.prop
    have hStar : star W ∈ unitary (Matrix n n ℂ) :=
      Unitary.star_mem hW_unitary
    exact hStar
  have hReal : (ℜ (u : Matrix n n ℂ) : selfAdjoint (Matrix n n ℂ)) = a :=
    selfAdjoint.realPart_unitarySelfAddISMul a ha_norm
  have hReal_coe : (ℜ (u : Matrix n n ℂ) : Matrix n n ℂ) = P := by
    have h1 : ((ℜ (u : Matrix n n ℂ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)
        = (a : Matrix n n ℂ) := congrArg Subtype.val hReal
    have h2 : (a : Matrix n n ℂ) = P := rfl
    calc (ℜ (u : Matrix n n ℂ) : Matrix n n ℂ)
        = ((ℜ (u : Matrix n n ℂ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) := rfl
      _ = (a : Matrix n n ℂ) := h1
      _ = P := h2
  have hReal_apply :
      (ℜ (u : Matrix n n ℂ) : Matrix n n ℂ) =
        (2 : ℝ)⁻¹ • ((u : Matrix n n ℂ) + star (u : Matrix n n ℂ)) := by
    rw [realPart_apply_coe]
  have hAdd_eq : (u : Matrix n n ℂ) + star (u : Matrix n n ℂ) = W + Z := rfl
  have hP_eq_R : P = (2 : ℝ)⁻¹ • (W + Z) := by
    calc P = (ℜ (u : Matrix n n ℂ) : Matrix n n ℂ) := hReal_coe.symm
      _ = (2 : ℝ)⁻¹ • ((u : Matrix n n ℂ) + star (u : Matrix n n ℂ)) := hReal_apply
      _ = (2 : ℝ)⁻¹ • (W + Z) := by rw [hAdd_eq]
  have hR_to_C_eq :
      (2 : ℝ)⁻¹ • (W + Z) = ((2 : ℂ)⁻¹) • (W + Z) := by
    have h_scalar : Complex.ofReal ((2 : ℝ)⁻¹) = (2 : ℂ)⁻¹ := by
      norm_num
    calc (2 : ℝ)⁻¹ • (W + Z)
        = Complex.ofReal ((2 : ℝ)⁻¹) • (W + Z) := by
          rw [← Complex.coe_smul]
      _ = ((2 : ℂ)⁻¹) • (W + Z) := by rw [h_scalar]
  have hP_eq_C : P = ((2 : ℂ)⁻¹) • (W + Z) := by
    calc P = (2 : ℝ)⁻¹ • (W + Z) := hP_eq_R
      _ = ((2 : ℂ)⁻¹) • (W + Z) := hR_to_C_eq
  exact ⟨W, Z, hW_mem, hZ_mem, hP_eq_C⟩

/-- **Gram matrix of a finite complex operator.**

Let I be a finite index type and X an I×I complex matrix. The matrix contractionGram X is XᴴX,
the positive semidefinite Gram matrix of its columns.
-/
private def contractionGram {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix n n ℂ :=
  Xᴴ * X

private theorem contractionGram_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : (contractionGram X).IsHermitian :=
  isHermitian_conjTranspose_mul_self X

private theorem contractionGram_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : (contractionGram X).PosSemidef := by
  classical
  simpa [contractionGram] using posSemidef_conjTranspose_mul_self X

private theorem contractionGram_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : ‖X‖ ≤ 1) : ‖contractionGram X‖ ≤ 1 := by
  unfold contractionGram
  rw [l2_opNorm_conjTranspose_mul_self]
  have hNN : 0 ≤ ‖X‖ := norm_nonneg _
  calc ‖X‖ * ‖X‖ ≤ 1 * ‖X‖ := mul_le_mul_of_nonneg_right hX hNN
    _ = ‖X‖ := one_mul _
    _ ≤ 1 := hX

private theorem contractionGram_eigenvalues_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (i : n) :
    0 ≤ (contractionGram_posSemidef X).1.eigenvalues i :=
  (contractionGram_posSemidef X).eigenvalues_nonneg i

private theorem contractionGram_eigenvalues_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : ‖X‖ ≤ 1) (i : n) :
    (contractionGram_posSemidef X).1.eigenvalues i ≤ 1 := by
  have hNonneg : 0 ≤ (contractionGram_posSemidef X).1.eigenvalues i :=
    contractionGram_eigenvalues_nonneg X i
  have hNorm : ‖contractionGram X‖ ≤ 1 := contractionGram_norm_le_one X hX
  have hMemC : (RCLike.ofReal ((contractionGram_posSemidef X).1.eigenvalues i) : ℂ) ∈
      spectrum ℂ (contractionGram X) := by
    rw [(contractionGram_posSemidef X).1.spectrum_eq_image_range]
    exact ⟨(contractionGram_posSemidef X).1.eigenvalues i, ⟨i, rfl⟩, rfl⟩
  have hLeMul : ‖(RCLike.ofReal ((contractionGram_posSemidef X).1.eigenvalues i) : ℂ)‖ ≤
      ‖contractionGram X‖ * ‖(1 : Matrix n n ℂ)‖ :=
    spectrum.norm_le_norm_mul_of_mem hMemC
  have hOne : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
    classical
    have hEq : (1 : Matrix n n ℂ) = diagonal (fun _ : n => (1 : ℂ)) := by
      exact Matrix.diagonal_one.symm
    rw [hEq, l2_opNorm_diagonal]
    have hPi : ‖(fun _ : n => (1 : ℂ))‖ ≤ 1 := by
      apply pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) |>.mpr
      intro j
      simp
    exact hPi
  have hLe : ‖(RCLike.ofReal ((contractionGram_posSemidef X).1.eigenvalues i) : ℂ)‖ ≤
      ‖contractionGram X‖ := by
    calc ‖(RCLike.ofReal ((contractionGram_posSemidef X).1.eigenvalues i) : ℂ)‖
        ≤ ‖contractionGram X‖ * ‖(1 : Matrix n n ℂ)‖ := hLeMul
      _ ≤ ‖contractionGram X‖ * 1 :=
          mul_le_mul_of_nonneg_left hOne (norm_nonneg _)
      _ = ‖contractionGram X‖ := mul_one _
  have hEqNorm : ‖(RCLike.ofReal ((contractionGram_posSemidef X).1.eigenvalues i) : ℂ)‖ =
      (contractionGram_posSemidef X).1.eigenvalues i := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hNonneg]
  calc (contractionGram_posSemidef X).1.eigenvalues i
      = ‖(RCLike.ofReal ((contractionGram_posSemidef X).1.eigenvalues i) : ℂ)‖ := hEqNorm.symm
    _ ≤ ‖contractionGram X‖ := hLe
    _ ≤ 1 := hNorm

private noncomputable instance instPartialOrderMatrix {n : Type*} [Fintype n] [DecidableEq n] :
    PartialOrder (Matrix n n ℂ) :=
  CStarAlgebra.spectralOrder (Matrix n n ℂ)

private noncomputable instance instStarOrderedRingMatrix {n : Type*} [Fintype n] [DecidableEq n] :
    StarOrderedRing (Matrix n n ℂ) :=
  CStarAlgebra.spectralOrderedRing (Matrix n n ℂ)

private theorem contractionGram_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : 0 ≤ contractionGram X := by
  unfold contractionGram
  have h : Xᴴ = star X := by rw [Matrix.star_eq_conjTranspose]
  rw [h]
  exact star_mul_self_nonneg X

private noncomputable def contractionSqrt {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt (contractionGram X)

private theorem contractionSqrt_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : 0 ≤ contractionSqrt X :=
  CFC.sqrt_nonneg (contractionGram X)

private theorem contractionSqrt_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : (contractionSqrt X).IsHermitian := by
  have hNonneg : 0 ≤ contractionSqrt X := contractionSqrt_nonneg X
  have hSA : IsSelfAdjoint (contractionSqrt X) := IsSelfAdjoint.of_nonneg hNonneg
  exact hSA.isHermitian

private theorem contractionSqrt_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    contractionSqrt X * contractionSqrt X = contractionGram X :=
  CFC.sqrt_mul_sqrt_self (contractionGram X) (contractionGram_nonneg X)

private theorem contractionSqrt_norm_eq {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ‖contractionSqrt X‖ = ‖X‖ := by
  have hMul : contractionSqrt X * contractionSqrt X = contractionGram X :=
    contractionSqrt_mul_self X
  have hHerm : (contractionSqrt X).IsHermitian := contractionSqrt_isHermitian X
  have hSA : IsSelfAdjoint (contractionSqrt X) := hHerm.isSelfAdjoint
  have hNormSq : ‖contractionSqrt X * contractionSqrt X‖ = ‖contractionSqrt X‖ ^ 2 :=
    hSA.norm_mul_self
  have hGram : ‖contractionGram X‖ = ‖X‖ * ‖X‖ := by
    unfold contractionGram
    rw [l2_opNorm_conjTranspose_mul_self]
  have hEqSq : ‖contractionSqrt X‖ ^ 2 = ‖X‖ ^ 2 := by
    calc ‖contractionSqrt X‖ ^ 2
        = ‖contractionSqrt X * contractionSqrt X‖ := hNormSq.symm
      _ = ‖contractionGram X‖ := by rw [hMul]
      _ = ‖X‖ * ‖X‖ := hGram
      _ = ‖X‖ ^ 2 := by ring
  nlinarith [sq_nonneg (‖contractionSqrt X‖ - ‖X‖), norm_nonneg (contractionSqrt X),
    norm_nonneg X]

private theorem contractionSqrt_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : ‖X‖ ≤ 1) : ‖contractionSqrt X‖ ≤ 1 := by
  rw [contractionSqrt_norm_eq X]
  exact hX

private theorem contractionSqrt_spectral {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    contractionSqrt X =
      (contractionGram_isHermitian X).eigenvectorUnitary.val *
        diagonal (fun i =>
          (RCLike.ofReal (Real.sqrt ((contractionGram_isHermitian X).eigenvalues i)) : ℂ)) *
        star ((contractionGram_isHermitian X).eigenvectorUnitary.val) := by
  have hA : IsHermitian (contractionGram X) := contractionGram_isHermitian X
  have hNonneg : 0 ≤ contractionGram X := contractionGram_nonneg X
  calc contractionSqrt X
      = CFC.sqrt (contractionGram X) := rfl
    _ = cfcₙ Real.sqrt (contractionGram X) := by
        rw [CFC.sqrt_eq_real_sqrt (contractionGram X) hNonneg]
    _ = cfc Real.sqrt (contractionGram X) := by
        rw [cfcₙ_eq_cfc]
    _ = hA.cfc Real.sqrt := by
        rw [Matrix.IsHermitian.cfc_eq]
    _ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hA.eigenvalues)) := by
        rw [Matrix.IsHermitian.cfc]
    _ = hA.eigenvectorUnitary.val *
          diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hA.eigenvalues) *
          star (hA.eigenvectorUnitary.val) := by
        rw [Unitary.conjStarAlgAut_apply]
    _ = (contractionGram_isHermitian X).eigenvectorUnitary.val *
          diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt ((contractionGram_isHermitian X).eigenvalues i)) : ℂ)) *
          star ((contractionGram_isHermitian X).eigenvectorUnitary.val) := by
        rfl

private theorem contractionSqrt_mulVec_eigenvectorBasis {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (j : n) :
    contractionSqrt X *ᵥ
        ⇑((contractionGram_isHermitian X).eigenvectorBasis j) =
      (RCLike.ofReal
          (Real.sqrt ((contractionGram_isHermitian X).eigenvalues j)) : ℂ) •
        ⇑((contractionGram_isHermitian X).eigenvectorBasis j) := by
  let hA := contractionGram_isHermitian X
  have hSpec : contractionSqrt X =
      hA.eigenvectorUnitary.val *
        diagonal (fun i =>
          (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ)) *
        star hA.eigenvectorUnitary.val :=
    contractionSqrt_spectral X
  let v : n → ℂ := ⇑(hA.eigenvectorBasis j)
  have hStar : (star hA.eigenvectorUnitary.val) *ᵥ v = Pi.single j 1 :=
    hA.star_eigenvectorUnitary_mulVec j
  have hU : hA.eigenvectorUnitary.val *ᵥ Pi.single j 1 = v :=
    hA.eigenvectorUnitary_mulVec j
  have hDiag :
      diagonal (fun i =>
          (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ)) *ᵥ
        Pi.single j 1 =
        (RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) •
          Pi.single j 1 := by
    have h1 :
        diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ)) *ᵥ
          Pi.single j 1 =
          Pi.single j
            ((RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) * 1) :=
      Matrix.diagonal_mulVec_single _ j 1
    have h2 :
        Pi.single j
            ((RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) * 1) =
          (RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) •
            Pi.single j 1 := by
      ext k
      simp [Pi.single_apply, mul_ite, mul_one, mul_zero]
    calc diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ)) *ᵥ
          Pi.single j 1
        = Pi.single j
            ((RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) * 1) := h1
      _ = (RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) •
            Pi.single j 1 := h2
  calc contractionSqrt X *ᵥ v
      = (hA.eigenvectorUnitary.val *
          diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ)) *
          star hA.eigenvectorUnitary.val) *ᵥ v := by
        rw [hSpec]
    _ = (hA.eigenvectorUnitary.val *
          diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ))) *ᵥ
          ((star hA.eigenvectorUnitary.val) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
    _ = (hA.eigenvectorUnitary.val *
          diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ))) *ᵥ
          Pi.single j 1 := by
        rw [hStar]
    _ = hA.eigenvectorUnitary.val *ᵥ
          (diagonal (fun i =>
            (RCLike.ofReal (Real.sqrt (hA.eigenvalues i)) : ℂ)) *ᵥ
            Pi.single j 1) := by
        rw [Matrix.mulVec_mulVec]
    _ = hA.eigenvectorUnitary.val *ᵥ
          ((RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) •
            Pi.single j 1) := by
        rw [hDiag]
    _ = (RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) •
          (hA.eigenvectorUnitary.val *ᵥ Pi.single j 1) := by
        rw [Matrix.mulVec_smul]
    _ = (RCLike.ofReal (Real.sqrt (hA.eigenvalues j)) : ℂ) • v := by
        rw [hU]

private noncomputable abbrev contractionSupport {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Type _ :=
  { j : n // 0 < (contractionGram_isHermitian X).eigenvalues j }

private noncomputable def contractionSupportBasis {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix n (contractionSupport X) ℂ :=
  fun i s => (contractionGram_isHermitian X).eigenvectorUnitary.val i s.1

private theorem contractionSupportBasis_isometry {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix.IsIsometry (contractionSupportBasis X) := by
  classical
  let hA := contractionGram_isHermitian X
  let U := hA.eigenvectorUnitary.val
  have hU_mem : U ∈ unitaryGroup n ℂ := hA.eigenvectorUnitary.prop
  have hStar : star U * U = 1 := mem_unitaryGroup_iff'.mp hU_mem
  have hUU : Uᴴ * U = 1 := by
    calc Uᴴ * U = star U * U := by
          rw [Matrix.star_eq_conjTranspose]
      _ = 1 := hStar
  unfold Matrix.IsIsometry
  ext s t
  have hEq : (contractionSupportBasis X)ᴴ * contractionSupportBasis X =
      (contractionSupportBasis X)ᴴ * contractionSupportBasis X := rfl
  have hMul :
      ((contractionSupportBasis X)ᴴ * contractionSupportBasis X) s t =
        (Uᴴ * U) s.1 t.1 := by
    change (∑ i : n, star (U i s.1) * U i t.1) =
      ∑ i : n, star (U i s.1) * U i t.1
    rfl
  have hUU_entry :
      (Uᴴ * U) s.1 t.1 = (1 : Matrix n n ℂ) s.1 t.1 := by
    rw [hUU]
  have hOne_n : (1 : Matrix n n ℂ) s.1 t.1 =
      if s.1 = t.1 then 1 else 0 := by
    exact Matrix.one_apply (α := ℂ) (i := s.1) (j := t.1)
  have hValNe : s ≠ t → s.1 ≠ t.1 := by
    intro hne heq
    have : s = t := Subtype.ext heq
    exact hne this
  have hIfEq :
      (if s.1 = t.1 then (1 : ℂ) else 0) =
        if s = t then 1 else 0 := by
    by_cases hs : s = t
    · subst hs
      simp
    · have hv : s.1 ≠ t.1 := hValNe hs
      simp [hv, hs]
  calc ((contractionSupportBasis X)ᴴ * contractionSupportBasis X) s t
      = (Uᴴ * U) s.1 t.1 := hMul
    _ = (1 : Matrix n n ℂ) s.1 t.1 := hUU_entry
    _ = if s.1 = t.1 then 1 else 0 := hOne_n
    _ = if s = t then 1 else 0 := hIfEq
    _ = (1 : Matrix (contractionSupport X) (contractionSupport X) ℂ) s t := by
        exact (Matrix.one_apply (α := ℂ) (i := s) (j := t)).symm

private theorem contractionGram_mulVec_eigenvectorBasis {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (j : n) :
    contractionGram X *ᵥ ⇑((contractionGram_isHermitian X).eigenvectorBasis j) =
      ((contractionGram_isHermitian X).eigenvalues j) •
        ⇑((contractionGram_isHermitian X).eigenvectorBasis j) :=
  (contractionGram_isHermitian X).mulVec_eigenvectorBasis j

private noncomputable def contractionSupport_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (s : contractionSupport X) : ℝ :=
  Real.sqrt ((contractionGram_isHermitian X).eigenvalues s.1)

private theorem contractionSupport_sqrt_pos {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (s : contractionSupport X) :
    0 < contractionSupport_sqrt X s := by
  unfold contractionSupport_sqrt
  exact Real.sqrt_pos.mpr s.2

private theorem contractionSupport_sqrt_sq {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (s : contractionSupport X) :
    (contractionSupport_sqrt X s) ^ 2 = (contractionGram_isHermitian X).eigenvalues s.1 := by
  unfold contractionSupport_sqrt
  exact Real.sq_sqrt (le_of_lt s.2)

private noncomputable def contractionSupport_image {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix n (contractionSupport X) ℂ :=
  fun i s =>
    ((RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ •
        (X *ᵥ ⇑((contractionGram_isHermitian X).eigenvectorBasis s.1))) i

private theorem contractionSupport_image_isometry {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Matrix.IsIsometry (contractionSupport_image X) := by
  classical
  let hA := contractionGram_isHermitian X
  have hOrtho : Orthonormal ℂ (fun i => hA.eigenvectorBasis i) :=
    hA.eigenvectorBasis.orthonormal
  have hInner : ∀ i j : n,
      inner (𝕜 := ℂ) (hA.eigenvectorBasis i) (hA.eigenvectorBasis j) =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp hOrtho) i j
    simpa using h
  have hFullDot : ∀ i j : n,
      (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    have hEq : (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis j)) =
        inner (𝕜 := ℂ) (hA.eigenvectorBasis i) (hA.eigenvectorBasis j) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [hEq, hInner]
  -- Gram inner product of `X v` via `Xᴴ * X`
  have hStarDot : ∀ a b : n,
      (star (X *ᵥ ⇑(hA.eigenvectorBasis a)) ⬝ᵥ X *ᵥ ⇑(hA.eigenvectorBasis b)) =
        (star (⇑(hA.eigenvectorBasis a)) ⬝ᵥ
          (contractionGram X *ᵥ ⇑(hA.eigenvectorBasis b))) := by
    intro a b
    calc (star (X *ᵥ ⇑(hA.eigenvectorBasis a)) ⬝ᵥ X *ᵥ ⇑(hA.eigenvectorBasis b))
        = ((star (⇑(hA.eigenvectorBasis a))) ᵥ* Xᴴ ⬝ᵥ X *ᵥ ⇑(hA.eigenvectorBasis b)) := by
          rw [Matrix.star_mulVec]
      _ = (star (⇑(hA.eigenvectorBasis a)) ⬝ᵥ Xᴴ *ᵥ X *ᵥ ⇑(hA.eigenvectorBasis b)) := by
          rw [← Matrix.dotProduct_mulVec]
      _ = (star (⇑(hA.eigenvectorBasis a)) ⬝ᵥ (Xᴴ * X) *ᵥ ⇑(hA.eigenvectorBasis b)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (star (⇑(hA.eigenvectorBasis a)) ⬝ᵥ
          (contractionGram X *ᵥ ⇑(hA.eigenvectorBasis b))) := rfl
  have hGramEig : ∀ j : n,
      contractionGram X *ᵥ ⇑(hA.eigenvectorBasis j) =
        (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) :=
    fun j => contractionGram_mulVec_eigenvectorBasis X j
  -- Eigenvector equation plus real-to-complex scalar
  have hDotEig : ∀ i j : n,
      (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ
        (contractionGram X *ᵥ ⇑(hA.eigenvectorBasis j))) =
        (RCLike.ofReal (hA.eigenvalues j) : ℂ) *
          (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis j)) := by
    intro i j
    rw [hGramEig j]
    have hSmul : ∀ k : n,
        ((hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) : n → ℂ) k =
          (RCLike.ofReal (hA.eigenvalues j) : ℂ) * ⇑(hA.eigenvectorBasis j) k := by
      intro k
      simp [Pi.smul_apply, RCLike.real_smul_eq_coe_mul]
    calc (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ
            (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j))
        = ∑ k : n, star (⇑(hA.eigenvectorBasis i) k) *
            ((hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) : n → ℂ) k := rfl
      _ = ∑ k : n, star (⇑(hA.eigenvectorBasis i) k) *
            ((RCLike.ofReal (hA.eigenvalues j) : ℂ) * ⇑(hA.eigenvectorBasis j) k) := by
          simp_rw [hSmul]
      _ = (RCLike.ofReal (hA.eigenvalues j) : ℂ) *
          ∑ k : n, star (⇑(hA.eigenvectorBasis i) k) * ⇑(hA.eigenvectorBasis j) k := by
          rw [Finset.mul_sum]
          congr 1
          ext k
          ring
      _ = (RCLike.ofReal (hA.eigenvalues j) : ℂ) *
          (star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis j)) := rfl
  have hDot : ∀ i j : n,
      (star (X *ᵥ ⇑(hA.eigenvectorBasis i)) ⬝ᵥ X *ᵥ ⇑(hA.eigenvectorBasis j)) =
        (RCLike.ofReal (hA.eigenvalues j) : ℂ) *
          if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [hStarDot i j, hDotEig i j, hFullDot i j]
  have hSqrtNe : ∀ s : contractionSupport X,
      (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) ≠ 0 := by
    intro s
    exact RCLike.ofReal_ne_zero.mpr (ne_of_gt (contractionSupport_sqrt_pos X s))
  -- Real scalar: star fixes `ofReal`
  have hStarReal : ∀ r : ℝ, star (RCLike.ofReal r : ℂ) = RCLike.ofReal r := by
    intro r
    rw [RCLike.star_def, RCLike.conj_ofReal]
  have hStarInv : ∀ s : contractionSupport X,
      star ((RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹) =
        (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ := by
    intro s
    rw [star_inv₀, hStarReal]
  -- Factor normalized columns: `c_s⁻¹ c_t⁻¹ * ⟨X v_s, X v_t⟩`
  have hImageEntry : ∀ s t : contractionSupport X,
      ((contractionSupport_image X)ᴴ * contractionSupport_image X) s t =
        (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
          (star (X *ᵥ ⇑(hA.eigenvectorBasis s.1)) ⬝ᵥ
            X *ᵥ ⇑(hA.eigenvectorBasis t.1)) := by
    intro s t
    simp only [conjTranspose_apply, mul_apply, contractionSupport_image,
      Pi.smul_apply, smul_eq_mul, dotProduct]
    have hStarSmul : ∀ i : n,
        star (((RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i)) =
          (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
            star ((X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i) := by
      intro i
      rw [star_mul, hStarInv s, mul_comm]
    calc ∑ i : n, star ((contractionSupport_image X) i s) * (contractionSupport_image X) i t
        = ∑ i : n,
            star (((RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
              (X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i)) *
              ((RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
                (X *ᵥ ⇑(hA.eigenvectorBasis t.1)) i) := rfl
      _ = ∑ i : n,
            ((RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
              star ((X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i)) *
              ((RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
                (X *ᵥ ⇑(hA.eigenvectorBasis t.1)) i) := by
          simp_rw [hStarSmul]
      _ = (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
          ∑ i : n, star ((X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i) *
            (X *ᵥ ⇑(hA.eigenvectorBasis t.1)) i := by
          have hComm : ∀ i : n,
              (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                star ((X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i) *
                ((RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
                  (X *ᵥ ⇑(hA.eigenvectorBasis t.1)) i) =
                (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                  (RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
                  (star ((X *ᵥ ⇑(hA.eigenvectorBasis s.1)) i) *
                    (X *ᵥ ⇑(hA.eigenvectorBasis t.1)) i) := by
            intro i; ring
          simp_rw [hComm, ← Finset.mul_sum]
  unfold Matrix.IsIsometry
  ext s t
  rw [hImageEntry s t, hDot s.1 t.1]
  have hIf : (if s.1 = t.1 then (1 : ℂ) else 0) =
      if s = t then (1 : ℂ) else 0 := by
    by_cases hs : s = t
    · subst hs; simp
    · have hNeVal : s.1 ≠ t.1 := by
        intro hEq
        exact hs (Subtype.ext hEq)
      simp [hNeVal, hs]
  rw [hIf]
  by_cases hs : s = t
  · subst hs
    have hSq : (contractionSupport_sqrt X s) ^ 2 = hA.eigenvalues s.1 :=
      contractionSupport_sqrt_sq X s
    have hOfRealSq : (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) ^ 2 =
        (RCLike.ofReal (hA.eigenvalues s.1) : ℂ) := by
      rw [← RCLike.ofReal_pow, hSq]
    have hNe : (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) ≠ 0 := hSqrtNe s
    calc (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          ((RCLike.ofReal (hA.eigenvalues s.1) : ℂ) * if s = s then 1 else 0)
        = (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (hA.eigenvalues s.1) : ℂ) := by simp
      _ = (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) ^ 2 := by rw [hOfRealSq]
      _ = 1 := by
          have hInv : (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
              (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) = 1 :=
            inv_mul_cancel₀ hNe
          calc (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) ^ 2
              = (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                ((RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) *
                (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)) := by ring
            _ = (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
                (1 * (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)) := by rw [hInv]
            _ = 1 := by rw [one_mul, inv_mul_cancel₀ hNe]
      _ = (1 : Matrix (contractionSupport X) (contractionSupport X) ℂ) s s := by
          simp
  · have hZero : (if s = t then (1 : ℂ) else 0) = 0 := by simp [hs]
    calc (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)⁻¹ *
          (RCLike.ofReal (contractionSupport_sqrt X t) : ℂ)⁻¹ *
          ((RCLike.ofReal (hA.eigenvalues t.1) : ℂ) * if s = t then 1 else 0)
        = 0 := by rw [hZero, mul_zero, mul_zero]
      _ = (1 : Matrix (contractionSupport X) (contractionSupport X) ℂ) s t := by
          simp [hs]

private theorem exists_contractionPolarUnitary {n : Type*} [Fintype n]
    [DecidableEq n] (X : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, U ∈ unitaryGroup n ℂ ∧
      U * contractionSupportBasis X = contractionSupport_image X := by
  classical
  have hB : Matrix.IsIsometry (contractionSupportBasis X) :=
    contractionSupportBasis_isometry X
  have hI : Matrix.IsIsometry (contractionSupport_image X) :=
    contractionSupport_image_isometry X
  exact Matrix.exists_unitary_mul_eq_of_isometry
    (contractionSupportBasis X) (contractionSupport_image X) hB hI

private theorem contractionPolarUnitary_mulVec_eigenvectorBasis {n : Type*}
    [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (U : Matrix n n ℂ)
    (_hU : U ∈ unitaryGroup n ℂ)
    (hEq : U * contractionSupportBasis X = contractionSupport_image X)
    (s : contractionSupport X) :
    (U * contractionSqrt X) *ᵥ
        ⇑((contractionGram_isHermitian X).eigenvectorBasis s.1) =
      X *ᵥ ⇑((contractionGram_isHermitian X).eigenvectorBasis s.1) := by
  classical
  let hA := contractionGram_isHermitian X
  let v : n → ℂ := ⇑(hA.eigenvectorBasis s.1)
  let c : ℂ := (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ)
  have hc_pos : 0 < contractionSupport_sqrt X s :=
    contractionSupport_sqrt_pos X s
  have hc_ne : c ≠ 0 := by
    unfold c
    exact RCLike.ofReal_ne_zero.mpr (ne_of_gt hc_pos)
  have hSqrt : contractionSqrt X *ᵥ v = c • v := by
    have h0 := contractionSqrt_mulVec_eigenvectorBasis X s.1
    have h1 : contractionSupport_sqrt X s =
        Real.sqrt (hA.eigenvalues s.1) := rfl
    calc contractionSqrt X *ᵥ v
        = (RCLike.ofReal (Real.sqrt (hA.eigenvalues s.1)) : ℂ) • v := h0
      _ = (RCLike.ofReal (contractionSupport_sqrt X s) : ℂ) • v := by
          rw [h1]
      _ = c • v := rfl
  have hBasis_col : (contractionSupportBasis X).col s = v := by
    ext i
    simp only [contractionSupportBasis, Matrix.col_apply,
      hA.eigenvectorUnitary_apply, v]
  have hBasis_mul : contractionSupportBasis X *ᵥ Pi.single s 1 = v := by
    calc contractionSupportBasis X *ᵥ Pi.single s 1
        = (contractionSupportBasis X).col s := by
          rw [Matrix.mulVec_single_one]
      _ = v := hBasis_col
  have hImage_col : (contractionSupport_image X).col s =
      c⁻¹ • (X *ᵥ v) := by
    ext i
    simp only [contractionSupport_image, Matrix.col_apply,
      Pi.smul_apply, smul_eq_mul, v, c]
  have hImage_mul : contractionSupport_image X *ᵥ Pi.single s 1 =
      c⁻¹ • (X *ᵥ v) := by
    calc contractionSupport_image X *ᵥ Pi.single s 1
        = (contractionSupport_image X).col s := by
          rw [Matrix.mulVec_single_one]
      _ = c⁻¹ • (X *ᵥ v) := hImage_col
  have hU_v : U *ᵥ v = c⁻¹ • (X *ᵥ v) := by
    have hLeft : (U * contractionSupportBasis X) *ᵥ Pi.single s 1 =
        U *ᵥ (contractionSupportBasis X *ᵥ Pi.single s 1) := by
      rw [Matrix.mulVec_mulVec]
    have hRight : (U * contractionSupportBasis X) *ᵥ Pi.single s 1 =
        contractionSupport_image X *ᵥ Pi.single s 1 := by
      rw [hEq]
    calc U *ᵥ v
        = U *ᵥ (contractionSupportBasis X *ᵥ Pi.single s 1) := by
          rw [hBasis_mul]
      _ = (U * contractionSupportBasis X) *ᵥ Pi.single s 1 := hLeft.symm
      _ = contractionSupport_image X *ᵥ Pi.single s 1 := hRight
      _ = c⁻¹ • (X *ᵥ v) := hImage_mul
  have hMul : (U * contractionSqrt X) *ᵥ v =
      U *ᵥ (contractionSqrt X *ᵥ v) := by
    rw [Matrix.mulVec_mulVec]
  calc (U * contractionSqrt X) *ᵥ v
      = U *ᵥ (contractionSqrt X *ᵥ v) := hMul
    _ = U *ᵥ (c • v) := by rw [hSqrt]
    _ = c • (U *ᵥ v) := by rw [Matrix.mulVec_smul]
    _ = c • (c⁻¹ • (X *ᵥ v)) := by rw [hU_v]
    _ = (c * c⁻¹) • (X *ᵥ v) := by rw [smul_smul]
    _ = (1 : ℂ) • (X *ᵥ v) := by rw [mul_inv_cancel₀ hc_ne]
    _ = X *ᵥ v := by rw [one_smul]

private theorem exists_contractionPolarUnitary_mul_contractionSqrt_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ,
      U ∈ unitaryGroup n ℂ ∧ U * contractionSqrt X = X := by
  classical
  obtain ⟨U, hU_mem, hU_eq⟩ := exists_contractionPolarUnitary X
  refine ⟨U, hU_mem, ?_⟩
  let hA := contractionGram_isHermitian X
  have hBasisEq : ∀ j : n,
      (U * contractionSqrt X) *ᵥ ⇑(hA.eigenvectorBasis j) =
        X *ᵥ ⇑(hA.eigenvectorBasis j) := by
    intro j
    by_cases hPos : 0 < hA.eigenvalues j
    · exact contractionPolarUnitary_mulVec_eigenvectorBasis X U hU_mem hU_eq ⟨j, hPos⟩
    · have hNonneg : 0 ≤ hA.eigenvalues j := contractionGram_eigenvalues_nonneg X j
      have hZero : hA.eigenvalues j = 0 := by
        have hLe : hA.eigenvalues j ≤ 0 := not_lt.mp hPos
        linarith
      have hGram : contractionGram X *ᵥ ⇑(hA.eigenvectorBasis j) = 0 := by
        calc contractionGram X *ᵥ ⇑(hA.eigenvectorBasis j)
            = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) :=
              contractionGram_mulVec_eigenvectorBasis X j
          _ = (0 : ℝ) • ⇑(hA.eigenvectorBasis j) := by rw [hZero]
          _ = 0 := by simp
      have hXZero : X *ᵥ ⇑(hA.eigenvectorBasis j) = 0 := by
        have hEquiv :=
          Matrix.conjTranspose_mul_self_mulVec_eq_zero X ⇑(hA.eigenvectorBasis j)
        have hGramEq : (Xᴴ * X) *ᵥ ⇑(hA.eigenvectorBasis j) = 0 := by
          simpa [contractionGram] using hGram
        exact hEquiv.mp hGramEq
      have hSqrtZero : contractionSqrt X *ᵥ ⇑(hA.eigenvectorBasis j) = 0 := by
        calc contractionSqrt X *ᵥ ⇑(hA.eigenvectorBasis j)
            = (RCLike.ofReal
                (Real.sqrt (hA.eigenvalues j)) : ℂ) • ⇑(hA.eigenvectorBasis j) :=
              contractionSqrt_mulVec_eigenvectorBasis X j
          _ = (RCLike.ofReal (Real.sqrt 0) : ℂ) • ⇑(hA.eigenvectorBasis j) := by
              rw [hZero]
          _ = 0 := by simp [Real.sqrt_zero]
      have hUSqrtZero :
          (U * contractionSqrt X) *ᵥ ⇑(hA.eigenvectorBasis j) = 0 := by
        calc (U * contractionSqrt X) *ᵥ ⇑(hA.eigenvectorBasis j)
            = U *ᵥ (contractionSqrt X *ᵥ ⇑(hA.eigenvectorBasis j)) := by
              rw [Matrix.mulVec_mulVec]
          _ = U *ᵥ (0 : n → ℂ) := by rw [hSqrtZero]
          _ = 0 := by rw [Matrix.mulVec_zero]
      calc (U * contractionSqrt X) *ᵥ ⇑(hA.eigenvectorBasis j)
          = 0 := hUSqrtZero
        _ = X *ᵥ ⇑(hA.eigenvectorBasis j) := by rw [hXZero]
        _ = X *ᵥ ⇑(hA.eigenvectorBasis j) := rfl
  let V := hA.eigenvectorUnitary.val
  have hV_mem : V ∈ unitaryGroup n ℂ := hA.eigenvectorUnitary.prop
  have hVCol : ∀ j : n, Matrix.col V j = ⇑(hA.eigenvectorBasis j) :=
    fun j => hA.eigenvectorUnitary_col_eq j
  have hMulV : (U * contractionSqrt X) * V = X * V := by
    ext i j
    have h1 : ((U * contractionSqrt X) * V) i j =
        ((U * contractionSqrt X) *ᵥ Matrix.col V j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply]
    have h2 : (X * V) i j = (X *ᵥ Matrix.col V j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply]
    rw [h1, h2, hVCol j, hBasisEq j]
  have hStar : V * star V = 1 := mem_unitaryGroup_iff.mp hV_mem
  calc U * contractionSqrt X
      = (U * contractionSqrt X) * 1 := by rw [mul_one]
    _ = (U * contractionSqrt X) * (V * star V) := by rw [← hStar]
    _ = (U * contractionSqrt X * V) * star V := by rw [← mul_assoc]
    _ = (X * V) * star V := by rw [hMulV]
    _ = X * (V * star V) := by rw [mul_assoc]
    _ = X * 1 := by rw [hStar]
    _ = X := by rw [mul_one]

namespace Matrix

public theorem exists_eq_average_two_unitaries_of_norm_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : ‖X‖ ≤ 1) :
    ∃ U V : Matrix n n ℂ,
      U ∈ unitaryGroup n ℂ ∧ V ∈ unitaryGroup n ℂ ∧
        X = ((2 : ℂ)⁻¹) • (U + V) := by
  obtain ⟨P, hP_mem, hP_eq⟩ :=
    exists_contractionPolarUnitary_mul_contractionSqrt_eq X
  have hSqrt_herm : (contractionSqrt X).IsHermitian :=
    contractionSqrt_isHermitian X
  have hSqrt_norm : ‖contractionSqrt X‖ ≤ 1 :=
    contractionSqrt_norm_le_one X hX
  obtain ⟨W, Z, hW_mem, hZ_mem, hSqrt_avg⟩ :=
    exists_eq_average_two_unitaries_of_isHermitian
      (contractionSqrt X) hSqrt_herm hSqrt_norm
  refine ⟨P * W, P * Z, ?_, ?_, ?_⟩
  · exact (unitaryGroup n ℂ).mul_mem hP_mem hW_mem
  · exact (unitaryGroup n ℂ).mul_mem hP_mem hZ_mem
  · calc X = P * contractionSqrt X := hP_eq.symm
      _ = P * (((2 : ℂ)⁻¹) • (W + Z)) := by rw [hSqrt_avg]
      _ = ((2 : ℂ)⁻¹) • (P * (W + Z)) := by rw [Matrix.mul_smul]
      _ = ((2 : ℂ)⁻¹) • (P * W + P * Z) := by rw [Matrix.mul_add]

end Matrix

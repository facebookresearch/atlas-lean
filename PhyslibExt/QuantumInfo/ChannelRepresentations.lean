/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Channels

/-!
# Channel representations: Kraus and Choi forms

## i. Overview

The channel representation theorem (Watrous, Corollary 2.27, combining
Theorems 2.22 and 2.26) assembled over Physlib's `CPTPMap`:
a linear map between matrix spaces underlies a channel exactly when it has
a Kraus representation whose operators satisfy the completeness relation,
and exactly when its Choi matrix is positive semidefinite with
partial trace over the output factor the identity. The underlying complete-positivity
characterization is Watrous Theorem 2.22. The unitary-with-ancilla
realization (the unitary form of Stinespring's dilation theorem) is
Physlib's purification `CPTPMap.exists_purify`, not proved here.

Audit receipts: complete positivity is `MatrixMap.IsCompletelyPositive`,
with the Choi criterion `MatrixMap.choi_PSD_iff_CP_map`; the Kraus
decomposition of a completely positive map is
`MatrixMap.IsCompletelyPositive.exists_kraus`; the Kraus form
`MatrixMap.of_kraus` is completely positive by
`MatrixMap.of_kraus_isCompletelyPositive`; trace preservation reads on the
Choi matrix through `MatrixMap.IsTracePreserving_iff_trace_choi`; the
bundled constructions are `CPTPMap.CPTP_of_choi_PSD_Tr`,
`CPTPMap.choi_PSD_of_CPTP`, and the dilation `CPTPMap.exists_purify`.
Partial-trace and measurement channels are already bundled instances
(`CPTPMap.traceLeft`, `CPTPMap.traceRight`, `POVM.measurementMap`), so no
instance work remains here. The genuinely new pieces are the completeness
relation for Kraus operators of a trace-preserving map, the bundled
channel built from Kraus operators, the packaging of the equivalences,
and the transpose nonvacuity example: transposition is positive but not
completely positive, since its Choi matrix (the swap operator) has a
negative eigenvalue.

## ii. Key results

- `kraus_sum_eq_one_of_isTracePreserving`: the Kraus completeness relation.
- `exists_kraus_of_cptpMap`: every channel has Kraus operators satisfying it.
- `ofKraus`: the channel built from Kraus operators satisfying it.
- `exists_cptpMap_iff_kraus`, `exists_cptpMap_iff_choi`: the equivalences.
- `transposeMap_isPositive`, `transposeMap_not_isCompletelyPositive`:
  positivity does not imply complete positivity.

## iii. Table of contents

- Kraus completeness and the two constructions.
- The Choi and Kraus characterizations of channels.
- The transpose map.

## iv. References

John Watrous, The Theory of Quantum Information, Cambridge University
Press, 2018, Theorem 2.22 (complete positivity), Theorem 2.26
(trace preservation), Corollary 2.27 (channel representations combining
Theorems 2.22 and 2.26), and Section 2.2 (dilations).
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.Channels

open scoped Matrix ComplexOrder

set_option autoImplicit false

/-- **Kraus completeness relation.** If the Kraus map of `K` is trace
preserving, then `∑ k, (K k)ᴴ * K k = 1`. -/
lemma kraus_sum_eq_one_of_isTracePreserving {dIn dOut : Type*}
    [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
    {κ : Type*} [Fintype κ] (K : κ → Matrix dOut dIn ℂ)
    (hTP : (MatrixMap.of_kraus K K).IsTracePreserving) :
    ∑ k, (K k).conjTranspose * (K k) = 1 := by
  have hkey : ∀ X : Matrix dIn dIn ℂ,
      (∑ k, K k * X * (K k).conjTranspose).trace =
        (((∑ k, (K k).conjTranspose * (K k))) * X).trace := by
    intro X
    rw [Finset.sum_mul]
    rw [Matrix.trace_sum _ _, Matrix.trace_sum _ _]
    apply Finset.sum_congr rfl
    intro k _
    exact Matrix.trace_mul_cycle _ _ _
  have hPhi : ∀ X : Matrix dIn dIn ℂ,
      (MatrixMap.of_kraus K K) X = ∑ k, K k * X * (K k).conjTranspose := by
    intro X
    simp [MatrixMap.of_kraus, Matrix.sum_apply, Matrix.mul_apply]
  have h : ∀ X : Matrix dIn dIn ℂ,
      (((∑ k, (K k).conjTranspose * (K k))) * X).trace = (1 * X).trace := by
    intro X
    have h1 : (∑ k, K k * X * (K k).conjTranspose).trace = X.trace := by
      have ht := hTP X
      rw [hPhi X] at ht
      exact ht
    rw [← hkey X, h1, Matrix.one_mul]
  exact Matrix.ext_iff_trace_mul_right.mpr h

/-- **Kraus operators of a channel.** Every `CPTPMap` is the Kraus map of a
family of operators satisfying the completeness relation. -/
lemma exists_kraus_of_cptpMap {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dOut] (Λ : CPTPMap dIn dOut) :
    ∃ K : (dOut × dIn) → Matrix dOut dIn ℂ,
      Λ.map = MatrixMap.of_kraus K K ∧ ∑ k, (K k).conjTranspose * (K k) = 1 := by
  obtain ⟨K, hKeq⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Λ.map Λ.cp
  have hTP' : (MatrixMap.of_kraus K K).IsTracePreserving := by
    rw [← hKeq]
    exact Λ.TP
  have hKsum := kraus_sum_eq_one_of_isTracePreserving K hTP'
  exact ⟨K, hKeq, hKsum⟩

/-- **The channel of a Kraus family** satisfying the completeness relation. -/
def ofKraus {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn]
    [DecidableEq dOut] {κ : Type*} [Fintype κ] (K : κ → Matrix dOut dIn ℂ)
    (hK : ∑ k, (K k).conjTranspose * (K k) = 1) : CPTPMap dIn dOut where
  toLinearMap := MatrixMap.of_kraus K K
  cp := MatrixMap.of_kraus_isCompletelyPositive K
  TP := by
    intro X
    have hPhi : (MatrixMap.of_kraus K K) X = ∑ k, K k * X * (K k).conjTranspose := by
      simp [MatrixMap.of_kraus, Matrix.sum_apply, Matrix.mul_apply]
    rw [hPhi]
    have hkey : (∑ k, K k * X * (K k).conjTranspose).trace =
        (((∑ k, (K k).conjTranspose * (K k))) * X).trace := by
      rw [Finset.sum_mul]
      rw [Matrix.trace_sum _ _, Matrix.trace_sum _ _]
      apply Finset.sum_congr rfl
      intro k _
      exact Matrix.trace_mul_cycle _ _ _
    rw [hkey, hK, Matrix.one_mul]

/-- The underlying map of `ofKraus` is the Kraus map. -/
lemma ofKraus_map {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dOut] {κ : Type*} [Fintype κ]
    (K : κ → Matrix dOut dIn ℂ) (hK : ∑ k, (K k).conjTranspose * (K k) = 1) :
    (ofKraus K hK).map = MatrixMap.of_kraus K K :=
  rfl

/-- **Kraus characterization of channels** (Watrous, Corollary 2.27): a
linear map underlies a `CPTPMap` exactly when it is the Kraus map of a
family satisfying the completeness relation. -/
lemma exists_cptpMap_iff_kraus {dIn dOut : Type*} [Fintype dIn]
    [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
    [Nonempty dIn] [Nonempty dOut]
    (Φ : MatrixMap dIn dOut ℂ) :
    (∃ Λ : CPTPMap dIn dOut, Λ.map = Φ) ↔
      ∃ K : (dOut × dIn) → Matrix dOut dIn ℂ,
        Φ = MatrixMap.of_kraus K K ∧ ∑ k, (K k).conjTranspose * (K k) = 1 := by
  constructor
  · intro ⟨Λ, hΛ⟩
    obtain ⟨K, hKeq, hKsum⟩ := exists_kraus_of_cptpMap Λ
    exact ⟨K, hΛ.symm.trans hKeq, hKsum⟩
  · intro ⟨K, hKeq, hKsum⟩
    refine ⟨ofKraus K hKsum, ?_⟩
    rw [ofKraus_map]
    exact hKeq.symm

/-- **Choi characterization of channels** (Watrous, Corollary 2.27): a linear
map underlies a `CPTPMap` exactly when its Choi matrix is positive
semidefinite and its partial trace over the output factor is the identity. -/
lemma exists_cptpMap_iff_choi {dIn dOut : Type*} [Fintype dIn]
    [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
    [Nonempty dIn] [Nonempty dOut]
    (Φ : MatrixMap dIn dOut ℂ) :
    (∃ Λ : CPTPMap dIn dOut, Λ.map = Φ) ↔
      Φ.choi_matrix.PosSemidef ∧ Φ.choi_matrix.traceLeft = 1 := by
  constructor
  · intro ⟨Λ, hΛ⟩
    have hPSD : Λ.map.choi_matrix.PosSemidef := CPTPMap.choi_PSD_of_CPTP Λ
    have hTr : Λ.map.choi_matrix.traceLeft = 1 :=
      (MatrixMap.IsTracePreserving_iff_trace_choi Λ.map).mp Λ.TP
    have hPSD' : Φ.choi_matrix.PosSemidef := by
      rw [← hΛ]
      exact hPSD
    have hTr' : Φ.choi_matrix.traceLeft = 1 := by
      rw [← hΛ]
      exact hTr
    exact ⟨hPSD', hTr'⟩
  · intro ⟨hPSD, hTr⟩
    refine ⟨CPTPMap.CPTP_of_choi_PSD_Tr hPSD hTr, ?_⟩
    exact MatrixMap.choi_map_inv Φ

/-- **The transpose map** on square matrices, as a matrix map. -/
def transposeMap (d : Type*) [Fintype d] : MatrixMap d d ℂ where
  toFun X := X.transpose
  map_add' _ _ := Matrix.transpose_add _ _
  map_smul' _ _ := Matrix.transpose_smul _ _

/-- Transposition is positive: it sends positive semidefinite matrices to
positive semidefinite matrices. -/
lemma transposeMap_isPositive {d : Type*} [Fintype d] [DecidableEq d] :
    (transposeMap d).IsPositive := by
  intro M hM
  simpa [transposeMap] using hM.transpose

/-- Test vector for the transpose example: `1` at `(0, 1)` and `-1` at
`(1, 0)`. -/
private def transposeTestVec : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

/-- The swap operator, in the form of the Choi matrix of transposition. -/
private def transposeSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j => if i.1 = j.2 ∧ i.2 = j.1 then (1 : ℂ) else 0

/-- Transposition on a two-dimensional space is not completely positive:
its Choi matrix is the swap operator, which has eigenvalue `-1`. -/
lemma transposeMap_not_isCompletelyPositive :
    ¬ (transposeMap (Fin 2)).IsCompletelyPositive := by
  intro hCP
  have hPSD : (transposeMap (Fin 2)).choi_matrix.PosSemidef :=
    (MatrixMap.choi_PSD_iff_CP_map (transposeMap (Fin 2))).mp hCP
  have hchoi_eq : (transposeMap (Fin 2)).choi_matrix = transposeSwap := by
    ext p q
    obtain ⟨a1, b1⟩ := p
    obtain ⟨a2, b2⟩ := q
    fin_cases a1 <;> fin_cases b1 <;> fin_cases a2 <;> fin_cases b2 <;> rfl
  have hquad_S : star transposeTestVec ⬝ᵥ (transposeSwap *ᵥ transposeTestVec) = -2 := by
    simp only [dotProduct, Matrix.mulVec, transposeSwap, transposeTestVec, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    simp
    have hv1 : transposeTestVec (0, 1) = 1 := rfl
    have hv2 : transposeTestVec (1, 0) = -1 := rfl
    rw [hv1, hv2]
    simp
    ring
  have hquad : star transposeTestVec ⬝ᵥ
      (((transposeMap (Fin 2)).choi_matrix) *ᵥ transposeTestVec) = -2 := by
    rw [hchoi_eq]
    exact hquad_S
  have hnonneg := hPSD.dotProduct_mulVec_nonneg transposeTestVec
  rw [hquad] at hnonneg
  have hcontra : ¬ (0 : ℂ) ≤ (-2 : ℂ) := by
    rw [Complex.nonneg_iff]
    simp
  exact hcontra hnonneg

end PhyslibExt.QuantumInfo.Channels

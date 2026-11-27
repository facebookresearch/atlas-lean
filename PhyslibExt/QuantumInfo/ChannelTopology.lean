/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Channels

/-!
# Topology of the space of quantum channels

## i. Overview

The space `CPTPMap dIn dOut` of quantum channels between finite-dimensional
systems, with the topology Physlib induces from the Choi matrix, is compact,
and the basic channel operations are continuous: applying a channel to a
matrix or a state, composing channels, and tensoring channels. The Choi
image is the set of positive semidefinite matrices whose left partial trace
is the identity; it is closed, and it is bounded because a positive
semidefinite matrix is at most its trace times the identity while the trace
of a channel's Choi matrix is the input dimension. Continuity of
application is entrywise linearity in the Choi matrix. Tensor products of
states and measurement probabilities are also continuous, which is what
continuity of acceptance probabilities in interactive protocols consumes.

## ii. Key results

- `instCompactSpaceCPTPMap`: channels between fixed finite systems form a
  compact space.
- `continuous_channel_apply`, `continuous_compose`, `continuous_tensor`:
  the channel operations are jointly continuous.

## iii. Table of contents

- The Choi image: `range_choi`, `isCompact_range_choi`.
- Compactness: `instCompactSpaceCPTPMap`.
- Continuity: `continuous_map_apply`, `continuous_channel_apply`,
  `continuous_compose`, `continuous_tensor`, `continuous_state_prod`,
  `continuous_measure`.

## iv. References

John Watrous, The Theory of Quantum Information, Cambridge University Press,
2018, Section 2.2 (the Choi representation of a channel).
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.ChannelTopology

set_option autoImplicit false

open scoped Matrix ComplexOrder Kronecker

variable {dIn dOut dM : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut]
  [DecidableEq dOut] [Fintype dM] [DecidableEq dM]

/-- The Choi image of the channel space: positive semidefinite matrices
with left partial trace `1`. -/
lemma range_choi :
    Set.range (CPTPMap.choi (dIn := dIn) (dOut := dOut)) =
      {C : Matrix (dOut × dIn) (dOut × dIn) ℂ | C.PosSemidef ∧ C.traceLeft = 1} := by
  ext C
  constructor
  · rintro ⟨Λ, rfl⟩
    refine ⟨CPTPMap.choi_PSD_of_CPTP Λ, ?_⟩
    have h := (MatrixMap.IsTracePreserving_iff_trace_choi Λ.map).mp Λ.TP
    simpa [CPTPMap.choi] using h
  · rintro ⟨hPSD, hTr⟩
    exact ⟨CPTPMap.CPTP_of_choi_PSD_Tr (M := C) hPSD hTr, CPTPMap.choi_of_CPTP_of_choi C⟩

/-- The Choi image is closed. -/
lemma isClosed_range_choi :
    IsClosed (Set.range (CPTPMap.choi (dIn := dIn) (dOut := dOut))) := by
  rw [range_choi]
  have hTr : Continuous fun C : Matrix (dOut × dIn) (dOut × dIn) ℂ => C.traceLeft := by
    unfold Matrix.traceLeft
    fun_prop
  exact isClosed_setOfPred_posSemidef.inter (isClosed_eq hTr continuous_const)

/-- The Choi image is bounded by the input dimension times the identity. -/
lemma range_choi_subset :
    Set.range (CPTPMap.choi (dIn := dIn) (dOut := dOut)) ⊆
      HermitianMat.mat '' Set.Icc (0 : HermitianMat (dOut × dIn) ℂ)
        ((Fintype.card dIn : ℝ) • 1) := by
  rintro C ⟨Λ, rfl⟩
  have hpsd : Λ.choi.PosSemidef := CPTPMap.choi_PSD_of_CPTP Λ
  let A : HermitianMat (dOut × dIn) ℂ := ⟨Λ.choi, hpsd.1⟩
  have h0 : 0 ≤ A := by
    rw [HermitianMat.zero_le_iff]
    exact hpsd
  have hTr : A.trace = (Fintype.card dIn : ℝ) := by
    have h1 : A.trace = Complex.re Λ.choi.trace := rfl
    rw [h1, CPTPMap.Tr_of_choi_of_CPTP Λ]
    simp
  have hle : A ≤ (Fintype.card dIn : ℝ) • 1 := by
    rw [← hTr]
    exact HermitianMat.le_trace_smul_one h0
  exact ⟨A, ⟨h0, hle⟩, rfl⟩

/-- The Choi image is compact. -/
lemma isCompact_range_choi :
    IsCompact (Set.range (CPTPMap.choi (dIn := dIn) (dOut := dOut))) := by
  refine IsCompact.of_isClosed_subset
    ((isCompact_Icc (a := (0 : HermitianMat (dOut × dIn) ℂ))
      (b := ((Fintype.card dIn : ℝ) • 1))).image
      HermitianMat.continuous_mat) ?_ ?_
  · exact isClosed_range_choi
  · exact range_choi_subset

/-- Channels between fixed finite systems form a compact space, through
the Choi embedding. -/
instance instCompactSpaceCPTPMap : CompactSpace (CPTPMap dIn dOut) := by
  rw [← isCompact_univ_iff]
  have hmem := (CPTPMap.choi_IsEmbedding (dIn := dIn) (dOut := dOut)).isCompact_iff (s := Set.univ)
  rw [Set.image_univ] at hmem
  exact hmem.mpr isCompact_range_choi

/-- The `(b, b')` entry of a channel applied to a matrix unit is a Choi
entry, hence continuous in the channel. -/
lemma continuous_map_single (a a' : dIn) (b b' : dOut) :
    Continuous fun Λ : CPTPMap dIn dOut => Λ.map (Matrix.single a a' 1) b b' := by
  exact CPTPMap.choi_IsEmbedding.continuous.matrix_elem (b, a) (b', a')

/-- Applying a channel's underlying linear map is jointly continuous in
the channel and the matrix. -/
lemma continuous_map_apply :
    Continuous fun p : CPTPMap dIn dOut × Matrix dIn dIn ℂ => p.1.map p.2 := by
  have hmap : ∀ Λ : CPTPMap dIn dOut, Λ.map = MatrixMap.of_choi_matrix Λ.choi := by
    intro Λ
    exact (MatrixMap.choi_map_inv Λ.map).symm
  simp_rw [hmap]
  refine continuous_matrix fun b₁ b₂ => ?_
  change Continuous fun p : CPTPMap dIn dOut × Matrix dIn dIn ℂ =>
    ∑ a₁, ∑ a₂, p.2 a₁ a₂ * p.1.choi (b₁, a₁) (b₂, a₂)
  have hchoi : Continuous (CPTPMap.choi (dIn := dIn) (dOut := dOut)) :=
    CPTPMap.choi_IsEmbedding.continuous
  exact continuous_finsetSum _ (fun a₁ _ =>
    continuous_finsetSum _ (fun a₂ _ =>
      ((continuous_snd.matrix_elem a₁ a₂).mul
        ((hchoi.matrix_elem (b₁, a₁) (b₂, a₂)).comp continuous_fst))))

/-- Applying a channel to a state is jointly continuous. -/
lemma continuous_channel_apply :
    Continuous fun p : CPTPMap dIn dOut × MState dIn => p.1 p.2 := by
  apply continuous_induced_rng.2
  apply continuous_induced_rng.2
  change Continuous fun p : CPTPMap dIn dOut × MState dIn => p.1.map p.2.m
  have hM : Continuous fun ρ : MState dIn => ρ.m := MState.Continuous_Matrix
  exact continuous_map_apply.comp (continuous_fst.prodMk (hM.comp continuous_snd))

/-- Composition of channels is jointly continuous. -/
lemma continuous_compose :
    Continuous fun p : CPTPMap dM dOut × CPTPMap dIn dM => p.1 ∘ₘ p.2 := by
  rw [CPTPMap.choi_IsEmbedding.isInducing.continuous_iff]
  refine continuous_matrix fun ij₁ ij₂ => ?_
  obtain ⟨j₁, i₁⟩ := ij₁; obtain ⟨j₂, i₂⟩ := ij₂
  change Continuous fun p : CPTPMap dM dOut × CPTPMap dIn dM =>
    p.1.map (p.2.map (Matrix.single i₁ i₂ 1)) j₁ j₂
  have hY : Continuous fun p : CPTPMap dM dOut × CPTPMap dIn dM =>
      p.2.map (Matrix.single i₁ i₂ 1) :=
    (continuous_map_apply (dIn := dIn) (dOut := dM)).comp
      (continuous_snd.prodMk continuous_const)
  have hZ := (continuous_map_apply (dIn := dM) (dOut := dOut)).comp
    (show Continuous fun p : CPTPMap dM dOut × CPTPMap dIn dM =>
      (p.1, p.2.map (Matrix.single i₁ i₂ 1)) from continuous_fst.prodMk hY)
  exact hZ.matrix_elem j₁ j₂

/-- The tensor product of channels is jointly continuous. -/
lemma continuous_tensor {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂]
    [Fintype dO₁] [Fintype dO₂] [DecidableEq dI₁] [DecidableEq dI₂]
    [DecidableEq dO₁] [DecidableEq dO₂] :
    Continuous fun p : CPTPMap dI₁ dO₁ × CPTPMap dI₂ dO₂ => p.1 ⊗ᶜᵖ p.2 := by
  rw [CPTPMap.choi_IsEmbedding.isInducing.continuous_iff]
  refine continuous_matrix fun ij₁ ij₂ => ?_
  obtain ⟨⟨o₁₁, o₂₁⟩, ⟨i₁₁, i₂₁⟩⟩ := ij₁
  obtain ⟨⟨o₁₂, o₂₂⟩, ⟨i₁₂, i₂₂⟩⟩ := ij₂
  have h1 : ∀ (a a' : dI₁) (b b' : dO₁),
      Continuous fun p : CPTPMap dI₁ dO₁ × CPTPMap dI₂ dO₂ =>
        p.1.map (Matrix.single a a' 1) b b' := by
    intro a a' b b'
    exact (continuous_map_single a a' b b').comp continuous_fst
  have h2 : ∀ (a a' : dI₂) (b b' : dO₂),
      Continuous fun p : CPTPMap dI₁ dO₁ × CPTPMap dI₂ dO₂ =>
        p.2.map (Matrix.single a a' 1) b b' := by
    intro a a' b b'
    exact (continuous_map_single a a' b b').comp continuous_snd
  change Continuous fun p : CPTPMap dI₁ dO₁ × CPTPMap dI₂ dO₂ =>
    ((p.1 ⊗ᶜᵖ p.2).map (Matrix.single (i₁₁, i₂₁) (i₁₂, i₂₂) 1)) (o₁₁, o₂₁) (o₁₂, o₂₂)
  change Continuous fun p : CPTPMap dI₁ dO₁ × CPTPMap dI₂ dO₂ =>
    (p.1.map.kron p.2.map) (Matrix.single (i₁₁, i₂₁) (i₁₂, i₂₂) 1) (o₁₁, o₂₁) (o₁₂, o₂₂)
  have hsingle : Matrix.single (i₁₁, i₂₁) (i₁₂, i₂₂) (1 : ℂ) =
      (Matrix.single i₁₁ i₁₂ 1) ⊗ₖ (Matrix.single i₂₁ i₂₂ 1) := by
    rw [Matrix.single_kronecker_single]
    simp
  have heq : ∀ p : CPTPMap dI₁ dO₁ × CPTPMap dI₂ dO₂,
      (p.1.map.kron p.2.map) (Matrix.single (i₁₁, i₂₁) (i₁₂, i₂₂) 1) (o₁₁, o₂₁) (o₁₂, o₂₂) =
        p.1.map (Matrix.single i₁₁ i₁₂ 1) o₁₁ o₁₂ *
          p.2.map (Matrix.single i₂₁ i₂₂ 1) o₂₁ o₂₂ := by
    intro p
    rw [hsingle, MatrixMap.kron_map_of_kron_state, Matrix.kroneckerMap_apply]
  simp only [heq]
  exact (h1 i₁₁ i₁₂ o₁₁ o₁₂).mul (h2 i₂₁ i₂₂ o₂₁ o₂₂)

/-- The tensor product of states is jointly continuous. -/
lemma continuous_state_prod {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂] :
    Continuous fun p : MState d₁ × MState d₂ => p.1 ⊗ᴹ p.2 := by
  apply continuous_induced_rng.2
  apply continuous_induced_rng.2
  change Continuous fun p : MState d₁ × MState d₂ => p.1.m ⊗ₖ p.2.m
  refine continuous_matrix fun ij₁ ij₂ => ?_
  obtain ⟨i₁, i₂⟩ := ij₁
  obtain ⟨j₁, j₂⟩ := ij₂
  simp_rw [Matrix.kroneckerMap_apply]
  have hM1 : Continuous fun ρ : MState d₁ => ρ.m := MState.Continuous_Matrix
  have hM2 : Continuous fun ρ : MState d₂ => ρ.m := MState.Continuous_Matrix
  exact ((hM1.comp continuous_fst).matrix_elem i₁ j₁).mul
    ((hM2.comp continuous_snd).matrix_elem i₂ j₂)

/-- Measurement probabilities are continuous in the state. -/
lemma continuous_measure {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ : POVM X d) (x : X) :
    Continuous fun ρ : MState d => Λ.measure ρ x := by
  apply continuous_induced_rng.2
  change Continuous fun ρ : MState d => inner ℝ (Λ.mats x) ρ.M
  have hM : Continuous fun ρ : MState d => ρ.M := MState.Continuous_HermitianMat
  exact continuous_const.inner hM

end PhyslibExt.QuantumInfo.ChannelTopology

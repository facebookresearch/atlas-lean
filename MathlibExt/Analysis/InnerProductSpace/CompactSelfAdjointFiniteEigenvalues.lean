/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

@[expose] public section

open Function Set Filter Topology
open Module End

namespace MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvalues

/-!
# Eigenvalues of a compact self-adjoint operator bounded away from zero are finite

For a compact self-adjoint operator `T` on a Hilbert space, only finitely many
eigenvalues can satisfy `ε ≤ ‖μ‖` for any fixed `ε > 0`. This is the part of the
book's maximum principle (Theorem, May 11, 2021 section) that says the nonzero
eigenvalues, ordered by decreasing modulus, tend to `0`: if infinitely many
eigenvalues were bounded below, unit eigenvectors for distinct eigenvalues would
be pairwise orthogonal, so their images under `T` would stay `ε`-separated and
could not have a convergent subsequence, contradicting compactness.

The v1 formalization of the maximum principle is left unproved and is not
ported here; the statement below is proved from scratch. Mathlib's
`Module.End.finite_hasEigenvalue` proves finiteness of all eigenvalues
for finite-dimensional vector spaces, under `Module.Finite`. The theorem
below applies on a complete inner-product space of arbitrary dimension:
compactness, self-adjointness and a positive norm threshold give a finite
set of distinct eigenvalues. A related private MathlibExt lemma,
`CompactSpectralWanted.aux_finite_eigenvalues`, handles compact normal operators
over `ℂ`; `compactNormal_hilbertBasis` provides a related public spectral
decomposition over `ℂ`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle`
(Theorem (Maximum principle), May 11, 2021). The full ordered eigenvalue
sequence of that theorem is not proved here, only the finiteness above
`ε` (compare Batch 11, which proved the norm-attained eigenvalue, and
Batch 12, which proved the range decomposition).
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The norm of an eigenvalue of a bounded linear operator is at most the
operator norm: if `T x = μ • x` for a nonzero vector `x`, then
`‖μ‖ * ‖x‖ = ‖T x‖ ≤ ‖T‖ * ‖x‖`. -/
theorem norm_hasEigenvalue_le {T : H →L[𝕜] H} {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ) : ‖μ‖ ≤ ‖T‖ := by
  obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
  have hxT : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx_mem
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hle : ‖μ‖ * ‖x‖ ≤ ‖T‖ * ‖x‖ := by
    calc ‖μ‖ * ‖x‖ = ‖T x‖ := by rw [hxT, norm_smul]
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  exact le_of_mul_le_mul_right hle hpos

/-- **Finiteness of eigenvalues bounded away from zero.** For a compact
self-adjoint operator `T` and any `ε > 0`, the set of eigenvalues `μ` of `T`
with `ε ≤ ‖μ‖` is finite. -/
theorem finite_eigenvalues_of_ge {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : 𝕜 | Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) μ ∧ ε ≤ ‖μ‖} := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e := hinf.natEmbedding with hedef
  have ha : ∀ n, Module.End.HasEigenvalue (T : H →ₗ[𝕜] H) ((e n : 𝕜)) ∧
      ε ≤ ‖(e n : 𝕜)‖ := fun n => (e n).2
  have hinj : Function.Injective (fun n => ((e n : 𝕜))) := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have hex : ∀ n, ∃ x : H, T x = ((e n : 𝕜)) • x ∧ ‖x‖ = 1 := by
    intro n
    obtain ⟨x, hx_mem, hx_ne⟩ := (ha n).1.exists_hasEigenvector
    have hxT : T x = ((e n : 𝕜)) • x := Module.End.mem_eigenspace_iff.mp hx_mem
    refine ⟨(((‖x‖⁻¹ : ℝ)) : 𝕜) • x, ?_, ?_⟩
    · rw [map_smul, hxT]
      exact (smul_comm _ _ _).symm
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx_ne)]
  choose u hu_eig hu_norm using hex
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have horth : ∀ m n, m ≠ n → @inner 𝕜 H _ (u m) (u n) = 0 := by
    intro m n hmn
    have hne : ((e m : 𝕜)) ≠ ((e n : 𝕜)) := fun hcon => hmn (hinj hcon)
    exact hsym.orthogonalFamily_eigenspaces hne
      ⟨u m, Module.End.mem_eigenspace_iff.mpr (hu_eig m)⟩
      ⟨u n, Module.End.mem_eigenspace_iff.mpr (hu_eig n)⟩
  have hsep : ∀ m n, m ≠ n → ε ≤ ‖T (u m) - T (u n)‖ := by
    intro m n hmn
    have h1 : T (u m) - T (u n)
        = ((e m : 𝕜)) • (u m) - ((e n : 𝕜)) • (u n) := by
      rw [hu_eig m, hu_eig n]
    have hort : @inner 𝕜 H _ (((e m : 𝕜)) • (u m)) (((e n : 𝕜)) • (u n)) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth m n hmn, mul_zero, mul_zero]
    have hpyth : ‖T (u m) - T (u n)‖ ^ 2
        = ‖((e m : 𝕜))‖ ^ 2 + ‖((e n : 𝕜))‖ ^ 2 := by
      have hnorm : ‖((e m : 𝕜)) • (u m) - ((e n : 𝕜)) • (u n)‖ ^ 2
          = ‖((e m : 𝕜)) • (u m)‖ ^ 2
            - 2 * RCLike.re (@inner 𝕜 H _ (((e m : 𝕜)) • (u m)) (((e n : 𝕜)) • (u n)))
            + ‖((e n : 𝕜)) • (u n)‖ ^ 2 :=
        norm_sub_sq _ _
      rw [h1, hnorm, hort]
      simp [norm_smul, hu_norm m, hu_norm n]
    have hge : ε ^ 2 ≤ ‖T (u m) - T (u n)‖ ^ 2 := by
      rw [hpyth]
      have hm := (ha m).2
      have hn := (ha n).2
      nlinarith [sq_nonneg (‖((e m : 𝕜))‖ - ε), sq_nonneg (‖((e n : 𝕜))‖ - ε),
        sq_nonneg ‖((e m : 𝕜))‖, sq_nonneg ‖((e n : 𝕜))‖]
    have hnn : (0 : ℝ) ≤ ‖T (u m) - T (u n)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T (u m) - T (u n)‖ - ε), hge, hnn, hε]
  have hcompact := hc.isCompact_closure_image_closedBall (1 : ℝ)
  have hmem : ∀ n, T (u n)
      ∈ closure (⇑T '' Metric.closedBall (0 : H) 1) := by
    intro n
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hu_norm n]
  obtain ⟨L, -, φ, hmono, hlim⟩ := hcompact.tendsto_subseq hmem
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 2) (by linarith)
  have h1 := hN (N + 1) (Nat.le_succ N) N (le_refl N)
  simp only [Function.comp_apply] at h1
  have h2 : ε ≤ dist (T (u (φ (N + 1)))) (T (u (φ N))) := by
    rw [dist_eq_norm]
    apply hsep
    exact ne_of_gt (hmono (Nat.lt_succ_self N))
  linarith

end MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvalues

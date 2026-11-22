/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple

/-!
# Tests for the maximum principle for compact self-adjoint operators

* The zero operator on `ℓ²(ℕ, ℝ)` has ordered eigenvalue sequence
  identically `0`.
* The orthogonal projection onto the span of the first basis vector of
  `ℓ²(ℕ, ℝ)` is compact and self-adjoint; its ordered eigenvalue sequence
  starts at `1`, is nonnegative, and decays below `1 / 2` eventually.
-/

open ContinuousLinearMap InnerProductSpace
open Filter Topology
open scoped lp
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrincipleTests

set_option linter.style.haveILetI false in
/-- `ℓ²(ℕ, ℝ)` is infinite-dimensional: its default Hilbert basis is an
infinite linearly independent family. -/
theorem not_finiteDimensional_lp_nat :
    ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ) := by
  intro h
  have hli := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)).orthonormal.linearIndependent
  haveI := h
  exact (not_finite_iff_infinite.mpr inferInstance) (LinearIndependent.finite hli)

/-- For the zero operator on `ℓ²(ℕ, ℝ)`, every eigenvalue in the ordered
sequence is `0`. -/
example : ∃ (s : ℕ → ℝ) (u : ℕ → ℓ²(ℕ, ℝ)),
    (∀ n, (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)) (u n) =
      (s n : ℝ) • u n) ∧
    Orthonormal ℝ u ∧ (∀ n, |s (n + 1)| ≤ |s n|) ∧
    Filter.Tendsto (fun n => |s n|) Filter.atTop (nhds 0) ∧
    ∀ n, s n = 0 := by
  obtain ⟨s, u, heig, horth, hmono, htend, hvar⟩ :=
    exists_ordered_eigenvalue_sequence (T := (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)))
      (by simp [IsSelfAdjoint])
      (isCompactOperator_zero) not_finiteDimensional_lp_nat
  refine ⟨s, u, heig, horth, hmono, htend, ?_⟩
  intro n
  have hatt := (hvar n).2
  simp only [zero_apply, inner_zero_left, norm_zero] at hatt
  exact abs_eq_zero.mp hatt.symm

set_option linter.style.haveILetI false in
/-- The orthogonal projection onto the span of the first basis vector of
`ℓ²(ℕ, ℝ)` has first eigenvalue `1`, nonnegative eigenvalues, and the
eigenvalue moduli decay below `1 / 2`. -/
example : ∃ (s : ℕ → ℝ) (u : ℕ → ℓ²(ℕ, ℝ)),
    Orthonormal ℝ u ∧ s 0 = 1 ∧ (∀ n, 0 ≤ s n) ∧
    ∃ N, |s N| < 1 / 2 := by
  classical
  set e : ℓ²(ℕ, ℝ) := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0 with he
  have he_norm : ‖e‖ = 1 := by
    rw [he]
    exact (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)).orthonormal.norm_eq_one 0
  set S : Submodule ℝ ℓ²(ℕ, ℝ) :=
    Submodule.span ℝ (({e} : Finset ℓ²(ℕ, ℝ)) : Set ℓ²(ℕ, ℝ))
    with hS
  have heS : e ∈ S := Submodule.subset_span (by simp)
  haveI : FiniteDimensional ℝ ↥S := by
    rw [hS]
    infer_instance
  have hTsa : IsSelfAdjoint S.starProjection := isSelfAdjoint_starProjection S
  have hTcomp : IsCompactOperator (S.starProjection : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
    -- `orthogonalProjectionOnto` lands in the finite-dimensional subspace
    -- `S`, which is locally compact, so it is a compact operator; composing
    -- with the inclusion `subtypeL` gives `starProjection`.
    have hco : IsCompactOperator (S.orthogonalProjectionOnto :
        ℓ²(ℕ, ℝ) → ↥S) := isCompactOperator_of_locallyCompactSpace_dom _
    have hcomp := hco.clm_comp S.subtypeL
    have heq : (⇑S.subtypeL) ∘ (⇑S.orthogonalProjectionOnto : ℓ²(ℕ, ℝ) → ↥S) =
        (⇑S.starProjection : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
      ext x
      rfl
    rw [heq] at hcomp
    exact hcomp
  obtain ⟨s, u, heig, horth, hmono, htend, hvar⟩ :=
    exists_ordered_eigenvalue_sequence
      (T := S.starProjection) hTsa hTcomp not_finiteDimensional_lp_nat
  have hPe : S.starProjection e = e := Submodule.starProjection_eq_self_iff.mpr heS
  have hRayleigh_pos : ∀ x : ℓ²(ℕ, ℝ), 0 ≤ ⟪S.starProjection x, x⟫_ℝ := by
    intro x
    have horth' : ⟪S.starProjection x, x - S.starProjection x⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem x)
        (Submodule.sub_starProjection_mem_orthogonal x)
    have hpos : 0 ≤ ⟪S.starProjection x, S.starProjection x⟫_ℝ := by
      rw [inner_self_eq_norm_sq_to_K]
      positivity
    have h1 : ⟪S.starProjection x, x⟫_ℝ =
        ⟪S.starProjection x, S.starProjection x⟫_ℝ :=
      sub_eq_zero.mp (by rw [← inner_sub_right]; exact horth')
    rw [h1]
    exact hpos
  have hs_nonneg : ∀ n, 0 ≤ s n := by
    intro n
    have hn1 : ‖u n‖ = 1 := horth.norm_eq_one n
    have h1 : ⟪S.starProjection (u n), u n⟫_ℝ = s n := by
      rw [heig n, inner_smul_left, RCLike.conj_ofReal,
        inner_self_eq_norm_sq_to_K, hn1]
      simp
    rw [← h1]
    exact hRayleigh_pos (u n)
  have hs0_abs : |s 0| = 1 := by
    apply le_antisymm
    · have hatt := (hvar 0).2
      have hu0 : ‖u 0‖ = 1 := horth.norm_eq_one 0
      have hPle : ‖S.starProjection (u 0)‖ ≤ ‖S.starProjection‖ := by
        have h1 := ContinuousLinearMap.le_opNorm S.starProjection (u 0)
        rw [hu0, mul_one] at h1
        exact h1
      calc |s 0| = ‖⟪S.starProjection (u 0), u 0⟫_ℝ‖ := hatt.symm
        _ ≤ ‖S.starProjection (u 0)‖ * ‖u 0‖ := norm_inner_le_norm _ _
        _ ≤ ‖S.starProjection‖ * ‖u 0‖ :=
            mul_le_mul_of_nonneg_right hPle (norm_nonneg _)
        _ = ‖S.starProjection‖ := by rw [hu0, mul_one]
        _ ≤ 1 := Submodule.starProjection_norm_le S
    · have hmax := (hvar 0).1 e he_norm (by intro j hj; exact absurd hj (Nat.not_lt_zero j))
      have h1 : ‖⟪S.starProjection e, e⟫_ℝ‖ = 1 := by
        rw [hPe, inner_self_eq_norm_sq_to_K, he_norm]
        simp
      rw [h1] at hmax
      exact hmax
  have hs0 : s 0 = 1 := by
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hs0_abs
    rcases hs0_abs with h | h
    · exact h
    · have h2 := hs_nonneg 0
      rw [h] at h2
      norm_num at h2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (1 / 2) (by norm_num)
  have hN' : |s N| < 1 / 2 := by
    have h2 := hN N (le_refl N)
    rw [dist_eq_norm, sub_zero] at h2
    simpa using h2
  exact ⟨s, u, horth, hs0, hs_nonneg, N, hN'⟩


/-- The zero operator on a finite-dimensional space has no nonzero terms. -/
example : ∃ (N : ℕ) (s : Fin N → ℝ) (u : Fin N → ℝ),
    N = 0 ∧ Orthonormal ℝ u ∧ ∀ i, s i ≠ 0 := by
  obtain ⟨N, s, u, hs, -, horth, -, hvar, -⟩ :=
    exists_finite_eigenvalue_enumeration (T := (0 : ℝ →L[ℝ] ℝ))
      (by simp [IsSelfAdjoint]) isCompactOperator_zero
  have hN : N = 0 := by
    by_contra h
    let i : Fin N := ⟨0, Nat.pos_of_ne_zero h⟩
    have hzero : |s i| = 0 := by simpa using (hvar i).2.symm
    exact hs i (abs_eq_zero.mp hzero)
  exact ⟨N, s, u, hN, horth, hs⟩

/-- The one-dimensional identity produces one nonzero term, equal to one. -/
example : ∃ (s : Fin 1 → ℝ) (u : Fin 1 → ℝ),
    Orthonormal ℝ u ∧ s 0 = 1 ∧
    ∀ x : ℝ, (∀ i, ⟪x, u i⟫_ℝ = 0) → (ContinuousLinearMap.id ℝ ℝ) x = 0 := by
  obtain ⟨N, s, u, -, heig, horth, -, -, hstop⟩ :=
    exists_finite_eigenvalue_enumeration (T := ContinuousLinearMap.id ℝ ℝ)
      (by rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_id])
      (isCompactOperator_of_locallyCompactSpace_dom _)
  have hNle : N ≤ 1 := by
    simpa using horth.linearIndependent.fintype_card_le_finrank
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    have hz := hstop 1 (fun i => Fin.elim0 i)
    norm_num at hz
  have hN : N = 1 := by omega
  subst N
  refine ⟨s, u, horth, ?_, hstop⟩
  have hu : ‖u 0‖ = 1 := horth.norm_eq_one 0
  have h := congrArg (fun v : ℝ => ⟪v, u 0⟫_ℝ) (heig 0)
  simp only [ContinuousLinearMap.id_apply, inner_smul_left, RCLike.conj_ofReal,
    inner_self_eq_norm_sq_to_K, hu] at h
  norm_num at h
  exact h.symm


private theorem projection_eigenvector_mem {S : Submodule ℝ ℓ²(ℕ, ℝ)}
    [S.HasOrthogonalProjection] {r : ℝ} {v : ℓ²(ℕ, ℝ)} (hr : r ≠ 0)
    (hv : S.starProjection v = r • v) : v ∈ S := by
  have hrv : r • v ∈ S := by
    rw [← hv]
    exact S.starProjection_apply_mem v
  rw [show v = r⁻¹ • (r • v) from (inv_smul_smul₀ hr v).symm]
  exact S.smul_mem _ hrv

private theorem projection_family_orthonormal {ι : Type*}
    (S : Submodule ℝ ℓ²(ℕ, ℝ)) [S.HasOrthogonalProjection]
    (s : ι → ℝ) (u : ι → ℓ²(ℕ, ℝ)) (hs : ∀ i, s i ≠ 0)
    (heig : ∀ i, S.starProjection (u i) = s i • u i) (horth : Orthonormal ℝ u) :
    Orthonormal ℝ (fun i => (⟨u i, projection_eigenvector_mem (hs i) (heig i)⟩ : S)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪u i, u j⟫_ℝ = if i = j then 1 else 0
  exact orthonormal_iff_ite.mp horth i j

/-- A rank-one projection has one nonzero term even in an infinite ambient space. -/
example : let e := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0
    let S : Submodule ℝ ℓ²(ℕ, ℝ) := ℝ ∙ e
    ∃ (s : Fin 1 → ℝ) (u : Fin 1 → ℓ²(ℕ, ℝ)),
      Orthonormal ℝ u ∧ s 0 = 1 ∧
      ∀ x, (∀ i, ⟪x, u i⟫_ℝ = 0) → S.starProjection x = 0 := by
  classical
  let e := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0
  let S : Submodule ℝ ℓ²(ℕ, ℝ) := ℝ ∙ e
  have he1 : ‖e‖ = 1 := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)).orthonormal.norm_eq_one 0
  have he0 : e ≠ 0 := norm_ne_zero_iff.mp (by rw [he1]; norm_num)
  have heS : e ∈ S := Submodule.subset_span (by simp)
  haveI : FiniteDimensional ℝ S := FiniteDimensional.span_singleton ℝ e
  have hcompact : IsCompactOperator (S.starProjection : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
    have hco : IsCompactOperator (S.orthogonalProjectionOnto : ℓ²(ℕ, ℝ) → S) :=
      isCompactOperator_of_locallyCompactSpace_dom _
    have h := hco.clm_comp S.subtypeL
    have heq : (⇑S.subtypeL) ∘ (⇑S.orthogonalProjectionOnto : ℓ²(ℕ, ℝ) → S) =
        (⇑S.starProjection : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by ext x; rfl
    rw [heq] at h
    exact h
  rcases exists_nonzero_eigenvalue_enumeration (isSelfAdjoint_starProjection S) hcompact
      with hfin | hinf
  · obtain ⟨N, s, u, hs, heig, horth, -, -, hstop⟩ := hfin
    have horthS := projection_family_orthonormal S s u hs heig horth
    have hrank : Module.finrank ℝ S = 1 := finrank_span_singleton he0
    have hNle : N ≤ 1 := by
      simpa only [Fintype.card_fin, hrank]
        using horthS.linearIndependent.fintype_card_le_finrank
    have hN0 : N ≠ 0 := by
      intro h
      subst N
      have hz := hstop e (fun i => Fin.elim0 i)
      rw [Submodule.starProjection_eq_self_iff.mpr heS] at hz
      exact he0 hz
    have hN : N = 1 := by omega
    subst N
    refine ⟨s, u, horth, ?_, hstop⟩
    have huS := projection_eigenvector_mem (hs 0) (heig 0)
    have h := congrArg (fun v : ℓ²(ℕ, ℝ) => ⟪v, u 0⟫_ℝ) (heig 0)
    rw [Submodule.starProjection_eq_self_iff.mpr huS, inner_smul_left,
      RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, horth.norm_eq_one 0] at h
    norm_num at h
    exact h.symm
  · obtain ⟨s, u, hs, heig, horth, -⟩ := hinf
    have horthS := projection_family_orthonormal S s u hs heig horth
    exact False.elim ((not_finite_iff_infinite.mpr inferInstance)
      horthS.linearIndependent.finite)


private noncomputable def weight (n : ℕ) : ℝ := (1 / 2) ^ n

private noncomputable def diagonal : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) :=
  lp.mapCLM 2 (fun n => weight n • ContinuousLinearMap.id ℝ ℝ)
    (by norm_num : (0 : ℝ) ≤ 1) (by
      intro n
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by dsimp [weight]; positivity)]
      exact pow_le_one₀ (by norm_num) (by norm_num))

private theorem diagonal_apply (x : ℓ²(ℕ, ℝ)) (n : ℕ) :
    diagonal x n = weight n * x n := by
  simp [diagonal, lp.mapCLM_apply_coe]

private theorem diagonal_selfAdjoint : IsSelfAdjoint diagonal := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪diagonal x, y⟫_ℝ = ⟪x, diagonal y⟫_ℝ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  ext n
  rw [diagonal_apply, diagonal_apply]
  change ⟪weight n • x n, y n⟫_ℝ = ⟪x n, weight n • y n⟫_ℝ
  rw [inner_smul_left, inner_smul_right]
  simp

private theorem diagonal_injective : Function.Injective diagonal := by
  intro x y h
  apply lp.ext
  funext n
  have hcoord := congrArg (fun v : ℓ²(ℕ, ℝ) => v n) h
  rw [diagonal_apply, diagonal_apply] at hcoord
  exact mul_left_cancel₀ (by dsimp [weight]; positivity) hcoord

private noncomputable def partialDiagonal (N : ℕ) : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) :=
  ∑ n ∈ Finset.range N, weight n •
    ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n) ∘L
      lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)

private theorem partialDiagonal_compact (N : ℕ) :
    IsCompactOperator (partialDiagonal N : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
  have hterm : ∀ n : ℕ, IsCompactOperator
      ((weight n • ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n) ∘L
        lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)) : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
    intro n
    have h := (isCompactOperator_of_locallyCompactSpace_dom
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)).clm_comp
        (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n)
    simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_smul]
      using h.smul (weight n)
  induction N with
  | zero => simpa [partialDiagonal] using (isCompactOperator_zero :
      IsCompactOperator (0 : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)))
  | succ N ih =>
      have heq : (partialDiagonal (N + 1) : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) =
          (partialDiagonal N : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) +
            ((weight N • ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 N) ∘L
              lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 N)) : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
        funext x
        simp [partialDiagonal, Finset.sum_range_succ]
      rw [heq]
      exact ih.add (hterm N)

private theorem partialDiagonal_apply (N : ℕ) (x : ℓ²(ℕ, ℝ)) (j : ℕ) :
    partialDiagonal N x j = if j < N then weight j * x j else 0 := by
  induction N with
  | zero => simp [partialDiagonal]
  | succ N ih =>
      have heq : partialDiagonal (N + 1) = partialDiagonal N +
          weight N • ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 N) ∘L
            lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 N) := by
        simp only [partialDiagonal, Finset.sum_range_succ]
      change (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j) (partialDiagonal (N + 1) x) = _
      rw [heq, ContinuousLinearMap.add_apply, map_add]
      change partialDiagonal N x j +
        (weight N • ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 N) ∘L
          lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 N)) x j = _
      rw [ih]
      have hterm : (weight N • ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 N) ∘L
          lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 N)) x j =
          if j = N then weight N * x N else 0 := by
        change (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j)
          (weight N • lp.single 2 N (x N)) = _
        rw [map_smul]
        change weight N * (lp.single 2 N (x N) : ℓ²(ℕ, ℝ)) j = _
        simp [lp.single_apply, Pi.single_apply]
      rw [hterm]
      by_cases hj : j < N
      · simp [hj, ne_of_lt hj, lt_trans hj (Nat.lt_succ_self N)]
      · by_cases hEq : j = N
        · subst j; simp
        · have hj' : ¬ j < N + 1 := by omega
          simp [hj, hEq, hj']


private noncomputable def tailCoeff (N n : ℕ) : ℝ →L[ℝ] ℝ :=
  if n < N then 0 else weight n • ContinuousLinearMap.id ℝ ℝ

private theorem tailCoeff_bound (N n : ℕ) : ‖tailCoeff N n‖ ≤ weight N := by
  by_cases h : n < N
  · simp only [tailCoeff, if_pos h, norm_zero]
    dsimp [weight]
    positivity
  · rw [tailCoeff, if_neg h, norm_smul, ContinuousLinearMap.norm_id, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (by dsimp [weight]; positivity)]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

private noncomputable def tailDiagonal (N : ℕ) : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) :=
  lp.mapCLM 2 (tailCoeff N) (by dsimp [weight]; positivity) (tailCoeff_bound N)

private theorem diagonal_sub_partial (N : ℕ) :
    diagonal - partialDiagonal N = tailDiagonal N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n) ((diagonal - partialDiagonal N) x) = _
  rw [ContinuousLinearMap.sub_apply, map_sub]
  change diagonal x n - partialDiagonal N x n = tailDiagonal N x n
  rw [diagonal_apply, partialDiagonal_apply]
  have htail : tailDiagonal N x n = if n < N then 0 else weight n * x n := by
    by_cases h : n < N <;> simp [tailDiagonal, lp.mapCLM_apply_coe, tailCoeff, h]
  rw [htail]
  by_cases h : n < N <;> simp [h]

private theorem norm_diagonal_sub_partial (N : ℕ) :
    ‖diagonal - partialDiagonal N‖ ≤ weight N := by
  rw [diagonal_sub_partial]
  exact lp.norm_mapCLM_le 2 (tailCoeff N) (by dsimp [weight]; positivity) (tailCoeff_bound N)

private theorem partialDiagonal_tendsto : Tendsto partialDiagonal atTop (𝓝 diagonal) := by
  have hw : Tendsto weight atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hw ε hε
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_eq_norm, norm_sub_rev]
  apply lt_of_le_of_lt (norm_diagonal_sub_partial n)
  have h := hN n hn
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs] at h
  exact lt_of_le_of_lt (le_abs_self (weight n)) h

private theorem diagonal_compact : IsCompactOperator (diagonal : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) :=
  isClosed_setOfPred_isCompactOperator.mem_of_tendsto partialDiagonal_tendsto
    (Filter.Eventually.of_forall partialDiagonal_compact)

/-- A compact injective diagonal on l2 has a nonterminating nonzero enumeration. -/
example : ∃ (s : ℕ → ℝ) (u : ℕ → ℓ²(ℕ, ℝ)),
    (∀ n, s n ≠ 0) ∧ (∀ n, diagonal (u n) = s n • u n) ∧
    Orthonormal ℝ u ∧ Tendsto (fun n => |s n|) atTop (𝓝 0) := by
  rcases exists_nonzero_eigenvalue_enumeration diagonal_selfAdjoint diagonal_compact
      with hfin | hinf
  · obtain ⟨N, s, u, -, -, horth, -, -, hstop⟩ := hfin
    have hsp : (Submodule.span ℝ (Set.range u))ᗮ = ⊥ := by
      apply le_antisymm
      · intro x hx
        apply (Submodule.mem_bot ℝ).mpr
        apply diagonal_injective
        rw [hstop x (fun i => Submodule.inner_left_of_mem_orthogonal
          (Submodule.subset_span (Set.mem_range_self i)) hx), map_zero]
      · exact bot_le
    let b := OrthonormalBasis.mkOfOrthogonalEqBot horth hsp
    haveI : FiniteDimensional ℝ ℓ²(ℕ, ℝ) := Module.Finite.of_basis b.toBasis
    have hli := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)).orthonormal.linearIndependent
    exact False.elim ((not_finite_iff_infinite.mpr inferInstance) hli.finite)
  · obtain ⟨s, u, hs, heig, horth, -, htend, -⟩ := hinf
    exact ⟨s, u, hs, heig, horth, htend⟩

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrincipleTests

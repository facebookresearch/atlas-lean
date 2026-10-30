/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Kantorovich, Bhatia–Davis, and Popoviciu inequalities

Let `T` be a symmetric operator on a finite-dimensional real inner product
space, and suppose its Rayleigh quotients lie in `[m, M]`, i.e.
`m * ‖x‖² ≤ ⟪x, T x⟫_ℝ ≤ M * ‖x‖²` for every `x`. For a unit vector `x`,
write `μ = ⟪x, T x⟫_ℝ` for the Rayleigh quotient and
`var = ⟪x, T (T x)⟫_ℝ - μ²` for the variance of `T` at `x`
(the variance of the spectral measure of `T` at `x`). Then:

* `bhatia_davis_inequality` (**Bhatia–Davis**): `var ≤ (M - μ) * (μ - m)`.
* `popoviciu_inequality` (**Popoviciu**): `var ≤ ((M - m) / 2)²`.
* `kantorovich_inequality` (**Kantorovich**, for `0 < m` and `S` a two-sided
  inverse of `T`): `μ * ⟪x, S x⟫_ℝ ≤ (M + m)² / (4 * m * M)`.

The proofs diagonalize `T` in its orthonormal eigenbasis (Mathlib's
`LinearMap.IsSymmetric.eigenvectorBasis`): with weights
`w i = ((eigenvectorBasis).repr x i)²`, one has `∑ w = ‖x‖²`,
`μ = ∑ w i * λ i`, `⟪x, T (T x)⟫_ℝ = ∑ w i * λ i²`, and
`⟪x, S x⟫_ℝ = ∑ w i / λ i`, and all three inequalities reduce to the
corresponding scalar weighted lemmas (`weighted_bhatia_davis`,
`weighted_popoviciu`, `weighted_kantorovich`), which are proved by
expanding `∑ w i * (λ i - m) * (M - λ i) ≥ 0`
(and, for Kantorovich, `∑ w i * (λ i - m) * (M - λ i) / λ i ≥ 0`)
and applying the AM–GM inequality.

These are companions to the Rayleigh-quotient and spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis` (parallelogram law, spectral
theorem for self-adjoint operators, Rayleigh bounds). They are not among
the 72 v1 targets, and none of them is in the pinned Mathlib or base
MathlibExt: Mathlib's Bhatia–Davis and Popoviciu lemmas
(`variance_le_sub_mul_sub`, `variance_le_sq_of_bounded`) are statements
about the variance of a real random variable, and MathlibExt's
`Kantorovich.lean` is Kantorovich duality for optimal transport, a
different theorem. Kantorovich's inequality is classical; see e.g.
Bhatia–Davis, *A Cauchy–Schwarz inequality for operators with applications*
(Linear Algebra Appl., 1993), and Popoviciu, *Sur l'écart quadratique*
(1935).
-/

@[expose] public section

open scoped _root_.InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.KantorovichInequality

open Finset

section Scalar

variable {n : ℕ} {w lam : Fin n → ℝ} {m M : ℝ}

/-- The weighted variance equals the weighted squared deviation from the
weighted mean. -/
theorem weighted_variance_eq (hw_sum : ∑ i, w i = 1) :
    (∑ i, w i * lam i ^ 2) - (∑ i, w i * lam i) ^ 2
      = ∑ i, w i * (lam i - ∑ j, w j * lam j) ^ 2 := by
  have h1 : (∑ i, w i * (lam i - ∑ j, w j * lam j) ^ 2)
      = (∑ i, w i * lam i ^ 2)
        - 2 * (∑ i, w i * lam i) * (∑ i, w i * lam i)
        + (∑ i, w i * lam i) ^ 2 * (∑ i, w i) := by
    rw [show (∑ i, w i * (lam i - ∑ j, w j * lam j) ^ 2)
        = ∑ i, (w i * lam i ^ 2
          - 2 * (∑ i, w i * lam i) * (w i * lam i)
          + (∑ i, w i * lam i) ^ 2 * w i) from
      Finset.sum_congr rfl (fun i _ => by ring)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    try ring
  rw [h1, hw_sum]
  ring

/-- **Bhatia–Davis inequality**, scalar weighted form: if the weights are
nonnegative, sum to `1`, and every `λ i` lies in `[m, M]`, then the weighted
variance is at most `(M - μ) * (μ - m)`, where `μ` is the weighted mean. -/
theorem weighted_bhatia_davis (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hlam : ∀ i, m ≤ lam i ∧ lam i ≤ M) :
    (∑ i, w i * lam i ^ 2) - (∑ i, w i * lam i) ^ 2
      ≤ (M - ∑ i, w i * lam i) * (∑ i, w i * lam i - m) := by
  have hkey : 0 ≤ ∑ i, w i * ((lam i - m) * (M - lam i)) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw_nonneg i)
      (mul_nonneg (sub_nonneg.mpr (hlam i).1) (sub_nonneg.mpr (hlam i).2))
  have hexpand : (∑ i, w i * ((lam i - m) * (M - lam i)))
      = -(∑ i, w i * lam i ^ 2) + (M + m) * (∑ i, w i * lam i) - m * M := by
    rw [show (∑ i, w i * ((lam i - m) * (M - lam i)))
        = ∑ i, (-(w i * lam i ^ 2) + (M + m) * (w i * lam i) - m * M * w i) from
      Finset.sum_congr rfl (fun i _ => by ring)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hw_sum]
    try ring
  have hprod : (M - ∑ i, w i * lam i) * (∑ i, w i * lam i - m)
      = (M + m) * (∑ i, w i * lam i) - m * M - (∑ i, w i * lam i) ^ 2 := by ring
  rw [hprod]
  linarith

/-- **Popoviciu's inequality**, scalar weighted form: the weighted variance
is at most `((M - m) / 2)²`. -/
theorem weighted_popoviciu (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hlam : ∀ i, m ≤ lam i ∧ lam i ≤ M) :
    (∑ i, w i * lam i ^ 2) - (∑ i, w i * lam i) ^ 2 ≤ ((M - m) / 2) ^ 2 := by
  have hb := weighted_bhatia_davis hw_nonneg hw_sum hlam
  have hident : (M - ∑ i, w i * lam i) * (∑ i, w i * lam i - m)
      = ((M - m) / 2) ^ 2 - (∑ i, w i * lam i - (M + m) / 2) ^ 2 := by ring
  rw [hident] at hb
  linarith [sq_nonneg (∑ i, w i * lam i - (M + m) / 2)]

/-- **Kantorovich's inequality**, scalar weighted form: if the weights are
nonnegative, sum to `1`, every `λ i` lies in `[m, M]`, and `0 < m`, then
`(∑ w i * λ i) * (∑ w i / λ i) ≤ (M + m)² / (4 * m * M)`. -/
theorem weighted_kantorovich (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hm : 0 < m) (hlam : ∀ i, m ≤ lam i ∧ lam i ≤ M) :
    (∑ i, w i * lam i) * (∑ i, w i / lam i) ≤ (M + m) ^ 2 / (4 * m * M) := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hne | hnne
  · simp at hw_sum
  · obtain ⟨i₀⟩ := hnne
    have hM : 0 < M := hm.trans_le ((hlam i₀).1.trans (hlam i₀).2)
    have hlam_pos : ∀ i, 0 < lam i := fun i => hm.trans_le (hlam i).1
    set μ : ℝ := ∑ i, w i * lam i with hμ
    set ν : ℝ := ∑ i, w i / lam i with hν
    have hkey : 0 ≤ ∑ i, w i * ((lam i - m) * (M - lam i) / lam i) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hw_nonneg i)
        (div_nonneg (mul_nonneg (sub_nonneg.mpr (hlam i).1) (sub_nonneg.mpr (hlam i).2))
          (le_of_lt (hlam_pos i)))
    have hexpand : (∑ i, w i * ((lam i - m) * (M - lam i) / lam i))
        = -μ + (M + m) - m * M * ν := by
      rw [show (∑ i, w i * ((lam i - m) * (M - lam i) / lam i))
          = ∑ i, (-(w i * lam i) + (M + m) * w i - m * M * (w i / lam i)) from
        Finset.sum_congr rfl (fun i _ => by
          have hi : lam i ≠ 0 := ne_of_gt (hlam_pos i)
          field_simp
          ring)]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum, hw_sum]
      rw [← hμ, ← hν]
      try ring
    have hsum : μ + m * M * ν ≤ M + m := by linarith
    have hμ_nonneg : 0 ≤ μ := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (hw_nonneg i) (le_of_lt (hlam_pos i))
    have hν_nonneg : 0 ≤ ν := by
      apply Finset.sum_nonneg
      intro i _
      exact div_nonneg (hw_nonneg i) (le_of_lt (hlam_pos i))
    have hsum_nonneg : 0 ≤ μ + m * M * ν :=
      add_nonneg hμ_nonneg (mul_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hM)) hν_nonneg)
    have hamgm : 4 * (μ * (m * M * ν)) ≤ (μ + m * M * ν) ^ 2 := by
      have hsq : (μ + m * M * ν) ^ 2 - 4 * (μ * (m * M * ν))
          = (μ - m * M * ν) ^ 2 := by ring
      linarith [sq_nonneg (μ - m * M * ν)]
    have hsq_le : (μ + m * M * ν) ^ 2 ≤ (M + m) ^ 2 :=
      pow_le_pow_left₀ hsum_nonneg hsum 2
    have h4 : 4 * m * M * (μ * ν) ≤ (M + m) ^ 2 := by nlinarith [hamgm, hsq_le]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * m * M)]
    linarith

end Scalar

section Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {T S : E →ₗ[ℝ] E} {n : ℕ} {m M : ℝ}

/-- Real-valued form of `LinearMap.IsSymmetric.apply_eigenvectorBasis`: the
eigenvalue is a plain real scalar, with no `ℝ → 𝕜` coercion. -/
theorem apply_eigenvectorBasis_real (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (i : Fin n) :
    T ((hT.eigenvectorBasis hn) i) = (hT.eigenvalues hn i) • (hT.eigenvectorBasis hn) i := by
  simp [hT.apply_eigenvectorBasis hn i]

/-- The eigenvalues of a symmetric operator lie in `[m, M]` whenever its
Rayleigh quotients do. -/
theorem eigenvalue_mem_Icc_of_rayleigh_bounds (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hray : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ ∧ ⟪x, T x⟫_ℝ ≤ M * ‖x‖ ^ 2)
    (i : Fin n) :
    m ≤ hT.eigenvalues hn i ∧ hT.eigenvalues hn i ≤ M := by
  set b := hT.eigenvectorBasis hn with hb
  have hinner : ⟪b i, T (b i)⟫_ℝ = hT.eigenvalues hn i := by
    rw [apply_eigenvectorBasis_real hT hn i, real_inner_smul_right, b.inner_eq_one i,
      mul_one]
  have hnorm : ‖b i‖ = 1 := b.norm_eq_one i
  obtain ⟨h1, h2⟩ := hray (b i)
  rw [hnorm, hinner] at h1 h2
  simp only [one_pow, mul_one] at h1 h2
  exact ⟨h1, h2⟩

/-- The eigenbasis weights sum to `‖x‖²`. -/
theorem sum_weights_eq_norm_sq (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (x : E) :
    ∑ i, ((hT.eigenvectorBasis hn).repr x i) ^ 2 = ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn with hb
  have h := b.sum_sq_norm_inner_right x
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [← b.repr_apply_apply x i, Real.norm_eq_abs, sq_abs]

/-- The Rayleigh quotient is the weighted average of the eigenvalues, with
weights `((eigenvectorBasis).repr x i)²`. -/
theorem rayleigh_eq_weighted_sum (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = n)
    (x : E) :
    ⟪x, T x⟫_ℝ
      = ∑ i, ((hT.eigenvectorBasis hn).repr x i) ^ 2 * hT.eigenvalues hn i := by
  set b := hT.eigenvectorBasis hn with hb
  set c : Fin n → ℝ := fun i => ⟪b i, x⟫_ℝ with hc
  have hTx : T x = ∑ i, (c i * hT.eigenvalues hn i) • b i := by
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, apply_eigenvectorBasis_real hT hn i, smul_smul]
  calc ⟪x, T x⟫_ℝ
      = ⟪∑ i, c i • b i, ∑ i, (c i * hT.eigenvalues hn i) • b i⟫_ℝ := by
        rw [b.sum_repr', hTx]
    _ = ∑ i, (starRingEnd ℝ) (c i) * (c i * hT.eigenvalues hn i) :=
        (b.orthonormal).inner_sum c (fun i => c i * hT.eigenvalues hn i) Finset.univ
    _ = ∑ i, (b.repr x i) ^ 2 * hT.eigenvalues hn i := by
        apply Finset.sum_congr rfl
        intro i _
        simp [hc, b.repr_apply_apply x i]
        try ring

/-- The second-moment quadratic form is the weighted average of the squared
eigenvalues. -/
theorem second_moment_eq_weighted_sum (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (x : E) :
    ⟪x, T (T x)⟫_ℝ
      = ∑ i, ((hT.eigenvectorBasis hn).repr x i) ^ 2 * (hT.eigenvalues hn i) ^ 2 := by
  set b := hT.eigenvectorBasis hn with hb
  set c : Fin n → ℝ := fun i => ⟪b i, x⟫_ℝ with hc
  have hTx : T x = ∑ i, (c i * hT.eigenvalues hn i) • b i := by
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, apply_eigenvectorBasis_real hT hn i, smul_smul]
  have hT2x : T (T x) = ∑ i, (c i * (hT.eigenvalues hn i) ^ 2) • b i := by
    conv_lhs => rw [hTx]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, apply_eigenvectorBasis_real hT hn i, smul_smul]
    congr 1
    ring
  calc ⟪x, T (T x)⟫_ℝ
      = ⟪∑ i, c i • b i, ∑ i, (c i * (hT.eigenvalues hn i) ^ 2) • b i⟫_ℝ := by
        rw [b.sum_repr', hT2x]
    _ = ∑ i, (starRingEnd ℝ) (c i) * (c i * (hT.eigenvalues hn i) ^ 2) :=
        (b.orthonormal).inner_sum c
          (fun i => c i * (hT.eigenvalues hn i) ^ 2) Finset.univ
    _ = ∑ i, (b.repr x i) ^ 2 * (hT.eigenvalues hn i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [hc, b.repr_apply_apply x i]
        try ring

/-- The quadratic form of a two-sided inverse is the weighted average of the
reciprocal eigenvalues. -/
theorem inv_rayleigh_eq_weighted_sum_div (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (hm : 0 < m)
    (hray : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ ∧ ⟪x, T x⟫_ℝ ≤ M * ‖x‖ ^ 2)
    (hTS : ∀ x, T (S x) = x) (hST : ∀ x, S (T x) = x) (x : E) :
    ⟪x, S x⟫_ℝ
      = ∑ i, ((hT.eigenvectorBasis hn).repr x i) ^ 2 / hT.eigenvalues hn i := by
  set b := hT.eigenvectorBasis hn with hb
  set c : Fin n → ℝ := fun i => ⟪b i, x⟫_ℝ with hc
  have hlam : ∀ i, m ≤ hT.eigenvalues hn i ∧ hT.eigenvalues hn i ≤ M :=
    fun i => eigenvalue_mem_Icc_of_rayleigh_bounds hT hn hray i
  have hlam_pos : ∀ i, 0 < hT.eigenvalues hn i :=
    fun i => hm.trans_le (hlam i).1
  have hSx : S x = ∑ i, (c i / hT.eigenvalues hn i) • b i := by
    have hTSx : T (∑ i, (c i / hT.eigenvalues hn i) • b i) = x := by
      rw [map_sum, ← b.sum_repr' x]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, apply_eigenvectorBasis_real hT hn i, smul_smul,
        div_mul_cancel₀ _ (ne_of_gt (hlam_pos i))]
    have h1 : T (∑ i, (c i / hT.eigenvalues hn i) • b i) = T (S x) := by
      rw [hTSx, hTS]
    have h2 : (∑ i, (c i / hT.eigenvalues hn i) • b i) = S x := by
      simpa [hST] using congr_arg S h1
    exact h2.symm
  calc ⟪x, S x⟫_ℝ
      = ⟪∑ i, c i • b i, ∑ i, (c i / hT.eigenvalues hn i) • b i⟫_ℝ := by
        rw [b.sum_repr', hSx]
    _ = ∑ i, (starRingEnd ℝ) (c i) * (c i / hT.eigenvalues hn i) :=
        (b.orthonormal).inner_sum c
          (fun i => c i / hT.eigenvalues hn i) Finset.univ
    _ = ∑ i, (b.repr x i) ^ 2 / hT.eigenvalues hn i := by
        apply Finset.sum_congr rfl
        intro i _
        simp [hc, b.repr_apply_apply x i]
        try ring

/-- The variance of `T` at a unit vector is the weighted squared deviation
of the eigenvalues from the Rayleigh quotient. -/
theorem variance_eq_weighted_sum_sq (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (x : E) (hx : ‖x‖ = 1) :
    ⟪x, T (T x)⟫_ℝ - ⟪x, T x⟫_ℝ ^ 2
      = ∑ i, ((hT.eigenvectorBasis hn).repr x i) ^ 2
        * (hT.eigenvalues hn i - ⟪x, T x⟫_ℝ) ^ 2 := by
  rw [second_moment_eq_weighted_sum hT hn x, rayleigh_eq_weighted_sum hT hn x]
  exact weighted_variance_eq (by
    rw [sum_weights_eq_norm_sq hT hn x, hx]
    simp)

/-- **Bhatia–Davis inequality** for a symmetric operator: the variance of `T`
at a unit vector is at most `(M - μ) * (μ - m)`, where `μ` is the Rayleigh
quotient. -/
theorem bhatia_davis_inequality (hT : T.IsSymmetric)
    (x : E) (hx : ‖x‖ = 1)
    (hray : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ ∧ ⟪x, T x⟫_ℝ ≤ M * ‖x‖ ^ 2) :
    ⟪x, T (T x)⟫_ℝ - ⟪x, T x⟫_ℝ ^ 2
      ≤ (M - ⟪x, T x⟫_ℝ) * (⟪x, T x⟫_ℝ - m) := by
  let n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  rw [second_moment_eq_weighted_sum hT hn x, rayleigh_eq_weighted_sum hT hn x]
  apply weighted_bhatia_davis
  · intro i
    exact sq_nonneg _
  · rw [sum_weights_eq_norm_sq hT hn x, hx]
    simp
  · intro i
    exact eigenvalue_mem_Icc_of_rayleigh_bounds hT hn hray i

/-- **Popoviciu's inequality** for a symmetric operator: the variance of `T`
at a unit vector is at most `((M - m) / 2)²`. -/
theorem popoviciu_inequality (hT : T.IsSymmetric)
    (x : E) (hx : ‖x‖ = 1)
    (hray : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ ∧ ⟪x, T x⟫_ℝ ≤ M * ‖x‖ ^ 2) :
    ⟪x, T (T x)⟫_ℝ - ⟪x, T x⟫_ℝ ^ 2 ≤ ((M - m) / 2) ^ 2 := by
  let n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  rw [second_moment_eq_weighted_sum hT hn x, rayleigh_eq_weighted_sum hT hn x]
  apply weighted_popoviciu
  · intro i
    exact sq_nonneg _
  · rw [sum_weights_eq_norm_sq hT hn x, hx]
    simp
  · intro i
    exact eigenvalue_mem_Icc_of_rayleigh_bounds hT hn hray i

/-- **Kantorovich's inequality** for a symmetric operator: for a unit vector
`x`, the product of the Rayleigh quotient of `T` and the Rayleigh quotient
of its two-sided inverse `S` is at most `(M + m)² / (4 * m * M)`. -/
theorem kantorovich_inequality (hT : T.IsSymmetric)
    (x : E) (hx : ‖x‖ = 1)
    (hray : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ ∧ ⟪x, T x⟫_ℝ ≤ M * ‖x‖ ^ 2)
    (hm : 0 < m) (hTS : ∀ x, T (S x) = x) (hST : ∀ x, S (T x) = x) :
    ⟪x, T x⟫_ℝ * ⟪x, S x⟫_ℝ ≤ (M + m) ^ 2 / (4 * m * M) := by
  let n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  rw [rayleigh_eq_weighted_sum hT hn x,
    inv_rayleigh_eq_weighted_sum_div hT hn hm hray hTS hST x]
  apply weighted_kantorovich
  · intro i
    exact sq_nonneg _
  · rw [sum_weights_eq_norm_sq hT hn x, hx]
    simp
  · exact hm
  · intro i
    exact eigenvalue_mem_Icc_of_rayleigh_bounds hT hn hray i

end Operator

end MathlibExt.Analysis.InnerProductSpace.KantorovichInequality

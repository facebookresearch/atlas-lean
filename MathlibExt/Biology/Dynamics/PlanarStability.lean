/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.LinearAlgebra.Matrix.MMatrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import MathlibExt.Biology.Dynamics.TuringPatterns

/-!
# Trace–determinant stability of planar linearizations

A real `2 × 2` matrix `M` with trace `τ = tr M` and determinant `Δ = det M` has characteristic
polynomial `z² - τ z + Δ`. This file collects the planar trace–determinant theory used by planar
models such as `MathlibExt.Biology.Biophysics.FitzHughNagumo`, and relates it to
`Matrix.IsHurwitz` and to the complex eigenvalues of `M`.

## Main results

* **Eigenvalues.** `IsCharRoot τ Δ z`: `z ∈ ℂ` is a root of `z² - τ z + Δ`.
  `mem_spectrum_iff_isCharRoot`: the complex eigenvalues of `M` (the spectrum of its
  complexification, as in `Matrix.IsHurwitz`) are exactly the roots for `(tr M, det M)`;
  `exists_mulVec_eq_smul_iff_isCharRoot` and `mem_spectrum_iff_exists_mulVec_eq_smul` give the
  same in terms of complex eigenvectors. `IsCharRoot.re_neg`, `IsCharRoot.re_pos`,
  `IsCharRoot.re_eq_zero`, `IsCharRoot.im_eq_zero`, `IsCharRoot.im_ne_zero` and
  `exists_isCharRoot` locate the roots from the signs of `τ`, `Δ` and `τ² - 4Δ`.
* **Stability.** `isLinearlyStable_iff` is the planar Routh–Hurwitz criterion: every root lies in
  the open left half-plane iff `τ < 0 < Δ`. `isHurwitz_iff_isLinearlyStable` identifies
  `M.IsHurwitz` with `IsLinearlyStable (tr M) (det M)`, so `isHurwitz_iff_trace_neg_and_det_pos`:
  `M` is Hurwitz iff `tr M < 0 < det M`.
* **Instability.** `exists_spectrum_re_pos_iff`: `M` has an eigenvalue with positive real part
  iff `0 < tr M` or `det M < 0`. This is `TuringPatterns.exists_eigenvalue_re_pos_iff`, restated
  for the spectrum; `isLinearlyUnstable_iff`, the same criterion for `(τ, Δ)`, follows from it
  through the companion matrix `!![0, -Δ; 1, τ]`.
* **Classification.** `linearType τ Δ` sorts a planar linearization into saddle, degenerate,
  center, stable or unstable node, and stable or unstable focus (`linearType_eq_*_iff`);
  `isLinearlyStable_iff_linearType` and `isLinearlyUnstable_of_linearType` relate the classes to
  stability.

## References

* S. H. Strogatz, *Nonlinear Dynamics and Chaos*, 2nd ed., Westview Press (2015), Chapter 5.
-/

@[expose] public noncomputable section

open Matrix

namespace MathlibExt.Biology.Dynamics.PlanarStability

/-! ### Characteristic roots -/

/-- Roots `z ∈ ℂ` of the characteristic polynomial `z² - τ z + Δ` of a planar linear system with
trace `τ` and determinant `Δ`. -/
def IsCharRoot (τ Δ : ℝ) (z : ℂ) : Prop := z ^ 2 - τ * z + Δ = 0

section Roots

variable {τ Δ : ℝ} {z : ℂ}

theorem IsCharRoot.re_im (h : IsCharRoot τ Δ z) :
    z.re ^ 2 - z.im ^ 2 - τ * z.re + Δ = 0 ∧ z.im * (2 * z.re - τ) = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  constructor <;> linarith

/-- If `τ < 0 < Δ`, every characteristic root lies in the open left half-plane. -/
theorem IsCharRoot.re_neg (h : IsCharRoot τ Δ z) (hτ : τ < 0) (hΔ : 0 < Δ) : z.re < 0 := by
  obtain ⟨h1, h2⟩ := h.re_im
  rcases mul_eq_zero.1 h2 with him | hre
  · rw [him] at h1
    by_contra hz
    push Not at hz
    nlinarith
  · linarith

/-- If `0 < τ` and `0 < Δ`, every characteristic root lies in the open right half-plane. -/
theorem IsCharRoot.re_pos (h : IsCharRoot τ Δ z) (hτ : 0 < τ) (hΔ : 0 < Δ) : 0 < z.re := by
  obtain ⟨h1, h2⟩ := h.re_im
  rcases mul_eq_zero.1 h2 with him | hre
  · rw [him] at h1
    by_contra hz
    push Not at hz
    nlinarith
  · linarith

/-- If `τ = 0 < Δ`, the characteristic roots are purely imaginary. -/
theorem IsCharRoot.re_eq_zero (h : IsCharRoot τ Δ z) (hτ : τ = 0) (hΔ : 0 < Δ) : z.re = 0 := by
  obtain ⟨h1, h2⟩ := h.re_im
  rcases mul_eq_zero.1 h2 with him | hre
  · rw [him, hτ] at h1
    nlinarith
  · linarith

/-- If `4 Δ ≤ τ²`, every characteristic root is real. -/
theorem IsCharRoot.im_eq_zero (h : IsCharRoot τ Δ z) (hd : 4 * Δ ≤ τ ^ 2) : z.im = 0 := by
  obtain ⟨h1, h2⟩ := h.re_im
  rcases mul_eq_zero.1 h2 with him | hre
  · exact him
  · have : z.re = τ / 2 := by linarith
    rw [this] at h1
    nlinarith [sq_nonneg z.im]

/-- If `τ² < 4 Δ`, no characteristic root is real. -/
theorem IsCharRoot.im_ne_zero (h : IsCharRoot τ Δ z) (hd : τ ^ 2 < 4 * Δ) : z.im ≠ 0 := by
  intro him
  obtain ⟨h1, -⟩ := h.re_im
  rw [him] at h1
  nlinarith [sq_nonneg (2 * z.re - τ)]

/-- A characteristic root with real part at least `τ / 2`, which is positive when `Δ < 0` and
nonnegative when `Δ ≤ 0` (an explicit root of the quadratic). -/
theorem exists_isCharRoot (τ Δ : ℝ) :
    ∃ z, IsCharRoot τ Δ z ∧ τ / 2 ≤ z.re ∧ (Δ < 0 → 0 < z.re) ∧ (Δ ≤ 0 → 0 ≤ z.re) := by
  by_cases hd : 4 * Δ ≤ τ ^ 2
  · set s := √(τ ^ 2 - 4 * Δ)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs : s ^ 2 = τ ^ 2 - 4 * Δ := Real.sq_sqrt (by linarith)
    refine ⟨(((τ + s) / 2 : ℝ) : ℂ), ?_, ?_, fun hΔ => ?_, fun hΔ => ?_⟩
    · unfold IsCharRoot
      have : ((τ + s) / 2) ^ 2 - τ * ((τ + s) / 2) + Δ = 0 := by nlinarith
      exact_mod_cast this
    · simp only [Complex.ofReal_re]; linarith
    · simp only [Complex.ofReal_re]
      nlinarith [sq_abs τ, abs_nonneg τ, neg_abs_le τ]
    · simp only [Complex.ofReal_re]
      nlinarith [sq_abs τ, abs_nonneg τ, neg_abs_le τ]
  · push Not at hd
    set s := √(4 * Δ - τ ^ 2)
    have hs : s ^ 2 = 4 * Δ - τ ^ 2 := Real.sq_sqrt (by linarith)
    refine ⟨⟨τ / 2, s / 2⟩, ?_, le_rfl, fun hΔ => by nlinarith, fun hΔ => by nlinarith⟩
    unfold IsCharRoot
    apply Complex.ext <;> simp [pow_two] <;> nlinarith

end Roots

/-! ### Eigenvalues of a real `2 × 2` matrix -/

/-- A real `2 × 2` matrix `M` has a complex eigenvector for `z` iff `z` is a root of
`z² - (tr M) z + det M`. -/
theorem exists_mulVec_eq_smul_iff_isCharRoot (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = z • v) ↔ IsCharRoot M.trace M.det z := by
  have hdet : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M.map Complex.ofReal).det =
      z ^ 2 - (M.trace : ℂ) * z + (M.det : ℂ) := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.map_apply]
    ring
  rw [IsCharRoot, ← hdet, ← Matrix.exists_mulVec_eq_zero_iff]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

/-- The complex eigenvalues of a real `2 × 2` matrix `M` (the spectrum of its complexification, as
in `Matrix.IsHurwitz`) are exactly the roots of `z² - (tr M) z + det M`. -/
theorem mem_spectrum_iff_isCharRoot (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) ↔ IsCharRoot M.trace M.det z := by
  have hdet : (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z - M.map (algebraMap ℝ ℂ)).det =
      z ^ 2 - (M.trace : ℂ) * z + (M.det : ℂ) := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.det_fin_two, Matrix.trace_fin_two]
    ring
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, hdet,
    IsCharRoot]

/-- The spectrum of a real `2 × 2` matrix consists of the values with a complex eigenvector. -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = z • v :=
  (mem_spectrum_iff_isCharRoot M z).trans (exists_mulVec_eq_smul_iff_isCharRoot M z).symm

/-! ### Stability and instability -/

section Stability

variable {τ Δ : ℝ}

/-- Linear stability of a trace–determinant pair: every root of `z² - τ z + Δ` (every eigenvalue of
a `2 × 2` matrix with trace `τ` and determinant `Δ`) lies in the open left half-plane. For a
matrix this is `Matrix.IsHurwitz` (`isHurwitz_iff_isLinearlyStable`). -/
def IsLinearlyStable (τ Δ : ℝ) : Prop := ∀ z, IsCharRoot τ Δ z → z.re < 0

/-- Linear instability of a trace–determinant pair: some root of `z² - τ z + Δ` lies in the open
right half-plane. -/
def IsLinearlyUnstable (τ Δ : ℝ) : Prop := ∃ z, IsCharRoot τ Δ z ∧ 0 < z.re

/-- **Routh–Hurwitz for planar systems.** All roots lie in the open left half-plane iff `τ < 0`
and `Δ > 0`. -/
theorem isLinearlyStable_iff : IsLinearlyStable τ Δ ↔ τ < 0 ∧ 0 < Δ := by
  constructor
  · intro h
    obtain ⟨z, hz, h1, -, h3⟩ := exists_isCharRoot τ Δ
    have := h z hz
    refine ⟨by linarith, ?_⟩
    by_contra hΔ
    push Not at hΔ
    linarith [h3 hΔ]
  · rintro ⟨hτ, hΔ⟩ z hz
    exact hz.re_neg hτ hΔ

/-- For a real `2 × 2` matrix, `Matrix.IsHurwitz` is `IsLinearlyStable` of its trace and
determinant. -/
theorem isHurwitz_iff_isLinearlyStable (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.IsHurwitz ↔ IsLinearlyStable M.trace M.det := by
  simp only [Matrix.IsHurwitz, IsLinearlyStable, mem_spectrum_iff_isCharRoot]

/-- **Routh–Hurwitz for `2 × 2` matrices.** A real `2 × 2` matrix is Hurwitz iff its trace is
negative and its determinant positive. -/
theorem isHurwitz_iff_trace_neg_and_det_pos (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.IsHurwitz ↔ M.trace < 0 ∧ 0 < M.det := by
  rw [isHurwitz_iff_isLinearlyStable, isLinearlyStable_iff]

/-- **Instability criterion for `2 × 2` matrices.** A real `2 × 2` matrix has a complex eigenvalue
with positive real part iff its trace is positive or its determinant negative. This is
`TuringPatterns.exists_eigenvalue_re_pos_iff`, restated for the spectrum used by
`Matrix.IsHurwitz`. -/
theorem exists_spectrum_re_pos_iff (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (∃ μ ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)), 0 < μ.re) ↔ 0 < M.trace ∨ M.det < 0 := by
  rw [← TuringPatterns.exists_eigenvalue_re_pos_iff M]
  simp only [mem_spectrum_iff_exists_mulVec_eq_smul]
  exact ⟨fun ⟨μ, hμ, hre⟩ => ⟨μ, hre, hμ⟩, fun ⟨μ, hre, hμ⟩ => ⟨μ, hμ, hre⟩⟩

/-- **Instability criterion for planar systems.** Some root of `z² - τ z + Δ` lies in the open
right half-plane iff `τ > 0` or `Δ < 0`: `exists_spectrum_re_pos_iff` for the companion matrix
`!![0, -Δ; 1, τ]`, whose trace is `τ` and determinant `Δ`. -/
theorem isLinearlyUnstable_iff : IsLinearlyUnstable τ Δ ↔ 0 < τ ∨ Δ < 0 := by
  have htr : (!![0, -Δ; 1, τ] : Matrix (Fin 2) (Fin 2) ℝ).trace = τ := by
    simp [Matrix.trace_fin_two]
  have hdet : (!![0, -Δ; 1, τ] : Matrix (Fin 2) (Fin 2) ℝ).det = Δ := by
    simp [Matrix.det_fin_two]
  have h := exists_spectrum_re_pos_iff (!![0, -Δ; 1, τ] : Matrix (Fin 2) (Fin 2) ℝ)
  simp only [mem_spectrum_iff_isCharRoot, htr, hdet] at h
  exact h

end Stability

/-! ### Trace–determinant classification -/

section Classification

variable {τ Δ : ℝ}

/-- Types of a planar linearization with trace `τ` and determinant `Δ`. -/
inductive LinearType
  /-- `Δ < 0`: real eigenvalues of opposite signs. -/
  | saddle
  /-- `Δ = 0`: a zero eigenvalue. -/
  | degenerate
  /-- `τ = 0 < Δ`: purely imaginary eigenvalues (a linear center; the equilibrium is
  nonhyperbolic). -/
  | center
  /-- `τ < 0 < Δ`, `4Δ ≤ τ²`: real negative eigenvalues. -/
  | stableNode
  /-- `τ < 0`, `τ² < 4Δ`: non-real eigenvalues with negative real part. -/
  | stableFocus
  /-- `0 < τ`, `0 < Δ ≤ τ²/4`: real positive eigenvalues. -/
  | unstableNode
  /-- `0 < τ`, `τ² < 4Δ`: non-real eigenvalues with positive real part. -/
  | unstableFocus
  deriving DecidableEq

/-- The trace–determinant classification of a planar linearization. -/
def linearType (τ Δ : ℝ) : LinearType :=
  if Δ < 0 then .saddle
  else if Δ = 0 then .degenerate
  else if τ = 0 then .center
  else if τ < 0 then (if 4 * Δ ≤ τ ^ 2 then .stableNode else .stableFocus)
  else (if 4 * Δ ≤ τ ^ 2 then .unstableNode else .unstableFocus)

theorem linearType_eq_saddle_iff : linearType τ Δ = .saddle ↔ Δ < 0 := by
  unfold linearType; split_ifs <;> grind

theorem linearType_eq_degenerate_iff : linearType τ Δ = .degenerate ↔ Δ = 0 := by
  unfold linearType; split_ifs <;> grind

theorem linearType_eq_center_iff : linearType τ Δ = .center ↔ 0 < Δ ∧ τ = 0 := by
  unfold linearType; split_ifs <;> grind

theorem linearType_eq_stableNode_iff :
    linearType τ Δ = .stableNode ↔ 0 < Δ ∧ τ < 0 ∧ 4 * Δ ≤ τ ^ 2 := by
  unfold linearType; split_ifs <;> grind

theorem linearType_eq_stableFocus_iff :
    linearType τ Δ = .stableFocus ↔ 0 < Δ ∧ τ < 0 ∧ τ ^ 2 < 4 * Δ := by
  unfold linearType; split_ifs <;> grind

theorem linearType_eq_unstableNode_iff :
    linearType τ Δ = .unstableNode ↔ 0 < Δ ∧ 0 < τ ∧ 4 * Δ ≤ τ ^ 2 := by
  unfold linearType; split_ifs <;> grind

theorem linearType_eq_unstableFocus_iff :
    linearType τ Δ = .unstableFocus ↔ 0 < Δ ∧ 0 < τ ∧ τ ^ 2 < 4 * Δ := by
  unfold linearType; split_ifs <;> grind

/-- The stable classes are exactly the linearly stable linearizations (all eigenvalues in the
open left half-plane). -/
theorem isLinearlyStable_iff_linearType :
    IsLinearlyStable τ Δ ↔ linearType τ Δ = .stableNode ∨ linearType τ Δ = .stableFocus := by
  rw [isLinearlyStable_iff, linearType_eq_stableNode_iff, linearType_eq_stableFocus_iff]
  constructor
  · rintro ⟨hτ, hΔ⟩
    rcases le_or_gt (4 * Δ) (τ ^ 2) with h | h
    exacts [Or.inl ⟨hΔ, hτ, h⟩, Or.inr ⟨hΔ, hτ, h⟩]
  · rintro (⟨hΔ, hτ, -⟩ | ⟨hΔ, hτ, -⟩) <;> exact ⟨hτ, hΔ⟩

/-- Saddles and unstable nodes and foci have an eigenvalue in the open right half-plane. -/
theorem isLinearlyUnstable_of_linearType
    (h : linearType τ Δ = .saddle ∨ linearType τ Δ = .unstableNode ∨
      linearType τ Δ = .unstableFocus) : IsLinearlyUnstable τ Δ := by
  rw [isLinearlyUnstable_iff]
  rw [linearType_eq_saddle_iff, linearType_eq_unstableNode_iff,
    linearType_eq_unstableFocus_iff] at h
  rcases h with h | ⟨-, h, -⟩ | ⟨-, h, -⟩
  exacts [Or.inr h, Or.inl h, Or.inl h]

end Classification

end MathlibExt.Biology.Dynamics.PlanarStability

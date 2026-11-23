/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import MathlibExt.Analysis.Control.RecursiveLeastSquares
import MathlibExt.LinearAlgebra.Matrix.PosSemidefDeterminant

/-!
# Elliptical potential lemma

This module proves the elliptical potential lemma for linear bandits
(Tor Lattimore and Csaba Szepesvari, Bandit Algorithms, Chapter 19, Lemma 19.4):
for a positive definite initial matrix and bounded action vectors, the sum over
rounds of the capped inverse-matrix quadratic forms is bounded by twice the
logarithm of the determinant ratio, which is in turn bounded by an explicit
dimension-dependent quantity.

This module covers only the elliptical potential estimate. The stochastic
bandit history law, self-normalized concentration, and regret theorems are
separate work and are not formalized here.

The first determinant inequality reuses the recursive-least-squares
logarithmic gain bound; the determinant-trace step goes through Hermitian
eigenvalues and arithmetic-geometric means.
-/

@[expose] public section

open scoped Matrix

namespace Cslib.MachineLearning.LinearBandit

noncomputable def ellipticalGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  V0 + ∑ k ∈ Finset.range t, Matrix.vecMulVec (a k) (a k)

noncomputable def ellipticalQuadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  a k ⬝ᵥ ((ellipticalGram V0 a k)⁻¹ *ᵥ a k)

noncomputable def ellipticalPotential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  min 1 (ellipticalQuadratic V0 a k)

theorem ellipticalGram_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) :
    ellipticalGram V0 a 0 = V0 := by
  simp [ellipticalGram]

theorem ellipticalGram_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) (t : ℕ) :
    ellipticalGram V0 a (t + 1) =
      ellipticalGram V0 a t + Matrix.vecMulVec (a t) (a t) := by
  simp only [ellipticalGram, Finset.sum_range_succ, add_assoc]

theorem ellipticalGram_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V0 : Matrix ι ι ℝ} (hV0 : V0.PosDef) (a : ℕ → ι → ℝ) (t : ℕ) :
    (ellipticalGram V0 a t).PosDef := by
  have hsum : ∀ s : Finset ℕ,
      (∑ k ∈ s, Matrix.vecMulVec (a k) (a k)).PosSemidef := by
    intro s
    refine Finset.induction ?_ ?_ s
    · simpa using Matrix.PosSemidef.zero
    · intro k s hk ih
      rw [Finset.sum_insert hk]
      have h1 : (Matrix.vecMulVec (a k) (a k)).PosSemidef := by
        simpa using Matrix.posSemidef_vecMulVec_self_star (a k)
      exact h1.add ih
  exact hV0.add_posSemidef (hsum (Finset.range t))

theorem ellipticalGram_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V0 : Matrix ι ι ℝ) (a : ℕ → ι → ℝ) (t : ℕ) :
    (ellipticalGram V0 a t).trace =
      V0.trace + ∑ k ∈ Finset.range t, a k ⬝ᵥ a k := by
  simp only [ellipticalGram, Matrix.trace_add, Matrix.trace_sum,
    Matrix.trace_vecMulVec]

theorem ellipticalQuadratic_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V0 : Matrix ι ι ℝ} (hV0 : V0.PosDef) (a : ℕ → ι → ℝ) (k : ℕ) :
    0 ≤ ellipticalQuadratic V0 a k := by
  have hpsd : ((ellipticalGram V0 a k)⁻¹).PosSemidef :=
    (ellipticalGram_posDef hV0 a k).inv.posSemidef
  simpa [ellipticalQuadratic] using hpsd.dotProduct_mulVec_nonneg (a k)

theorem sum_ellipticalPotential_le_of_gain {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V0 : Matrix ι ι ℝ} (hV0 : V0.PosDef) (a : ℕ → ι → ℝ) (n : ℕ)
    (hgain : ∑ k ∈ Finset.range n,
        ellipticalQuadratic V0 a k / (1 + ellipticalQuadratic V0 a k) ≤
        Real.log (ellipticalGram V0 a n).det - Real.log V0.det) :
    ∑ k ∈ Finset.range n, ellipticalPotential V0 a k ≤
      2 * Real.log ((ellipticalGram V0 a n).det / V0.det) := by
  have hterm : ∀ k ∈ Finset.range n, ellipticalPotential V0 a k ≤
      2 * (ellipticalQuadratic V0 a k / (1 + ellipticalQuadratic V0 a k)) := by
    intro k hk
    have hx : 0 ≤ ellipticalQuadratic V0 a k :=
      ellipticalQuadratic_nonneg hV0 a k
    have hpos : (0 : ℝ) < 1 + ellipticalQuadratic V0 a k := by linarith
    by_cases h : ellipticalQuadratic V0 a k ≤ 1
    · rw [ellipticalPotential, min_eq_right h]
      have heq : (2 : ℝ) * (ellipticalQuadratic V0 a k /
          (1 + ellipticalQuadratic V0 a k)) =
          2 * ellipticalQuadratic V0 a k / (1 + ellipticalQuadratic V0 a k) := by
        ring
      rw [heq, le_div_iff₀ hpos]
      nlinarith [mul_le_mul_of_nonneg_right h hx]
    · rw [ellipticalPotential, min_eq_left (le_of_not_ge h)]
      have heq : (2 : ℝ) * (ellipticalQuadratic V0 a k /
          (1 + ellipticalQuadratic V0 a k)) =
          2 * ellipticalQuadratic V0 a k / (1 + ellipticalQuadratic V0 a k) := by
        ring
      rw [heq, le_div_iff₀ hpos]
      linarith
  calc ∑ k ∈ Finset.range n, ellipticalPotential V0 a k
      ≤ ∑ k ∈ Finset.range n,
        2 * (ellipticalQuadratic V0 a k / (1 + ellipticalQuadratic V0 a k)) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ k ∈ Finset.range n,
        (ellipticalQuadratic V0 a k / (1 + ellipticalQuadratic V0 a k)) :=
        (Finset.mul_sum ..).symm
    _ ≤ 2 * (Real.log (ellipticalGram V0 a n).det - Real.log V0.det) :=
        mul_le_mul_of_nonneg_left hgain (by norm_num)
    _ = 2 * Real.log ((ellipticalGram V0 a n).det / V0.det) := by
        rw [Real.log_div (ne_of_gt ((ellipticalGram_posDef hV0 a n).det_pos))
          (ne_of_gt hV0.det_pos)]

theorem sum_ellipticalPotential_le_two_log_det_ratio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V0 : Matrix ι ι ℝ} (hV0 : V0.PosDef) (a : ℕ → ι → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ellipticalPotential V0 a k ≤
      2 * Real.log ((ellipticalGram V0 a n).det / V0.det) := by
  have hV0inv : (V0⁻¹).PosDef := hV0.inv
  have hunit : IsUnit V0.det := isUnit_iff_ne_zero.mpr (ne_of_gt hV0.det_pos)
  have hInv : (V0⁻¹)⁻¹ = V0 := Matrix.nonsing_inv_nonsing_inv V0 hunit
  have hGram : ∀ k,
      MathlibExt.Analysis.Control.RecursiveLeastSquares.rlsInformation V0⁻¹ a k =
        ellipticalGram V0 a k := by
    intro k
    change (V0⁻¹)⁻¹ + (∑ j ∈ Finset.range k, Matrix.vecMulVec (a j) (a j)) =
      V0 + (∑ j ∈ Finset.range k, Matrix.vecMulVec (a j) (a j))
    rw [hInv]
  have hgain :=
    MathlibExt.Analysis.Control.RecursiveLeastSquares.sum_rls_gain_le_log_det hV0inv a
      (fun _ => 0) (fun _ => 0) n
  simp only [MathlibExt.Analysis.Control.RecursiveLeastSquares.rls_snd_eq_inv hV0inv a
    (fun _ => 0) (fun _ => 0), hGram, hInv] at hgain
  exact sum_ellipticalPotential_le_of_gain hV0 a n hgain

theorem log_det_ellipticalGram_ratio_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V0 : Matrix ι ι ℝ} (hV0 : V0.PosDef) (a : ℕ → ι → ℝ)
    {L : ℝ} (_hL : 0 ≤ L) (n : ℕ)
    (ha : ∀ k < n, a k ⬝ᵥ a k ≤ L ^ 2) (hd : 0 < Fintype.card ι) :
    Real.log ((ellipticalGram V0 a n).det / V0.det) ≤
      (Fintype.card ι : ℝ) *
        Real.log ((V0.trace + (n : ℝ) * L ^ 2) /
          ((Fintype.card ι : ℝ) * V0.det ^ ((Fintype.card ι : ℝ)⁻¹))) := by
  have hGpd : (ellipticalGram V0 a n).PosDef := ellipticalGram_posDef hV0 a n
  have hGps : (ellipticalGram V0 a n).PosSemidef := hGpd.posSemidef
  have hdet := hGps.det_le_pow_trace_div_card hd
  have htrace := ellipticalGram_trace V0 a n
  have hsum : ∑ k ∈ Finset.range n, a k ⬝ᵥ a k ≤ (n : ℝ) * L ^ 2 := by
    calc ∑ k ∈ Finset.range n, a k ⬝ᵥ a k
        ≤ ∑ k ∈ Finset.range n, L ^ 2 :=
          Finset.sum_le_sum (fun k hk => ha k (Finset.mem_range.mp hk))
      _ = (n : ℝ) * L ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hX : (ellipticalGram V0 a n).trace ≤ V0.trace + (n : ℝ) * L ^ 2 := by
    rw [htrace]; linarith
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have htrace_nn : (0 : ℝ) ≤ (ellipticalGram V0 a n).trace := hGps.trace_nonneg
  have hle : (ellipticalGram V0 a n).trace / (Fintype.card ι : ℝ) ≤
      (V0.trace + (n : ℝ) * L ^ 2) / (Fintype.card ι : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hX (inv_nonneg.mpr hcard_pos.le)
  have hpow : ((ellipticalGram V0 a n).trace / (Fintype.card ι : ℝ)) ^ Fintype.card ι ≤
      ((V0.trace + (n : ℝ) * L ^ 2) / (Fintype.card ι : ℝ)) ^ Fintype.card ι :=
    pow_le_pow_left₀ (div_nonneg htrace_nn hcard_pos.le) hle _
  have hVdet_pos : (0 : ℝ) < V0.det := hV0.det_pos
  have hGdet_pos : (0 : ℝ) < (ellipticalGram V0 a n).det := hGpd.det_pos
  have hrpowV : (V0.det ^ ((Fintype.card ι : ℝ))⁻¹) ^ Fintype.card ι = V0.det := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVdet_pos.le, inv_mul_cancel₀ hcard_ne,
      Real.rpow_one]
  have hdetY : (ellipticalGram V0 a n).det / V0.det ≤
      ((V0.trace + (n : ℝ) * L ^ 2) /
        ((Fintype.card ι : ℝ) * V0.det ^ ((Fintype.card ι : ℝ)⁻¹))) ^
        Fintype.card ι := by
    have h1 : (ellipticalGram V0 a n).det ≤
        ((V0.trace + (n : ℝ) * L ^ 2) / (Fintype.card ι : ℝ)) ^ Fintype.card ι :=
      le_trans hdet hpow
    have h2 : (ellipticalGram V0 a n).det / V0.det ≤
        (((V0.trace + (n : ℝ) * L ^ 2) / (Fintype.card ι : ℝ)) ^ Fintype.card ι) /
          V0.det := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hVdet_pos.le)
    have halg : (((V0.trace + (n : ℝ) * L ^ 2) / (Fintype.card ι : ℝ)) ^
        Fintype.card ι) / V0.det =
        ((V0.trace + (n : ℝ) * L ^ 2) /
          ((Fintype.card ι : ℝ) * V0.det ^ ((Fintype.card ι : ℝ)⁻¹))) ^
          Fintype.card ι := by
      rw [div_pow, div_pow, mul_pow, hrpowV, div_div]
    rwa [halg] at h2
  calc Real.log ((ellipticalGram V0 a n).det / V0.det)
      ≤ Real.log ((((V0.trace + (n : ℝ) * L ^ 2) /
        ((Fintype.card ι : ℝ) * V0.det ^ ((Fintype.card ι : ℝ)⁻¹))) ^
        Fintype.card ι)) :=
        Real.log_le_log (div_pos hGdet_pos hVdet_pos) hdetY
    _ = (Fintype.card ι : ℝ) * Real.log ((V0.trace + (n : ℝ) * L ^ 2) /
        ((Fintype.card ι : ℝ) * V0.det ^ ((Fintype.card ι : ℝ)⁻¹))) :=
        Real.log_pow _ _

theorem elliptical_potential_lemma
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V0 : Matrix ι ι ℝ} (hV0 : V0.PosDef) (a : ℕ → ι → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (n : ℕ)
    (ha : ∀ k < n, a k ⬝ᵥ a k ≤ L ^ 2) (hd : 0 < Fintype.card ι) :
    ∑ k ∈ Finset.range n, ellipticalPotential V0 a k ≤
        2 * Real.log ((ellipticalGram V0 a n).det / V0.det) ∧
      2 * Real.log ((ellipticalGram V0 a n).det / V0.det) ≤
        2 * (Fintype.card ι : ℝ) *
          Real.log ((V0.trace + (n : ℝ) * L ^ 2) /
            ((Fintype.card ι : ℝ) * V0.det ^ ((Fintype.card ι : ℝ)⁻¹))) := by
  refine ⟨sum_ellipticalPotential_le_two_log_det_ratio hV0 a n, ?_⟩
  have h := log_det_ellipticalGram_ratio_le hV0 a hL n ha hd
  have h2 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
  rwa [mul_assoc]

end Cslib.MachineLearning.LinearBandit

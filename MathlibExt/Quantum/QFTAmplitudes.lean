/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# QFT row normalization and orthogonality

The QFT amplitude from input `j` to output `k` is
`ω^(j*k) * s` with `‖ω‖ = 1`. Each row is normalized
(`∑ k, normSq = 1` when `s^2 * N = 1`), and distinct rows
are orthogonal given the vanishing geometric sum for their
difference. The full unitary QFT on state vectors and
phase estimation are not included here.
-/

@[expose] public section

/-- QFT amplitudes (core of QCI-09): for input basis index
`j`, output index `k`, the amplitude is `ω^(j*k) * s` where
`ω` is a complex number of norm `1` and `s` a real scale
with `s^2 = 2^{-n}`-normalization as a hypothesis on the
number of outputs `N`: `s^2 * N = 1`. -/
noncomputable def qftAmp (ω : ℂ) (s : ℝ) (j k : ℕ) : ℂ :=
  (ω ^ (j * k)) * s

/-- Each QFT output distribution is normalized: summing the
squared magnitudes over all `N` outputs gives `1`. -/
theorem qftAmp_norm_sum {N : ℕ} (ω : ℂ) (hω : ‖ω‖ = 1)
    (s : ℝ) (hs : s ^ 2 * N = 1) (j : ℕ) :
    ∑ k ∈ Finset.range N, Complex.normSq (qftAmp ω s j k) = 1 := by
  have hωsq : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hω, one_pow]
  have hterm : ∀ k : ℕ, Complex.normSq (qftAmp ω s j k) = s ^ 2 := by
    intro k
    show Complex.normSq ((ω ^ (j * k)) * (s : ℂ)) = s ^ 2
    rw [Complex.normSq_mul, map_pow, hωsq, one_pow, one_mul,
      Complex.normSq_ofReal, pow_two]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  exact hs

/-- Distinct input rows are orthogonal, given the vanishing
geometric sum for their difference (the root-of-unity filter
input). -/
theorem qftAmp_inner_eq_zero {N : ℕ} (ω : ℂ) (s : ℝ)
    {j₁ j₂ : ℕ}
    (hsum : ∑ k ∈ Finset.range N,
      (starRingEnd ℂ (ω ^ (j₁ * k))) * (ω ^ (j₂ * k)) = 0) :
    ∑ k ∈ Finset.range N,
      (starRingEnd ℂ (qftAmp ω s j₁ k)) * (qftAmp ω s j₂ k) = 0 := by
  have hterm : ∀ k : ℕ, (starRingEnd ℂ (qftAmp ω s j₁ k)) * (qftAmp ω s j₂ k)
      = ((s : ℂ) * (s : ℂ)) *
        ((starRingEnd ℂ (ω ^ (j₁ * k))) * (ω ^ (j₂ * k))) := by
    intro k
    show (starRingEnd ℂ ((ω ^ (j₁ * k)) * (s : ℂ))) * ((ω ^ (j₂ * k)) * (s : ℂ)) = _
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← Finset.mul_sum, hsum, mul_zero]

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# QFT row normalization and orthogonality

For `ω : ℂ` and a real scale `s`, `qftAmp ω s j k = ω ^ (j * k) * s` is the amplitude from
input basis index `j` to output index `k`. With `ω = exp (2πi / N)` and `s = 1 / √N` these
are the entries of the quantum Fourier transform on `N` basis states. Each result below
states the hypotheses on `ω` and `s` that it uses.

## Main results

* `MathlibExt.Quantum.QFTAmplitudes.qftAmp_norm_sum`: if `‖ω‖ = 1` and `s ^ 2 * N = 1`,
  the squared magnitudes of a row sum to `1` over the `N` outputs.
* `MathlibExt.Quantum.QFTAmplitudes.qftAmp_inner_eq_zero`: if `ω` is a primitive `N`-th
  root of unity, the rows of distinct inputs `j₁ ≠ j₂` in `Fin N` are orthogonal. The
  unscaled sum is a geometric series in `ω⁻¹ ^ j₁ * ω ^ j₂`, an `N`-th root of unity
  different from `1`.
* `MathlibExt.Quantum.QFTAmplitudes.qftAmp_inner_eq`: scaling helper, the inner product of
  two rows is `s ^ 2` times the unscaled sum.

The unitary QFT acting on state vectors and phase estimation are not included here.

## References

* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*,
  Cambridge University Press, 2000, Section 5.1.
-/

@[expose] public section

namespace MathlibExt.Quantum.QFTAmplitudes

/-- The amplitude `ω ^ (j * k) * s` from input basis index `j` to output index `k`. With
`ω = exp (2πi / N)` and `s = 1 / √N` these are the QFT matrix entries on `N` basis
states. -/
noncomputable def qftAmp (ω : ℂ) (s : ℝ) (j k : ℕ) : ℂ :=
  (ω ^ (j * k)) * s

/-- Each row is normalized: if `‖ω‖ = 1` and `s ^ 2 * N = 1`, summing the squared
magnitudes of the amplitudes over all `N` outputs gives `1`. -/
theorem qftAmp_norm_sum {N : ℕ} (ω : ℂ) (hω : ‖ω‖ = 1)
    (s : ℝ) (hs : s ^ 2 * N = 1) (j : ℕ) :
    ∑ k ∈ Finset.range N, Complex.normSq (qftAmp ω s j k) = 1 := by
  have hωsq : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hω, one_pow]
  have hterm : ∀ k : ℕ, Complex.normSq (qftAmp ω s j k) = s ^ 2 := by
    intro k
    rw [qftAmp, Complex.normSq_mul, map_pow, hωsq, one_pow, one_mul,
      Complex.normSq_ofReal, pow_two]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  exact hs

/-- Scaling helper: the inner product of the rows of inputs `j₁` and `j₂` is `s ^ 2` times
the unscaled sum of `conj (ω ^ (j₁ * k)) * ω ^ (j₂ * k)`. -/
theorem qftAmp_inner_eq (ω : ℂ) (s : ℝ) (N j₁ j₂ : ℕ) :
    ∑ k ∈ Finset.range N, (starRingEnd ℂ (qftAmp ω s j₁ k)) * (qftAmp ω s j₂ k) =
      (s : ℂ) ^ 2 *
        ∑ k ∈ Finset.range N, (starRingEnd ℂ (ω ^ (j₁ * k))) * (ω ^ (j₂ * k)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qftAmp, qftAmp, map_mul, Complex.conj_ofReal]
  ring

/-- Distinct rows are orthogonal: if `ω` is a primitive `N`-th root of unity and
`j₁ ≠ j₂` in `Fin N`, the rows of inputs `j₁` and `j₂` have inner product `0`, for every
scale `s`. -/
theorem qftAmp_inner_eq_zero {N : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω N) (s : ℝ)
    {j₁ j₂ : Fin N} (hne : j₁ ≠ j₂) :
    ∑ k ∈ Finset.range N,
      (starRingEnd ℂ (qftAmp ω s j₁ k)) * (qftAmp ω s j₂ k) = 0 := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact j₁.elim0
  have hω0 : ω ≠ 0 := hω.ne_zero hN
  have hconj : starRingEnd ℂ ω = ω⁻¹ := (Complex.inv_eq_conj (hω.norm'_eq_one hN)).symm
  -- Each unscaled term is the `k`-th power of `z = ω⁻¹ ^ j₁ * ω ^ j₂`.
  set z : ℂ := ω⁻¹ ^ (j₁ : ℕ) * ω ^ (j₂ : ℕ) with hz
  have hterm : ∀ k : ℕ,
      (starRingEnd ℂ (ω ^ ((j₁ : ℕ) * k))) * (ω ^ ((j₂ : ℕ) * k)) = z ^ k := by
    intro k
    rw [map_pow, hconj, hz, mul_pow, ← pow_mul, ← pow_mul]
  have hzN : z ^ N = 1 := by
    rw [hz, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j₁ : ℕ) N, mul_comm (j₂ : ℕ) N,
      pow_mul, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow, one_pow, one_mul]
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, inv_pow] at h
    have hpow : ω ^ (j₁ : ℕ) = ω ^ (j₂ : ℕ) :=
      (inv_mul_eq_one₀ (pow_ne_zero _ hω0)).mp h
    exact hne (Fin.ext (hω.pow_inj j₁.isLt j₂.isLt hpow))
  have hgeom : (∑ k ∈ Finset.range N, z ^ k) * (z - 1) = 0 := by
    rw [geom_sum_mul, hzN, sub_self]
  have hsum : ∑ k ∈ Finset.range N, z ^ k = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hz1)
  rw [qftAmp_inner_eq, Finset.sum_congr rfl fun k _ => hterm k, hsum, mul_zero]

end MathlibExt.Quantum.QFTAmplitudes

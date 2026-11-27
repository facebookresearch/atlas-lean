/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Phase-estimation coefficient bound

For `0 < N` and a real offset `δ`, `peAmp N δ` is the normalized geometric sum
`(1 / N) * ∑ y < N, exp (2 * π * i * δ * y)`. With `N = 2 ^ m` it is the coefficient in equation
(5.3) of §5 of R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited"
(arXiv:quant-ph/9708016). There `δ` is the offset of the phase from its best `m`-bit estimate,
and the coefficient is the amplitude of that estimate after the inverse quantum Fourier
transform.

This module proves the analytic step of that argument: when `|δ| ≤ 1 / (2 * N)`, the squared
norm of `peAmp N δ` is at least `4 / π ^ 2` (equation (5.4) for `N = 2 ^ m`). The proof uses the
closed form of the geometric sum (equation (5.3)) and a chord bound from Jordan's inequality.
The results bound a scalar coefficient for a given offset. They do not choose the nearest
outcome, relate the coefficient to the inverse quantum Fourier transform or model measurement,
so they do not state the success probability of phase estimation.
-/

@[expose] public section

open BigOperators Real

namespace MathlibExt.Quantum.PhaseEstimationAnalytic

/-- **Phase-estimation coefficient.** For `N : ℕ` and a real offset `δ`,
`peAmp N δ = (1 / N) * ∑ y ∈ Finset.range N, exp (2 * π * i * δ * y)`. For `N = 2 ^ m` this is
the normalized geometric sum of Cleve et al., equation (5.3). -/
noncomputable def peAmp (N : ℕ) (δ : ℝ) : ℂ :=
  (1 / N : ℂ) * ∑ y ∈ Finset.range N, Complex.exp (2 * π * Complex.I * δ * y)

/-- **Chord bound from Jordan's inequality.** For a real `θ` with `|θ| ≤ π`,
`2 / π * |θ| ≤ ‖1 - exp (i * θ)‖`. -/
theorem norm_one_sub_exp_ge (θ : ℝ) (hθ : |θ| ≤ π) :
    2 / π * |θ| ≤ ‖1 - Complex.exp (Complex.I * θ)‖ := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hθ
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    show |(2 : ℝ)| = 2 from by norm_num]
  by_cases hθ0 : 0 ≤ θ
  · rw [abs_of_nonneg hθ0]
    have h2nn : (0 : ℝ) ≤ θ / 2 := by linarith
    have h2le : θ / 2 ≤ π / 2 := by linarith [Real.pi_pos]
    have hsin : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h2nn (by linarith [Real.pi_pos])
    rw [abs_of_nonneg hsin]
    have hj := Real.mul_le_sin h2nn h2le
    linarith [hj, Real.pi_pos]
  · push Not at hθ0
    rw [abs_of_neg hθ0]
    have h2nn : (0 : ℝ) ≤ -θ / 2 := by linarith
    have h2le : -θ / 2 ≤ π / 2 := by linarith [Real.pi_pos]
    have hsin : 0 ≤ Real.sin (-θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h2nn (by linarith [Real.pi_pos])
    have habs : |Real.sin (θ / 2)| = Real.sin (-θ / 2) := by
      have e : θ / 2 = -(-θ / 2) := by ring
      rw [e, Real.sin_neg, abs_neg, abs_of_nonneg hsin]
    rw [habs]
    have hj := Real.mul_le_sin h2nn h2le
    linarith [hj, Real.pi_pos]

/-- **Closed form of the coefficient.** For `0 < N` and an offset `δ` with
`exp (2 * π * i * δ) ≠ 1`, summing the geometric series gives
`peAmp N δ = (1 / N) * (1 - exp (2 * π * i * δ) ^ N) / (1 - exp (2 * π * i * δ))`
(Cleve et al., equation (5.3)). -/
theorem peAmp_eq_div (N : ℕ) (δ : ℝ) (hN : 0 < N)
    (hω : Complex.exp (2 * π * Complex.I * δ) ≠ 1) :
    peAmp N δ =
      (1 / N) * (1 - Complex.exp (2 * π * Complex.I * δ) ^ N) /
        (1 - Complex.exp (2 * π * Complex.I * δ)) := by
  have hterm : ∀ y ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * δ * y) =
        Complex.exp (2 * π * Complex.I * δ) ^ y := by
    intro y _
    have harg : (2 * π * Complex.I * δ * y : ℂ) =
        (y : ℂ) * (2 * π * Complex.I * δ) := by
      ring
    rw [harg]
    exact Complex.exp_nat_mul _ y
  have hNℂ : ((N : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hsub : Complex.exp (2 * π * Complex.I * δ) - 1 ≠ 0 := sub_ne_zero.mpr hω
  have hsub' : (1 : ℂ) - Complex.exp (2 * π * Complex.I * δ) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hω)
  unfold peAmp
  rw [Finset.sum_congr rfl hterm, geom_sum_eq hω N]
  field_simp
  ring

/-- **Coefficient at offset zero.** For `0 < N`, `peAmp N 0 = 1`. -/
theorem peAmp_zero (N : ℕ) (hN : 0 < N) : peAmp N 0 = 1 := by
  have hexp : ∀ y ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * (0 : ℝ) * y) = 1 := by
    intro y _
    have h0 : (2 * π * Complex.I * (0 : ℝ) * y : ℂ) = 0 := by simp
    rw [h0, Complex.exp_zero]
  have hNℂ : ((N : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hN
  unfold peAmp
  rw [Finset.sum_congr rfl hexp, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  exact one_div_mul_cancel hNℂ

/-- **Coefficient bound.** For `0 < N` and a real offset `δ` with `|δ| ≤ 1 / (2 * N)`, `δ = 0`
included, `4 / π ^ 2 ≤ ‖peAmp N δ‖ ^ 2`. -/
theorem four_div_pi_sq_le_normSq_peAmp (N : ℕ) (hN : 0 < N) (δ : ℝ)
    (hδ : |δ| ≤ 1 / (2 * N)) : 4 / π ^ 2 ≤ ‖peAmp N δ‖ ^ 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hπne : π ≠ 0 := ne_of_gt hpi
  have hNℝ : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNℝ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := mul_pos (by norm_num) hNℝ
  have h2Nne : (2 : ℝ) * (N : ℝ) ≠ 0 := ne_of_gt h2N
  have hδ2N : 2 * (N : ℝ) * |δ| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hδ (le_of_lt h2N)
    have hcancel : 2 * (N : ℝ) * (1 / (2 * (N : ℝ))) = 1 :=
      mul_one_div_cancel h2Nne
    rw [hcancel] at h
    exact h
  by_cases hδ0 : δ = 0
  · subst hδ0
    rw [peAmp_zero N hN, norm_one, one_pow]
    have hπ2 : (8 : ℝ) ≤ π ^ 2 := by
      nlinarith [Real.pi_gt_three, sq_nonneg (π - 3), hpi]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < π ^ 2)]
    linarith
  · have hφ : (2 : ℝ) * π * δ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hπne) hδ0
    have hφπ : |2 * π * δ| ≤ π := by
      have h2δ : 2 * |δ| ≤ 1 := by
        have hle : (2 : ℝ) * |δ| * 1 ≤ 2 * |δ| * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hN1 (by positivity)
        have hle2 : (2 : ℝ) * |δ| ≤ 2 * (N : ℝ) * |δ| := by linarith [hle]
        linarith [hle2, hδ2N]
      have habs : |2 * π * δ| = 2 * π * |δ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hpi.le]
      rw [habs]
      have hle : π * (2 * |δ|) ≤ π * 1 := mul_le_mul_of_nonneg_left h2δ hpi.le
      linarith [hle]
    have hωφ : Complex.exp (2 * π * Complex.I * δ) =
        Complex.exp (Complex.I * ((2 * π * δ : ℝ))) := by
      congr 1
      push_cast
      ring
    have hL1φ := norm_one_sub_exp_ge (2 * π * δ) hφπ
    rw [← hωφ] at hL1φ
    have habsφ : (0 : ℝ) < |2 * π * δ| := abs_pos.mpr hφ
    have h2pi : (0 : ℝ) < 2 / π := by positivity
    have hpos : (0 : ℝ) < 2 / π * |2 * π * δ| := mul_pos h2pi habsφ
    have hω1 : Complex.exp (2 * π * Complex.I * δ) ≠ 1 := by
      intro hcon
      rw [hcon, sub_self, norm_zero] at hL1φ
      linarith
    have hθπ : |2 * π * δ * (N : ℝ)| ≤ π := by
      have habs : |2 * π * δ * (N : ℝ)| = π * (2 * (N : ℝ) * |δ|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hpi.le, abs_of_nonneg hNℝ.le]
        ring
      rw [habs]
      have hle : π * (2 * (N : ℝ) * |δ|) ≤ π * 1 :=
        mul_le_mul_of_nonneg_left hδ2N hpi.le
      linarith [hle]
    have hωN : Complex.exp (2 * π * Complex.I * δ) ^ N =
        Complex.exp (Complex.I * ((2 * π * δ * N : ℝ))) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hL1N := norm_one_sub_exp_ge (2 * π * δ * N) hθπ
    rw [← hωN] at hL1N
    have habsN : |2 * π * δ * (N : ℝ)| = 2 * π * |δ| * (N : ℝ) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hpi.le, abs_of_nonneg hNℝ.le]
    rw [habsN] at hL1N
    have hnum : (4 : ℝ) * |δ| * (N : ℝ) ≤
        ‖1 - Complex.exp (2 * π * Complex.I * δ) ^ N‖ := by
      have heq : (2 : ℝ) / π * (2 * π * |δ| * (N : ℝ)) = 4 * |δ| * (N : ℝ) := by
        field_simp
        ring
      rw [heq] at hL1N
      exact hL1N
    have hden : ‖1 - Complex.exp (2 * π * Complex.I * δ)‖ ≤ 2 * π * |δ| := by
      rw [norm_sub_rev, hωφ]
      have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (2 * π * δ : ℝ))
      have hnorm : ‖(2 * π * δ : ℝ)‖ = 2 * π * |δ| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hpi.le]
      rw [hnorm] at hle
      exact hle
    have hb : (0 : ℝ) < ‖1 - Complex.exp (2 * π * Complex.I * δ)‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr (Ne.symm hω1)
    have hL2 := peAmp_eq_div N δ hN hω1
    have hNℂ : ‖((N : ℂ))‖ = (N : ℝ) := Complex.norm_natCast N
    have hnorm : ‖peAmp N δ‖ =
        ((1 / (N : ℝ)) * ‖1 - Complex.exp (2 * π * Complex.I * δ) ^ N‖) /
          ‖1 - Complex.exp (2 * π * Complex.I * δ)‖ := by
      rw [hL2, norm_div, norm_mul, norm_div, norm_one, hNℂ]
    have hge : (2 : ℝ) / π ≤ ‖peAmp N δ‖ := by
      rw [hnorm, le_div_iff₀ hb]
      have h1 : (2 : ℝ) / π * ‖1 - Complex.exp (2 * π * Complex.I * δ)‖ ≤
          4 * |δ| := by
        have hh : (2 : ℝ) / π * ‖1 - Complex.exp (2 * π * Complex.I * δ)‖ ≤
            2 / π * (2 * π * |δ|) := mul_le_mul_of_nonneg_left hden h2pi.le
        have heq : (2 : ℝ) / π * (2 * π * |δ|) = 4 * |δ| := by
          field_simp
          ring
        rw [heq] at hh
        exact hh
      have h2 : (4 : ℝ) * |δ| ≤ (1 / (N : ℝ)) *
          ‖1 - Complex.exp (2 * π * Complex.I * δ) ^ N‖ := by
        have hh : (1 / (N : ℝ)) * (4 * |δ| * (N : ℝ)) ≤ (1 / (N : ℝ)) *
            ‖1 - Complex.exp (2 * π * Complex.I * δ) ^ N‖ :=
          mul_le_mul_of_nonneg_left hnum (by positivity)
        have heq : (1 / (N : ℝ)) * (4 * |δ| * (N : ℝ)) = 4 * |δ| := by
          field_simp
        rw [heq] at hh
        exact hh
      linarith [h1, h2]
    have hsq : ((2 : ℝ) / π) ^ 2 ≤ ‖peAmp N δ‖ ^ 2 := by
      have h2p : (0 : ℝ) ≤ 2 / π := by positivity
      have hnn : (0 : ℝ) ≤ ‖peAmp N δ‖ := norm_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr hge) (add_nonneg hnn h2p)]
    have heq : ((2 : ℝ) / π) ^ 2 = 4 / π ^ 2 := by
      field_simp
      ring
    rw [heq] at hsq
    exact hsq

/-- **Coefficient bound for `N = 2 ^ m`.** For an offset `δ` with `0 < |δ|` and
`|δ| ≤ 1 / 2 ^ (m + 1)`, `4 / π ^ 2 ≤ ‖peAmp (2 ^ m) δ‖ ^ 2`. This is the inequality of
Cleve et al., equation (5.4), under the source's hypotheses on `δ`. The bound itself does not
need `0 < |δ|`: `four_div_pi_sq_le_normSq_peAmp` allows `δ = 0`. -/
theorem four_div_pi_sq_le_normSq_peAmp_two_pow (m : ℕ) (δ : ℝ) (_hδ : 0 < |δ|)
    (hδm : |δ| ≤ 1 / 2 ^ (m + 1)) : 4 / π ^ 2 ≤ ‖peAmp (2 ^ m) δ‖ ^ 2 := by
  have h2m : 0 < 2 ^ m := by positivity
  refine four_div_pi_sq_le_normSq_peAmp (2 ^ m) h2m δ ?_
  have heq : (2 : ℝ) * (((2 ^ m : ℕ)) : ℝ) = 2 ^ (m + 1) := by
    push_cast
    rw [pow_succ']
  rw [heq]
  exact hδm

end MathlibExt.Quantum.PhaseEstimationAnalytic

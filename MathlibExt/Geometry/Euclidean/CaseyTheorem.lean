/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Ptolemy equality for four unit-modulus complex numbers whose consecutive
pairwise "crosses" are positive. From `(z1-z3)(z2-z4) = (z1-z2)(z3-z4) + (z2-z3)(z1-z4)`
it suffices to show `conj P * Q` is a positive real, where `P, Q` are the two
summand factors. Writing `conj P * Q = -(1-z1 conj z2)(1-z2 conj z3)(1-z3 conj z4)(1-z4 conj z1)`
and factoring each `(1 - zj conj zk) = Sjk * (mjk + I)` exhibits the real and
imaginary parts explicitly. -/
private lemma complex_ptolemy {z1 z2 z3 z4 : ℂ}
    {D12 D23 D34 D41 S12 S23 S34 S41 : ℝ}
    (h1 : Complex.normSq z1 = 1) (h2 : Complex.normSq z2 = 1)
    (h3 : Complex.normSq z3 = 1) (h4 : Complex.normSq z4 = 1)
    (hD12 : ((starRingEnd ℂ) z1 * z2).re = D12)
    (hD23 : ((starRingEnd ℂ) z2 * z3).re = D23)
    (hD34 : ((starRingEnd ℂ) z3 * z4).re = D34)
    (hD41 : ((starRingEnd ℂ) z4 * z1).re = D41)
    (hS12 : ((starRingEnd ℂ) z1 * z2).im = S12)
    (hS23 : ((starRingEnd ℂ) z2 * z3).im = S23)
    (hS34 : ((starRingEnd ℂ) z3 * z4).im = S34)
    (hS41 : ((starRingEnd ℂ) z4 * z1).im = S41)
    (hS12pos : 0 < S12) (hS23pos : 0 < S23) (hS34pos : 0 < S34) (hS41pos : 0 < S41)
    (hA12 : 0 < 1 - D12) (hA23 : 0 < 1 - D23)
    (hA34 : 0 < 1 - D34) (hA41 : 0 < 1 - D41)
    : ‖z1 - z2‖ * ‖z3 - z4‖ + ‖z2 - z3‖ * ‖z1 - z4‖
      = ‖z1 - z3‖ * ‖z2 - z4‖ := by
  set P : ℂ := (z1 - z2) * (z3 - z4) with hP
  set Q : ℂ := (z2 - z3) * (z1 - z4) with hQ
  set Rr : ℂ := (z1 - z3) * (z2 - z4) with hRr
  set w : ℂ := (starRingEnd ℂ) P * Q with hw
  clear_value P Q Rr w
  have hPQR : P + Q = Rr := by rw [hP, hQ, hRr]; ring
  have nz1 : z1 ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at h1; exact zero_ne_one h1
  have nz2 : z2 ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at h2; exact zero_ne_one h2
  have nz3 : z3 ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at h3; exact zero_ne_one h3
  have nz4 : z4 ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at h4; exact zero_ne_one h4
  have c1 : (starRingEnd ℂ) z1 = z1⁻¹ := by simp [Complex.inv_def, h1]
  have c2 : (starRingEnd ℂ) z2 = z2⁻¹ := by simp [Complex.inv_def, h2]
  have c3 : (starRingEnd ℂ) z3 = z3⁻¹ := by simp [Complex.inv_def, h3]
  have c4 : (starRingEnd ℂ) z4 = z4⁻¹ := by simp [Complex.inv_def, h4]
  -- rewrite `a * conj b` knowing `conj a * b`
  have key : ∀ a b : ℂ, ∀ D S : ℝ, ((starRingEnd ℂ) a * b).re = D →
      ((starRingEnd ℂ) a * b).im = S →
      a * (starRingEnd ℂ) b = ((D : ℝ) : ℂ) - ((S : ℝ) : ℂ) * Complex.I := by
    intro a b D S hD hS
    have hDS : (starRingEnd ℂ) a * b = ((D : ℝ) : ℂ) + ((S : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im ((starRingEnd ℂ) a * b)]
      rw [hD, hS]
    have hconj : (starRingEnd ℂ) ((starRingEnd ℂ) a * b)
        = a * (starRingEnd ℂ) b := by
      rw [map_mul, starRingEnd_self_apply]
    rw [← hconj, hDS, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have u12 : ((1 - D12 : ℝ) : ℂ) + (S12 : ℂ) * Complex.I
      = 1 - z1 * (starRingEnd ℂ) z2 := by
    rw [key z1 z2 D12 S12 hD12 hS12]
    push_cast
    ring
  have u23 : ((1 - D23 : ℝ) : ℂ) + (S23 : ℂ) * Complex.I
      = 1 - z2 * (starRingEnd ℂ) z3 := by
    rw [key z2 z3 D23 S23 hD23 hS23]
    push_cast
    ring
  have u34 : ((1 - D34 : ℝ) : ℂ) + (S34 : ℂ) * Complex.I
      = 1 - z3 * (starRingEnd ℂ) z4 := by
    rw [key z3 z4 D34 S34 hD34 hS34]
    push_cast
    ring
  have u41 : ((1 - D41 : ℝ) : ℂ) + (S41 : ℂ) * Complex.I
      = 1 - z4 * (starRingEnd ℂ) z1 := by
    rw [key z4 z1 D41 S41 hD41 hS41]
    push_cast
    ring
  -- the product in factored form
  set Uu : ℂ := ((((1 - D12 : ℝ) : ℂ) + (S12 : ℂ) * Complex.I) *
    (((((1 - D23 : ℝ) : ℂ) + (S23 : ℂ) * Complex.I) *
    ((((1 - D34 : ℝ) : ℂ) + (S34 : ℂ) * Complex.I) *
      ((((1 - D41 : ℝ) : ℂ) + (S41 : ℂ) * Complex.I)))))) with hUu
  clear_value Uu
  have eP : (starRingEnd ℂ) P
      = ((starRingEnd ℂ) z1 - (starRingEnd ℂ) z2)
        * ((starRingEnd ℂ) z3 - (starRingEnd ℂ) z4) := by
    rw [hP, map_mul, map_sub, map_sub]
  have hC1 : w = -Uu := by
    rw [hw, hUu, u12, u23, u34, u41, eP, c1, c2, c3, c4, hQ]
    field_simp
    ring
  -- modulus inversion facts
  have ePc : (starRingEnd ℂ) P = P * (z1 * z2 * z3 * z4)⁻¹ := by
    rw [eP, c1, c2, c3, c4, hP]
    field_simp
    ring
  have eQc : (starRingEnd ℂ) Q = Q * (z1 * z2 * z3 * z4)⁻¹ := by
    have eQ : (starRingEnd ℂ) Q
        = ((starRingEnd ℂ) z2 - (starRingEnd ℂ) z3)
          * ((starRingEnd ℂ) z1 - (starRingEnd ℂ) z4) := by
      rw [hQ, map_mul, map_sub, map_sub]
    rw [eQ, c1, c2, c3, c4, hQ]
    field_simp
    ring
  have hc : (starRingEnd ℂ) w = w := by
    rw [hw, map_mul, starRingEnd_self_apply, eQc, ePc]
    ring
  have hwim : w.im = 0 := Complex.conj_eq_iff_im.mp hc
  -- half-angle slopes
  have nS12 : S12 ≠ 0 := ne_of_gt hS12pos
  have nS23 : S23 ≠ 0 := ne_of_gt hS23pos
  have nS34 : S34 ≠ 0 := ne_of_gt hS34pos
  have nS41 : S41 ≠ 0 := ne_of_gt hS41pos
  set m12 : ℝ := (1 - D12) / S12 with hm12
  set m23 : ℝ := (1 - D23) / S23 with hm23
  set m34 : ℝ := (1 - D34) / S34 with hm34
  set m41 : ℝ := (1 - D41) / S41 with hm41
  set M1 : ℝ := m12 * m23 with hM1
  set N1 : ℝ := m12 + m23 with hN1
  set M2 : ℝ := m34 * m41 with hM2
  set N2 : ℝ := m34 + m41 with hN2
  have eSm : ∀ A S : ℝ, S ≠ 0 → ∀ m : ℝ, m = A / S →
      ((S : ℝ) : ℂ) * (((m : ℝ) : ℂ) + Complex.I)
        = ((A : ℝ) : ℂ) + (S : ℂ) * Complex.I := by
    intro A S hS m hm
    have hS' : ((S : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hS
    rw [hm]
    push_cast
    field_simp
  have e12 : ((S12 : ℝ) : ℂ) * (((m12 : ℝ) : ℂ) + Complex.I)
      = ((1 - D12 : ℝ) : ℂ) + (S12 : ℂ) * Complex.I :=
    eSm (1 - D12) S12 nS12 m12 hm12
  have e23 : ((S23 : ℝ) : ℂ) * (((m23 : ℝ) : ℂ) + Complex.I)
      = ((1 - D23 : ℝ) : ℂ) + (S23 : ℂ) * Complex.I :=
    eSm (1 - D23) S23 nS23 m23 hm23
  have e34 : ((S34 : ℝ) : ℂ) * (((m34 : ℝ) : ℂ) + Complex.I)
      = ((1 - D34 : ℝ) : ℂ) + (S34 : ℂ) * Complex.I :=
    eSm (1 - D34) S34 nS34 m34 hm34
  have e41 : ((S41 : ℝ) : ℂ) * (((m41 : ℝ) : ℂ) + Complex.I)
      = ((1 - D41 : ℝ) : ℂ) + (S41 : ℂ) * Complex.I :=
    eSm (1 - D41) S41 nS41 m41 hm41
  set Ww : ℂ := ((((m12 : ℝ) : ℂ) + Complex.I) *
    (((((m23 : ℝ) : ℂ) + Complex.I) *
    ((((m34 : ℝ) : ℂ) + Complex.I) * ((((m41 : ℝ) : ℂ) + Complex.I)))))) with hWw
  clear_value Ww
  have eProd : Uu = ((S12 * S23 * S34 * S41 : ℝ) : ℂ) * Ww := by
    rw [hUu, hWw, ← e12, ← e23, ← e34, ← e41]
    push_cast
    ring
  set P1 : ℂ := ((((m12 : ℝ) : ℂ) + Complex.I) * ((((m23 : ℝ) : ℂ) + Complex.I))) with hP1
  set P2 : ℂ := ((((m34 : ℝ) : ℂ) + Complex.I) * ((((m41 : ℝ) : ℂ) + Complex.I))) with hP2
  clear_value P1 P2
  have hWw12 : Ww = P1 * P2 := by rw [hWw, hP1, hP2]; ring
  have eP1re : P1.re = M1 - 1 := by
    rw [hP1, hM1]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have eP1im : P1.im = N1 := by
    rw [hP1, hN1]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have eP2re : P2.re = M2 - 1 := by
    rw [hP2, hM2]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have eP2im : P2.im = N2 := by
    rw [hP2, hN2]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hV : Uu.im = (S12 * S23 * S34 * S41) * ((M1 - 1) * N2 + N1 * (M2 - 1)) := by
    have eWim : Ww.im = (M1 - 1) * N2 + N1 * (M2 - 1) := by
      rw [hWw12]
      simp only [Complex.mul_im]
      rw [eP1re, eP1im, eP2re, eP2im]
    rw [eProd]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [eWim]
    ring
  have hU : Uu.re = (S12 * S23 * S34 * S41) * ((M1 - 1) * (M2 - 1) - N1 * N2) := by
    have eWre : Ww.re = (M1 - 1) * (M2 - 1) - N1 * N2 := by
      rw [hWw12]
      simp only [Complex.mul_re]
      rw [eP1re, eP1im, eP2re, eP2im]
    rw [eProd]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [eWre]
    ring
  have hSprod : 0 < S12 * S23 * S34 * S41 :=
    mul_pos (mul_pos (mul_pos hS12pos hS23pos) hS34pos) hS41pos
  have hV0 : (M1 - 1) * N2 + N1 * (M2 - 1) = 0 := by
    have hUU : Uu.im = 0 := by
      have h2 := hwim
      rw [hC1] at h2
      simpa using h2
    rw [hV] at hUU
    exact (mul_eq_zero.mp hUU).resolve_left (ne_of_gt hSprod)
  have hm12pos : 0 < m12 := div_pos hA12 hS12pos
  have hm23pos : 0 < m23 := div_pos hA23 hS23pos
  have hm34pos : 0 < m34 := div_pos hA34 hS34pos
  have hm41pos : 0 < m41 := div_pos hA41 hS41pos
  have hN1 : 0 < N1 := by rw [hN1]; linarith
  have hN2 : 0 < N2 := by rw [hN2]; linarith
  have hK2 : (N1 * N2 - (M1 - 1) * (M2 - 1)) * N2
      = N1 * (N2 ^ 2 + (M2 - 1) ^ 2) := by
    linear_combination -(M2 - 1) * hV0
  have hKpos : 0 < N1 * N2 - (M1 - 1) * (M2 - 1) := by
    have h1 : 0 < (N1 * N2 - (M1 - 1) * (M2 - 1)) * N2 := by
      rw [hK2]
      exact mul_pos hN1 (by positivity)
    exact (mul_pos_iff_of_pos_right hN2).mp h1
  have hwre : w.re = (S12 * S23 * S34 * S41) * (N1 * N2 - (M1 - 1) * (M2 - 1)) := by
    rw [hC1]
    simp only [Complex.neg_re]
    rw [hU]
    ring
  have hwpos : 0 < w.re := by
    rw [hwre]
    exact mul_pos hSprod hKpos
  have hwR : w = ((w.re : ℝ) : ℂ) := by
    have h := Complex.re_add_im w
    rw [hwim] at h
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.symm
  have hPQc : P * (starRingEnd ℂ) Q = (starRingEnd ℂ) w := by
    rw [hw, map_mul, starRingEnd_self_apply]
  have e1 : Complex.normSq (P + Q)
      = Complex.normSq P + Complex.normSq Q + 2 * w.re := by
    rw [Complex.normSq_add, hPQc, Complex.conj_re]
  have e2 : ‖P‖ * ‖Q‖ = w.re := by
    have hnn : 0 ≤ ‖P‖ * ‖Q‖ := by positivity
    have h2 : (‖P‖ * ‖Q‖) ^ 2 = w.re ^ 2 := by
      have g1 : (‖P‖ * ‖Q‖) ^ 2 = Complex.normSq P * Complex.normSq Q := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; ring
      have g2 : Complex.normSq P * Complex.normSq Q = Complex.normSq w := by
        rw [hw, Complex.normSq_mul, Complex.normSq_conj]
      have g3 : Complex.normSq w = w.re ^ 2 := by
        conv_lhs => rw [hwR, Complex.normSq_ofReal]
        ring
      rw [g1, g2]; exact g3
    exact (sq_eq_sq₀ hnn (le_of_lt hwpos)).mp h2
  have hsq : ‖P + Q‖ ^ 2 = (‖P‖ + ‖Q‖) ^ 2 := by
    have e3 : (‖P‖ + ‖Q‖) ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 + 2 * w.re := by
      rw [add_sq]
      linear_combination 2 * e2
    have e1' : ‖P + Q‖ ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 + 2 * w.re := by
      simp only [← Complex.normSq_eq_norm_sq]
      exact e1
    linear_combination e1' - e3
  have hPtol : ‖P‖ + ‖Q‖ = ‖Rr‖ := by
    have h2 : (‖P‖ + ‖Q‖) ^ 2 = ‖Rr‖ ^ 2 := by rw [← hsq, hPQR]
    exact (sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp h2
  rw [hP, hQ, hRr, norm_mul, norm_mul, norm_mul] at hPtol
  exact hPtol

set_option linter.unusedVariables false in
/-- **Casey's theorem.** In the Euclidean plane, let a circle have center $O$ and radius $R > 0$,
and let four circles have centers $c_1, c_2, c_3, c_4$ and radii $r_1, r_2, r_3, r_4$ with
$0 < r_i < R$ and $|c_i O| + r_i = R$ for each $i$, so that each is internally tangent to the
outer circle. Assume that the four circles lie outside each other, $r_i + r_j < |c_i c_j|$ for
all $i \ne j$, and that they appear counterclockwise around $O$ with every consecutive angular
gap less than $\pi$: writing $u \times v = u_1 v_2 - u_2 v_1$ for vectors $u = (u_1, u_2)$ and
$v = (v_1, v_2)$ of the plane, $(c_i - O) \times (c_j - O) > 0$ for
$(i, j) = (1, 2), (2, 3), (3, 4), (4, 1)$. For the pairs $ij = 12, 23, 34, 41, 13, 24$ let
$t_{ij} > 0$ satisfy $t_{ij}^2 = |c_i c_j|^2 - (r_i - r_j)^2$, the length of an exterior common
tangent of the circles $i$ and $j$. Then $t_{12} t_{34} + t_{23} t_{41} = t_{13} t_{24}$.

Configurations with a consecutive angular gap of at least $\pi$ are not covered here; they are
covered by the cyclic-order form of Casey's theorem.

Proves `Wanted` entry `casey_theorem`.

Source: https://en.wikipedia.org/wiki/Casey%27s_theorem.
-/
theorem casey_theorem {O c1 c2 c3 c4 : EuclideanSpace ℝ (Fin 2)}
    {R r1 r2 r3 r4 t12 t23 t34 t41 t13 t24 : ℝ}
    (hR : 0 < R)
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hr3 : 0 < r3) (hr4 : 0 < r4)
    (hlt1 : r1 < R) (hlt2 : r2 < R) (hlt3 : r3 < R) (hlt4 : r4 < R)
    (hinner1 : dist c1 O + r1 = R)
    (hinner2 : dist c2 O + r2 = R)
    (hinner3 : dist c3 O + r3 = R)
    (hinner4 : dist c4 O + r4 = R)
    (hdisj12 : r1 + r2 < dist c1 c2)
    (hdisj23 : r2 + r3 < dist c2 c3)
    (hdisj34 : r3 + r4 < dist c3 c4)
    (hdisj41 : r4 + r1 < dist c4 c1)
    (hdisj13 : r1 + r3 < dist c1 c3)
    (hdisj24 : r2 + r4 < dist c2 c4)
    (ht12 : t12 ^ 2 = dist c1 c2 ^ 2 - (r1 - r2) ^ 2)
    (ht23 : t23 ^ 2 = dist c2 c3 ^ 2 - (r2 - r3) ^ 2)
    (ht34 : t34 ^ 2 = dist c3 c4 ^ 2 - (r3 - r4) ^ 2)
    (ht41 : t41 ^ 2 = dist c4 c1 ^ 2 - (r4 - r1) ^ 2)
    (ht13 : t13 ^ 2 = dist c1 c3 ^ 2 - (r1 - r3) ^ 2)
    (ht24 : t24 ^ 2 = dist c2 c4 ^ 2 - (r2 - r4) ^ 2)
    (ht12pos : 0 < t12) (ht23pos : 0 < t23) (ht34pos : 0 < t34)
    (ht41pos : 0 < t41) (ht13pos : 0 < t13) (ht24pos : 0 < t24)
    (hcyc12 : 0 < ((c1 - O).ofLp 0 * (c2 - O).ofLp 1 - (c1 - O).ofLp 1 * (c2 - O).ofLp 0))
    (hcyc23 : 0 < ((c2 - O).ofLp 0 * (c3 - O).ofLp 1 - (c2 - O).ofLp 1 * (c3 - O).ofLp 0))
    (hcyc34 : 0 < ((c3 - O).ofLp 0 * (c4 - O).ofLp 1 - (c3 - O).ofLp 1 * (c4 - O).ofLp 0))
    (hcyc41 : 0 < ((c4 - O).ofLp 0 * (c1 - O).ofLp 1 - (c4 - O).ofLp 1 * (c1 - O).ofLp 0))
    : t12 * t34 + t23 * t41 = t13 * t24 := by
  -- reduced radii `di = R - ri`, the distances from `O` to the small centers
  set d1 : ℝ := R - r1 with hd1
  set d2 : ℝ := R - r2 with hd2
  set d3 : ℝ := R - r3 with hd3
  set d4 : ℝ := R - r4 with hd4
  have hdi1 : 0 < d1 := by rw [hd1]; linarith
  have hdi2 : 0 < d2 := by rw [hd2]; linarith
  have hdi3 : 0 < d3 := by rw [hd3]; linarith
  have hdi4 : 0 < d4 := by rw [hd4]; linarith
  -- centered vectors `ui = ci - O`
  set u1 : EuclideanSpace ℝ (Fin 2) := c1 - O with hu1
  set u2 : EuclideanSpace ℝ (Fin 2) := c2 - O with hu2
  set u3 : EuclideanSpace ℝ (Fin 2) := c3 - O with hu3
  set u4 : EuclideanSpace ℝ (Fin 2) := c4 - O with hu4
  have hn1 : ‖u1‖ = d1 := by
    have hdist : dist c1 O = ‖u1‖ := by rw [hu1, dist_eq_norm]
    rw [hd1]; linarith [hinner1, hdist]
  have hn2 : ‖u2‖ = d2 := by
    have hdist : dist c2 O = ‖u2‖ := by rw [hu2, dist_eq_norm]
    rw [hd2]; linarith [hinner2, hdist]
  have hn3 : ‖u3‖ = d3 := by
    have hdist : dist c3 O = ‖u3‖ := by rw [hu3, dist_eq_norm]
    rw [hd3]; linarith [hinner3, hdist]
  have hn4 : ‖u4‖ = d4 := by
    have hdist : dist c4 O = ‖u4‖ := by rw [hu4, dist_eq_norm]
    rw [hd4]; linarith [hinner4, hdist]
  -- unit vectors `vi = ui / di`
  set v1 : EuclideanSpace ℝ (Fin 2) := d1⁻¹ • u1 with hv1
  set v2 : EuclideanSpace ℝ (Fin 2) := d2⁻¹ • u2 with hv2
  set v3 : EuclideanSpace ℝ (Fin 2) := d3⁻¹ • u3 with hv3
  set v4 : EuclideanSpace ℝ (Fin 2) := d4⁻¹ • u4 with hv4
  have hv1n : ‖v1‖ = 1 := by
    rw [hv1, norm_smul, hn1, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdi1),
      inv_mul_cancel₀ (ne_of_gt hdi1)]
  have hv2n : ‖v2‖ = 1 := by
    rw [hv2, norm_smul, hn2, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdi2),
      inv_mul_cancel₀ (ne_of_gt hdi2)]
  have hv3n : ‖v3‖ = 1 := by
    rw [hv3, norm_smul, hn3, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdi3),
      inv_mul_cancel₀ (ne_of_gt hdi3)]
  have hv4n : ‖v4‖ = 1 := by
    rw [hv4, norm_smul, hn4, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdi4),
      inv_mul_cancel₀ (ne_of_gt hdi4)]
  have hu1v : u1 = d1 • v1 := by rw [hv1, smul_inv_smul₀ (ne_of_gt hdi1)]
  have hu2v : u2 = d2 • v2 := by rw [hv2, smul_inv_smul₀ (ne_of_gt hdi2)]
  have hu3v : u3 = d3 • v3 := by rw [hv3, smul_inv_smul₀ (ne_of_gt hdi3)]
  have hu4v : u4 = d4 • v4 := by rw [hv4, smul_inv_smul₀ (ne_of_gt hdi4)]
  -- coordinates
  set X1 : ℝ := v1 0 with hX1
  set Y1 : ℝ := v1 1 with hY1
  set X2 : ℝ := v2 0 with hX2
  set Y2 : ℝ := v2 1 with hY2
  set X3 : ℝ := v3 0 with hX3
  set Y3 : ℝ := v3 1 with hY3
  set X4 : ℝ := v4 0 with hX4
  set Y4 : ℝ := v4 1 with hY4
  have hXY1 : X1 ^ 2 + Y1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v1
    rw [Fin.sum_univ_two, hv1n, one_pow] at h
    rw [hX1, hY1]
    exact h.symm
  have hXY2 : X2 ^ 2 + Y2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v2
    rw [Fin.sum_univ_two, hv2n, one_pow] at h
    rw [hX2, hY2]
    exact h.symm
  have hXY3 : X3 ^ 2 + Y3 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v3
    rw [Fin.sum_univ_two, hv3n, one_pow] at h
    rw [hX3, hY3]
    exact h.symm
  have hXY4 : X4 ^ 2 + Y4 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq v4
    rw [Fin.sum_univ_two, hv4n, one_pow] at h
    rw [hX4, hY4]
    exact h.symm
  -- dots of unit vectors
  have hD12 : @inner ℝ _ _ v1 v2 = X1 * X2 + Y1 * Y2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, Fin.sum_univ_two, ← hX1, ← hY1,
      ← hX2, ← hY2]
    ring
  have hD23 : @inner ℝ _ _ v2 v3 = X2 * X3 + Y2 * Y3 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, Fin.sum_univ_two, ← hX2, ← hY2,
      ← hX3, ← hY3]
    ring
  have hD34 : @inner ℝ _ _ v3 v4 = X3 * X4 + Y3 * Y4 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, Fin.sum_univ_two, ← hX3, ← hY3,
      ← hX4, ← hY4]
    ring
  have hD41 : @inner ℝ _ _ v4 v1 = X4 * X1 + Y4 * Y1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, Fin.sum_univ_two, ← hX4, ← hY4,
      ← hX1, ← hY1]
    ring
  have hD13 : @inner ℝ _ _ v1 v3 = X1 * X3 + Y1 * Y3 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, Fin.sum_univ_two, ← hX1, ← hY1,
      ← hX3, ← hY3]
    ring
  have hD24 : @inner ℝ _ _ v2 v4 = X2 * X4 + Y2 * Y4 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, Fin.sum_univ_two, ← hX2, ← hY2,
      ← hX4, ← hY4]
    ring
  -- coordinates of `ui` in terms of `di` and unit coordinates
  have eX1 : u1.ofLp 0 = d1 * X1 := by
    simp only [hu1v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hX1]
  have eY1 : u1.ofLp 1 = d1 * Y1 := by
    simp only [hu1v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hY1]
  have eX2 : u2.ofLp 0 = d2 * X2 := by
    simp only [hu2v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hX2]
  have eY2 : u2.ofLp 1 = d2 * Y2 := by
    simp only [hu2v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hY2]
  have eX3 : u3.ofLp 0 = d3 * X3 := by
    simp only [hu3v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hX3]
  have eY3 : u3.ofLp 1 = d3 * Y3 := by
    simp only [hu3v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hY3]
  have eX4 : u4.ofLp 0 = d4 * X4 := by
    simp only [hu4v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hX4]
  have eY4 : u4.ofLp 1 = d4 * Y4 := by
    simp only [hu4v, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← hY4]
  -- crosses of unit vectors are positive
  have hS12 : 0 < X1 * Y2 - Y1 * X2 := by
    have e : u1.ofLp 0 * u2.ofLp 1 - u1.ofLp 1 * u2.ofLp 0
        = d1 * d2 * (X1 * Y2 - Y1 * X2) := by
      rw [eX1, eY1, eX2, eY2]; ring
    rw [e] at hcyc12
    by_contra h
    push Not at h
    have hle : d1 * d2 * (X1 * Y2 - Y1 * X2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos hdi1 hdi2)) h
    linarith
  have hS23 : 0 < X2 * Y3 - Y2 * X3 := by
    have e : u2.ofLp 0 * u3.ofLp 1 - u2.ofLp 1 * u3.ofLp 0
        = d2 * d3 * (X2 * Y3 - Y2 * X3) := by
      rw [eX2, eY2, eX3, eY3]; ring
    rw [e] at hcyc23
    by_contra h
    push Not at h
    have hle : d2 * d3 * (X2 * Y3 - Y2 * X3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos hdi2 hdi3)) h
    linarith
  have hS34 : 0 < X3 * Y4 - Y3 * X4 := by
    have e : u3.ofLp 0 * u4.ofLp 1 - u3.ofLp 1 * u4.ofLp 0
        = d3 * d4 * (X3 * Y4 - Y3 * X4) := by
      rw [eX3, eY3, eX4, eY4]; ring
    rw [e] at hcyc34
    by_contra h
    push Not at h
    have hle : d3 * d4 * (X3 * Y4 - Y3 * X4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos hdi3 hdi4)) h
    linarith
  have hS41 : 0 < X4 * Y1 - Y4 * X1 := by
    have e : u4.ofLp 0 * u1.ofLp 1 - u4.ofLp 1 * u1.ofLp 0
        = d4 * d1 * (X4 * Y1 - Y4 * X1) := by
      rw [eX4, eY4, eX1, eY1]; ring
    rw [e] at hcyc41
    by_contra h
    push Not at h
    have hle : d4 * d1 * (X4 * Y1 - Y4 * X1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos hdi4 hdi1)) h
    linarith
  -- tangent lengths squared via unit dots
  have ht12' : t12 ^ 2 = 2 * d1 * d2 * (1 - (X1 * X2 + Y1 * Y2)) := by
    have e1 : dist c1 c2 = ‖u1 - u2‖ := by
      rw [dist_eq_norm, hu1, hu2]; congr 1; abel
    have e2 : ‖u1 - u2‖ ^ 2
        = ‖u1‖ ^ 2 + ‖u2‖ ^ 2 - 2 * @inner ℝ _ _ u1 u2 := by
      rw [norm_sub_sq_real u1 u2]; ring
    have e3 : @inner ℝ _ _ u1 u2 = d1 * d2 * (X1 * X2 + Y1 * Y2) := by
      rw [hu1v, hu2v, real_inner_smul_left, real_inner_smul_right, hD12]; ring
    rw [ht12, e1, e2, hn1, hn2, e3, hd1, hd2]
    ring
  have ht23' : t23 ^ 2 = 2 * d2 * d3 * (1 - (X2 * X3 + Y2 * Y3)) := by
    have e1 : dist c2 c3 = ‖u2 - u3‖ := by
      rw [dist_eq_norm, hu2, hu3]; congr 1; abel
    have e2 : ‖u2 - u3‖ ^ 2
        = ‖u2‖ ^ 2 + ‖u3‖ ^ 2 - 2 * @inner ℝ _ _ u2 u3 := by
      rw [norm_sub_sq_real u2 u3]; ring
    have e3 : @inner ℝ _ _ u2 u3 = d2 * d3 * (X2 * X3 + Y2 * Y3) := by
      rw [hu2v, hu3v, real_inner_smul_left, real_inner_smul_right, hD23]; ring
    rw [ht23, e1, e2, hn2, hn3, e3, hd2, hd3]
    ring
  have ht34' : t34 ^ 2 = 2 * d3 * d4 * (1 - (X3 * X4 + Y3 * Y4)) := by
    have e1 : dist c3 c4 = ‖u3 - u4‖ := by
      rw [dist_eq_norm, hu3, hu4]; congr 1; abel
    have e2 : ‖u3 - u4‖ ^ 2
        = ‖u3‖ ^ 2 + ‖u4‖ ^ 2 - 2 * @inner ℝ _ _ u3 u4 := by
      rw [norm_sub_sq_real u3 u4]; ring
    have e3 : @inner ℝ _ _ u3 u4 = d3 * d4 * (X3 * X4 + Y3 * Y4) := by
      rw [hu3v, hu4v, real_inner_smul_left, real_inner_smul_right, hD34]; ring
    rw [ht34, e1, e2, hn3, hn4, e3, hd3, hd4]
    ring
  have ht41' : t41 ^ 2 = 2 * d4 * d1 * (1 - (X4 * X1 + Y4 * Y1)) := by
    have e1 : dist c4 c1 = ‖u4 - u1‖ := by
      rw [dist_eq_norm, hu4, hu1]; congr 1; abel
    have e2 : ‖u4 - u1‖ ^ 2
        = ‖u4‖ ^ 2 + ‖u1‖ ^ 2 - 2 * @inner ℝ _ _ u4 u1 := by
      rw [norm_sub_sq_real u4 u1]; ring
    have e3 : @inner ℝ _ _ u4 u1 = d4 * d1 * (X4 * X1 + Y4 * Y1) := by
      rw [hu4v, hu1v, real_inner_smul_left, real_inner_smul_right, hD41]; ring
    rw [ht41, e1, e2, hn4, hn1, e3, hd4, hd1]
    ring
  have ht13' : t13 ^ 2 = 2 * d1 * d3 * (1 - (X1 * X3 + Y1 * Y3)) := by
    have e1 : dist c1 c3 = ‖u1 - u3‖ := by
      rw [dist_eq_norm, hu1, hu3]; congr 1; abel
    have e2 : ‖u1 - u3‖ ^ 2
        = ‖u1‖ ^ 2 + ‖u3‖ ^ 2 - 2 * @inner ℝ _ _ u1 u3 := by
      rw [norm_sub_sq_real u1 u3]; ring
    have e3 : @inner ℝ _ _ u1 u3 = d1 * d3 * (X1 * X3 + Y1 * Y3) := by
      rw [hu1v, hu3v, real_inner_smul_left, real_inner_smul_right, hD13]; ring
    rw [ht13, e1, e2, hn1, hn3, e3, hd1, hd3]
    ring
  have ht24' : t24 ^ 2 = 2 * d2 * d4 * (1 - (X2 * X4 + Y2 * Y4)) := by
    have e1 : dist c2 c4 = ‖u2 - u4‖ := by
      rw [dist_eq_norm, hu2, hu4]; congr 1; abel
    have e2 : ‖u2 - u4‖ ^ 2
        = ‖u2‖ ^ 2 + ‖u4‖ ^ 2 - 2 * @inner ℝ _ _ u2 u4 := by
      rw [norm_sub_sq_real u2 u4]; ring
    have e3 : @inner ℝ _ _ u2 u4 = d2 * d4 * (X2 * X4 + Y2 * Y4) := by
      rw [hu2v, hu4v, real_inner_smul_left, real_inner_smul_right, hD24]; ring
    rw [ht24, e1, e2, hn2, hn4, e3, hd2, hd4]
    ring
  -- the `1 - dot` factors are positive
  have hA12 : 0 < 1 - (X1 * X2 + Y1 * Y2) := by
    by_contra h
    push Not at h
    have hdd : (0:ℝ) < 2 * d1 * d2 := mul_pos (mul_pos two_pos hdi1) hdi2
    have hle : 2 * d1 * d2 * (1 - (X1 * X2 + Y1 * Y2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdd) h
    rw [← ht12'] at hle
    have hpos : 0 < t12 ^ 2 := pow_pos ht12pos 2
    linarith
  have hA23 : 0 < 1 - (X2 * X3 + Y2 * Y3) := by
    by_contra h
    push Not at h
    have hdd : (0:ℝ) < 2 * d2 * d3 := mul_pos (mul_pos two_pos hdi2) hdi3
    have hle : 2 * d2 * d3 * (1 - (X2 * X3 + Y2 * Y3)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdd) h
    rw [← ht23'] at hle
    have hpos : 0 < t23 ^ 2 := pow_pos ht23pos 2
    linarith
  have hA34 : 0 < 1 - (X3 * X4 + Y3 * Y4) := by
    by_contra h
    push Not at h
    have hdd : (0:ℝ) < 2 * d3 * d4 := mul_pos (mul_pos two_pos hdi3) hdi4
    have hle : 2 * d3 * d4 * (1 - (X3 * X4 + Y3 * Y4)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdd) h
    rw [← ht34'] at hle
    have hpos : 0 < t34 ^ 2 := pow_pos ht34pos 2
    linarith
  have hA41 : 0 < 1 - (X4 * X1 + Y4 * Y1) := by
    by_contra h
    push Not at h
    have hdd : (0:ℝ) < 2 * d4 * d1 := mul_pos (mul_pos two_pos hdi4) hdi1
    have hle : 2 * d4 * d1 * (1 - (X4 * X1 + Y4 * Y1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdd) h
    rw [← ht41'] at hle
    have hpos : 0 < t41 ^ 2 := pow_pos ht41pos 2
    linarith
  -- unit complex numbers from unit coordinates
  set z1 : ℂ := ⟨X1, Y1⟩ with hz1
  set z2 : ℂ := ⟨X2, Y2⟩ with hz2
  set z3 : ℂ := ⟨X3, Y3⟩ with hz3
  set z4 : ℂ := ⟨X4, Y4⟩ with hz4
  have hz1n : Complex.normSq z1 = 1 := by
    rw [hz1]
    simp only [Complex.normSq_apply]
    linear_combination hXY1
  have hz2n : Complex.normSq z2 = 1 := by
    rw [hz2]
    simp only [Complex.normSq_apply]
    linear_combination hXY2
  have hz3n : Complex.normSq z3 = 1 := by
    rw [hz3]
    simp only [Complex.normSq_apply]
    linear_combination hXY3
  have hz4n : Complex.normSq z4 = 1 := by
    rw [hz4]
    simp only [Complex.normSq_apply]
    linear_combination hXY4
  have hDz12 : ((starRingEnd ℂ) z1 * z2).re = X1 * X2 + Y1 * Y2 := by
    rw [hz1, hz2]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hDz23 : ((starRingEnd ℂ) z2 * z3).re = X2 * X3 + Y2 * Y3 := by
    rw [hz2, hz3]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hDz34 : ((starRingEnd ℂ) z3 * z4).re = X3 * X4 + Y3 * Y4 := by
    rw [hz3, hz4]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hDz41 : ((starRingEnd ℂ) z4 * z1).re = X4 * X1 + Y4 * Y1 := by
    rw [hz4, hz1]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hSz12 : ((starRingEnd ℂ) z1 * z2).im = X1 * Y2 - Y1 * X2 := by
    rw [hz1, hz2]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hSz23 : ((starRingEnd ℂ) z2 * z3).im = X2 * Y3 - Y2 * X3 := by
    rw [hz2, hz3]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hSz34 : ((starRingEnd ℂ) z3 * z4).im = X3 * Y4 - Y3 * X4 := by
    rw [hz3, hz4]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hSz41 : ((starRingEnd ℂ) z4 * z1).im = X4 * Y1 - Y4 * X1 := by
    rw [hz4, hz1]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  -- tangent lengths via chord lengths
  have ht12z : t12 = Real.sqrt (d1 * d2) * ‖z1 - z2‖ := by
    have hnn : 0 ≤ Real.sqrt (d1 * d2) * ‖z1 - z2‖ := by positivity
    have hdd : (0:ℝ) ≤ d1 * d2 := le_of_lt (mul_pos hdi1 hdi2)
    have hc : Complex.normSq (z1 - z2) = 2 * (1 - (X1 * X2 + Y1 * Y2)) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz1, hz2]
      linear_combination hXY1 + hXY2
    have h2 : t12 ^ 2 = (Real.sqrt (d1 * d2) * ‖z1 - z2‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdd, ← Complex.normSq_eq_norm_sq, ht12', hc]
      ring
    exact (sq_eq_sq₀ (le_of_lt ht12pos) hnn).mp h2
  have ht23z : t23 = Real.sqrt (d2 * d3) * ‖z2 - z3‖ := by
    have hnn : 0 ≤ Real.sqrt (d2 * d3) * ‖z2 - z3‖ := by positivity
    have hdd : (0:ℝ) ≤ d2 * d3 := le_of_lt (mul_pos hdi2 hdi3)
    have hc : Complex.normSq (z2 - z3) = 2 * (1 - (X2 * X3 + Y2 * Y3)) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz2, hz3]
      linear_combination hXY2 + hXY3
    have h2 : t23 ^ 2 = (Real.sqrt (d2 * d3) * ‖z2 - z3‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdd, ← Complex.normSq_eq_norm_sq, ht23', hc]
      ring
    exact (sq_eq_sq₀ (le_of_lt ht23pos) hnn).mp h2
  have ht34z : t34 = Real.sqrt (d3 * d4) * ‖z3 - z4‖ := by
    have hnn : 0 ≤ Real.sqrt (d3 * d4) * ‖z3 - z4‖ := by positivity
    have hdd : (0:ℝ) ≤ d3 * d4 := le_of_lt (mul_pos hdi3 hdi4)
    have hc : Complex.normSq (z3 - z4) = 2 * (1 - (X3 * X4 + Y3 * Y4)) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz3, hz4]
      linear_combination hXY3 + hXY4
    have h2 : t34 ^ 2 = (Real.sqrt (d3 * d4) * ‖z3 - z4‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdd, ← Complex.normSq_eq_norm_sq, ht34', hc]
      ring
    exact (sq_eq_sq₀ (le_of_lt ht34pos) hnn).mp h2
  have ht41z : t41 = Real.sqrt (d4 * d1) * ‖z1 - z4‖ := by
    have hnn : 0 ≤ Real.sqrt (d4 * d1) * ‖z1 - z4‖ := by positivity
    have hdd : (0:ℝ) ≤ d4 * d1 := le_of_lt (mul_pos hdi4 hdi1)
    have hc : Complex.normSq (z1 - z4) = 2 * (1 - (X4 * X1 + Y4 * Y1)) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz1, hz4]
      linear_combination hXY1 + hXY4
    have h2 : t41 ^ 2 = (Real.sqrt (d4 * d1) * ‖z1 - z4‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdd, ← Complex.normSq_eq_norm_sq, ht41', hc]
      ring
    exact (sq_eq_sq₀ (le_of_lt ht41pos) hnn).mp h2
  have ht13z : t13 = Real.sqrt (d1 * d3) * ‖z1 - z3‖ := by
    have hnn : 0 ≤ Real.sqrt (d1 * d3) * ‖z1 - z3‖ := by positivity
    have hdd : (0:ℝ) ≤ d1 * d3 := le_of_lt (mul_pos hdi1 hdi3)
    have hc : Complex.normSq (z1 - z3) = 2 * (1 - (X1 * X3 + Y1 * Y3)) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz1, hz3]
      linear_combination hXY1 + hXY3
    have h2 : t13 ^ 2 = (Real.sqrt (d1 * d3) * ‖z1 - z3‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdd, ← Complex.normSq_eq_norm_sq, ht13', hc]
      ring
    exact (sq_eq_sq₀ (le_of_lt ht13pos) hnn).mp h2
  have ht24z : t24 = Real.sqrt (d2 * d4) * ‖z2 - z4‖ := by
    have hnn : 0 ≤ Real.sqrt (d2 * d4) * ‖z2 - z4‖ := by positivity
    have hdd : (0:ℝ) ≤ d2 * d4 := le_of_lt (mul_pos hdi2 hdi4)
    have hc : Complex.normSq (z2 - z4) = 2 * (1 - (X2 * X4 + Y2 * Y4)) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz2, hz4]
      linear_combination hXY2 + hXY4
    have h2 : t24 ^ 2 = (Real.sqrt (d2 * d4) * ‖z2 - z4‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hdd, ← Complex.normSq_eq_norm_sq, ht24', hc]
      ring
    exact (sq_eq_sq₀ (le_of_lt ht24pos) hnn).mp h2
  -- apply Ptolemy and conclude
  have hPtol := complex_ptolemy hz1n hz2n hz3n hz4n
    hDz12 hDz23 hDz34 hDz41 hSz12 hSz23 hSz34 hSz41
    hS12 hS23 hS34 hS41 hA12 hA23 hA34 hA41
  have hdd12 : (0:ℝ) ≤ d1 * d2 := le_of_lt (mul_pos hdi1 hdi2)
  have hdd23 : (0:ℝ) ≤ d2 * d3 := le_of_lt (mul_pos hdi2 hdi3)
  have hdd13 : (0:ℝ) ≤ d1 * d3 := le_of_lt (mul_pos hdi1 hdi3)
  have e12 : t12 * t34
      = Real.sqrt (d1 * d2 * d3 * d4) * (‖z1 - z2‖ * ‖z3 - z4‖) := by
    have e : Real.sqrt (d1 * d2) * Real.sqrt (d3 * d4)
        = Real.sqrt (d1 * d2 * d3 * d4) := by
      rw [← Real.sqrt_mul hdd12]
      congr 1
      ring
    rw [ht12z, ht34z]
    linear_combination (‖z1 - z2‖ * ‖z3 - z4‖) * e
  have e23 : t23 * t41
      = Real.sqrt (d1 * d2 * d3 * d4) * (‖z2 - z3‖ * ‖z1 - z4‖) := by
    have e : Real.sqrt (d2 * d3) * Real.sqrt (d4 * d1)
        = Real.sqrt (d1 * d2 * d3 * d4) := by
      rw [← Real.sqrt_mul hdd23]
      congr 1
      ring
    rw [ht23z, ht41z]
    linear_combination (‖z2 - z3‖ * ‖z1 - z4‖) * e
  have e13 : t13 * t24
      = Real.sqrt (d1 * d2 * d3 * d4) * (‖z1 - z3‖ * ‖z2 - z4‖) := by
    have e : Real.sqrt (d1 * d3) * Real.sqrt (d2 * d4)
        = Real.sqrt (d1 * d2 * d3 * d4) := by
      rw [← Real.sqrt_mul hdd13]
      congr 1
      ring
    rw [ht13z, ht24z]
    linear_combination (‖z1 - z3‖ * ‖z2 - z4‖) * e
  rw [e12, e23, e13, ← mul_add, hPtol]

end MetaMathlibExt

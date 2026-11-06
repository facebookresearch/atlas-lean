/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MathlibExt.NumberTheory.PrimeCounting.WeightedHilbert
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Weighted large sieve

The weighted large-sieve inequality obtained from the weighted Hilbert
inequality and the exact finite geometric sum.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace MathlibExt.NumberTheory.PrimeCounting

private noncomputable def btAddChar (t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

private theorem btAddChar_zero : btAddChar 0 = 1 := by
  simp [btAddChar]

private theorem btAddChar_add (u v : ℝ) :
    btAddChar (u + v) = btAddChar u * btAddChar v := by
  rw [btAddChar, btAddChar, btAddChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem btAddChar_neg (u : ℝ) : btAddChar (-u) = (btAddChar u)⁻¹ := by
  rw [btAddChar, btAddChar, show ((2 * Real.pi * -u : ℝ) : ℂ) * Complex.I =
    -(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_neg]

private theorem btAddChar_conj (u : ℝ) : conj (btAddChar u) = btAddChar (-u) := by
  rw [btAddChar, btAddChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem btAddChar_norm (u : ℝ) : ‖btAddChar u‖ = 1 := by
  rw [btAddChar]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * u)

private theorem btAddChar_nat_mul (n : ℕ) (u : ℝ) :
    btAddChar (n * u) = btAddChar u ^ n := by
  rw [btAddChar, btAddChar, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem btAddChar_sub (u v : ℝ) :
    btAddChar (u - v) = btAddChar u * conj (btAddChar v) := by
  rw [sub_eq_add_neg, btAddChar_add, btAddChar_conj]

private theorem btAddChar_sub_one (u : ℝ) :
    btAddChar u - 1 =
      2 * Complex.I * btAddChar (u / 2) * Real.sin (Real.pi * u) := by
  rw [btAddChar, btAddChar, Complex.exp_ofReal_mul_I (2 * Real.pi * u),
    Complex.exp_ofReal_mul_I (2 * Real.pi * (u / 2))]
  rw [show 2 * Real.pi * (u / 2) = Real.pi * u by ring]
  rw [show 2 * Real.pi * u = 2 * (Real.pi * u) by ring]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, mul_zero, add_zero, sub_zero, zero_sub, mul_one]
    norm_num
    rw [← Complex.ofReal_mul]
    simp only [Complex.sin_ofReal_re, Complex.cos_ofReal_im]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * u)]
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_im, mul_zero, add_zero, sub_zero, mul_one]
    norm_num
    rw [← Complex.ofReal_mul]
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    rw [Real.sin_two_mul]
    ring

private theorem btAddChar_ne_one_of_sin_ne {u : ℝ}
    (hu : Real.sin (Real.pi * u) ≠ 0) : btAddChar u ≠ 1 := by
  intro h
  have hzero : btAddChar u - 1 = 0 := by rw [h, sub_self]
  rw [btAddChar_sub_one] at hzero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have he : btAddChar (u / 2) ≠ 0 := by
    unfold btAddChar
    exact Complex.exp_ne_zero _
  have hsin : (Real.sin (Real.pi * u) : ℂ) ≠ 0 := by exact_mod_cast hu
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hI) he) hsin hzero

private theorem btGeomSum (N : ℕ) {u : ℝ}
    (hu : Real.sin (Real.pi * u) ≠ 0) :
    ∑ n ∈ Finset.range N, btAddChar (n * u) =
      Complex.I / 2 *
        (btAddChar (-u / 2) - btAddChar ((N : ℝ) * u - u / 2)) /
          Real.sin (Real.pi * u) := by
  rw [show (∑ n ∈ Finset.range N, btAddChar (n * u)) =
      ∑ n ∈ Finset.range N, btAddChar u ^ n by
    apply Finset.sum_congr rfl
    intro n _
    exact btAddChar_nat_mul n u]
  rw [geom_sum_eq (btAddChar_ne_one_of_sin_ne hu) N]
  have he : btAddChar (u / 2) ≠ 0 := by
    unfold btAddChar
    exact Complex.exp_ne_zero _
  have hsin : (Real.sin (Real.pi * u) : ℂ) ≠ 0 := by exact_mod_cast hu
  have hchar : btAddChar ((N : ℝ) * u) = btAddChar u ^ N := by
    simpa only [Nat.cast_mul] using btAddChar_nat_mul N u
  have hden := btAddChar_sub_one u
  rw [← hchar, hden]
  have hhalf : btAddChar (-(u / 2)) = (btAddChar (u / 2))⁻¹ :=
    btAddChar_neg (u / 2)
  rw [show -u / 2 = -(u / 2) by ring, hhalf]
  have hlast : btAddChar ((N : ℝ) * u - u / 2) =
      btAddChar ((N : ℝ) * u) * (btAddChar (u / 2))⁻¹ := by
    rw [btAddChar_sub, btAddChar_conj, hhalf]
  rw [hlast]
  have hsin' : (Real.sin (u * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sin (u * Real.pi) ≠ 0 by simpa [mul_comm] using hu)
  field_simp [hsin, hsin']
  rw [Complex.I_sq]
  ring

private theorem btSynthesis_expand {ι : Type*} [Fintype ι]
    (N : ℕ) (x : ι → ℝ) (v : ι → ℂ) :
    ((∑ n ∈ Finset.range N,
        ‖∑ r, v r * btAddChar (n * x r)‖ ^ 2 : ℝ) : ℂ) =
      ∑ r, ∑ s, v r * conj (v s) *
        ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s)) := by
  push_cast
  rw [show (∑ r, ∑ s, v r * conj (v s) *
      ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) =
      ∑ n ∈ Finset.range N, ∑ r, ∑ s,
        v r * conj (v s) * btAddChar (n * (x r - x s)) by
    simp_rw [Finset.mul_sum]
    calc
      (∑ r, ∑ s, ∑ n ∈ Finset.range N,
          v r * conj (v s) * btAddChar (n * (x r - x s))) =
          ∑ r, ∑ n ∈ Finset.range N, ∑ s,
            v r * conj (v s) * btAddChar (n * (x r - x s)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = ∑ n ∈ Finset.range N, ∑ r, ∑ s,
          v r * conj (v s) * btAddChar (n * (x r - x s)) := by
        rw [Finset.sum_comm]]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.mul_conj']
  simp only [map_sum, map_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [btAddChar_conj]
  rw [show -(n * x s) = n * (-x s) by ring]
  rw [show n * (x r - x s) = n * x r + n * (-x s) by ring]
  rw [btAddChar_add]
  ring

private theorem btSine_ne_zero_of_circle_separated {ι : Type*}
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖)
    (r s : ι) (hrs : r ≠ s) :
    Real.sin (Real.pi * (x r - x s)) ≠ 0 := by
  have hnorm : 0 < ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ :=
    (hδ r).trans_le (hsep r s hrs)
  have hcircle : ((x r - x s : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
    simpa only [norm_pos_iff] using hnorm
  intro hsin
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hn' : (n : ℝ) = x r - x s := by
    nlinarith [Real.pi_pos]
  apply hcircle
  rw [← hn']
  simp

private theorem btPhase_pair {ι : Type*} (x : ι → ℝ) (v : ι → ℂ)
    (c : ℝ) (r s : ι) :
    (v r * btAddChar (c * x r)) * conj (v s * btAddChar (c * x s)) =
      v r * conj (v s) * btAddChar (c * (x r - x s)) := by
  rw [map_mul, btAddChar_conj]
  rw [show -(c * x s) = c * (-x s) by ring]
  calc
    v r * btAddChar (c * x r) * (conj (v s) * btAddChar (c * -x s)) =
        v r * conj (v s) *
          (btAddChar (c * x r) * btAddChar (c * -x s)) := by ring
    _ = v r * conj (v s) * btAddChar (c * x r + c * -x s) := by
      rw [btAddChar_add]
    _ = v r * conj (v s) * btAddChar (c * (x r - x s)) := by
      congr 3
      ring

private theorem btCross_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (x δ : ι → ℝ) (v : ι → ℂ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        v r * conj (v s) *
          ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))‖ ≤
      3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by
  let c₀ : ℝ := -1 / 2
  let c₁ : ℝ := N - 1 / 2
  let z₀ : ι → ℂ := fun r => v r * btAddChar (c₀ * x r)
  let z₁ : ι → ℂ := fun r => v r * btAddChar (c₁ * x r)
  let H₀ : ℂ := ∑ r, ∑ s ∈ Finset.univ.erase r,
    z₀ r * conj (z₀ s) / Real.sin (Real.pi * (x r - x s))
  let H₁ : ℂ := ∑ r, ∑ s ∈ Finset.univ.erase r,
    z₁ r * conj (z₁ s) / Real.sin (Real.pi * (x r - x s))
  have hz₀ : ∑ r, ‖z₀ r‖ ^ 2 / δ r = ∑ r, ‖v r‖ ^ 2 / δ r := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [z₀, norm_mul, btAddChar_norm, mul_one]
  have hz₁ : ∑ r, ‖z₁ r‖ ^ 2 / δ r = ∑ r, ‖v r‖ ^ 2 / δ r := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [z₁, norm_mul, btAddChar_norm, mul_one]
  have hH₀ : ‖H₀‖ ≤ 3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by
    simpa only [H₀, hz₀] using weightedHilbertCosecant x δ z₀ hδ hsep
  have hH₁ : ‖H₁‖ ≤ 3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by
    simpa only [H₁, hz₁] using weightedHilbertCosecant x δ z₁ hδ hsep
  have hcross :
      (∑ r, ∑ s ∈ Finset.univ.erase r,
          v r * conj (v s) *
            ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) =
        Complex.I / 2 * (H₀ - H₁) := by
    have hterm (r s : ι) (hrs : s ∈ Finset.univ.erase r) :
        v r * conj (v s) *
            (∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) =
          Complex.I / 2 *
            (z₀ r * conj (z₀ s) / Real.sin (Real.pi * (x r - x s)) -
              z₁ r * conj (z₁ s) / Real.sin (Real.pi * (x r - x s))) := by
      have hrs' : r ≠ s := Ne.symm (Finset.mem_erase.mp hrs).1
      rw [btGeomSum N (btSine_ne_zero_of_circle_separated x δ hδ hsep r s hrs')]
      rw [show -(x r - x s) / 2 = c₀ * (x r - x s) by simp only [c₀]; ring]
      rw [show (N : ℝ) * (x r - x s) - (x r - x s) / 2 =
        c₁ * (x r - x s) by simp only [c₁]; ring]
      simp only [z₀, z₁]
      rw [btPhase_pair x v c₀ r s, btPhase_pair x v c₁ r s]
      push_cast
      ring
    rw [show (∑ r, ∑ s ∈ Finset.univ.erase r,
        v r * conj (v s) *
          ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) =
        ∑ r, ∑ s ∈ Finset.univ.erase r, Complex.I / 2 *
          (z₀ r * conj (z₀ s) / Real.sin (Real.pi * (x r - x s)) -
            z₁ r * conj (z₁ s) / Real.sin (Real.pi * (x r - x s))) by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s hs
      exact hterm r s hs]
    simp only [H₀, H₁]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
  rw [hcross]
  calc
    ‖Complex.I / 2 * (H₀ - H₁)‖ = 1 / 2 * ‖H₀ - H₁‖ := by
      rw [norm_mul, norm_div, Complex.norm_I]
      norm_num
    _ ≤ 1 / 2 * (‖H₀‖ + ‖H₁‖) := by
      gcongr
      exact norm_sub_le H₀ H₁
    _ ≤ 1 / 2 * ((3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r) +
        3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r) := by gcongr
    _ = 3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by ring

private theorem btSynthesis_le {ι : Type*} [Fintype ι]
    (N : ℕ) (x δ : ι → ℝ) (v : ι → ℂ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) :
    ∑ n ∈ Finset.range N, ‖∑ r, v r * btAddChar (n * x r)‖ ^ 2 ≤
      ∑ r, (N + 3 / (2 * δ r)) * ‖v r‖ ^ 2 := by
  classical
  let C : ℂ := ∑ r, ∑ s ∈ Finset.univ.erase r,
    v r * conj (v s) *
      ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))
  have hC : ‖C‖ ≤ 3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by
    simpa only [C] using btCross_sum_le N x δ v hδ hsep
  have hdiag (r : ι) :
      v r * conj (v r) *
          (∑ n ∈ Finset.range N, btAddChar (n * (x r - x r))) =
        ((N : ℝ) * ‖v r‖ ^ 2 : ℝ) := by
    rw [sub_self]
    simp only [mul_zero, btAddChar_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    rw [← Complex.mul_conj']
    ring
  have hfull :
      ((∑ n ∈ Finset.range N,
          ‖∑ r, v r * btAddChar (n * x r)‖ ^ 2 : ℝ) : ℂ) =
        ((N : ℝ) * ∑ r, ‖v r‖ ^ 2 : ℝ) + C := by
    rw [btSynthesis_expand]
    simp only [C]
    calc
      (∑ r, ∑ s, v r * conj (v s) *
          ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) =
          ∑ r, ((∑ s ∈ Finset.univ.erase r,
            v r * conj (v s) *
              ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) +
                v r * conj (v r) *
                  ∑ n ∈ Finset.range N, btAddChar (n * (x r - x r))) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ r)]
      _ = ∑ r, ((∑ s ∈ Finset.univ.erase r,
            v r * conj (v s) *
              ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s))) +
                ((N : ℝ) * ‖v r‖ ^ 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hdiag]
      _ = ((N : ℝ) * ∑ r, ‖v r‖ ^ 2 : ℝ) +
          ∑ r, ∑ s ∈ Finset.univ.erase r,
            v r * conj (v s) *
              ∑ n ∈ Finset.range N, btAddChar (n * (x r - x s)) := by
        push_cast
        simp_rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        ring
  have hdecomp :
      (∑ n ∈ Finset.range N, ‖∑ r, v r * btAddChar (n * x r)‖ ^ 2) =
        (N : ℝ) * ∑ r, ‖v r‖ ^ 2 + C.re := by
    have hre := congrArg Complex.re hfull
    simpa only [Complex.ofReal_re, Complex.add_re] using hre
  rw [hdecomp]
  calc
    (N : ℝ) * ∑ r, ‖v r‖ ^ 2 + C.re ≤
        (N : ℝ) * ∑ r, ‖v r‖ ^ 2 + ‖C‖ := by
      gcongr
      exact Complex.re_le_norm C
    _ ≤ (N : ℝ) * ∑ r, ‖v r‖ ^ 2 +
        3 / 2 * ∑ r, ‖v r‖ ^ 2 / δ r := by gcongr
    _ = ∑ r, (N + 3 / (2 * δ r)) * ‖v r‖ ^ 2 := by
      rw [Finset.mul_sum]
      simp_rw [add_mul, Finset.sum_add_distrib]
      apply congrArg₂ (· + ·) rfl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      field_simp [(hδ r).ne']

/--
**The Montgomery–Vaughan weighted large sieve.** Let $N$ be a natural number, let $a_n$ be complex
numbers, let $\iota$ be a finite index set and for $r \in \iota$ let $x_r$ and $\delta_r > 0$ be
real numbers. Write $\|t\|$ for the distance from a real number $t$ to the nearest integer, and
suppose that $\delta_r \le \|x_r - x_s\|$ for all $r \ne s$. Then
$$
\sum_{r} \left( N + \frac{3}{2 \delta_r} \right)^{-1}
\left| \sum_{n=0}^{N-1} a_n e^{2 \pi i n x_r} \right|^2 \le \sum_{n=0}^{N-1} |a_n|^2.
$$

Source: Montgomery–Vaughan, *The large sieve* (1973), Theorem 1, equations
(1.5)–(1.6) and (2.4), lines 227–321. The proof uses duality, the exact
geometric sum, and `weightedHilbertCosecant`.
-/
public theorem weightedLargeSieve {ι : Type*} [Fintype ι]
    (N : ℕ) (x δ : ι → ℝ) (a : ℕ → ℂ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) :
    ∑ r, (N + 3 / (2 * δ r))⁻¹ *
        ‖∑ n ∈ Finset.range N, a n *
          Complex.exp (((2 * Real.pi * (n * x r) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  classical
  change ∑ r, (N + 3 / (2 * δ r))⁻¹ *
      ‖∑ n ∈ Finset.range N, a n * btAddChar (n * x r)‖ ^ 2 ≤ _
  let D : ι → ℝ := fun r => N + 3 / (2 * δ r)
  let S : ι → ℂ := fun r => ∑ n ∈ Finset.range N, a n * btAddChar (n * x r)
  let w : ι → ℝ := fun r => (D r)⁻¹
  let v : ι → ℂ := fun r => w r * S r
  let T : ℕ → ℂ := fun n => ∑ r, v r * btAddChar (n * (-x r))
  let L : ℝ := ∑ r, w r * ‖S r‖ ^ 2
  let A : ℝ := ∑ n ∈ Finset.range N, ‖a n‖ ^ 2
  let B : ℝ := ∑ n ∈ Finset.range N, ‖T n‖ ^ 2
  have hD (r : ι) : 0 < D r := by
    simp only [D]
    have hthree : 0 < 3 / (2 * δ r) :=
      div_pos (by norm_num) (mul_pos (by norm_num) (hδ r))
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) hthree
  have hw (r : ι) : 0 < w r := by
    exact inv_pos.mpr (hD r)
  have hL0 : 0 ≤ L := by
    simp only [L]
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg (hw r).le (sq_nonneg _)
  have hA0 : 0 ≤ A := by
    simp only [A]
    exact Finset.sum_nonneg fun n _ => sq_nonneg ‖a n‖
  have hsepNeg : ∀ r s, r ≠ s →
      δ r ≤ ‖(((-x r) - (-x s) : ℝ) : AddCircle (1 : ℝ))‖ := by
    intro r s hrs
    have h := hsep r s hrs
    have heq : ((-x r - -x s : ℝ) : AddCircle (1 : ℝ)) =
        -((x r - x s : ℝ) : AddCircle (1 : ℝ)) := by
      congr 1
      ring
    rw [heq, norm_neg]
    exact h
  have hSynth : B ≤ ∑ r, D r * ‖v r‖ ^ 2 := by
    simpa only [B, T, D] using btSynthesis_le N (fun r => -x r) δ v hδ hsepNeg
  have hDv : ∑ r, D r * ‖v r‖ ^ 2 = L := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hw r)]
    have hDne := (hD r).ne'
    simp only [w]
    field_simp
  have hB : B ≤ L := hSynth.trans_eq hDv
  have hconjS (r : ι) :
      (∑ n ∈ Finset.range N, conj (a n) * btAddChar (n * (-x r))) =
        conj (S r) := by
    simp only [S, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [btAddChar_conj]
    rw [show -(n * x r) = n * (-x r) by ring]
  have hdual : (L : ℂ) = ∑ n ∈ Finset.range N, conj (a n) * T n := by
    calc
      (L : ℂ) = ∑ r, (w r : ℂ) * (S r * conj (S r)) := by
        simp only [L]
        push_cast
        apply Finset.sum_congr rfl
        intro r _
        rw [Complex.mul_conj']
      _ = ∑ r, v r * conj (S r) := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [v]
        ring
      _ = ∑ r, ∑ n ∈ Finset.range N,
          conj (a n) * (v r * btAddChar (n * (-x r))) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← hconjS r, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = ∑ n ∈ Finset.range N, conj (a n) * T n := by
        simp only [T]
        calc
          (∑ r, ∑ n ∈ Finset.range N,
              conj (a n) * (v r * btAddChar (n * -x r))) =
              ∑ n ∈ Finset.range N, ∑ r,
                conj (a n) * (v r * btAddChar (n * -x r)) := by
            rw [Finset.sum_comm]
          _ = ∑ n ∈ Finset.range N, conj (a n) *
              ∑ r, v r * btAddChar (n * -x r) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.mul_sum]
  have htriangle : L ≤ ∑ n ∈ Finset.range N, ‖a n‖ * ‖T n‖ := by
    calc
      L = ‖(L : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
      _ = ‖∑ n ∈ Finset.range N, conj (a n) * T n‖ := by rw [← hdual]
      _ ≤ ∑ n ∈ Finset.range N, ‖conj (a n) * T n‖ :=
        norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖a n‖ * ‖T n‖ := by
        apply Finset.sum_congr rfl
        intro n _
        rw [norm_mul, RCLike.norm_conj]
  have htriangle0 : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖ * ‖T n‖ := by
    positivity
  have hsq : L ^ 2 ≤ A * B := by
    calc
      L ^ 2 ≤ (∑ n ∈ Finset.range N, ‖a n‖ * ‖T n‖) ^ 2 :=
        pow_le_pow_left₀ hL0 htriangle 2
      _ ≤ (∑ n ∈ Finset.range N, ‖a n‖ ^ 2) *
          ∑ n ∈ Finset.range N, ‖T n‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) _ _
      _ = A * B := by rfl
  have hsq' : L ^ 2 ≤ A * L := hsq.trans (mul_le_mul_of_nonneg_left hB hA0)
  have hLA : L ≤ A := by
    by_cases hLzero : L = 0
    · rw [hLzero]
      exact hA0
    · have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLzero)
      nlinarith
  simpa only [L, w, D, S, A] using hLA

end MathlibExt.NumberTheory.PrimeCounting

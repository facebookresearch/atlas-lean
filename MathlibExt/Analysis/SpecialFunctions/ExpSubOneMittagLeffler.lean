/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeries

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# Mittag-Leffler expansion of the Bose-Einstein kernel
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators
open Complex

noncomputable section

/-- **Mittag-Leffler expansion of $1/(e^u - 1)$.** For every real number $u \neq 0$,
$$
\frac{1}{e^u - 1} = \frac{1}{u} - \frac{1}{2} + \sum_{m=1}^{\infty} \frac{2u}{u^2 + 4\pi^2 m^2}.
$$
-/
theorem one_div_exp_sub_one_eq_tsum (u : ℝ) (hu : u ≠ 0) :
    1 / (Real.exp u - 1) = 1 / u - 1 / 2 +
      ∑' m : ℕ, 2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) := by
  let z : ℂ := Complex.I * (u : ℂ) / (2 * (Real.pi : ℂ))
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz_im : z.im = u / (2 * Real.pi) := by
    dsimp [z]
    simp [Complex.div_im]
    field_simp [Real.pi_ne_zero]
  have hz : z ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨k, hk⟩
    have him := congr_arg Complex.im hk
    rw [hz_im] at him
    norm_num at him
    rcases div_eq_zero_iff.mp him.symm with hu0 | hpi0
    · exact hu hu0
    · exact Real.pi_ne_zero ((mul_eq_zero.mp hpi0).resolve_left (by norm_num))
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) =
      (Real.exp (-u) : ℝ) := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [z]
    field_simp [hpi]
    ring_nf
    simp
  have hq : Real.exp (-u) ≠ 1 := by
    simpa [Real.exp_eq_one_iff] using hu
  have hscaled := congr_arg (fun w : ℂ => Complex.I / (2 * (Real.pi : ℂ)) * w)
    (cot_series_rep' hz)
  rw [← tsum_mul_left] at hscaled
  have hleft :
      Complex.I / (2 * (Real.pi : ℂ)) *
          ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z) =
        ((1 / (Real.exp u - 1) + 1 / 2 - 1 / u : ℝ) : ℂ) := by
    rw [Complex.cot_pi_eq_exp_ratio, hexp]
    rw [Real.exp_neg]
    push_cast
    have heu : Real.exp u ≠ 0 := Real.exp_ne_zero u
    rw [← Complex.ofReal_exp]
    have hdenR : (1 : ℝ) - (Real.exp u)⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      intro he
      apply hq
      rw [Real.exp_neg, he]
    have hden : (1 : ℂ) - (Real.exp u : ℂ)⁻¹ ≠ 0 := by
      exact_mod_cast hdenR
    have hEuR : Real.exp u - 1 ≠ 0 := by
      rw [sub_ne_zero]
      exact (Real.exp_eq_one_iff u).not.mpr hu
    have hEu : (Real.exp u : ℂ) - 1 ≠ 0 := by
      exact_mod_cast hEuR
    dsimp [z]
    field_simp [hpi, Complex.I_ne_zero, Complex.I_mul_I, hu, heu, hden, hEu]
    ring
  have hterm : ∀ m : ℕ,
      Complex.I / (2 * (Real.pi : ℂ)) *
          (1 / (z - ((m : ℂ) + 1)) + 1 / (z + ((m : ℂ) + 1))) =
        ((2 * u / (u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) : ℝ) : ℂ) := by
    intro m
    have hmden : (u : ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := by
      have heq : (u : ℂ) ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * ((m + 1 : ℕ) : ℂ) ^ 2 =
          ((u ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
    have hminus : z - ((m : ℂ) + 1) ≠ 0 := by
      simpa [sub_eq_add_neg] using
        (Complex.integerComplement_add_ne_zero hz (-((m : ℤ) + 1)))
    have hplus : z + ((m : ℂ) + 1) ≠ 0 := by
      simpa using (Complex.integerComplement_add_ne_zero hz ((m : ℤ) + 1))
    field_simp [hpi, hmden, hminus, hplus]
    dsimp [z]
    push_cast
    field_simp [hpi, Complex.I_mul_I]
    have hmden' : (u : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 * ((m : ℂ) + 1) ^ 2 * 4 ≠ 0 := by
      convert hmden using 1
      push_cast
      ring
    rw [eq_div_iff hmden']
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hleft] at hscaled
  simp_rw [hterm] at hscaled
  rw [← Complex.ofReal_tsum] at hscaled
  have hr := Complex.ofReal_inj.mp hscaled
  linarith

private def expSubOnePole (m : ℕ) : ℝ :=
  2 * Real.pi * (m + 1)

private def expSubOneKernelTerm (v : ℝ) (m : ℕ) : ℝ :=
  2 * v / (v ^ 2 + expSubOnePole m ^ 2)

private def expSubOneKernelCoeff (n m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ n / expSubOnePole m ^ (2 * n + 2)

private def expSubOneRemainderTerm (N : ℕ) (v : ℝ) (m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ N * v ^ (2 * N + 1) /
    (expSubOnePole m ^ (2 * N) * (v ^ 2 + expSubOnePole m ^ 2))

private def expSubOneRemainderDerivTerm (N : ℕ) (v : ℝ) (m : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ N / expSubOnePole m ^ (2 * N) *
    (((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / (v ^ 2 + expSubOnePole m ^ 2) -
      2 * v ^ (2 * N + 2) / (v ^ 2 + expSubOnePole m ^ 2) ^ 2)

private def expSubOneRemainder (N : ℕ) (v : ℝ) : ℝ :=
  ∑' m : ℕ, expSubOneRemainderTerm N v m

private def expSubOneBound (N : ℕ) : ℝ :=
  2 * (2 * N + 3 : ℕ) * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹

private lemma expSubOnePole_pos (m : ℕ) : 0 < expSubOnePole m := by
  unfold expSubOnePole
  positivity

private lemma expSubOneBound_nonneg (N : ℕ) : 0 ≤ expSubOneBound N := by
  unfold expSubOneBound
  exact mul_nonneg (by positivity) (tsum_nonneg fun m =>
    inv_nonneg.mpr (pow_nonneg (expSubOnePole_pos m).le _))

private lemma expSubOnePole_inv_pow_summable (q : ℕ) (hq : 2 ≤ q) :
    Summable (fun m : ℕ => (expSubOnePole m ^ q)⁻¹) := by
  have hs : Summable (fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ) ^ q)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega))
  let C : ℝ := ((2 * Real.pi) ^ q)⁻¹
  convert hs.mul_left C using 1
  ext m
  unfold C expSubOnePole
  push_cast
  rw [mul_pow]
  field_simp

private lemma expSubOneRemainderTerm_abs_le (N : ℕ) (v : ℝ) (m : ℕ) :
    |expSubOneRemainderTerm N v m| ≤
      2 * |v| ^ (2 * N + 1) * (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
  have ha := expSubOnePole_pos m
  have hden : 0 < expSubOnePole m ^ (2 * N) * (v ^ 2 + expSubOnePole m ^ 2) := by
    positivity
  have hsmall : expSubOnePole m ^ (2 * N) * expSubOnePole m ^ 2 ≤
      expSubOnePole m ^ (2 * N) * (v ^ 2 + expSubOnePole m ^ 2) := by
    gcongr
    nlinarith [sq_nonneg v]
  have hnum : |2 * (-1 : ℝ) ^ N * v ^ (2 * N + 1)| =
      2 * |v| ^ (2 * N + 1) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow,
      abs_neg, abs_one, one_pow, mul_one, abs_pow]
  unfold expSubOneRemainderTerm
  rw [abs_div, hnum, abs_of_pos hden]
  calc
    2 * |v| ^ (2 * N + 1) /
          (expSubOnePole m ^ (2 * N) * (v ^ 2 + expSubOnePole m ^ 2)) ≤
        2 * |v| ^ (2 * N + 1) /
          (expSubOnePole m ^ (2 * N) * expSubOnePole m ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsmall
    _ = 2 * |v| ^ (2 * N + 1) * (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
      rw [← pow_add]
      ring

private lemma expSubOneRemainderTerm_summable (N : ℕ) (v : ℝ) :
    Summable (expSubOneRemainderTerm N v) := by
  have hw := expSubOnePole_inv_pow_summable (2 * N + 2) (by omega)
  have hmajorant := hw.mul_left (2 * |v| ^ (2 * N + 1))
  exact hmajorant.of_norm_bounded fun m => by
    rw [Real.norm_eq_abs]
    exact expSubOneRemainderTerm_abs_le N v m

private lemma expSubOneRemainderTerm_hasDerivAt (N : ℕ) (v : ℝ) (m : ℕ) :
    HasDerivAt (fun y => expSubOneRemainderTerm N y m)
      (expSubOneRemainderDerivTerm N v m) v := by
  let a := expSubOnePole m
  let C := 2 * (-1 : ℝ) ^ N / a ^ (2 * N)
  have ha : a ≠ 0 := ne_of_gt (expSubOnePole_pos m)
  have hd : v ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hnum : HasDerivAt (fun y : ℝ => C * y ^ (2 * N + 1))
      (C * (((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N))) v := by
    simpa only [show 2 * N + 1 - 1 = 2 * N by omega] using
      (hasDerivAt_pow (2 * N + 1) v).const_mul C
  have hden : HasDerivAt (fun y : ℝ => y ^ 2 + a ^ 2) (2 * v) v := by
    convert (hasDerivAt_pow 2 v).add_const (a ^ 2) using 1
    all_goals ring
  have h := hnum.div hden hd
  have hfun : (fun y : ℝ => C * y ^ (2 * N + 1) / (y ^ 2 + a ^ 2)) =
      (fun y => expSubOneRemainderTerm N y m) := by
    funext y
    unfold C a expSubOneRemainderTerm
    field_simp [ha]
  change HasDerivAt (fun y : ℝ => C * y ^ (2 * N + 1) / (y ^ 2 + a ^ 2)) _ v at h
  rw [hfun] at h
  convert h using 1
  unfold expSubOneRemainderDerivTerm C a
  field_simp [ha, hd]
  ring

private lemma expSubOneRemainderDerivTerm_abs_le (N : ℕ) (v : ℝ) (m : ℕ) :
    |expSubOneRemainderDerivTerm N v m| ≤
      2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N) *
        (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
  let a := expSubOnePole m
  let D := v ^ 2 + a ^ 2
  have ha : 0 < a := expSubOnePole_pos m
  have hD : 0 < D := by unfold D; positivity
  have haD : a ^ 2 ≤ D := by
    unfold D
    nlinarith [sq_nonneg v]
  have hA : |(((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / D)| ≤
      ((2 * N + 1 : ℕ) : ℝ) * |v| ^ (2 * N) / a ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_of_pos hD]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos ha) haD
  have hvpow : |v| ^ (2 * N + 2) = |v| ^ (2 * N) * |v| ^ 2 := by
    rw [show 2 * N + 2 = 2 * N + 2 by rfl, pow_add]
  have hB : |2 * v ^ (2 * N + 2) / D ^ 2| ≤
      2 * |v| ^ (2 * N) / a ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow,
      abs_pow, abs_of_pos hD, hvpow, sq_abs]
    apply (div_le_div_iff₀ (pow_pos hD 2) (pow_pos ha 2)).2
    have hcore : v ^ 2 * a ^ 2 ≤ D ^ 2 := by
      unfold D
      nlinarith [sq_nonneg v, sq_nonneg a]
    calc
      2 * (|v| ^ (2 * N) * v ^ 2) * a ^ 2 =
          (2 * |v| ^ (2 * N)) * (v ^ 2 * a ^ 2) := by ring
      _ ≤ (2 * |v| ^ (2 * N)) * D ^ 2 :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 2 * |v| ^ (2 * N) * D ^ 2 := by ring
  unfold expSubOneRemainderDerivTerm
  change |2 * (-1 : ℝ) ^ N / a ^ (2 * N) *
      ((((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / D) -
        2 * v ^ (2 * N + 2) / D ^ 2)| ≤ _
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow,
    abs_neg, abs_one, one_pow, mul_one, abs_pow, abs_of_pos ha]
  calc
    (2 / a ^ (2 * N)) *
          |(((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / D) -
            2 * v ^ (2 * N + 2) / D ^ 2| ≤
        (2 / a ^ (2 * N)) *
          (|((2 * N + 1 : ℕ) : ℝ) * v ^ (2 * N) / D| +
            |2 * v ^ (2 * N + 2) / D ^ 2|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ (2 / a ^ (2 * N)) *
        ((((2 * N + 1 : ℕ) : ℝ) * |v| ^ (2 * N) / a ^ 2) +
          2 * |v| ^ (2 * N) / a ^ 2) := by
      gcongr
    _ = 2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N) *
        (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
      unfold a
      rw [show (2 * N + 3 : ℕ) = (2 * N + 1) + 2 by omega]
      push_cast
      rw [pow_add]
      ring

private lemma expSubOneRemainderDerivTerm_summable (N : ℕ) (v : ℝ) :
    Summable (expSubOneRemainderDerivTerm N v) := by
  have hw := expSubOnePole_inv_pow_summable (2 * N + 2) (by omega)
  have hm := hw.mul_left (2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N))
  exact hm.of_norm_bounded fun m => by
    rw [Real.norm_eq_abs]
    exact expSubOneRemainderDerivTerm_abs_le N v m

private lemma expSubOneRemainder_hasDerivAt (N : ℕ) (v : ℝ) :
    HasDerivAt (expSubOneRemainder N)
      (∑' m : ℕ, expSubOneRemainderDerivTerm N v m) v := by
  let R := |v| + 1
  let u : ℕ → ℝ := fun m =>
    2 * (2 * N + 3 : ℕ) * R ^ (2 * N) * (expSubOnePole m ^ (2 * N + 2))⁻¹
  have hR : 0 < R := by unfold R; positivity
  have hu : Summable u := by
    unfold u
    exact (expSubOnePole_inv_pow_summable (2 * N + 2) (by omega)).mul_left _
  have hv : v ∈ Set.Ioo (-R) R := by
    rw [Set.mem_Ioo, ← abs_lt]
    unfold R
    linarith
  exact hasDerivAt_tsum_of_isPreconnected
    (u := u)
    (g := fun m y => expSubOneRemainderTerm N y m)
    (g' := fun m y => expSubOneRemainderDerivTerm N y m)
    (t := Set.Ioo (-R) R) (y₀ := v) (y := v)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun m y _ => expSubOneRemainderTerm_hasDerivAt N y m)
    (fun m y hy => by
      rw [Real.norm_eq_abs]
      calc
        |expSubOneRemainderDerivTerm N y m| ≤
            2 * (2 * N + 3 : ℕ) * |y| ^ (2 * N) *
              (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
          expSubOneRemainderDerivTerm_abs_le N y m
        _ ≤ u m := by
          unfold u
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg y) (abs_lt.mpr hy).le _)
              (by positivity))
            (inv_nonneg.mpr (pow_nonneg (expSubOnePole_pos m).le _)))
    hv (expSubOneRemainderTerm_summable N v) hv

private lemma expSubOneRemainder_deriv_abs_le (N : ℕ) (v : ℝ) :
    |∑' m : ℕ, expSubOneRemainderDerivTerm N v m| ≤
      2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N) *
        ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
  have hd := expSubOneRemainderDerivTerm_summable N v
  have hw := expSubOnePole_inv_pow_summable (2 * N + 2) (by omega)
  have hm := hw.mul_left (2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N))
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' m : ℕ, expSubOneRemainderDerivTerm N v m‖ ≤
        ∑' m : ℕ, ‖expSubOneRemainderDerivTerm N v m‖ := norm_tsum_le_tsum_norm hd.norm
    _ ≤ ∑' m : ℕ, 2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N) *
        (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
      hd.norm.tsum_le_tsum (fun m => by
        rw [Real.norm_eq_abs]
        exact expSubOneRemainderDerivTerm_abs_le N v m) hm
    _ = 2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N) *
        ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
      rw [tsum_mul_left]

private lemma expSubOneRemainder_deriv_abs_le_bound (N : ℕ) (v : ℝ) :
    |∑' m : ℕ, expSubOneRemainderDerivTerm N v m| ≤
      expSubOneBound N * |v| ^ (2 * N) := by
  calc
    |∑' m : ℕ, expSubOneRemainderDerivTerm N v m| ≤
        2 * (2 * N + 3 : ℕ) * |v| ^ (2 * N) *
          ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
      expSubOneRemainder_deriv_abs_le N v
    _ = expSubOneBound N * |v| ^ (2 * N) := by
      unfold expSubOneBound
      ring

private lemma expSubOneRemainder_abs_le (N : ℕ) (v : ℝ) :
    |expSubOneRemainder N v| ≤
      2 * |v| ^ (2 * N + 1) * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
  have hr := expSubOneRemainderTerm_summable N v
  have hw := expSubOnePole_inv_pow_summable (2 * N + 2) (by omega)
  have hm := hw.mul_left (2 * |v| ^ (2 * N + 1))
  unfold expSubOneRemainder
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' m : ℕ, expSubOneRemainderTerm N v m‖ ≤
        ∑' m : ℕ, ‖expSubOneRemainderTerm N v m‖ := norm_tsum_le_tsum_norm hr.norm
    _ ≤ ∑' m : ℕ,
        2 * |v| ^ (2 * N + 1) * (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
      hr.norm.tsum_le_tsum (fun m => by
        rw [Real.norm_eq_abs]
        exact expSubOneRemainderTerm_abs_le N v m) hm
    _ = 2 * |v| ^ (2 * N + 1) *
        ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ := by
      rw [tsum_mul_left]

private lemma expSubOneRemainder_abs_le_bound (N : ℕ) (v : ℝ) :
    |expSubOneRemainder N v| ≤ expSubOneBound N * |v| ^ (2 * N + 1) := by
  calc
    |expSubOneRemainder N v| ≤
        2 * |v| ^ (2 * N + 1) *
          ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
      expSubOneRemainder_abs_le N v
    _ ≤ expSubOneBound N * |v| ^ (2 * N + 1) := by
      unfold expSubOneBound
      have hW : 0 ≤ ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
        tsum_nonneg fun m => inv_nonneg.mpr (pow_nonneg (expSubOnePole_pos m).le _)
      have hp : 0 ≤ |v| ^ (2 * N + 1) := by positivity
      have hc : (2 : ℝ) ≤ 2 * (2 * N + 3 : ℕ) := by
        norm_cast
        omega
      calc
        2 * |v| ^ (2 * N + 1) *
            (∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹) =
            (2 * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹) *
              |v| ^ (2 * N + 1) := by ring
        _ ≤ (2 * (2 * N + 3 : ℕ) *
              ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹) *
                |v| ^ (2 * N + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hW) hp

private lemma expSubOneRemainderTerm_zero (v : ℝ) (m : ℕ) :
    expSubOneRemainderTerm 0 v m = expSubOneKernelTerm v m := by
  simp [expSubOneRemainderTerm, expSubOneKernelTerm]

private lemma expSubOneRemainderTerm_succ (N : ℕ) (v : ℝ) (m : ℕ) :
    expSubOneRemainderTerm N v m =
      2 * (-1 : ℝ) ^ N * v ^ (2 * N + 1) / expSubOnePole m ^ (2 * N + 2) +
        expSubOneRemainderTerm (N + 1) v m := by
  have ha : expSubOnePole m ≠ 0 := ne_of_gt (expSubOnePole_pos m)
  have hd : v ^ 2 + expSubOnePole m ^ 2 ≠ 0 := by positivity
  unfold expSubOneRemainderTerm
  field_simp [ha, hd]
  ring

private lemma expSubOneKernelCoeff_summable (n : ℕ) :
    Summable (expSubOneKernelCoeff n) := by
  unfold expSubOneKernelCoeff
  simpa only [div_eq_mul_inv] using
    (expSubOnePole_inv_pow_summable (2 * n + 2) (by omega)).mul_left (2 * (-1 : ℝ) ^ n)

private lemma expSubOne_tsum_one_div_succ_pow (k : ℕ) (hk : 1 ≤ k) :
    (∑' m : ℕ, 1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k))) =
      (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) *
        (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) := by
  have hz := hasSum_zeta_nat (Nat.ne_of_gt hk)
  have hs := hz.summable
  have hdecomp := hs.sum_add_tsum_nat_add 1
  rw [hz.tsum_eq] at hdecomp
  have hk2 : 2 * k ≠ 0 := by omega
  simp [zero_pow hk2] at hdecomp
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using hdecomp

private lemma expSubOneKernelCoeff_tsum (n : ℕ) :
    (∑' m : ℕ, expSubOneKernelCoeff n m) =
      (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) := by
  let k := n + 1
  let C : ℝ := 2 * (-1 : ℝ) ^ n / (2 * Real.pi) ^ (2 * k)
  have hterm : ∀ m : ℕ, expSubOneKernelCoeff n m =
      C * (1 / (((m + 1 : ℕ) : ℝ) ^ (2 * k))) := by
    intro m
    unfold expSubOneKernelCoeff expSubOnePole C k
    push_cast
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    rw [mul_pow]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, expSubOne_tsum_one_div_succ_pow k (by omega)]
  have heven : n + (n + 1 + 1) = 2 * (n + 1) := by omega
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n + 1 + 1) = 1 := by
    rw [← pow_add, heven, pow_mul]
    norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold C k
  rw [show 2 * (n + 1) = 2 * n + 2 by omega,
    show n + 1 + 1 = n + 2 by omega, mul_pow]
  field_simp [hpi]
  calc
    2 * (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n + 2) * 2 ^ (2 * n + 2 - 1) *
          (bernoulli (2 * n + 2) : ℝ) =
        2 * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ (n + 1 + 1)) *
          2 ^ (2 * n + 2 - 1) * (bernoulli (2 * n + 2) : ℝ) := by
      rw [show n + 2 = n + 1 + 1 by omega]
      ring
    _ = 2 * 2 ^ (2 * n + 2 - 1) * (bernoulli (2 * n + 2) : ℝ) := by
      rw [hsign]
      ring
    _ = 2 ^ (2 * n + 2) * (bernoulli (2 * n + 2) : ℝ) := by
      rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega,
        show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
      ring

private lemma expSubOneRemainder_succ (N : ℕ) (v : ℝ) :
    expSubOneRemainder N v =
      (bernoulli (2 * N + 2) : ℝ) / ((2 * N + 2).factorial : ℝ) *
        v ^ (2 * N + 1) + expSubOneRemainder (N + 1) v := by
  have hc := expSubOneKernelCoeff_summable N
  have hr := expSubOneRemainderTerm_summable (N + 1) v
  unfold expSubOneRemainder
  calc
    (∑' m : ℕ, expSubOneRemainderTerm N v m) =
        ∑' m : ℕ, (expSubOneKernelCoeff N m * v ^ (2 * N + 1) +
          expSubOneRemainderTerm (N + 1) v m) := by
      apply tsum_congr
      intro m
      rw [expSubOneRemainderTerm_succ]
      unfold expSubOneKernelCoeff
      ring
    _ = (∑' m : ℕ, expSubOneKernelCoeff N m * v ^ (2 * N + 1)) +
        ∑' m : ℕ, expSubOneRemainderTerm (N + 1) v m :=
      (hc.mul_right _).tsum_add hr
    _ = (bernoulli (2 * N + 2) : ℝ) / ((2 * N + 2).factorial : ℝ) *
        v ^ (2 * N + 1) + ∑' m : ℕ, expSubOneRemainderTerm (N + 1) v m := by
      rw [show (∑' m : ℕ, expSubOneKernelCoeff N m * v ^ (2 * N + 1)) =
          v ^ (2 * N + 1) * ∑' m : ℕ, expSubOneKernelCoeff N m by
        calc
          (∑' m : ℕ, expSubOneKernelCoeff N m * v ^ (2 * N + 1)) =
              ∑' m : ℕ, v ^ (2 * N + 1) * expSubOneKernelCoeff N m := by
            apply tsum_congr
            intro m
            ring
          _ = v ^ (2 * N + 1) * ∑' m : ℕ, expSubOneKernelCoeff N m := tsum_mul_left]
      rw [expSubOneKernelCoeff_tsum]
      ring

private lemma expSubOneKernel_tsum_eq (N : ℕ) (v : ℝ) :
    (∑' m : ℕ, expSubOneKernelTerm v m) =
      (∑ n ∈ Finset.range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          v ^ (2 * n + 1)) + expSubOneRemainder N v := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      unfold expSubOneRemainder
      apply tsum_congr
      intro m
      exact (expSubOneRemainderTerm_zero v m).symm
  | succ N ih =>
      rw [ih, expSubOneRemainder_succ, Finset.sum_range_succ]
      ring

private lemma expSubOneKernelTerm_eq_mittag (v : ℝ) (m : ℕ) :
    expSubOneKernelTerm v m =
      2 * v / (v ^ 2 + 4 * Real.pi ^ 2 * (m + 1 : ℕ) ^ 2) := by
  unfold expSubOneKernelTerm expSubOnePole
  push_cast
  congr 2
  ring

private lemma expSubOneKernel_eq (N : ℕ) (v : ℝ) (hv : v ≠ 0) :
    1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
        ∑ n ∈ Finset.range N,
          (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
            v ^ (2 * n + 1) =
      expSubOneRemainder N v := by
  have hmittag := one_div_exp_sub_one_eq_tsum v hv
  simp_rw [← expSubOneKernelTerm_eq_mittag] at hmittag
  rw [hmittag, expSubOneKernel_tsum_eq]
  ring

/-- **Remainder of the Laurent expansion of $1/(e^v - 1)$.** For a natural number $N$, the
function $R_N : \mathbb{R} \to \mathbb{R}$ is defined by $R_N(0) = 0$ and, for $v \neq 0$,
$$
R_N(v) = \frac{1}{e^v - 1} - \frac{1}{v} + \frac{1}{2} -
  \sum_{n=0}^{N-1} \frac{B_{2n+2}}{(2n+2)!} v^{2n+1},
$$
where $B_k$ are the Bernoulli numbers. This is the remainder after truncating the Laurent
expansion of $1/(e^v - 1)$ at $0$ after its first $N$ terms of positive odd degree.
-/
def oneDivExpSubOneLaurentRemainder (N : ℕ) (v : ℝ) : ℝ :=
  if v = 0 then 0 else
    1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
      ∑ n ∈ Finset.range N,
        (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
          v ^ (2 * n + 1)

private lemma expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder (N : ℕ) (v : ℝ) :
    expSubOneRemainder N v = oneDivExpSubOneLaurentRemainder N v := by
  by_cases hv : v = 0
  · subst v
    simp [expSubOneRemainder, expSubOneRemainderTerm, oneDivExpSubOneLaurentRemainder]
  · simp only [oneDivExpSubOneLaurentRemainder, hv, ↓reduceIte]
    exact (expSubOneKernel_eq N v hv).symm

/-- **The Laurent remainder of $1/(e^v - 1)$ is differentiable.** For every natural number $N$,
the function $R_N : \mathbb{R} \to \mathbb{R}$ given by $R_N(0) = 0$ and, for $v \neq 0$,
$$
R_N(v) = \frac{1}{e^v - 1} - \frac{1}{v} + \frac{1}{2} -
  \sum_{n=0}^{N-1} \frac{B_{2n+2}}{(2n+2)!} v^{2n+1},
$$
where $B_k$ are the Bernoulli numbers, is differentiable at every point of $\mathbb{R}$. -/
theorem differentiable_oneDivExpSubOneLaurentRemainder (N : ℕ) :
    Differentiable ℝ (oneDivExpSubOneLaurentRemainder N) := by
  have hfun : oneDivExpSubOneLaurentRemainder N = expSubOneRemainder N := by
    funext v
    exact (expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder N v).symm
  rw [hfun]
  exact fun v => (expSubOneRemainder_hasDerivAt N v).differentiableAt

/-- **Bound on the Laurent remainder of $1/(e^v - 1)$.** For a natural number $N$, let
$R_N : \mathbb{R} \to \mathbb{R}$ be given by $R_N(0) = 0$ and, for $v \neq 0$,
$$
R_N(v) = \frac{1}{e^v - 1} - \frac{1}{v} + \frac{1}{2} -
  \sum_{n=0}^{N-1} \frac{B_{2n+2}}{(2n+2)!} v^{2n+1},
$$
where $B_k$ are the Bernoulli numbers. Then for every real number $v$,
$$
|R_N(v)| \le 2(2N + 3) \left( \sum_{m=0}^{\infty} \frac{1}{(2\pi(m + 1))^{2N+2}} \right) |v|^{2N+1}.
$$
-/
theorem oneDivExpSubOneLaurentRemainder_abs_le (N : ℕ) (v : ℝ) :
    |oneDivExpSubOneLaurentRemainder N v| ≤
      (2 * (2 * N + 3 : ℕ) *
        ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹) *
        |v| ^ (2 * N + 1) := by
  rw [← expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder]
  simpa only [expSubOneBound, expSubOnePole] using expSubOneRemainder_abs_le_bound N v

/-- **Bound on the derivative of the Laurent remainder of $1/(e^v - 1)$.** For a natural
number $N$, let $R_N : \mathbb{R} \to \mathbb{R}$ be given by $R_N(0) = 0$ and, for $v \neq 0$,
$$
R_N(v) = \frac{1}{e^v - 1} - \frac{1}{v} + \frac{1}{2} -
  \sum_{n=0}^{N-1} \frac{B_{2n+2}}{(2n+2)!} v^{2n+1},
$$
where $B_k$ are the Bernoulli numbers. Then for every real number $v$, the derivative of $R_N$
satisfies
$$
|R_N'(v)| \le 2(2N + 3) \left( \sum_{m=0}^{\infty} \frac{1}{(2\pi(m + 1))^{2N+2}} \right) |v|^{2N}.
$$
-/
theorem abs_deriv_oneDivExpSubOneLaurentRemainder_le (N : ℕ) (v : ℝ) :
    |deriv (oneDivExpSubOneLaurentRemainder N) v| ≤
      (2 * (2 * N + 3 : ℕ) *
        ∑' m : ℕ, ((2 * Real.pi * (m + 1)) ^ (2 * N + 2))⁻¹) *
        |v| ^ (2 * N) := by
  have hfun : oneDivExpSubOneLaurentRemainder N = expSubOneRemainder N := by
    funext y
    exact (expSubOneRemainder_eq_oneDivExpSubOneLaurentRemainder N y).symm
  rw [hfun, (expSubOneRemainder_hasDerivAt N v).deriv]
  simpa only [expSubOneBound, expSubOnePole] using expSubOneRemainder_deriv_abs_le_bound N v

/-- **Global remainder bound for the Laurent expansion of $1/(e^v - 1)$.** For every natural
number $N$ there is a constant $C \ge 0$ such that for every real number $v \neq 0$,
$$
\left| \frac{1}{e^v - 1} - \frac{1}{v} + \frac{1}{2} -
  \sum_{n=0}^{N-1} \frac{B_{2n+2}}{(2n+2)!} v^{2n+1} \right| \le C |v|^{2N+1},
$$
where $B_k$ are the Bernoulli numbers.
-/
theorem abs_one_div_exp_sub_one_sub_laurent_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, v ≠ 0 →
      |1 / (Real.exp v - 1) - 1 / v + 1 / 2 -
          ∑ n ∈ Finset.range N,
            (bernoulli (2 * n + 2) : ℝ) / ((2 * n + 2).factorial : ℝ) *
              v ^ (2 * n + 1)| ≤
        C * |v| ^ (2 * N + 1) := by
  let C := 2 * ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg (by norm_num) (tsum_nonneg fun m =>
      inv_nonneg.mpr (pow_nonneg (expSubOnePole_pos m).le _))
  refine ⟨C, hC, fun v hv => ?_⟩
  rw [expSubOneKernel_eq N v hv]
  calc
    |expSubOneRemainder N v| ≤
        2 * |v| ^ (2 * N + 1) *
          ∑' m : ℕ, (expSubOnePole m ^ (2 * N + 2))⁻¹ :=
      expSubOneRemainder_abs_le N v
    _ = C * |v| ^ (2 * N + 1) := by
      unfold C
      ring

end

end MetaMathlibExt

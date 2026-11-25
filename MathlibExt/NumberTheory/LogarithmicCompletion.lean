/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwistedCompleteExponentialSum
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MathlibExt.NumberTheory.IncompleteExponentialSum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Logarithmic completion of incomplete exponential sums

`MetaMathlibExt.norm_incompleteSum_lt_sup_mul_log` bounds an interval sum by the largest
complete additive twist times the logarithm of the modulus.

For `p ≥ 32`, Fourier inversion reduces the estimate to the sum of the norms of the interval
kernel. Pairing opposite frequencies bounds the nonzero terms by a harmonic sum and an
explicit remainder. For smaller primes, the interval and its complement give two length bounds,
and the largest complete twist has norm at least `√p`.
-/

namespace MetaMathlibExt

open Complex Finset

namespace norm_incompleteSum_lt_sup_mul_log

variable {p : ℕ} [NeZero p]

private lemma sum_residues {M : Type*} [AddCommMonoid M] (F : ZMod p → M) :
    ∑ x : ZMod p, F x = ∑ i ∈ range p, F i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  rw [← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ => congrArg F (ZMod.natCast_zmod_val i).symm

private lemma sum_representatives (F : ZMod p → ℂ) :
    ∑ x : ZMod p, F x = ∑ i ∈ Icc 1 p, F i := by
  rw [← Equiv.sum_comp (Equiv.addLeft (1 : ZMod p)) F, sum_residues,
    ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp

/-- The Fourier kernel for the interval from 1 to `B`. -/
private noncomputable def kernel (B : ℕ) (y : ZMod p) : ℂ :=
  ∑ x ∈ Icc 1 B, ZMod.stdAddChar ((x : ZMod p) * y)

private lemma norm_kernel_le (B y : ℕ) (hy : 0 < y) (hyp : y < p) :
    ‖kernel B (y : ZMod p)‖ ≤ 1 / Real.sin (Real.pi * (y / (p : ℝ))) := by
  let z := ZMod.stdAddChar (y : ZMod p)
  have hz : ‖z‖ = 1 := AddChar.norm_apply ..
  have hgeom : kernel B (y : ZMod p) = z * ∑ i ∈ range B, z ^ i := by
    simp only [kernel, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      mul_sum, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, z, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul, AddChar.map_add_eq_mul]
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hr : (y : ℝ) / p < 1 := (div_lt_one hp₀).mpr (by exact_mod_cast hyp)
  have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi * ((y : ℝ) / p) by positivity)
    (by simpa using mul_lt_mul_of_pos_left hr Real.pi_pos)
  have hchord : ‖z - 1‖ = 2 * Real.sin (Real.pi * ((y : ℝ) / p)) := by
    have he : z = exp (I * ((2 * Real.pi * (y / (p : ℝ)) : ℝ) : ℂ)) := by
      calc
        z = exp (2 * Real.pi * I * (y : ℂ) / p) := by
          simpa [z] using ZMod.stdAddChar_coe (N := p) (y : ℤ)
        _ = _ := by push_cast; congr 1; ring
    rw [he, norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
      show 2 * Real.pi * ((y : ℝ) / p) / 2 = Real.pi * (y / (p : ℝ)) by ring,
      abs_of_pos (by positivity)]
  have hb := norm_sub_le (z ^ B) (1 : ℂ)
  rw [norm_pow, hz, one_pow, norm_one, ← geom_sum_mul z B, norm_mul, hchord] at hb
  rw [hgeom, norm_mul, hz, one_mul, le_div_iff₀ hs]
  linarith

/-- Pair frequencies `y` and `p - y` in the sum of reciprocal sines. -/
private lemma sum_cosec_eq_twice {m : ℕ} (hm : p = 2 * m + 1) :
    let c := fun y : ℕ => 1 / Real.sin (Real.pi * (y / (p : ℝ)))
    ∑ y ∈ Ico 1 p, c y = 2 * ∑ y ∈ Icc 1 m, c y := by
  intro c
  rw [← sum_Ico_consecutive c (show 1 ≤ m + 1 by omega) (show m + 1 ≤ p by omega)]
  have href := sum_Ico_reflect c 1 (m := m + 1) (n := p) (by omega)
  rw [show p + 1 - (m + 1) = m + 1 by omega, Nat.add_sub_cancel] at href
  rw [← href, Ico_add_one_right_eq_Icc, two_mul]
  congr 1
  apply sum_congr rfl
  intro y hy
  obtain ⟨_, hym⟩ := mem_Icc.mp hy
  have hp₀ : (p : ℝ) ≠ 0 := NeZero.ne _
  dsimp [c]
  rw [Nat.cast_sub (show y ≤ p by omega),
    show Real.pi * ((p - (y : ℝ)) / p) = Real.pi - Real.pi * (y / p) by
      field_simp, Real.sin_pi_sub]

private lemma half_cosec_bound {m : ℕ} (hm : p = 2 * m + 1) :
    (∑ y ∈ Icc 1 m, 1 / Real.sin (Real.pi * (y / (p : ℝ)))) ≤
      (p / Real.pi) * ((harmonic m : ℝ) + 1 / 3) := by
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hp' : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hm
  have hpoint (y : ℕ) (hy : y ∈ Icc 1 m) :
      1 / Real.sin (Real.pi * (y / (p : ℝ))) ≤
        (p / Real.pi) * ((y : ℝ)⁻¹ + (8 / (3 * (p : ℝ) ^ 2)) * y) := by
    obtain ⟨hy₁, hym⟩ := mem_Icc.mp hy
    let t := (y : ℝ) / p
    have ht : 0 < t := div_pos (by exact_mod_cast hy₁) hp₀
    have ht' : t ≤ 1 / 2 := by
      dsimp [t]
      rw [div_le_div_iff₀ hp₀ (by norm_num)]
      linarith [show (y : ℝ) ≤ m by exact_mod_cast hym]
    have hden : 3 / 4 ≤ 1 - t ^ 2 := by
      nlinarith [sq_le_sq₀ ht.le (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mpr ht']
    have hc : 2 * t / (1 - t ^ 2) ≤ 8 / 3 * t := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hden ht.le]
    calc
      _ ≤ _ := (one_div_sin_pi_lt t ht (by linarith)).le
      _ ≤ 1 / Real.pi * (1 / t + 8 / 3 * t) := by gcongr
      _ = _ := by
        dsimp [t]
        field_simp
  -- The linear error term sums to at most one third after factoring out p / π.
  have hsum (n : ℕ) : ∑ y ∈ Icc 1 n, (y : ℝ) = n * (n + 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  calc
    _ ≤ _ := sum_le_sum hpoint
    _ = (p / Real.pi) * ((harmonic m : ℝ) + (8 / (3 * (p : ℝ) ^ 2)) * (m * (m + 1) / 2)) := by
      simp only [← mul_sum, sum_add_distrib, hsum, harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := by
      gcongr
      field_simp
      nlinarith [hp']

private lemma kernel_sum_lt {m : ℕ} (hm : p = 2 * m + 1) (hp32 : 32 ≤ p)
    (B : ℕ) (hB : B ≤ p) :
    ∑ y : ZMod p, ‖kernel B y‖ < p * Real.log p := by
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hm₀ : 0 < m := by omega
  -- For m ≥ 6 the decreasing difference Hₘ - log m is less than 2/3.
  have hH := (Real.strictAnti_eulerMascheroniSeq'.antitone (show 6 ≤ m by omega)).trans_lt
    Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', hm₀.ne', ite_false] at hH
  have hlogm : Real.log m ≤ Real.log p - Real.log 2 := by
    rw [← Real.log_div hp₀.ne' (by norm_num)]
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (show m * 2 ≤ p by omega)
  have hlogp : 5 * Real.log 2 ≤ Real.log p := by
    rw [show (5 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 5) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hp32)
  have hcoeff : 1 + 2 / Real.pi * ((harmonic m : ℝ) + 1 / 3) < Real.log p := by
    have hlog : 1 < Real.log p := by linarith [Real.log_two_gt_d9]
    have := mul_lt_mul_of_pos_right Real.pi_gt_d2 (sub_pos.mpr hlog)
    field_simp
    nlinarith [Real.log_two_gt_d9]
  rw [sum_residues, sum_range_eq_add_Ico _ (NeZero.pos p)]
  simp only [Nat.cast_zero]
  have hzero : ‖kernel B (0 : ZMod p)‖ = B := by simp [kernel, Nat.card_Icc]
  rw [hzero]
  calc
    _ ≤ p + ∑ y ∈ Ico 1 p, 1 / Real.sin (Real.pi * (y / (p : ℝ))) := by
      exact add_le_add (by exact_mod_cast hB) (sum_le_sum fun y hy =>
        norm_kernel_le B y (mem_Ico.mp hy).1 (mem_Ico.mp hy).2)
    _ ≤ (p : ℝ) * (1 + 2 / Real.pi * ((harmonic m : ℝ) + 1 / 3)) := by
      rw [sum_cosec_eq_twice hm]
      calc
        _ ≤ p + 2 * ((p / Real.pi) * ((harmonic m : ℝ) + 1 / 3)) := by
          gcongr
          exact half_cosec_bound hm
        _ = _ := by ring
    _ < _ := mul_lt_mul_of_pos_left hcoeff hp₀

/-- Fourier inversion followed by the triangle inequality for the interval kernel. -/
private lemma large_modulus_bound {m : ℕ} (hm : p = 2 * m + 1) (hp32 : 32 ≤ p)
    (g : ZMod p → ℂ) (B : ℕ) (hB : B ≤ p) {M : ℝ} (hM : 0 < M)
    (hcoeff : ∀ y, ‖ZMod.dft g y‖ ≤ M) :
    ‖∑ x ∈ Icc 1 B, g x‖ < M * Real.log p := by
  have hinv (x : ℕ) : (p : ℂ) * g x =
      ∑ y : ZMod p, ZMod.stdAddChar ((x : ZMod p) * y) * ZMod.dft g y := by
    have h := ZMod.invDFT_apply (ZMod.dft g) (x : ZMod p)
    rw [LinearEquiv.symm_apply_apply, smul_eq_mul] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (NeZero.ne _), one_mul]
    simp [mul_comm]
  have hcomplete : (p : ℂ) * ∑ x ∈ Icc 1 B, g x =
      ∑ y : ZMod p, kernel B y * ZMod.dft g y := by
    simp_rw [mul_sum, hinv, kernel, sum_mul]
    rw [sum_comm]
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  apply (mul_lt_mul_iff_of_pos_left hp₀).mp
  calc
    (p : ℝ) * ‖∑ x ∈ Icc 1 B, g x‖ = ‖(p : ℂ) * ∑ x ∈ Icc 1 B, g x‖ := by simp
    _ ≤ ∑ y : ZMod p, ‖kernel B y * ZMod.dft g y‖ := hcomplete ▸ norm_sum_le ..
    _ ≤ ∑ y : ZMod p, ‖kernel B y‖ * M := by
      simp only [norm_mul]
      gcongr with y
      apply hcoeff
    _ = (∑ y : ZMod p, ‖kernel B y‖) * M := (sum_mul ..).symm
    _ < p * Real.log p * M := mul_lt_mul_of_pos_right (kernel_sum_lt hm hp32 B hB) hM
    _ = _ := by ring

/-- On the range of small primes from 7 to 31, the elementary interval and complement
bounds suffice because `(1 + √p)/2 < log p`. -/
private lemma small_log_bound {q : ℝ} (h₇ : 7 ≤ q) (h₃₂ : q ≤ 32) :
    (1 + Real.sqrt q) / 2 < Real.log q := by
  have hc : ConcaveOn ℝ (Set.Ioi 0) (fun x : ℝ => Real.log x - (1 / 4) * x) :=
    strictConcaveOn_log_Ioi.concaveOn.sub ((convexOn_id (convex_Ioi _)).smul (by norm_num))
  have hq₀ : 0 ≤ q := by linarith
  have ht : Real.sqrt q ∈ Set.Icc (5 / 2 : ℝ) 6 := by
    constructor <;> nlinarith [Real.sq_sqrt hq₀, Real.sqrt_nonneg q]
  have hmin := hc.min_le_of_mem_Icc (by norm_num : (5 / 2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (6 : ℝ) ∈ Set.Ioi 0) ht
  have hlt : (1 / 4 : ℝ) <
      min (Real.log (5 / 2) - 1 / 4 * (5 / 2)) (Real.log 6 - 1 / 4 * 6) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show Real.log 6 = Real.log 2 + Real.log 3 by norm_num [← Real.log_mul]]
    exact lt_min (by linarith [Real.log_five_gt_d9, Real.log_two_lt_d9])
      (by linarith [Real.log_two_gt_d9, Real.log_three_gt_d9])
  have h := hlt.trans_le hmin
  rw [Real.log_sqrt hq₀] at h
  linarith

omit [NeZero p] in
private lemma small_modulus_bound (hp : p.Prime) (hp5 : 5 ≤ p) (hp32 : p < 32)
    (g : ZMod p → ℂ) (hg : ∀ x, ‖g x‖ = 1) (B : ℕ) (hB₁ : 1 ≤ B) (hB₂ : B ≤ p)
    {M : ℝ} (hM : Real.sqrt p ≤ M) (hfull : ‖∑ x ∈ Icc 1 p, g x‖ ≤ M) :
    ‖∑ x ∈ Icc 1 B, g x‖ < M * Real.log p := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hM₀ := (Real.sqrt_pos.2 hp₀).trans_le hM
  have hlen (s : Finset ℕ) : ‖∑ x ∈ s, g x‖ ≤ #s := by
    simpa [hg] using norm_sum_le s (fun x : ℕ => g x)
  have hleft : ‖∑ x ∈ Icc 1 B, g x‖ ≤ B := by simpa using hlen (Icc 1 B)
  have hright : ‖∑ x ∈ Icc 1 B, g x‖ ≤ M + (p - B : ℝ) := by
    have hsplit := sum_Ico_consecutive (fun x : ℕ => g x)
      (hB₁.trans B.le_succ) (Nat.succ_le_succ hB₂)
    simp only [Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc] at hsplit
    rw [eq_sub_of_add_eq hsplit]
    refine (norm_sub_le ..).trans (add_le_add hfull ?_)
    simpa [Nat.card_Icc, Nat.cast_sub hB₂] using hlen (Icc (B + 1) p)
  by_cases h5 : p = 5
  · have ht : 2 < M := by
      apply lt_of_lt_of_le _ hM
      rw [h5, Real.lt_sqrt (by norm_num)]
      norm_num
    have hlog : (3 / 2 : ℝ) < Real.log p := by
      rw [h5]
      exact lt_trans (by norm_num) Real.log_five_gt_d9
    have hlt := mul_lt_mul_of_pos_left hlog hM₀
    rcases le_or_gt B 3 with hB | hB
    · linarith [show (B : ℝ) ≤ 3 by exact_mod_cast hB]
    · linarith [show (p : ℝ) = 5 by exact_mod_cast h5, show 4 ≤ (B : ℝ) by exact_mod_cast hB]
  · have h₇ : 7 ≤ p := by
      have ho := hp.odd_of_ne_two (by omega)
      obtain ⟨k, hk⟩ := ho
      omega
    have hl := small_log_bound (q := p) (by exact_mod_cast h₇) (by exact_mod_cast hp32.le)
    have hprod := mul_lt_mul_of_pos_left hl hM₀
    have hsq := Real.sq_sqrt hp₀.le
    nlinarith [mul_le_mul_of_nonneg_right hM (Real.sqrt_nonneg p)]

end norm_incompleteSum_lt_sup_mul_log

open norm_incompleteSum_lt_sup_mul_log

set_option linter.unusedVariables false in
/-- **Logarithmic completion bound for incomplete exponential sums.** Let $p \ge 5$ be a prime,
write $e_p(t) = e^{2\pi i t/p}$, let $f$ be a polynomial with integer coefficients whose reduction
modulo $p$ has degree at least $2$, and let $B$ be an integer with $1 \le B \le p$. Put
$\Phi(f, p) = \max_{0 \le y \le p-1} \left|\sum_{x=1}^{p} e_p(f(x) + yx)\right|$. Then
$\left|\sum_{x=1}^{B} e_p(f(x))\right| < \Phi(f, p) \log p$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Corollary 1.1 (`integers-2025-A48-cor-1-1`). -/
public theorem norm_incompleteSum_lt_sup_mul_log (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (f : Polynomial ℤ) (hf : 2 ≤ (f.map (Int.castRingHom (ZMod p))).natDegree) (B : ℕ)
    (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p)‖ <
      (((range p).sup fun y : ℕ =>
          ‖∑ x ∈ Icc 1 p,
            exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ) *
        Real.log p := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let g (x : ZMod p) := ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod p))).eval x)
  let S (y : ℕ) := ∑ x ∈ Icc 1 p,
    exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)
  let M : ℝ := ((range p).sup fun y => ‖S y‖₊ : NNReal)
  have hM : Real.sqrt p ≤ M := sqrt_le_sup_norm_completeSum p hp f
  have htwist (y : ZMod p) : ZMod.dft g (-y) = S y.val := by
    rw [ZMod.dft_apply, sum_representatives]
    apply sum_congr rfl
    intro x _
    rw [← ZMod.stdAddChar_coe (N := p), Int.cast_add, AddChar.map_add_eq_mul]
    simp [g, mul_comm]
  have hcoeff (y : ZMod p) : ‖ZMod.dft g y‖ ≤ M := by
    rw [← neg_neg y, htwist]
    exact NNReal.coe_le_coe.mpr (le_sup (f := fun k => ‖S k‖₊) (mem_range.mpr (ZMod.val_lt _)))
  have hphase (x : ℕ) : exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p) = g x := by
    rw [← ZMod.stdAddChar_coe (N := p)]
    simp [g]
  simp_rw [hphase]
  by_cases hp32 : 32 ≤ p
  · obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
    exact large_modulus_bound hm hp32 g B hB₂ ((Real.sqrt_pos.2 (by positivity)).trans_le hM) hcoeff
  · apply small_modulus_bound hp hp5 (by omega) g (fun x => AddChar.norm_apply ..) B hB₁ hB₂ hM
    simpa [ZMod.dft_apply_zero, sum_representatives] using hcoeff 0

end MetaMathlibExt

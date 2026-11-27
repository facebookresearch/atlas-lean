/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Polynomial
import MathlibExt.RingTheory.PowerSeries.LagrangeBurmannCoefficient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Asymptotic normality of short chords in non-crossing chord diagrams

This file proves convergence of the moment generating function of the standardized short-chord
count to that of the standard normal distribution. Lagrange–Bürmann inversion expresses the
generating function coefficients as polynomial coefficients. Fourier inversion at an exponentially
tilted radius gives a Gaussian integral after rescaling.
-/

open Filter Set MeasureTheory Complex Finset PowerSeries
open scoped Topology Asymptotics BigOperators

namespace MetaMathlibExt.noncrossingLinearKChordDiagram_shortChords_asymptoticallyNormal

private lemma coeff_truncated_prod {R : Type*} [CommSemiring R] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (f : ι → PowerSeries R) (d : ℕ) :
    coeff d (∏ i, f i) =
      ∑ a : ι → Fin (d + 1),
        if (∑ i, (a i : ℕ)) = d then ∏ i, coeff (a i) (f i) else 0 := by
  classical
  let g : ι → PowerSeries R := fun i =>
    ∑ j : Fin (d + 1), monomial j.val (coeff j.val (f i))
  have hlow (i : ι) (j : ℕ) (hj : j ≤ d) : coeff j (f i) = coeff j (g i) := by
    dsimp [g]
    rw [map_sum, Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (d + 1))]
    · simp
    · intro a _ ha
      have hja : j ≠ a.val := fun heq => ha (Fin.ext heq.symm)
      simp [coeff_monomial, hja]
    · simp
  have hprod : coeff d (∏ i, f i) = coeff d (∏ i, g i) := by
    rw [coeff_prod, coeff_prod]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro i hi
    apply hlow
    have hs := (Finset.mem_finsuppAntidiag.mp ha).1
    exact (Finset.single_le_sum (f := fun j => a j) (fun _ _ => Nat.zero_le _) hi).trans_eq hs
  rw [hprod]
  dsimp [g]
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [PowerSeries.prod_monomial, coeff_monomial]
  by_cases h : (∑ i, (a i : ℕ)) = d
  · simp [h]
  · simp [h, Ne.symm h]

private def convolution (k : ℕ) (T : ℕ → ℕ → ℕ) (n ℓ : ℕ) : ℕ :=
  ∑ m : Fin k → Fin (n + 1),
    ∑ s : Fin k → Fin (ℓ + 1),
      if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (s i : ℕ)) = ℓ then ∏ i, T (m i) (s i)
      else 0

private lemma le_convolution (k : ℕ) (hk : 2 ≤ k) (T : ℕ → ℕ → ℕ)
    (h0 : T 0 0 = 1) (n ℓ : ℕ) : T n ℓ ≤ convolution k T n ℓ := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let m : Fin k → Fin (n + 1) := fun i => if i = i₀ then ⟨n, by omega⟩ else 0
  let s : Fin k → Fin (ℓ + 1) := fun i => if i = i₀ then ⟨ℓ, by omega⟩ else 0
  have hm : (∑ i, (m i : ℕ)) = n := by simp [m, apply_ite Fin.val]
  have hs : (∑ i, (s i : ℕ)) = ℓ := by simp [s, apply_ite Fin.val]
  have hprod : (∏ i, T (m i) (s i)) = T n ℓ := by
    rw [Finset.prod_eq_single i₀]
    · simp [m, s]
    · intro i _ hi
      simp [m, s, hi, h0]
    · simp
  unfold convolution
  calc
    T n ℓ = (if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (s i : ℕ)) = ℓ then
        ∏ i, T (m i) (s i) else 0) := by simp [hm, hs, hprod]
    _ ≤ ∑ a : Fin k → Fin (ℓ + 1),
        if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (a i : ℕ)) = ℓ then
          ∏ i, T (m i) (a i) else 0 :=
      Finset.single_le_sum (f := fun a : Fin k → Fin (ℓ + 1) =>
          if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (a i : ℕ)) = ℓ then
            ∏ i, T (m i) (a i) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    _ ≤ _ := Finset.single_le_sum (f := fun b : Fin k → Fin (n + 1) =>
        ∑ a : Fin k → Fin (ℓ + 1),
          if (∑ i, (b i : ℕ)) = n ∧ (∑ i, (a i : ℕ)) = ℓ then
            ∏ i, T (b i) (a i) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)

private lemma counts_support (k : ℕ) (T : ℕ → ℕ → ℕ)
    (h0 : ∀ ℓ, 0 < ℓ → T 0 ℓ = 0)
    (hrec : ∀ n ℓ, T (n + 1) ℓ =
      convolution k T n ℓ - T n ℓ + if ℓ = 0 then 0 else T n (ℓ - 1)) :
    ∀ n ℓ, n < ℓ → T n ℓ = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | n
    · exact h0
    · intro ℓ hℓ
      have hconv : convolution k T n ℓ = 0 := by
        unfold convolution
        apply Finset.sum_eq_zero
        intro m _
        apply Finset.sum_eq_zero
        intro s _
        split
        · rename_i h
          have hex : ∃ i, (m i : ℕ) < (s i : ℕ) := by
            by_contra! H
            have hle := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
              H i)
            rw [h.1, h.2] at hle
            omega
          obtain ⟨i, hi⟩ := hex
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          exact ih (m i) (m i).isLt (s i) hi
        · rfl
      rw [hrec, hconv, ite_eq_right (by omega), ih n (by omega) (ℓ - 1) (by omega)]
      simp

private noncomputable def row (T : ℕ → ℕ → ℕ) (n : ℕ) : Polynomial ℂ :=
  ∑ ℓ ∈ Finset.range (n + 1), Polynomial.monomial ℓ (T n ℓ : ℂ)

private lemma row_coeff (T : ℕ → ℕ → ℕ)
    (hsupp : ∀ n ℓ, n < ℓ → T n ℓ = 0) (n ℓ : ℕ) :
    (row T n).coeff ℓ = (T n ℓ : ℂ) := by
  classical
  unfold row
  rw [Polynomial.finsetSum_coeff]
  by_cases h : ℓ ≤ n
  · rw [Finset.sum_eq_single ℓ]
    · simp
    · intro i _ hi
      simp [Polynomial.coeff_monomial, hi]
    · simp [h]
  · rw [hsupp _ _ (Nat.lt_of_not_ge h), Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ ℓ := fun heq => h (by simpa [heq, Nat.lt_succ_iff] using hi)
    simp [Polynomial.coeff_monomial, hne]

private noncomputable def shape {R : Type*} [CommRing R] (k : ℕ) (y : R) :
    Polynomial R :=
  (1 + Polynomial.X) ^ k + Polynomial.C (y - 1) * (1 + Polynomial.X)

-- Young's generating function equation, followed by coefficient extraction.
private lemma row_coefficient (k : ℕ) (hk : 2 ≤ k) (T : ℕ → ℕ → ℕ)
    (h00 : T 0 0 = 1) (h0 : ∀ ℓ, 0 < ℓ → T 0 ℓ = 0)
    (hrec : ∀ n ℓ, T (n + 1) ℓ =
      convolution k T n ℓ - T n ℓ + if ℓ = 0 then 0 else T n (ℓ - 1))
    (y : ℂ) (n : ℕ) (hn : 0 < n) :
    (n : ℂ) * (row T n).eval y = ((shape k y) ^ n).coeff (n - 1) := by
  classical
  let F : PowerSeries (Polynomial ℂ) := PowerSeries.mk (row T)
  let yₛ : Polynomial ℂ := Polynomial.X
  let hsupp := counts_support k T h0 hrec
  have hF0 : coeff 0 F = 1 := by simp [F, row, h00]
  have hrec' : F = 1 + X * (F ^ k + C (yₛ - 1) * F) := by
    ext n : 1
    cases n with
    | zero => simp [hF0]
    | succ n =>
      simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, zero_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
      rw [show F ^ k = ∏ _ : Fin k, F by simp, coeff_truncated_prod]
      simp only [F, coeff_mk]
      ext ℓ
      have hprod (m : Fin k → Fin (n + 1)) :
          (∏ i, row T (m i)).coeff ℓ =
            ∑ s : Fin k → Fin (ℓ + 1),
              if (∑ i, (s i : ℕ)) = ℓ then ∏ i, (T (m i) (s i) : ℂ) else 0 := by
        rw [← Polynomial.coeff_coe]
        let coeHom := Polynomial.coeToPowerSeries.ringHom (R := ℂ)
        change coeff ℓ (coeHom (∏ i, row T (m i))) = _
        rw [map_prod, coeff_truncated_prod]
        simp only [coeHom, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
          row_coeff T hsupp]
      have hsum : (∑ m : Fin k → Fin (n + 1), if (∑ i, (m i : ℕ)) = n then
          ∏ i, row T (m i) else 0).coeff ℓ = (convolution k T n ℓ : ℂ) := by
        rw [Polynomial.finsetSum_coeff]
        simp only [convolution, Nat.cast_sum, Nat.cast_ite, Nat.cast_prod, Nat.cast_zero]
        apply Finset.sum_congr rfl
        intro m _
        by_cases h : (∑ i, (m i : ℕ)) = n <;> simp [h, hprod]
      rw [Polynomial.coeff_add, hsum, sub_mul, Polynomial.coeff_sub, one_mul,
        row_coeff T hsupp, row_coeff T hsupp, hrec]
      rw [Nat.cast_add, Nat.cast_sub (le_convolution k hk T h00 n ℓ)]
      cases ℓ <;> simp [yₛ, row_coeff T hsupp, Polynomial.coeff_X_mul] <;> ring
  let A := F - 1
  let φ : PowerSeries (Polynomial ℂ) := (shape k yₛ : PowerSeries (Polynomial ℂ))
  have hA0 : constantCoeff A = 0 := by simp [A, ← coeff_zero_eq_constantCoeff, hF0]
  have hsubst := HasSubst.of_constantCoeff_zero' hA0
  have hfix : A = X * subst A φ := by
    rw [show φ = ((shape k yₛ : Polynomial (Polynomial ℂ)) :
        PowerSeries (Polynomial ℂ)) by rfl, subst_coe hsubst]
    simp only [shape, map_add, map_pow, map_one, Polynomial.aeval_X, map_mul,
      Polynomial.aeval_C]
    have hAF : 1 + A = F := by simp [A]
    rw [hAF, show A = F - 1 by rfl, sub_eq_iff_eq_add]
    simpa [add_comm] using hrec'
  have hb := _root_.fps_lagrange_burmann_coeff' A φ X hfix n hn
  have hb' : (n : Polynomial ℂ) * row T n = ((shape k yₛ) ^ n).coeff (n - 1) := by
    rw [subst_X hsubst] at hb
    simpa [A, F, coeff_one, hn.ne', φ, ← Polynomial.coe_pow, Polynomial.coeff_coe] using hb
  have he := congrArg (Polynomial.evalRingHom y) hb'
  rw [map_mul, map_natCast] at he
  change (n : ℂ) * (row T n).eval y = _ at he
  rw [he, ← Polynomial.coeff_map]
  congr 1
  simp [shape, yₛ, Polynomial.map_C]

private noncomputable def factor (p q : ℝ) (w : ℂ) : ℂ := q + p * Complex.exp w

-- The real part of the tilt cancels the mixed term of the quadratic expansion.
private noncomputable def kernel (k : ℕ) (p q a : ℝ) (s : ℝ) (θ : ℝ) : ℂ :=
  let w : ℂ := (a * s : ℝ) + Complex.I * θ
  Complex.exp (-((a * s : ℝ) + w)) *
    (factor p q w ^ k + a * (Complex.exp s - 1) * factor p q w)

private noncomputable def scale (n : ℕ) : ℝ := (Real.sqrt n)⁻¹

private lemma scale_tendsto : Tendsto scale atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

private lemma hasDerivAt_exp_linear (b : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (b * y)) (Complex.exp (b * x) * b) x := by
  have hd := ((hasDerivAt_id (x : ℂ)).const_mul b).cexp.comp_ofReal
  simpa using hd

private lemma kernel_pow_tendsto (k : ℕ) (hk : 2 ≤ k) (p q a : ℝ)
    (hpq : q + p = 1) (hkp : (k : ℝ) * p = 1) (t x : ℝ) :
    Tendsto (fun n : ℕ => kernel k p q a (scale n * t) (scale n * x) ^ n) atTop
      (𝓝 (Complex.exp (((a - (1 + q) * a ^ 2) * t ^ 2 / 2 - q * x ^ 2 / 2 : ℝ) : ℂ))) := by
  let w : ℂ := (a * t : ℝ) + Complex.I * x
  let b : ℂ := (a * t : ℝ) + w
  let G : ℝ → ℂ := fun y => factor p q (w * y)
  let H : ℝ → ℂ := fun y => G y ^ k + a * (Complex.exp ((t : ℂ) * y) - 1) * G y
  let F : ℝ → ℂ := fun y => Complex.exp (-b * y) * H y
  let D : ℝ → ℂ := fun y => (p : ℂ) * (Complex.exp (w * y) * w)
  have heval (y : ℝ) : F y = kernel k p q a (y * t) (y * x) := by
    have hw : w * (y : ℂ) = ((a * (y * t) : ℝ) : ℂ) + I * ((y * x : ℝ) : ℂ) := by
      dsimp [w]
      push_cast
      ring
    have hb : -b * (y : ℂ) = -(((a * (y * t) : ℝ) : ℂ) + w * y) := by
      dsimp [b]
      push_cast
      ring
    have ht : (t : ℂ) * y = ↑(y * t) := by push_cast; ring
    simp only [F, H, G, kernel, hb, ht, hw]
  have hpq' : (q : ℂ) + p = 1 := by exact_mod_cast hpq
  have hkp' : (k : ℂ) * p = 1 := by exact_mod_cast hkp
  have dG (y : ℝ) : HasDerivAt G (D y) y :=
    ((hasDerivAt_exp_linear w y).const_mul (p : ℂ)).const_add (q : ℂ)
  let J : ℝ → ℂ := fun y =>
    (k : ℂ) * G y ^ (k - 1) * D y +
      ((a : ℂ) * (Complex.exp ((t : ℂ) * y) * t) * G y +
        a * (Complex.exp ((t : ℂ) * y) - 1) * D y)
  have dH (y : ℝ) : HasDerivAt H (J y) y :=
    ((dG y).pow k).add <| (((hasDerivAt_exp_linear t y).sub_const 1).const_mul (a : ℂ)).mul (dG y)
  have hF : deriv F = fun y : ℝ => Complex.exp (-b * y) * (-b * H y + J y) := by
    funext y
    calc deriv F y = _ := ((hasDerivAt_exp_linear (-b) y).mul (dH y)).deriv
      _ = _ := by ring
  have hG0 : G 0 = 1 := by simp [G, factor, hpq']
  have hH0 : H 0 = 1 := by simp [H, hG0]
  have hJ0 : J 0 = b := by
    simp [J, D, hG0, b, ← mul_assoc, hkp', add_comm]
  have hF0 : F 0 = 1 := by simp [F, hH0]
  have hF'0 : deriv F 0 = 0 := by simp [hF, hH0, hJ0]
  have dJ : HasDerivAt J ((k : ℂ) * (k - 1 : ℕ) * ((p : ℂ) * w) ^ 2 +
      (k : ℂ) * p * w ^ 2 + a * t ^ 2 + 2 * a * t * p * w) 0 := by
    have dD := (((hasDerivAt_exp_linear w 0).mul_const w).const_mul (p : ℂ))
    have e := hasDerivAt_exp_linear (t : ℂ) 0
    have hd := ((((dG 0).pow (k - 1)).const_mul (k : ℂ)).mul dD).add <|
      (((e.mul_const (t : ℂ)).const_mul (a : ℂ)).mul (dG 0)).add <|
        (((e.sub_const 1).const_mul (a : ℂ)).mul dD)
    convert hd using 1
    simp only [Pi.pow_apply, hG0, D, ofReal_zero, mul_zero, zero_mul, exp_zero, one_mul, one_pow,
      sub_self, add_zero]
    ring
  have hF''0 : deriv (deriv F) 0 =
      (((a - (1 + q) * a ^ 2) * t ^ 2 - q * x ^ 2 : ℝ) : ℂ) := by
    rw [hF]
    calc _ = _ := ((hasDerivAt_exp_linear (-b) 0).mul (((dH 0).const_mul (-b)).add dJ)).deriv
      _ = _ := by
        simp only [Pi.add_apply, ofReal_zero, mul_zero, exp_zero, one_mul, hH0, hJ0]
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        have hq' : (q : ℂ) = 1 - p := eq_sub_of_add_eq hpq'
        push_cast
        rw [hq']
        have hi : I ^ 2 = (-1 : ℂ) := I_sq
        dsimp [b, w]
        push_cast
        linear_combination (I * (x : ℂ) + a * t) ^ 2 * ((k : ℂ) * p + 2 - p) *
          hkp' + (1 - p) * (x : ℂ) ^ 2 * hi
  have hTaylor :
      (fun y : ℝ => F y - (1 + (y : ℂ) ^ 2 *
        (((a - (1 + q) * a ^ 2) * t ^ 2 / 2 - q * x ^ 2 / 2 : ℝ) : ℂ))) =o[𝓝 0]
        (fun y : ℝ => y ^ 2) := by
    have he (c : ℂ) : ContDiff ℝ 2 (fun y : ℝ => Complex.exp (c * y)) :=
      Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
    have hg : ContDiff ℝ 2 G := contDiff_const.add (contDiff_const.mul (he w))
    have hh : ContDiff ℝ 2 H :=
      (hg.pow k).add ((contDiff_const.mul ((he t).sub contDiff_const)).mul hg)
    refine (taylor_isLittleO_univ (f := F) (x₀ := 0) ((he (-b)).mul hh)).congr'
      ?_ (Eventually.of_forall fun _ => by simp)
    apply Eventually.of_forall
    intro y
    norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ, iteratedDeriv_succ,
      hF0, hF'0, hF''0, real_smul]
    ring
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  refine (Complex.isLittleO_ofReal_right.mpr (hTaylor.comp_tendsto scale_tendsto)).congr'
    (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
  · simp only [Function.comp_apply]
    rw [heval, show (scale n : ℂ) ^ 2 = (n : ℂ)⁻¹ by
      rw [← ofReal_pow, scale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp]
    ring
  · change ((scale n ^ 2 : ℝ) : ℂ) = _
    rw [scale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp [one_div]

private lemma factor_norm_le (q b θ : ℝ) (hq : 0 < q) (hb : 0 < b) (hθ : |θ| ≤ Real.pi) :
    ‖(q : ℂ) + b * Complex.exp (I * θ)‖ ≤
      (q + b) * Real.exp (-(2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)) * θ ^ 2) := by
  have hn : ‖(q : ℂ) + b * Complex.exp (I * θ)‖ ^ 2 =
      (q + b) ^ 2 - 2 * q * b * (1 - Real.cos θ) := by
    rw [Complex.sq_norm, Complex.normSq_add]
    have he : (Complex.exp (I * θ)).re = Real.cos θ := by
      rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    have hne : Complex.normSq (Complex.exp (I * θ)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
      simp
    simp [Complex.normSq_mul, hne, Complex.mul_re, he, Complex.normSq_ofReal]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity)]
  rw [hn, mul_pow, ← Real.exp_nat_mul]
  have h := Real.cos_le_one_sub_mul_cos_sq hθ
  have hc : 0 < (q + b) ^ 2 * Real.pi ^ 2 := by positivity
  calc
    _ ≤ (q + b) ^ 2 * (1 + 2 * (-(2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)) * θ ^ 2)) := by
      have he : (q + b) ^ 2 *
          (1 + 2 * (-(2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)) * θ ^ 2)) =
          (q + b) ^ 2 - 2 * q * b * (2 / Real.pi ^ 2 * θ ^ 2) := by
        field_simp [hc.ne', (by positivity : 0 < q + b).ne', Real.pi_ne_zero]
        ring
      rw [he]
      apply sub_le_sub_left
      gcongr
      linarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [Nat.cast_ofNat, add_comm] using
        Real.add_one_le_exp (2 * (-(2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)) * θ ^ 2))

private lemma norm_pow_sub_le (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (z : ℂ)
    (hz : ‖z - q‖ ≤ b) (m : ℕ) :
    ‖z ^ m - (q : ℂ) ^ m‖ ≤ (q + b) ^ m - q ^ m := by
  have hz' : ‖z‖ ≤ q + b := calc
    ‖z‖ = ‖z - q + q‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - q‖ + ‖(q : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by simpa [Real.norm_of_nonneg hq, add_comm] using add_le_add_right hz q
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : z ^ (m + 1) - (q : ℂ) ^ (m + 1) =
        z * (z ^ m - q ^ m) + (z - q) * q ^ m := by ring
    rw [hsum, pow_succ (q + b), pow_succ q]
    calc
      _ ≤ ‖z * (z ^ m - (q : ℂ) ^ m)‖ + ‖(z - q) * (q : ℂ) ^ m‖ := norm_add_le _ _
      _ ≤ (q + b) * ((q + b) ^ m - q ^ m) + b * q ^ m := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq]
        gcongr
      _ = _ := by ring

private noncomputable def damping (p q a s : ℝ) : ℝ :=
  let b := p * Real.exp (a * s)
  2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)

private lemma kernel_norm_le (k : ℕ) (hk : 1 ≤ k) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (s θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    let a := q ^ (k - 1)
    ‖kernel k p q a s θ‖ ≤ ‖kernel k p q a s 0‖ *
      Real.exp (-(damping p q a s) * θ ^ 2) := by
  dsimp only
  let a := q ^ (k - 1)
  let b := p * Real.exp (a * s)
  let w : ℂ := ((a * s : ℝ) : ℂ) + I * θ
  let z := factor p q w
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hz : z = q + b * Complex.exp (I * θ) := by
    dsimp [z, factor, w, b]
    rw [Complex.exp_add]
    push_cast
    rw [mul_assoc]
  have hz' : ‖z - q‖ = b := by rw [hz, add_sub_cancel_left, norm_mul, norm_exp]; simp [hb.le]
  have hbound := factor_norm_le q b θ hq hb hθ
  rw [← hz] at hbound
  have hcenter : ‖Complex.exp (-(((a * s : ℝ) : ℂ) + w))‖ =
      Real.exp (-(a * s + a * s)) := by rw [Complex.norm_exp]; simp [w]
  -- Factor out one copy of the binomial generating function for the Gaussian bound.
  have htriangle : ‖z ^ (k - 1) + a * (Complex.exp s - 1)‖ ≤
      (q + b) ^ (k - 1) + a * (Real.exp s - 1) := by
    have hsimp : z ^ (k - 1) + a * (Complex.exp s - 1) =
        (z ^ (k - 1) - (q : ℂ) ^ (k - 1)) + a * Complex.exp s := by
      rw [show (a : ℂ) = (q : ℂ) ^ (k - 1) by simp [a]]
      ring
    rw [hsimp]
    calc
      _ ≤ ‖z ^ (k - 1) - (q : ℂ) ^ (k - 1)‖ + ‖(a : ℂ) * Complex.exp s‖ := norm_add_le _ _
      _ ≤ ((q + b) ^ (k - 1) - q ^ (k - 1)) + a * Real.exp s := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg ha.le, norm_exp, ofReal_re]
        gcongr
        exact norm_pow_sub_le q b hq.le hb.le z hz'.le (k - 1)
      _ = _ := by dsimp [a]; ring
  have hpoz : 0 ≤ (q + b) ^ (k - 1) + a * (Real.exp s - 1) := le_trans (norm_nonneg _) htriangle
  have hfact (v : ℂ) : v ^ k + a * (Complex.exp s - 1) * v =
      v * (v ^ (k - 1) + a * (Complex.exp s - 1)) := by
    rw [mul_add, ← pow_succ', Nat.sub_add_cancel hk]
    ring
  have hzero : ‖kernel k p q a s 0‖ =
      Real.exp (-(a * s + a * s)) * (q + b) *
        ((q + b) ^ (k - 1) + a * (Real.exp s - 1)) := by
    unfold kernel
    simp only [ofReal_zero, mul_zero, add_zero, hfact, norm_mul, norm_exp, neg_re,
      add_re, ofReal_re]
    have hreal : factor p q ((a * s : ℝ) : ℂ) = ((q + b : ℝ) : ℂ) := by
      simp [factor, b, Complex.ofReal_exp]
    rw [hreal, ← ofReal_exp, ← ofReal_one, ← ofReal_sub, ← ofReal_mul, ← ofReal_pow,
      ← ofReal_add, norm_real, norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ q + b),
      Real.norm_of_nonneg hpoz, mul_assoc]
  change ‖Complex.exp (-(((a * s : ℝ) : ℂ) + w)) *
    (z ^ k + a * (Complex.exp s - 1) * z)‖ ≤ _
  rw [hfact, norm_mul, norm_mul, hcenter, hzero]
  change _ ≤ (_ : ℝ) * Real.exp (-(2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)) * θ ^ 2)
  calc
    _ ≤ Real.exp (-(a * s + a * s)) *
        (((q + b) * Real.exp (-(2 * q * b / ((q + b) ^ 2 * Real.pi ^ 2)) * θ ^ 2)) *
          ((q + b) ^ (k - 1) + a * (Real.exp s - 1))) := by
      gcongr
    _ = _ := by ring

private noncomputable def angularIntegral (k : ℕ) (p q a : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  ∫ θ : ℝ in -Real.pi..Real.pi, kernel k p q a s θ ^ n * Complex.exp (I * θ)

private lemma scale_sq (n : ℕ) : scale n ^ 2 = (n : ℝ)⁻¹ := by
  rw [scale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

private lemma angularIntegral_scale_change (k : ℕ) (p q a : ℝ) (n : ℕ) (hn : 0 < n)
    (s : ℝ) :
    (∫ x : ℝ in Set.Ioc (-Real.pi * Real.sqrt n) (Real.pi * Real.sqrt n),
      kernel k p q a s (scale n * x) ^ n * Complex.exp (I * ((scale n * x : ℝ) : ℂ))) =
      (Real.sqrt n : ℂ) * angularIntegral k p q a n s := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs' : 0 < scale n := inv_pos.2 hs
  let G : ℝ → ℂ := fun θ => kernel k p q a s θ ^ n * Complex.exp (I * θ)
  have hends (r : ℝ) : scale n * (r * Real.sqrt n) = r := by
    rw [mul_left_comm, scale, inv_mul_cancel₀ hs.ne', mul_one]
  have horder : -Real.pi * Real.sqrt n ≤ Real.pi * Real.sqrt n := by
    linarith [mul_pos Real.pi_pos hs]
  calc
    _ = ∫ x : ℝ in (-Real.pi * Real.sqrt n)..(Real.pi * Real.sqrt n), G (scale n * x) :=
      (intervalIntegral.integral_of_le (f := fun x => G (scale n * x)) horder).symm
    _ = (scale n)⁻¹ • ∫ x : ℝ in
          (scale n * (-Real.pi * Real.sqrt n))..(scale n * (Real.pi * Real.sqrt n)), G x :=
      intervalIntegral.integral_comp_mul_left G hs'.ne'
    _ = _ := by
      rw [hends, hends]
      change (((scale n)⁻¹ : ℝ) : ℂ) * angularIntegral k p q a n s = _
      rw [scale, inv_inv]

private lemma gaussian_integral (v q t : ℝ) :
    (∫ x : ℝ, Complex.exp (((v * t ^ 2 / 2 - q * x ^ 2 / 2 : ℝ) : ℂ))) =
      ((Real.exp (v * t ^ 2 / 2) * Real.sqrt (Real.pi / (q / 2)) : ℝ) : ℂ) := by
  calc
    _ = ∫ x : ℝ, ((Real.exp (v * t ^ 2 / 2) * Real.exp (-(q / 2) * x ^ 2) : ℝ) : ℂ) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      dsimp only
      rw [ofReal_mul, ofReal_exp, ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by rw [integral_complex_ofReal, integral_const_mul, integral_gaussian]

private lemma angularIntegral_tendsto (k : ℕ) (hk : 2 ≤ k) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : q + p = 1) (hkp : (k : ℝ) * p = 1) (t : ℝ) :
    let a := q ^ (k - 1)
    let v := a - (1 + q) * a ^ 2
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) * angularIntegral k p q a n (scale n * t)) atTop
      (𝓝 ((Real.exp (v * t ^ 2 / 2) * Real.sqrt (Real.pi / (q / 2)) : ℝ) : ℂ)) := by
  dsimp only
  let a := q ^ (k - 1)
  let v := a - (1 + q) * a ^ 2
  let c := damping p q a 0 / 2
  let B := Real.exp (v * t ^ 2 / 2) + 1
  -- After scaling the integration variable, extend the integrand by zero on ℝ.
  let S (n : ℕ) := Set.Ioc (-Real.pi * Real.sqrt n) (Real.pi * Real.sqrt n)
  let E (n : ℕ) (x : ℝ) := kernel k p q a (scale n * t) (scale n * x) ^ n *
    Complex.exp (I * ((scale n * x : ℝ) : ℂ))
  have hc : 0 < c := by
    dsimp only [c, damping]
    positivity
  have hd : Tendsto (fun n => damping p q a (scale n * t)) atTop (𝓝 (damping p q a 0)) := by
    have hcont : ContinuousAt (damping p q a) 0 := by
      unfold damping
      fun_prop (disch := positivity)
    exact hcont.tendsto.comp (by simpa using scale_tendsto.mul_const t)
  have hboundC : ∀ᶠ n in atTop, c ≤ damping p q a (scale n * t) := by
    refine hd.eventually (le_mem_nhds (show c < damping p q a 0 from ?_))
    dsimp [c] at hc ⊢
    linarith
  have hboundB : ∀ᶠ n in atTop, ‖kernel k p q a (scale n * t) 0 ^ n‖ ≤ B := by
    have h := (kernel_pow_tendsto k hk p q a hpq hkp t 0).norm
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero, norm_exp, ofReal_re] at h
    exact h.eventually (ge_mem_nhds (by dsimp [B, v]; linarith))
  have hb : ∀ᶠ n in atTop, ∀ᵐ x : ℝ, ‖(S n).indicator (E n) x‖ ≤ B * Real.exp (-c * x ^ 2) := by
    filter_upwards [hboundB, hboundC, eventually_gt_atTop (0 : ℕ)] with n hB hC hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ S n
    · rw [Set.indicator_of_mem hx]
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
      have hθ : |scale n * x| ≤ Real.pi := by
        have hx' : -Real.pi * Real.sqrt n < x ∧ x ≤ Real.pi * Real.sqrt n := hx
        rw [abs_le, scale, inv_mul_eq_div, le_div_iff₀ hs, div_le_iff₀ hs]
        exact ⟨hx'.1.le, hx'.2⟩
      have hkn := kernel_norm_le k (by omega) p q hp hq (scale n * t) (scale n * x) hθ
      have hExp : Real.exp (-(damping p q a (scale n * t)) * (scale n * x) ^ 2) ≤
          Real.exp (-c * (scale n * x) ^ 2) := by
        rw [Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_right (neg_le_neg hC) (sq_nonneg _)
      have hnscale : (n : ℝ) * scale n ^ 2 = 1 := by rw [scale_sq, mul_inv_cancel₀ hn'.ne']
      have hpow : Real.exp (-c * (scale n * x) ^ 2) ^ n = Real.exp (-c * x ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        calc (n : ℝ) * (-c * (scale n * x) ^ 2) =
            ((n : ℝ) * scale n ^ 2) * (-c * x ^ 2) := by ring
          _ = _ := by rw [hnscale, one_mul]
      have hcomp : ‖kernel k p q a (scale n * t) (scale n * x)‖ ≤
          ‖kernel k p q a (scale n * t) 0‖ * Real.exp (-c * (scale n * x) ^ 2) :=
        hkn.trans (mul_le_mul_of_nonneg_left hExp (norm_nonneg _))
      dsimp [E]
      simp only [norm_mul, norm_exp, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero,
        sub_self, Real.exp_zero, mul_one, norm_pow]
      refine (pow_le_pow_left₀ (norm_nonneg _) hcomp _).trans ?_
      rw [mul_pow, hpow, ← norm_pow]
      exact mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hx, norm_zero]
      dsimp [B]
      positivity
  have hlim : ∀ x : ℝ, Tendsto (fun n => (S n).indicator (E n) x) atTop
      (𝓝 (Complex.exp (((v * t ^ 2 / 2 - q * x ^ 2 / 2 : ℝ) : ℂ)))) := by
    intro x
    have hs : Tendsto (fun n : ℕ => Real.pi * Real.sqrt n) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop Real.pi_pos
    have hx : ∀ᶠ n in atTop, x ∈ S n := by
      filter_upwards [hs.eventually (eventually_gt_atTop |x|)] with n hn
      exact ⟨by linarith [neg_abs_le x], (le_abs_self x).trans hn.le⟩
    have hphase : Tendsto (fun n => Complex.exp (I * ((scale n * x : ℝ) : ℂ))) atTop (𝓝 1) := by
      simpa [Function.comp_def] using (Complex.continuous_exp.tendsto _).comp
        (tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto _ |>.comp
          (scale_tendsto.mul_const x)))
    have h := (kernel_pow_tendsto k hk p q a hpq hkp t x).mul hphase
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hx] with n hn
    rw [Set.indicator_of_mem hn]
  have hm : ∀ᶠ n in atTop, AEStronglyMeasurable ((S n).indicator (E n)) volume := by
    refine Eventually.of_forall fun n =>
      (Measurable.indicator ?_ measurableSet_Ioc).aestronglyMeasurable
    apply Continuous.measurable
    unfold E kernel factor
    fun_prop
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => B * Real.exp (-c * x ^ 2)) hm hb
    ((integrable_exp_neg_mul_sq hc).const_mul B) (Eventually.of_forall hlim)
  rw [gaussian_integral] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (integral_indicator measurableSet_Ioc).trans
    (angularIntegral_scale_change k p q a n hn (scale n * t))

private lemma integral_polynomial (P : Polynomial ℂ) (r : ℂ) (d : ℕ) :
    (∫ θ : ℝ in -Real.pi..Real.pi,
      P.eval (r * Complex.exp (I * θ)) * Complex.exp (-(I * θ * (d : ℂ)))) =
      (2 * Real.pi : ℂ) * r ^ d * P.coeff d := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval_add, add_mul, Polynomial.coeff_add]
    rw [intervalIntegral.integral_add, hP, hQ, mul_add]
    all_goals
      apply Continuous.intervalIntegrable
      exact ((Polynomial.continuous _).comp (by fun_prop)).mul (by fun_prop)
  | monomial m z =>
    have hpoint (θ : ℝ) :
        (Polynomial.monomial m z).eval (r * Complex.exp (I * θ)) *
            Complex.exp (-(I * θ * (d : ℂ))) =
          (z * r ^ m) * Complex.exp (((((m : ℝ) - d) * θ : ℝ) : ℂ) * I) := by
      rw [Polynomial.eval_monomial, mul_pow, ← Complex.exp_nat_mul]
      rw [← mul_assoc, mul_assoc z, ← mul_assoc z, mul_assoc (z * r ^ m), ← Complex.exp_add]
      push_cast
      congr 2
      ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul]
    let j : ℤ := (m : ℤ) - d
    have hj : (j : ℝ) = (m : ℝ) - d := by push_cast [j]; rfl
    rw [← hj]
    by_cases h : m = d
    · subst m
      simp only [j, sub_self, Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
        intervalIntegral.integral_const, Complex.real_smul, Polynomial.coeff_monomial,
        Finsupp.single_eq_same]
      push_cast
      ring
    · have hj' : (j : ℝ) ≠ 0 := by
        exact_mod_cast (show j ≠ 0 by dsimp [j]; omega)
      simp_rw [mul_comm (j : ℝ)]
      have hshift := intervalIntegral.integral_comp_mul_right (a := -Real.pi) (b := Real.pi)
        (fun x : ℝ => Complex.exp ((x : ℂ) * I)) hj'
      rw [hshift, neg_mul, integral_exp_mul_I_eq_sin]
      simp [mul_comm Real.pi, Real.sin_int_mul_pi, Polynomial.coeff_monomial, h]

private lemma angularIntegral_eq (k : ℕ) (hk : 1 ≤ k) (p q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (s : ℝ) :
    let a := q ^ (k - 1)
    angularIntegral k p q a n s =
      ((2 * Real.pi : ℂ) * ((q : ℂ) ^ k) ^ n * (((p / q : ℝ) : ℂ) ^ (n - 1))) *
        (Complex.exp ((-(a * s * ((n : ℝ) + 1)) : ℝ) : ℂ) *
          ((shape k (Complex.exp s)) ^ n).coeff (n - 1)) := by
  dsimp only
  let a := q ^ (k - 1)
  let r := p / q
  let ρ := r * Real.exp (a * s)
  let P := shape k (Complex.exp s) ^ n
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpower : (q : ℂ) ^ k = (a : ℂ) * q := by
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    simp [a]
  have hcut : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hpoint (θ : ℝ) : kernel k p q a s θ ^ n * Complex.exp (I * θ) =
      (((q : ℂ) ^ k) ^ n * Complex.exp ↑(-(a * s * (2 * (n : ℝ)))) : ℂ) *
        (P.eval ((ρ : ℂ) * Complex.exp (I * θ)) *
          Complex.exp (-(I * θ * ((n - 1 : ℕ) : ℂ)))) := by
    let z := (ρ : ℂ) * Complex.exp (I * θ)
    let w : ℂ := ((a * s : ℝ) : ℂ) + I * θ
    have hf : factor p q w = (q : ℂ) * (1 + z) := by
      dsimp [z, w, ρ, r, factor]
      rw [Complex.exp_add]
      push_cast
      field_simp
    have heval : factor p q w ^ k + a * (Complex.exp s - 1) * factor p q w =
        (q : ℂ) ^ k * (shape k (Complex.exp s)).eval z := by
      rw [hf, mul_pow]
      simp only [shape, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]
      rw [hpower]
      ring
    change (Complex.exp (-(((a * s : ℝ) : ℂ) + w)) *
      (factor p q w ^ k + a * (Complex.exp s - 1) * factor p q w)) ^ n *
      Complex.exp (I * θ) = _
    rw [heval, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    have hexp : Complex.exp ((n : ℂ) * -(((a * s : ℝ) : ℂ) + w)) *
        Complex.exp (I * θ) =
        Complex.exp ((-(a * s * (2 * (n : ℝ))) : ℝ) : ℂ) *
          Complex.exp (-(I * θ * ((n - 1 : ℕ) : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add, hcut]
      congr 1
      dsimp [w]
      push_cast
      ring
    rw [show P.eval z = ((shape k (Complex.exp s)).eval z) ^ n by simp [P]]
    change _ = _ * (((shape k (Complex.exp s)).eval z) ^ n * _)
    linear_combination
      (((q : ℂ) ^ k) ^ n * ((shape k (Complex.exp s)).eval z) ^ n) * hexp
  change (∫ θ : ℝ in -Real.pi..Real.pi, kernel k p q a s θ ^ n * Complex.exp (I * θ)) = _
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ)]
  rw [intervalIntegral.integral_const_mul, integral_polynomial]
  have hρ : (ρ : ℂ) ^ (n - 1) =
      (r : ℂ) ^ (n - 1) * Complex.exp (((n - 1 : ℕ) : ℂ) * ((a * s : ℝ) : ℂ)) := by
    rw [show ρ = r * Real.exp (a * s) by rfl, ofReal_mul, mul_pow,
      ofReal_exp, ← Complex.exp_nat_mul]
  rw [hρ]
  change _ = (((2 * Real.pi : ℂ) * ((q : ℂ) ^ k) ^ n * (r : ℂ) ^ (n - 1))) *
    (Complex.exp ((-(a * s * ((n : ℝ) + 1)) : ℝ) : ℂ) * P.coeff (n - 1))
  have he :
      Complex.exp ((-(a * s * (2 * (n : ℝ))) : ℝ) : ℂ) *
          Complex.exp (((n - 1 : ℕ) : ℂ) * ((a * s : ℝ) : ℂ)) =
        Complex.exp ((-(a * s * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, hcut]
    congr 1
    push_cast
    ring
  linear_combination ((2 * Real.pi : ℂ) * ((q : ℂ) ^ k) ^ n *
    (r : ℂ) ^ (n - 1) * P.coeff (n - 1)) * he

private lemma row_eval (T : ℕ → ℕ → ℕ) (n : ℕ) (y : ℂ) :
    (row T n).eval y = ∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℂ) * y ^ ℓ := by
  classical
  simp [row, Polynomial.eval_finsetSum]

private lemma shortChord_mgf_tendsto (k : ℕ) (hk : 2 ≤ k) (T : ℕ → ℕ → ℕ)
    (h00 : T 0 0 = 1) (h0 : ∀ ℓ, 0 < ℓ → T 0 ℓ = 0)
    (hrec : ∀ n ℓ, T (n + 1) ℓ =
      convolution k T n ℓ - T n ℓ + if ℓ = 0 then 0 else T n (ℓ - 1))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : q + p = 1) (hkp : (k : ℝ) * p = 1)
    (u : ℝ) :
    let a := q ^ (k - 1)
    let v := a - (1 + q) * a ^ 2
    Tendsto (fun n : ℕ =>
      (∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ) *
        Real.exp (scale n * u * ((ℓ : ℝ) - a * n))) /
        ∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ)) atTop
      (𝓝 (Real.exp (v * u ^ 2 / 2))) := by
  dsimp only
  let a := q ^ (k - 1)
  let v := a - (1 + q) * a ^ 2
  let J (n : ℕ) (s : ℝ) := (Real.sqrt n : ℂ) * angularIntegral k p q a n s
  let C (n : ℕ) := (Real.sqrt n : ℂ) * ((2 * Real.pi : ℂ) * ((q : ℂ) ^ k) ^ n *
    (((p / q : ℝ) : ℂ) ^ (n - 1))) * (n : ℂ)
  let g := Real.sqrt (Real.pi / (q / 2))
  have hg : 0 < g := by dsimp [g]; positivity
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : Tendsto (fun n : ℕ => J n (scale n * u)) atTop
      (𝓝 ((Real.exp (v * u ^ 2 / 2) * g : ℝ) : ℂ)) :=
    angularIntegral_tendsto k hk p q hp hq hpq hkp u
  have hJ0 : Tendsto (fun n : ℕ => J n 0) atTop (𝓝 (g : ℂ)) := by
    simpa [J, g] using angularIntegral_tendsto k hk p q hp hq hpq hkp 0
  have hExp : Tendsto (fun n : ℕ => Complex.exp (((a * (scale n * u) : ℝ) : ℂ))) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => a * (scale n * u)) atTop (𝓝 0) := by
      simpa using (scale_tendsto.mul_const u).const_mul a
    simpa [Function.comp_def] using (Complex.continuous_exp.tendsto (0 : ℂ)).comp
      ((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp ht)
  have hratio : Tendsto
      (fun n : ℕ => Complex.exp (((a * (scale n * u) : ℝ) : ℂ)) * J n (scale n * u) / J n 0)
      atTop (𝓝 ((Real.exp (v * u ^ 2 / 2) : ℝ) : ℂ)) := by
    convert (hExp.mul hJ).div hJ0 hg' using 1
    rw [one_mul, ofReal_mul, mul_div_cancel_right₀ _ hg']
  have hJrow (n : ℕ) (hn : 0 < n) (s : ℝ) :
      J n s = C n *
        (Complex.exp ((-(a * s * ((n : ℝ) + 1)) : ℝ) : ℂ) * (row T n).eval (Complex.exp s)) := by
    have h := angularIntegral_eq k (by omega) p q hq n hn s
    dsimp only at h
    dsimp [J, C]
    rw [h, ← row_coefficient k hk T h00 h0 hrec _ n hn]
    ring
  have hEq : ∀ᶠ n in atTop,
      Complex.exp (((a * (scale n * u) : ℝ) : ℂ)) * J n (scale n * u) / J n 0 =
        (((∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ) *
          Real.exp (scale n * u * ((ℓ : ℝ) - a * n))) /
          ∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ)) : ℂ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    have hC : C n ≠ 0 := by
      have hC' : C n = (((Real.sqrt n * (2 * Real.pi * (q ^ k) ^ n *
          (p / q) ^ (n - 1)) * n : ℝ) : ℂ)) := by simp [C]
      rw [hC', ofReal_ne_zero]
      positivity
    let s := scale n * u
    change Complex.exp ((a * s : ℝ) : ℂ) * J n s / J n 0 = _
    rw [hJrow n hn s, hJrow n hn 0]
    simp only [mul_zero, zero_mul, ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
    rw [show Complex.exp ((a * s : ℝ) : ℂ) *
        (C n * (Complex.exp ((-(a * s * ((n : ℝ) + 1)) : ℝ) : ℂ) *
          (row T n).eval (Complex.exp s))) =
        C n * ((Complex.exp ((a * s : ℝ) : ℂ) *
          Complex.exp ((-(a * s * ((n : ℝ) + 1)) : ℝ) : ℂ)) *
          (row T n).eval (Complex.exp s)) by ring,
      mul_div_mul_left _ _ hC, ← Complex.exp_add, row_eval, row_eval]
    push_cast
    simp only [one_pow, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
    congr 2
    dsimp [s]
    push_cast
    ring
  have hreal := (Complex.continuous_re.tendsto _).comp (hratio.congr' hEq)
  simpa only [Function.comp_def, ← Complex.ofReal_div, Complex.ofReal_re] using hreal

private lemma variance_pos (k : ℕ) (hk : 2 ≤ k) :
    let q : ℝ := ((k - 1 : ℕ) : ℝ) / k
    let a := q ^ (k - 1)
    0 < a - (1 + q) * a ^ 2 := by
  dsimp only
  let j : ℝ := ((k - 1 : ℕ) : ℝ)
  let q : ℝ := j / k
  let a := q ^ (k - 1)
  change 0 < a - (1 + q) * a ^ 2
  have hj : 0 < j := by dsimp [j]; exact_mod_cast (by omega : 0 < k - 1)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hjk : j + 1 = (k : ℝ) := by
    dsimp [j]
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  have hq : 0 < q := div_pos hj hkR
  have hq1 : q < 1 := (div_lt_one hkR).2 (by linarith)
  have ha : 0 < a := pow_pos hq _
  have hinv : q⁻¹ = 1 + j⁻¹ := by
    dsimp [q]
    rw [inv_div, ← hjk, add_div, div_self hj.ne', one_div]
  have hab : a ≤ 1 / 2 := by
    have hinv_nonneg : 0 ≤ j⁻¹ := inv_nonneg.mpr hj.le
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ j⁻¹ by linarith) (k - 1)
    change 1 + j * j⁻¹ ≤ (1 + j⁻¹) ^ (k - 1) at h
    rw [mul_inv_cancel₀ hj.ne', ← hinv, inv_pow] at h
    have h' : 2 ≤ a⁻¹ := by linarith
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
      have hm := mul_le_mul_of_nonneg_right h' ha.le
      rwa [inv_mul_cancel₀ ha.ne', mul_comm 2 a] at hm)
  have hv : (1 + q) * a < 1 := calc
    (1 + q) * a ≤ (1 + q) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    _ < 1 := by linarith
  have := mul_pos ha (sub_pos.mpr hv)
  nlinarith

private lemma variance_eq (k : ℕ) (hk : 2 ≤ k) :
    let q : ℝ := ((k - 1 : ℕ) : ℝ) / k
    let a := q ^ (k - 1)
    q ^ (2 * k) * (k : ℝ) / (((k - 1 : ℕ) : ℝ) ^ 2) *
      (1 - 2 * (k : ℝ) + ((k - 1 : ℕ) : ℝ) * ((k : ℝ) / ((k - 1 : ℕ) : ℝ)) ^ k) =
      a - (1 + q) * a ^ 2 := by
  dsimp only
  let j : ℝ := ((k - 1 : ℕ) : ℝ)
  let q : ℝ := j / k
  let a := q ^ (k - 1)
  change q ^ (2 * k) * (k : ℝ) / j ^ 2 *
    (1 - 2 * (k : ℝ) + j * ((k : ℝ) / j) ^ k) = a - (1 + q) * a ^ 2
  have hj : 0 < j := by dsimp [j]; exact_mod_cast (by omega : 0 < k - 1)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hjk : j + 1 = (k : ℝ) := by
    dsimp [j]
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    ring
  have hq : 0 < q := div_pos hj hkR
  have ha : 0 < a := pow_pos hq _
  have hpow : q ^ k = a * q := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  rw [Nat.mul_comm 2 k, pow_mul, show (k : ℝ) / j = q⁻¹ by simp [q], inv_pow, hpow]
  have hqK : (k : ℝ) * q = j := by
    dsimp [q]
    field_simp
  have hconst : (a * q) ^ 2 * (k : ℝ) / j ^ 2 = a ^ 2 / (k : ℝ) := by
    rw [← hqK]
    field_simp [hq.ne', hkR.ne']
  have hlast : a ^ 2 / (k : ℝ) * (j * (a * q)⁻¹) = a := by
    rw [← hqK]
    field_simp [ha.ne', hq.ne', hkR.ne']
  have hqplus : q + (k : ℝ)⁻¹ = 1 := by
    dsimp [q]
    rw [← one_div, ← add_div, hjk, div_self hkR.ne']
  rw [hconst, mul_add, hlast]
  calc
    _ = a - (2 - (k : ℝ)⁻¹) * a ^ 2 := by
      field_simp [hkR.ne']
      ring
    _ = _ := by rw [show (2 - (k : ℝ)⁻¹) = 1 + q by linarith]

end MetaMathlibExt.noncrossingLinearKChordDiagram_shortChords_asymptoticallyNormal

namespace MetaMathlibExt

open MetaMathlibExt.noncrossingLinearKChordDiagram_shortChords_asymptoticallyNormal in
/--
The short-chord count in a uniformly chosen non-crossing linear `k`-chord diagram is
asymptotically normal with the stated mean and variance.

Source: Donovan Young, "Linear k-Chord Diagrams", Journal of Integer Sequences 23 (2020),
Article 20.9.1, Theorem lines 1014-1024 (§6.1),
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Young/young5.tex>.
-/
public theorem noncrossingLinearKChordDiagram_shortChords_asymptoticallyNormal
    (k : ℕ) (hk : 2 ≤ k) (T : ℕ → ℕ → ℕ)
    (hT : T 0 0 = 1 ∧
      (∀ ℓ, 0 < ℓ → T 0 ℓ = 0) ∧
      ∀ n ℓ,
        T (n + 1) ℓ =
          (∑ m : Fin k → Fin (n + 1),
            ∑ s : Fin k → Fin (ℓ + 1),
              if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (s i : ℕ)) = ℓ then
                ∏ i, T (m i) (s i)
              else 0) - T n ℓ + if ℓ = 0 then 0 else T n (ℓ - 1)) :
    let mean : ℕ → ℝ := fun n =>
      (((((k - 1 : ℕ) : ℝ) / (k : ℝ)) ^ (k - 1)) * n)
    let variance : ℕ → ℝ := fun n =>
      (((((k - 1 : ℕ) : ℝ) / (k : ℝ)) ^ (2 * k)) *
        (k : ℝ) / (((k - 1 : ℕ) : ℝ) ^ 2) *
        (1 - 2 * (k : ℝ) +
          ((k - 1 : ℕ) : ℝ) *
            (((k : ℝ) / ((k - 1 : ℕ) : ℝ)) ^ k)) * n)
    ∀ t : ℝ,
      Tendsto
        (fun n : ℕ =>
          (∑ ℓ ∈ Finset.range (n + 1),
              (T n ℓ : ℝ) *
                Real.exp
                  (t * (((ℓ : ℝ) - mean n) / Real.sqrt (variance n)))) /
            ∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ))
        atTop
        (nhds (Real.exp (t ^ 2 / 2))) := by
  dsimp only
  intro t
  rw [variance_eq k hk]
  obtain ⟨h00, h0, hrec⟩ := hT
  let p : ℝ := 1 / k
  let q : ℝ := ((k - 1 : ℕ) : ℝ) / k
  let a : ℝ := q ^ (k - 1)
  let v : ℝ := a - (1 + q) * a ^ 2
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by
    apply div_pos _ hkR
    exact_mod_cast (by omega : 0 < k - 1)
  have hpq : q + p = 1 := by
    dsimp [p, q]
    rw [← add_div, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, sub_add_cancel, div_self hkR.ne']
  have hkp : (k : ℝ) * p = 1 := by
    exact mul_one_div_cancel hkR.ne'
  have hv : 0 < v := variance_pos k hk
  have h := shortChord_mgf_tendsto k hk T h00 h0 hrec p q hp hq hpq hkp (t / Real.sqrt v)
  change Tendsto _ atTop (𝓝 (Real.exp (v * (t / Real.sqrt v) ^ 2 / 2))) at h
  have hexp : v * (t / Real.sqrt v) ^ 2 / 2 = t ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt hv.le]
    field_simp
  rw [hexp] at h
  refine h.congr fun n => ?_
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 2
  rw [Real.sqrt_mul hv.le, scale]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end MetaMathlibExt

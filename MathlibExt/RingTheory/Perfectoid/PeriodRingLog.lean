/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/BergerBst.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source file at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.PowerSeriesEvalMap
public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingBasic
public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRing
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# Logarithms in `B_dR^+`

For `y` in the kernel of Fontaine's map `θ` with `p` inverted, the logarithm series
`log(1 + X) = Σ_{n ≥ 1} (-1)^(n+1) X^n / n` converges at `y` in `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p`,
the completion along that kernel; its value is `log(1 + y)` (`PadicComplexInt.logOneAdd`). We
show that `log` is additive: `log((1 + y)(1 + z)) = log(1 + y) + log(1 + z)`
(`PadicComplexInt.logOneAdd_add`). Its special values are

* `log [ε] = log(1 + ([ε] - 1))` for `ε ∈ 𝓞_ℂ_[p]♭` with `ε♯ = 1`
  (`PadicComplexInt.logTeichmuller`), which is nonzero for `ε ≠ 1`
  (`PadicComplexInt.logTeichmuller_ne_zero`); for `ε = (1, ζ_p, ζ_{p²}, …)` this is Fontaine's
  period `t` of `ℤ_p(1)`;
* `log [p̃] = log([p̃]/p) = log(1 - ξ/p)` (`PadicComplexInt.logPTilde`), where `p̃ = p♭` is a
  chosen element of the tilt with `p̃♯ = p` (`PadicComplexInt.pFlat`) and `ξ = p - [p̃]`.

These are the logarithms of J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223
(1994), Exposé II, §1.5.4 (the period `t`) and §4.3.1 (the element `log([u₀]/p)`).

## Proof of additivity

Modulo `(ker θ)^N`, both sides are values of the truncated logarithm `P_N`, and the polynomial
identity `T^N ∣ P_N(Y + Z + YZ) - P_N(Y) - P_N(Z)` in `A[T]`, for `Y = yT` and `Z = zT`, holds
because the derivatives of both sides agree modulo `T^(N-1)` and the constant terms vanish.
Evaluating at `T = 1` inside the Rees algebra of `ker θ` gives the congruence.
-/

@[expose] public noncomputable section

open Ideal WittVector PowerSeries

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p

/-! ### The element `ξ/p` -/

/-- The element `ξ/p` of `W(𝓞_ℂ_[p]♭)[1/p]`, where `ξ = p - [p♭]`. -/
def xiDivP : 𝔸ₚ :=
  algebraMap 𝔸 𝔸ₚ (xi p) * algebraMap ℚ_[p] 𝔸ₚ (p : ℚ_[p])⁻¹

/-- `k · k⁻¹ = 1` in `W(𝓞_ℂ_[p]♭)[1/p]` for a nonzero natural number `k`, where `k⁻¹` is the
image of `(k : ℚ_[p])⁻¹`. -/
theorem natCast_mul_algebraMap_inv {k : ℕ} (hk : k ≠ 0) :
    (k : 𝔸ₚ) * algebraMap ℚ_[p] 𝔸ₚ (k : ℚ_[p])⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] 𝔸ₚ) k, ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk), map_one]

/-- `p · (ξ/p) = ξ`. -/
theorem natCast_mul_xiDivP : (p : 𝔸ₚ) * xiDivP p = algebraMap 𝔸 𝔸ₚ (xi p) := by
  rw [xiDivP, mul_left_comm, natCast_mul_algebraMap_inv p hp.out.ne_zero, mul_one]

/-- `ξ/p` lies in the kernel of `θ` with `p` inverted. -/
theorem xiDivP_mem_ker : xiDivP p ∈ 𝕀 :=
  Ideal.mul_mem_right _ _ (algebraMap_mem_ker_fontaineThetaInvertP p (fontaineTheta_xi p))

/-- `[p♭]/p - 1 = -ξ/p` in `W(𝓞_ℂ_[p]♭)[1/p]`. -/
theorem teichmuller_pFlat_div_sub_one :
    algebraMap 𝔸 𝔸ₚ (teichmuller p (pFlat p)) * algebraMap ℚ_[p] 𝔸ₚ (p : ℚ_[p])⁻¹ - 1 =
      -xiDivP p := by
  have h : teichmuller p (pFlat p) = (p : 𝔸) - xi p := by rw [xi, sub_sub_cancel]
  rw [h, map_sub, map_natCast, xiDivP]
  linear_combination natCast_mul_algebraMap_inv p hp.out.ne_zero

/-! ### The logarithm series -/

/-- The logarithm series `log(1 + X) = Σ_{n ≥ 1} (-1)^(n+1) X^n / n` over
`W(𝓞_ℂ_[p]♭)[1/p]`, a `ℚ_[p]`-algebra. -/
def logSeries : 𝔸ₚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) * algebraMap ℚ_[p] 𝔸ₚ (n : ℚ_[p])⁻¹

/-- **`log(1 + y)`** for `y` in the kernel of `θ` with `p` inverted: the value in `B_dR^+` of the
logarithm series at `y`. -/
def logOneAdd {y : 𝔸ₚ} (hy : y ∈ 𝕀) : 𝔹⁺ :=
  evalBDeRhamPlus p hy (logSeries p)

/-! ### Additivity of the logarithm -/

/-- The truncated logarithm `P_N = Σ_{1 ≤ n < N} (-1)^(n+1) X^n / n`. -/
private abbrev logPoly (N : ℕ) : Polynomial 𝔸ₚ := trunc N (logSeries p)

/-- `P_{M+1}' = Σ_{i < M} (-X)^i`. -/
private theorem derivative_logPoly (M : ℕ) :
    Polynomial.derivative (logPoly p (M + 1)) =
      ∑ i ∈ Finset.range M, Polynomial.C ((-1 : 𝔸ₚ) ^ i) * Polynomial.X ^ i := by
  ext m
  rw [Polynomial.coeff_derivative, coeff_trunc, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range M) m]
  by_cases hm : m < M
  · rw [ite_eq_left (by omega), ite_eq_left (Finset.mem_range.mpr hm), logSeries,
      PowerSeries.coeff_mk, ite_eq_right (by omega)]
    have h := natCast_mul_algebraMap_inv p (k := m + 1) (by omega)
    rw [← Nat.cast_succ]
    linear_combination (-1 : 𝔸ₚ) ^ m * h
  · rw [ite_eq_right (by omega), ite_eq_right (by simpa using hm), zero_mul]

/-- `(1 + X) P_{M+1}' = 1 - (-X)^M`. -/
private theorem one_add_X_mul_derivative_logPoly (M : ℕ) :
    (1 + Polynomial.X) * Polynomial.derivative (logPoly p (M + 1)) =
      1 - (-Polynomial.X) ^ M := by
  rw [derivative_logPoly, ← mul_neg_geom_sum, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, map_neg, map_one, neg_pow (Polynomial.X : Polynomial 𝔸ₚ) i]

/-- `1 + XV` is invertible modulo `X^M`: if `X^M ∣ (1 + XV) F`, then `X^M ∣ F`. -/
private theorem X_pow_dvd_of_X_pow_dvd_one_add_X_mul {R : Type*} [CommRing R] (M : ℕ)
    (V F : Polynomial R) (h : Polynomial.X ^ M ∣ (1 + Polynomial.X * V) * F) :
    Polynomial.X ^ M ∣ F := by
  have hg := mul_neg_geom_sum (-(Polynomial.X * V)) M
  rw [sub_neg_eq_add] at hg
  have hF : F = ((1 + Polynomial.X * V) * F) * ∑ i ∈ Finset.range M, (-(Polynomial.X * V)) ^ i +
      F * (-(Polynomial.X * V)) ^ M := by
    linear_combination (-F) * hg
  rw [hF]
  refine dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_left ?_ _)
  rw [neg_pow, mul_pow]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right dvd_rfl _) _

/-- The truncated logarithm has no constant term. -/
private theorem coeff_zero_logPoly (N : ℕ) : (logPoly p N).coeff 0 = 0 := by
  rw [coeff_trunc]
  split_ifs
  · rw [logSeries, PowerSeries.coeff_mk, ite_eq_left rfl]
  · rfl

/-- The key polynomial identity: with `Y = yT`, `Z = zT` and `W = Y + Z + YZ` in
`W(𝓞_ℂ_[p]♭)[1/p][T]`, `T^N ∣ P_N(W) - P_N(Y) - P_N(Z)`. -/
private theorem X_pow_dvd_logPoly (N : ℕ) (y z : 𝔸ₚ) :
    Polynomial.X ^ N ∣
      (logPoly p N).comp (Polynomial.C y * Polynomial.X + Polynomial.C z * Polynomial.X +
          Polynomial.C y * Polynomial.X * (Polynomial.C z * Polynomial.X)) -
        (logPoly p N).comp (Polynomial.C y * Polynomial.X) -
        (logPoly p N).comp (Polynomial.C z * Polynomial.X) := by
  rcases N with _ | M
  · simp
  set Y : Polynomial 𝔸ₚ := Polynomial.C y * Polynomial.X
  set Z : Polynomial 𝔸ₚ := Polynomial.C z * Polynomial.X
  set W := Y + Z + Y * Z
  set P := logPoly p (M + 1)
  set Q := P.comp W - P.comp Y - P.comp Z
  have hP := one_add_X_mul_derivative_logPoly p M
  have hcomp : ∀ R : Polynomial 𝔸ₚ, (1 + R) * (Polynomial.derivative P).comp R =
      1 - (-R) ^ M := fun R => by
    have := congrArg (fun F => F.comp R) hP
    simpa [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.pow_comp,
      Polynomial.neg_comp] using this
  have hDQ : Polynomial.derivative Q = Polynomial.derivative W * (Polynomial.derivative P).comp W -
      Polynomial.derivative Y * (Polynomial.derivative P).comp Y -
      Polynomial.derivative Z * (Polynomial.derivative P).comp Z := by
    simp only [Q, Polynomial.derivative_sub, Polynomial.derivative_comp]
  have hDW : Polynomial.derivative W = Polynomial.derivative Y * (1 + Z) +
      Polynomial.derivative Z * (1 + Y) := by
    simp only [W, Polynomial.derivative_add, Polynomial.derivative_mul]
    ring
  set V : Polynomial 𝔸ₚ := Polynomial.C y + Polynomial.C z +
    Polynomial.C y * Polynomial.C z * Polynomial.X
  have hU : (1 + Y) * (1 + Z) = 1 + Polynomial.X * V := by simp only [Y, Z, V]; ring
  have hW : W = Polynomial.X * V := by simp only [W, Y, Z, V]; ring
  have hUDQ : (1 + Polynomial.X * V) * Polynomial.derivative Q =
      -(-W) ^ M * Polynomial.derivative W + (1 + Z) * (-Y) ^ M * Polynomial.derivative Y +
        (1 + Y) * (-Z) ^ M * Polynomial.derivative Z := by
    rw [← hU, hDQ]
    have h1 := hcomp W
    have h2 := hcomp Y
    have h3 := hcomp Z
    have hW1 : 1 + W = (1 + Y) * (1 + Z) := by simp only [W]; ring
    rw [hW1] at h1
    linear_combination (Polynomial.derivative W) * h1 - (1 + Z) * Polynomial.derivative Y * h2 -
      (1 + Y) * Polynomial.derivative Z * h3 + hDW
  have hdvd : Polynomial.X ^ M ∣ Polynomial.derivative Q := by
    apply X_pow_dvd_of_X_pow_dvd_one_add_X_mul M V
    have hXW : Polynomial.X ∣ -W := by rw [hW]; exact (dvd_mul_right Polynomial.X V).neg_right
    have hXY : Polynomial.X ∣ -Y := (dvd_mul_left Polynomial.X (Polynomial.C y)).neg_right
    have hXZ : Polynomial.X ∣ -Z := (dvd_mul_left Polynomial.X (Polynomial.C z)).neg_right
    rw [hUDQ]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXW M).neg_right _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hXY M) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hXZ M) _) _
  rw [Polynomial.X_pow_dvd_iff] at hdvd ⊢
  intro d hd
  rcases d with _ | e
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_comp, W, Y, Z, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero,
      ← Polynomial.coeff_zero_eq_eval_zero, P, coeff_zero_logPoly, sub_zero]
  · have h := hdvd e (by omega)
    rw [Polynomial.coeff_derivative, ← Nat.cast_succ] at h
    exact (isUnit_natCast p (k := e + 1) (by omega)).mul_left_eq_zero.mp h

/-- If `Q` lies in the Rees algebra of `I` and `X^N ∣ Q`, then `Q(1) ∈ I^N`. -/
private theorem eval_one_mem_of_mem_reesAlgebra {R : Type*} [CommRing R] (I : Ideal R) (N : ℕ)
    (Q : Polynomial R) (hQ : Q ∈ reesAlgebra I) (hN : Polynomial.X ^ N ∣ Q) :
    Q.eval 1 ∈ I ^ N := by
  rw [Polynomial.eval_eq_sum_range]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [one_pow, mul_one]
  by_cases hk : k < N
  · rw [(Polynomial.X_pow_dvd_iff.mp hN) k hk]
    exact Ideal.zero_mem _
  · exact Ideal.pow_le_pow_right (by omega) ((mem_reesAlgebra_iff I Q).mp hQ k)

/-- For `y ∈ I`, the polynomial `yX` lies in the Rees algebra of `I`. -/
private theorem C_mul_X_mem_reesAlgebra {R : Type*} [CommRing R] (I : Ideal R) {y : R}
    (hy : y ∈ I) : Polynomial.C y * Polynomial.X ∈ reesAlgebra I := by
  rw [mem_reesAlgebra_iff]
  intro i
  rw [Polynomial.coeff_C_mul_X]
  split_ifs with h
  · subst h; rwa [pow_one]
  · exact Ideal.zero_mem _

/-- The Rees algebra of `I` is stable under composition `P ↦ P(W)`. -/
private theorem comp_mem_reesAlgebra {R : Type*} [CommRing R] (I : Ideal R) (P : Polynomial R)
    {W : Polynomial R} (hW : W ∈ reesAlgebra I) : P.comp W ∈ reesAlgebra I := by
  rw [Polynomial.comp_eq_aeval]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hW)
    (Polynomial.aeval_mem_adjoin_singleton _ _)

/-- **Additivity of the logarithm**: `log((1 + y)(1 + z)) = log(1 + y) + log(1 + z)` for `y`, `z`
in the kernel of `θ` with `p` inverted. -/
theorem logOneAdd_add {y z : 𝔸ₚ} (hy : y ∈ 𝕀) (hz : z ∈ 𝕀) (hyz : y + z + y * z ∈ 𝕀) :
    logOneAdd p hyz = logOneAdd p hy + logOneAdd p hz := by
  change AdicCompletion.evalPowerSeries 𝕀 hyz (logSeries p) =
    AdicCompletion.evalPowerSeries 𝕀 hy (logSeries p) +
      AdicCompletion.evalPowerSeries 𝕀 hz (logSeries p)
  refine AdicCompletion.ext_evalₐ fun N => ?_
  rw [map_add]
  simp only [AdicCompletion.evalₐ_evalPowerSeries]
  rw [← map_add, Ideal.Quotient.eq]
  have hY := C_mul_X_mem_reesAlgebra 𝕀 hy
  have hZ := C_mul_X_mem_reesAlgebra 𝕀 hz
  have hW : Polynomial.C y * Polynomial.X + Polynomial.C z * Polynomial.X +
      Polynomial.C y * Polynomial.X * (Polynomial.C z * Polynomial.X) ∈ reesAlgebra 𝕀 :=
    Subalgebra.add_mem _ (Subalgebra.add_mem _ hY hZ) (Subalgebra.mul_mem _ hY hZ)
  have hQ := eval_one_mem_of_mem_reesAlgebra 𝕀 N _
    (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (comp_mem_reesAlgebra _ _ hW)
      (comp_mem_reesAlgebra _ _ hY)) (comp_mem_reesAlgebra _ _ hZ)) (X_pow_dvd_logPoly p N y z)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_one] at hQ
  convert hQ using 1
  ring

/-- `log(1 + y)` depends only on `y`. -/
theorem logOneAdd_congr {y z : 𝔸ₚ} (hy : y ∈ 𝕀) (hz : z ∈ 𝕀) (h : y = z) :
    logOneAdd p hy = logOneAdd p hz := by
  subst h
  rfl

/-! ### `log [ε]` and `log [p̃]` -/

/-- For `ε ∈ 𝓞_ℂ_[p]♭` with `ε♯ = 1`, the element `[ε] - 1` lies in the kernel of `θ` (with `p`
inverted). -/
theorem algebraMap_teichmuller_sub_one_mem_ker {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) :
    algebraMap 𝔸 𝔸ₚ (teichmuller p ε - 1) ∈ 𝕀 :=
  algebraMap_mem_ker_fontaineThetaInvertP p (by
    rw [map_sub, fontaineTheta_teichmuller, h, map_one, sub_self])

/-- **`log [ε]`** for `ε ∈ 𝓞_ℂ_[p]♭` with `ε♯ = 1`: the value `log(1 + ([ε] - 1)) ∈ B_dR^+`. -/
def logTeichmuller {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) : 𝔹⁺ :=
  logOneAdd p (algebraMap_teichmuller_sub_one_mem_ker p h)

/-- An element of the tilt of `𝓞_ℂ_[p]` whose untilt vanishes is zero. -/
private theorem eq_zero_of_untilt_eq_zero {c : PreTilt 𝓞_ℂ_[p] p} (h : c.untilt = 0) : c = 0 := by
  apply Perfection.ext
  intro n
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow c n
  rw [h, pow_eq_zero_iff (pow_ne_zero n hp.out.ne_zero)] at h1
  have h2 := PreTilt.mk_untilt_eq_coeff_zero
    ((_root_.frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n] c)
  rw [h1, map_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at h2
  change PreTilt.coeff n c = PreTilt.coeff n 0
  rw [map_zero]
  exact h2.symm

/-- An element of the tilt of `𝓞_ℂ_[p]` divisible by every power of an element `ϖ` with
`ϖ♯ = p` is zero. -/
private theorem eq_zero_of_forall_pow_dvd {ϖ : PreTilt 𝓞_ℂ_[p] p} (hϖ : ϖ.untilt = p)
    {c : PreTilt 𝓞_ℂ_[p] p} (h : ∀ n, ϖ ^ n ∣ c) : c = 0 := by
  refine eq_zero_of_untilt_eq_zero p ?_
  apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
  intro n
  obtain ⟨d, hd⟩ := h n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, hd, map_mul, map_pow, hϖ]
  exact dvd_mul_right _ _

/-- `W(𝓞_ℂ_[p]♭)` is `ξ`-adically separated: a nonzero element does not lie in every `(ξ^n)`. -/
private theorem exists_notMem_span_xi_pow {x : 𝔸} (hx : x ≠ 0) :
    ∃ n, x ∉ span {xi p ^ n} := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x hx
  by_contra hcon
  have hb' : ∀ n, b ∈ span {xi p ^ n} := fun n =>
    mem_span_xi_pow_of_p_pow_mul_mem p n m b (not_not.mp (not_exists.mp hcon n))
  apply hb
  have h0 : WittVector.constantCoeff (xi p) = -pFlat p := by
    rw [xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    simp
  apply eq_zero_of_forall_pow_dvd p (untilt_pFlat p)
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hb' n)
  have := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_pow, h0] at this
  refine ⟨(-1) ^ n * WittVector.constantCoeff c, ?_⟩
  rw [← WittVector.constantCoeff_apply, ← this, neg_pow]
  ring

/-- Every nonzero `x ∈ W(𝓞_ℂ_[p]♭)` is `ξ^s w` with `θ(w) ≠ 0`. -/
private theorem exists_eq_xi_pow_mul {x : 𝔸} (hx : x ≠ 0) :
    ∃ (s : ℕ) (w : 𝔸), x = xi p ^ s * w ∧ fontaineTheta 𝓞_ℂ_[p] p w ≠ 0 := by
  classical
  have hex := exists_notMem_span_xi_pow p hx
  have hN : x ∉ span {xi p ^ Nat.find hex} := Nat.find_spec hex
  obtain ⟨M, hM⟩ : ∃ M, Nat.find hex = M + 1 := by
    refine ⟨Nat.find hex - 1, ?_⟩
    have hN0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hN
      rw [h0, pow_zero, Ideal.span_singleton_one]
      trivial
    omega
  have hxM : x ∈ span {xi p ^ M} := not_not.mp (Nat.find_min hex (by omega))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, w, by rw [← hw, mul_comm], fun hθ => hN ?_⟩
  have : w ∈ span {xi p} := by
    rw [← ker_fontaineTheta_eq_span_xi]
    exact hθ
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp this
  rw [hM, ← hw]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [pow_succ]; ring⟩

/-- For `ε ≠ 1`, `[ε] - 1 ≠ 0`. -/
private theorem teichmuller_sub_one_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (hne : ε ≠ 1) :
    teichmuller p ε - 1 ≠ 0 := by
  intro h
  apply hne
  have h1 : teichmuller p ε = 1 := sub_eq_zero.mp h
  have := congrArg (fun w => WittVector.coeff w 0) h1
  simpa [WittVector.teichmuller_coeff_zero] using this

/-- `P_{N+2} - X` is divisible by `X^2`. -/
private theorem exists_trunc_logSeries_sub_X (N : ℕ) :
    ∃ R : Polynomial 𝔸ₚ, trunc (N + 2) (logSeries p) - Polynomial.X = Polynomial.X ^ 2 * R := by
  change (Polynomial.X : Polynomial 𝔸ₚ) ^ 2 ∣ trunc (N + 2) (logSeries p) - Polynomial.X
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left (by omega), logSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_X]
  rcases d with _ | _ | d
  · simp
  · simp
  · omega

/-- **`log [ε] ≠ 0` for `ε ≠ 1`**: write `[ε] - 1 = ξ^s w` with `θ(w) ≠ 0` and `s ≥ 1`; modulo
`(ker θ)^(s+1)`, `log [ε] ≡ [ε] - 1 ≢ 0`. -/
theorem logTeichmuller_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (hne : ε ≠ 1) :
    logTeichmuller p h ≠ 0 := by
  intro h0
  obtain ⟨s, w, hx, hw⟩ := exists_eq_xi_pow_mul p (teichmuller_sub_one_ne_zero p hne)
  have hs : s ≠ 0 := by
    rintro rfl
    apply hw
    rw [pow_zero, one_mul] at hx
    rw [← hx, map_sub, fontaineTheta_teichmuller, h, map_one, sub_self]
  obtain ⟨R, hR⟩ := exists_trunc_logSeries_sub_X p (s - 1)
  rw [show s - 1 + 2 = s + 1 by omega] at hR
  have h0' : AdicCompletion.evalPowerSeries 𝕀 (algebraMap_teichmuller_sub_one_mem_ker p h)
      (logSeries p) = 0 := h0
  have hev := congrArg (AdicCompletion.evalₐ 𝕀 (s + 1)) h0'
  rw [AdicCompletion.evalₐ_evalPowerSeries, map_zero, Ideal.Quotient.eq_zero_iff_mem] at hev
  have hI := ker_fontaineThetaInvertP_pow_eq_span_xi_pow p (s + 1)
  set y := algebraMap 𝔸 𝔸ₚ (teichmuller p ε - 1) with hy_def
  have hy : y = algebraMap 𝔸 𝔸ₚ (xi p) ^ s * algebraMap 𝔸 𝔸ₚ w := by
    rw [hy_def, hx, map_mul, map_pow]
  have hsq : y ^ 2 * R.eval y ∈ 𝕀 ^ (s + 1) := by
    rw [hI, Ideal.mem_span_singleton]
    refine ⟨algebraMap 𝔸 𝔸ₚ (xi p) ^ (s - 1) * algebraMap 𝔸 𝔸ₚ w ^ 2 * R.eval y, ?_⟩
    rw [hy]
    have : 2 * s = (s + 1) + (s - 1) := by omega
    rw [mul_pow, ← pow_mul, mul_comm s 2, this, pow_add]
    ring
  have hyI : y ∈ 𝕀 ^ (s + 1) := by
    have he : y = (trunc (s + 1) (logSeries p)).eval y - y ^ 2 * R.eval y := by
      have := congrArg (Polynomial.eval y) hR
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X] at this
      linear_combination -this
    rw [he]
    exact Ideal.sub_mem _ hev hsq
  rw [hI] at hyI
  have hmem := mem_span_xi_pow_of_algebraMap_mem p (s + 1) _ hyI
  rw [hx] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hw' : w = xi p * c := by
    apply mul_left_cancel₀ (pow_ne_zero s (xi_ne_zero p))
    rw [← hc]
    ring
  apply hw
  rw [hw', map_mul, fontaineTheta_xi, zero_mul]

/-- **`log [p̃]`**, Fontaine's `log([p̃]/p) = Σ_{n ≥ 1} (-1)^(n+1) ([p̃]/p - 1)^n / n ∈ B_dR^+`,
where `p̃ = p♭ = (p, p^{1/p}, …)` (`PadicComplexInt.pFlat`) and `[p̃]/p - 1 = -ξ/p`. -/
def logPTilde : 𝔹⁺ :=
  logOneAdd p (neg_mem (xiDivP_mem_ker p))

end PadicComplexInt

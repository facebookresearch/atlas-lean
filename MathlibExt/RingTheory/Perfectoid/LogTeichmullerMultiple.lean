/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/PanBergerPst.lean` and
`ZInQKernel/Contrib/OneProof/BergerBst.lean` (https://github.com/Deicyde/diophantine-z-q),
compared with the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingUniformizer
public import MathlibExt.RingTheory.Perfectoid.MaximalPeriodRing
import Mathlib.NumberTheory.Basic

/-!
# The periods `log [ε]` are `ℤ_p`-multiples of `t`

Let `ε₀ ∈ 𝓞_ℂ_[p]♭` be a generator of `ℤ_p(1)`, that is, `ε₀ = (1, ζ_p, ζ_{p²}, …)` for a
compatible system of primitive `p`-power roots of unity, so that `(ε₀^{1/p})♯ = ζ_p` is a primitive
`p`-th root of unity, and let `t = log [ε₀]`. We show that for every `ε ∈ 𝓞_ℂ_[p]♭` with
`ε♯ = 1` there is `a ∈ ℤ_p` with `log [ε] = a t` in `B_dR^+`
(`PadicComplexInt.exists_logTeichmuller_eq_mul`): this is how J.-M. Fontaine, *Le corps des
périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.4 p. 72, attaches `t` to the
`ℤ_p`-module `ℤ_p(1)` of such `ε`. Fontaine's element `ε = (1, ζ_p, ζ_{p²}, …)`
(`PadicComplexInt.epsilon`) is such a generator
(`PadicComplexInt.isPrimitiveRoot_untilt_frobeniusEquiv_symm_epsilon`). Consequently the ring
`B_max`, defined by inverting every nonzero `log [ε]`, is `B_max^+[1/t]`
(`PadicComplexInt.bMax_eq_adjoin`).

## Proof

Write `ε^{(k)} = (ε^{1/p^k})♯`, a `p^k`-th root of unity. Since `ε₀^{(k)}` is a primitive `p^k`-th
root of unity, `ε^{(k)} = (ε₀^{(k)})^{b_k}` with `0 ≤ b_k < p^k`, and the `b_k` converge in `ℤ_p`
to some `a`. Then `ε ε₀^{p^k - b_k} = η^{p^k}` with `η♯ = 1`, so by additivity of the logarithm
(`PadicComplexInt.logTeichmuller_mul`) `log [ε] - b_k t ∈ p^k A_max`, and `log [ε] - a t` lies in
`p^k A_max` for every `k`, hence vanishes because `A_max` is `p`-adically separated in `B_dR^+`
(`PadicComplexInt.eq_zero_of_forall_eq_pow_mul_mem_aMax`).
-/

@[expose] public noncomputable section

open Ideal WittVector PowerSeries

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-! ### Multiplicativity of `log [·]` -/

/-- `log [x]` depends only on `x`. -/
private theorem logTeichmuller_congr {x y : PreTilt 𝓞_ℂ_[p] p} (hxy : x = y)
    (hx : x.untilt = 1) (hy : y.untilt = 1) : logTeichmuller p hx = logTeichmuller p hy := by
  subst hxy
  rfl

/-- `log [x y] = log [x] + log [y]` for `x♯ = y♯ = 1`. -/
theorem logTeichmuller_mul {x y : PreTilt 𝓞_ℂ_[p] p} (hx : x.untilt = 1) (hy : y.untilt = 1)
    (hxy : (x * y).untilt = 1) :
    logTeichmuller p hxy = logTeichmuller p hx + logTeichmuller p hy := by
  have hx' := algebraMap_teichmuller_sub_one_mem_ker p hx
  have hy' := algebraMap_teichmuller_sub_one_mem_ker p hy
  refine (logOneAdd_congr p _ (add_mem (add_mem hx' hy') (Ideal.mul_mem_right _ _ hx')) ?_).trans
    (logOneAdd_add p hx' hy' _)
  simp only [map_mul, map_sub, map_one]
  ring

/-- `log [1] = 0`. -/
theorem logTeichmuller_one (h : (1 : PreTilt 𝓞_ℂ_[p] p).untilt = 1) :
    logTeichmuller p h = 0 := by
  have h1 := logTeichmuller_mul p h h (by rw [mul_one]; exact h)
  rw [logTeichmuller_congr p (mul_one 1) _ h] at h1
  exact left_eq_add.mp h1

/-- `log [xⁿ] = n log [x]` for `x♯ = 1`. -/
theorem logTeichmuller_pow {x : PreTilt 𝓞_ℂ_[p] p} (hx : x.untilt = 1) (n : ℕ)
    (hxn : (x ^ n).untilt = 1) :
    logTeichmuller p hxn = (n : 𝔹⁺) * logTeichmuller p hx := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, logTeichmuller_congr p (pow_zero x) hxn (map_one _)]
    exact logTeichmuller_one p _
  | succ n ih =>
    have hxn' : (x ^ n).untilt = 1 := by rw [map_pow, hx, one_pow]
    rw [logTeichmuller_congr p (pow_succ x n) hxn (by rw [map_mul, hxn', hx, one_mul]),
      logTeichmuller_mul p hxn' hx, ih hxn']
    push_cast
    ring

/-! ### `A_max` is `p`-adically separated in `B_dR^+` -/

/-- The reduction `B_dR^+ → W(𝓞_ℂ_[p]♭)[1/p] ⧸ (ker θ)^m`, for `B_dR^+` the completion of
`W(𝓞_ℂ_[p]♭)[1/p]` along `ker θ`. -/
private def evalMod (m : ℕ) : 𝔹⁺ →+* 𝔸ₚ ⧸ 𝕀 ^ m :=
  (AdicCompletion.evalₐ 𝕀 m).toRingHom

private theorem evalMod_evalBDeRhamPlus {x : 𝔸ₚ} (hx : x ∈ 𝕀) (f : 𝔸ₚ⟦X⟧) (m : ℕ) :
    evalMod p m (evalBDeRhamPlus p hx f) = Ideal.Quotient.mk (𝕀 ^ m) ((trunc m f).eval x) :=
  AdicCompletion.evalₐ_evalPowerSeries 𝕀 hx f m

private theorem evalMod_natCast_pow (m k : ℕ) :
    evalMod p m ((p : 𝔹⁺) ^ k) = Ideal.Quotient.mk (𝕀 ^ m) ((p : 𝔸ₚ) ^ k) := by
  rw [map_pow, map_pow]
  exact congrArg (· ^ k)
    ((map_natCast (evalMod p m) p).trans (map_natCast (Ideal.Quotient.mk (𝕀 ^ m)) p).symm)

/-- `p^m (A (ξ/p)^i) = A ξ^i p^(m - i)` in `W(𝓞_ℂ_[p]♭)[1/p]` for `i ≤ m`. -/
private theorem natCast_pow_mul_xiDivP_pow {m i : ℕ} (hi : i ≤ m) (A : 𝔸ₚ) :
    (p : 𝔸ₚ) ^ m * (A * xiDivP p ^ i) =
      A * algebraMap 𝔸 𝔸ₚ (xi p) ^ i * (p : 𝔸ₚ) ^ (m - i) := by
  obtain ⟨q, hq⟩ : ∃ q, algebraMap ℚ_[p] 𝔸ₚ (p : ℚ_[p])⁻¹ = q := ⟨_, rfl⟩
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ, algebraMap 𝔸 𝔸ₚ (xi p) = Ξ := ⟨_, rfl⟩
  have hpq : ((p : 𝔸ₚ) * q) ^ i = 1 := by
    rw [← hq, natCast_mul_algebraMap_inv p hp.out.ne_zero, one_pow]
  have hxi : xiDivP p = Ξ * q := by
    rw [← hq, ← hΞ]
    rfl
  have hm : (p : 𝔸ₚ) ^ m = (p : 𝔸ₚ) ^ (m - i) * (p : 𝔸ₚ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  rw [hxi, hΞ]
  linear_combination (A * Ξ ^ i * q ^ i) * hm + (A * Ξ ^ i * (p : 𝔸ₚ) ^ (m - i)) * hpq

/-- Modulo `(ker θ)^m`, `p^m` times an element of `A_max` is the image of an element of
`W(𝓞_ℂ_[p]♭)`. -/
private theorem exists_evalMod_pow_mul_eq {y : 𝔹⁺} (hy : y ∈ aMax p) (m : ℕ) :
    ∃ w : 𝔸, evalMod p m ((p : 𝔹⁺) ^ m * y) = Ideal.Quotient.mk _ (algebraMap 𝔸 𝔸ₚ w) := by
  obtain ⟨f, -, rfl⟩ := Subring.mem_map.1 hy
  refine ⟨∑ i ∈ Finset.range m, PowerSeries.coeff i f * xi p ^ i * (p : 𝔸) ^ (m - i), ?_⟩
  rw [RingHom.comp_apply, map_mul, evalMod_evalBDeRhamPlus, evalMod_natCast_pow, ← map_mul]
  refine congrArg (Ideal.Quotient.mk (𝕀 ^ m)) ?_
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [RingHom.id_apply, PowerSeries.coeff_map, map_mul, map_pow, map_natCast]
  exact natCast_pow_mul_xiDivP_pow p (Finset.mem_range.mp hi).le _

/-- **`A_max` is `p`-adically separated inside `B_dR^+`**: an element of `B_dR^+` that lies in
`p^k A_max` for every `k` is `0`. -/
theorem eq_zero_of_forall_eq_pow_mul_mem_aMax (x : 𝔹⁺)
    (h : ∀ k : ℕ, ∃ y ∈ aMax p, x = (p : 𝔹⁺) ^ k * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  change evalMod p m x = evalMod p m 0
  rw [map_zero]
  choose y hy hxy using h
  choose w hw using fun k => exists_evalMod_pow_mul_eq p (hy k) m
  have hk : ∀ k, evalMod p m ((p : 𝔹⁺) ^ m * x) =
      Ideal.Quotient.mk _ ((p : 𝔸ₚ) ^ k * algebraMap 𝔸 𝔸ₚ (w k)) := by
    intro k
    rw [hxy k, mul_left_comm, map_mul, hw k, evalMod_natCast_pow, ← map_mul]
  have hw0 : w 0 ∈ span {xi p ^ m} := by
    refine mem_span_xi_pow_of_forall p m (w 0) fun k => ?_
    have e := Ideal.Quotient.eq.mp ((hk 0).symm.trans (hk k))
    rw [ker_fontaineThetaInvertP_pow_eq_span_xi_pow] at e
    have e' : algebraMap 𝔸 𝔸ₚ (w 0 - (p : 𝔸) ^ k * w k) ∈
        span {algebraMap 𝔸 𝔸ₚ (xi p) ^ m} := by
      convert e using 1
      simp only [map_sub, map_mul, map_pow, map_natCast, pow_zero, one_mul]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (mem_span_xi_pow_of_algebraMap_mem p m _ e')
    exact ⟨w k, b, by linear_combination -hb⟩
  have h0 : evalMod p m ((p : 𝔹⁺) ^ m * x) = 0 := by
    rw [hk 0, Ideal.Quotient.eq_zero_iff_mem, ker_fontaineThetaInvertP_pow_eq_span_xi_pow]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hw0
    exact Ideal.mem_span_singleton'.mpr ⟨algebraMap 𝔸 𝔸ₚ c, by
      rw [← hc, map_mul, map_pow, pow_zero, one_mul]⟩
  have hu : IsUnit (evalMod p m ((p : 𝔹⁺) ^ m)) := by
    rw [evalMod_natCast_pow p m m]
    exact ((isUnit_natCast p hp.out.ne_zero).pow m).map (Ideal.Quotient.mk (𝕀 ^ m))
  exact hu.mul_right_eq_zero.mp ((map_mul (evalMod p m) _ _).symm.trans h0)

/-! ### Roots of an element of the tilt -/

private theorem untiltRoot_add_pow (x : PreTilt 𝓞_ℂ_[p] p) (j m : ℕ) :
    x.untiltRoot (m + j) ^ p ^ m = x.untiltRoot j := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.add_right_comm, pow_succ', pow_mul, PreTilt.untiltRoot_succ_pow, ih]

private theorem untiltRoot_mul (x y : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) :
    (x * y).untiltRoot n = x.untiltRoot n * y.untiltRoot n := by
  rw [PreTilt.untiltRoot, PreTilt.untiltRoot, PreTilt.untiltRoot, iterate_map_mul, map_mul]

private theorem untiltRoot_npow (x : PreTilt 𝓞_ℂ_[p] p) (n c : ℕ) :
    (x ^ c).untiltRoot n = x.untiltRoot n ^ c := by
  rw [PreTilt.untiltRoot, PreTilt.untiltRoot, iterate_map_pow, map_pow]

/-- `(F^{-k} x) ^ (p ^ k) = x` in the tilt. -/
private theorem iterate_frobeniusEquiv_symm_pow (k : ℕ) (x : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k] x) ^ p ^ k = x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

/-! ### Fontaine's `ε` generates `ℤ_p(1)` -/

/-- Fontaine's `ε = (1, ζ_p, ζ_{p²}, …)` generates `ℤ_p(1)`: `(ε^{1/p})♯ = ζ_p` is a primitive
`p`-th root of unity. -/
theorem isPrimitiveRoot_untilt_frobeniusEquiv_symm_epsilon :
    IsPrimitiveRoot ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm (epsilon p)).untilt p := by
  have hu : ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm (epsilon p)).untilt = zetaPowInt p 1 :=
    untilt_eq_of_coeff p (fun n => zetaPowInt p (n + 1)) (fun n => zetaPowInt_succ_pow p (n + 1))
      _ fun n => PreTilt.coeff_iterate_frobeniusEquiv_symm n 1 (epsilon p)
  rw [hu, IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime ?_ (zetaPowInt_one_ne_one p)
  rw [zetaPowInt_succ_pow, zetaPowInt_zero]

/-! ### `log [ε] = a t` -/

/-- For a generator `ε₀` of `ℤ_p(1)`, `(ε₀^{1/p^k})♯` is a primitive `p ^ k`-th root of unity. -/
private theorem isPrimitiveRoot_untiltRoot {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h₀ : ε₀.untilt = 1)
    (hgen : IsPrimitiveRoot ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε₀).untilt p) (k : ℕ) :
    IsPrimitiveRoot (ε₀.untiltRoot k) (p ^ k) := by
  rcases k with _ | k
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    exact h₀
  · rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [untiltRoot_add_pow]
      exact hgen.ne_one hp.out.one_lt
    · rw [PreTilt.untiltRoot_pow]
      exact h₀

/-- For a generator `ε₀` of `ℤ_p(1)` and `ε♯ = 1`, `ε^{(k)} = (ε₀^{(k)})^b` with `b < p ^ k`. -/
private theorem exists_pow_eq_untiltRoot {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h₀ : ε₀.untilt = 1)
    (hgen : IsPrimitiveRoot ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε₀).untilt p)
    {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (k : ℕ) :
    ∃ b < p ^ k, ε₀.untiltRoot k ^ b = ε.untiltRoot k := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact (isPrimitiveRoot_untiltRoot p h₀ hgen k).eq_pow_of_pow_eq_one
    (by rw [PreTilt.untiltRoot_pow, h])

/-- **`log [ε] = b log [ε₀] + p^k z` with `z ∈ A_max`**, when `ε^{(k)} = (ε₀^{(k)})^b` and
`b ≤ p ^ k`: `ε ε₀^{p^k - b} = η^{p^k}` with `η♯ = 1`. -/
private theorem exists_logTeichmuller_eq_add {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h₀ : ε₀.untilt = 1)
    {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (k b : ℕ) (hbk : b ≤ p ^ k)
    (hb : ε₀.untiltRoot k ^ b = ε.untiltRoot k) :
    ∃ z ∈ aMax p, logTeichmuller p h = (b : 𝔹⁺) * logTeichmuller p h₀ + (p : 𝔹⁺) ^ k * z := by
  have hc0 : (ε₀ ^ (p ^ k - b)).untilt = 1 := by rw [map_pow, h₀, one_pow]
  have hx1 : (ε * ε₀ ^ (p ^ k - b)).untilt = 1 := by rw [map_mul, h, hc0, one_mul]
  have hη1 : ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k]
      (ε * ε₀ ^ (p ^ k - b))).untilt = 1 := by
    change (ε * ε₀ ^ (p ^ k - b)).untiltRoot k = 1
    rw [untiltRoot_mul, untiltRoot_npow, ← hb, ← pow_add, Nat.add_sub_cancel' hbk,
      PreTilt.untiltRoot_pow, h₀]
  have hηp := iterate_frobeniusEquiv_symm_pow p k (ε * ε₀ ^ (p ^ k - b))
  have hηp1 : (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k]
      (ε * ε₀ ^ (p ^ k - b))) ^ p ^ k).untilt = 1 := by rw [hηp]; exact hx1
  have e1 := logTeichmuller_mul p h hc0 hx1
  rw [logTeichmuller_pow p h₀ _ hc0] at e1
  have e2 := logTeichmuller_pow p hη1 (p ^ k) hηp1
  rw [logTeichmuller_congr p hηp hηp1 hx1] at e2
  refine ⟨_, Subring.sub_mem _ (logTeichmuller_mem_aMax p hη1) (logTeichmuller_mem_aMax p h₀), ?_⟩
  push_cast [Nat.cast_sub hbk] at e1 e2
  linear_combination e2 - e1

/-- Natural numbers `b k` with `b (k + 1) ≡ b k` modulo `p ^ k` converge in `ℤ_p`. -/
private theorem exists_sub_mem_span_pow (b : ℕ → ℕ) (hb : ∀ k, b (k + 1) ≡ b k [MOD p ^ k]) :
    ∃ a : ℤ_[p], ∀ k, a - (b k : ℤ_[p]) ∈ span {(p : ℤ_[p]) ^ k} := by
  have hmem : ∀ k m, k ≤ m → (b m : ℤ_[p]) - (b k : ℤ_[p]) ∈ span {(p : ℤ_[p]) ^ k} := by
    intro k m hkm
    have hmod : b m ≡ b k [MOD p ^ k] := by
      induction m, hkm using Nat.le_induction with
      | base => rfl
      | succ m hkm ih => exact ((hb m).of_dvd (pow_dvd_pow p hkm)).trans ih
    obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.mp hmod
    refine Ideal.mem_span_singleton'.mpr ⟨-(c : ℤ_[p]), ?_⟩
    have := congrArg (fun z : ℤ => (z : ℤ_[p])) hc
    push_cast at this
    linear_combination this
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hcs : CauchySeq (fun k => (b k : ℤ_[p])) := by
    rw [Metric.cauchySeq_iff']
    intro r hr
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hp1)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(b n : ℤ_[p]) - b N‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
          (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (hmem N n hn)
      _ = (p : ℝ)⁻¹ ^ N := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < r := hN
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨a, fun k => ?_⟩
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact le_of_tendsto (ha.sub_const (b k : ℤ_[p])).norm
    (Filter.eventually_atTop.mpr ⟨k, fun m hm =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (hmem k m hm)⟩)

/-- The image in `B_dR^+` of an element of `ℤ_p` lies in `A_max`. -/
private theorem algebraMap_padicInt_mem_aMax (c : ℤ_[p]) :
    algebraMap ℚ_[p] 𝔹⁺ (c : ℚ_[p]) ∈ aMax p := by
  have e : algebraMap ℚ_[p] 𝔹⁺ (c : ℚ_[p]) = algebraMap 𝔸 𝔹⁺ (padicIntToAinf p c) := by
    rw [IsScalarTower.algebraMap_apply ℚ_[p] 𝔸ₚ 𝔹⁺, IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺]
    exact congrArg _ (padicToLocalizationAway_coe p c)
  rw [e]
  exact algebraMap_mem_aMax p _

/-- **Every period `log [ε]` is a `ℤ_p`-multiple of `t = log [ε₀]`**: let `ε₀ ∈ 𝓞_ℂ_[p]♭` with
`ε₀♯ = 1` generate `ℤ_p(1)`, that is, `(ε₀^{1/p})♯` is a primitive `p`-th root of unity. Then for
every `ε ∈ 𝓞_ℂ_[p]♭` with `ε♯ = 1` there is `a ∈ ℤ_p` with `log [ε] = a log [ε₀]` in `B_dR^+`. -/
theorem exists_logTeichmuller_eq_mul {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h₀ : ε₀.untilt = 1)
    (hgen : IsPrimitiveRoot ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε₀).untilt p)
    {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) :
    ∃ a : ℤ_[p], logTeichmuller p h = algebraMap ℚ_[p] 𝔹⁺ (a : ℚ_[p]) * logTeichmuller p h₀ := by
  choose b hblt hb using exists_pow_eq_untiltRoot p h₀ hgen h
  have hcompat : ∀ k, b (k + 1) ≡ b k [MOD p ^ k] := by
    intro k
    have hP := isPrimitiveRoot_untiltRoot p h₀ hgen k
    have hfin : IsOfFinOrder (ε₀.untiltRoot k) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, pow_pos hp.out.pos k, hP.pow_eq_one⟩
    rw [hP.eq_orderOf]
    apply hfin.pow_eq_pow_iff_modEq.mp
    rw [hb k, ← PreTilt.untiltRoot_succ_pow ε k, ← hb (k + 1),
      ← PreTilt.untiltRoot_succ_pow ε₀ k, ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨a, ha⟩ := exists_sub_mem_span_pow p b hcompat
  refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall_eq_pow_mul_mem_aMax p _ fun k => ?_)⟩
  obtain ⟨z, hz, hlog⟩ := exists_logTeichmuller_eq_add p h₀ h k (b k) (hblt k).le (hb k)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha k)
  have hac : (a : ℚ_[p]) = (b k : ℚ_[p]) + (c : ℚ_[p]) * (p : ℚ_[p]) ^ k := by
    have := congrArg (fun y : ℤ_[p] => (y : ℚ_[p])) hc
    push_cast at this
    linear_combination -this
  refine ⟨z - algebraMap ℚ_[p] 𝔹⁺ (c : ℚ_[p]) * logTeichmuller p h₀,
    Subring.sub_mem _ hz (Subring.mul_mem _ (algebraMap_padicInt_mem_aMax p c)
      (logTeichmuller_mem_aMax p h₀)), ?_⟩
  rw [hlog, hac, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

/-- If `ε♯ = 1` and `ε ≠ 1`, the multiplier `a` with `log [ε] = a log [ε₀]` is nonzero, so that
`log [ε]` is a unit multiple of `log [ε₀]` in the `ℚ_[p]`-algebra `B_dR^+`. -/
theorem exists_logTeichmuller_eq_mul_of_ne_one {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h₀ : ε₀.untilt = 1)
    (hgen : IsPrimitiveRoot ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε₀).untilt p)
    {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (hne : ε ≠ 1) :
    ∃ a : ℤ_[p], a ≠ 0 ∧
      logTeichmuller p h = algebraMap ℚ_[p] 𝔹⁺ (a : ℚ_[p]) * logTeichmuller p h₀ := by
  obtain ⟨a, ha⟩ := exists_logTeichmuller_eq_mul p h₀ hgen h
  refine ⟨a, fun ha0 => logTeichmuller_ne_zero p h hne ?_, ha⟩
  rw [ha, ha0, PadicInt.coe_zero, map_zero, zero_mul]

/-- **`B_max = B_max^+[1/t]`** for `t = log [ε]` and Fontaine's `ε = (1, ζ_p, ζ_{p²}, …)`: inverting
every nonzero period `log [ε']` is the same as inverting `t`. -/
theorem bMax_eq_adjoin :
    bMax p = Algebra.adjoin ℚ_[p] (algebraMap 𝔹⁺ 𝔹 '' aMax p ∪
      {(algebraMap 𝔹⁺ 𝔹 (logTeichmuller p (untilt_epsilon p)))⁻¹}) := by
  apply le_antisymm
  · rw [bMax, Algebra.adjoin_le_iff]
    rintro _ (hz | ⟨ε, h, -, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl hz)
    · obtain ⟨a, ha⟩ := exists_logTeichmuller_eq_mul p (untilt_epsilon p)
        (isPrimitiveRoot_untilt_frobeniusEquiv_symm_epsilon p) h
      rw [ha, map_mul, ← IsScalarTower.algebraMap_apply, mul_inv, ← map_inv₀ (algebraMap ℚ_[p] 𝔹)]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin (Or.inr rfl))
  · rw [Algebra.adjoin_le_iff]
    rintro _ (hz | hz)
    · exact Algebra.subset_adjoin (Or.inl hz)
    · rw [Set.mem_singleton_iff] at hz
      exact Algebra.subset_adjoin (Or.inr ⟨epsilon p, untilt_epsilon p, epsilon_ne_one p, hz⟩)

end PadicComplexInt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/AcrisImageNormal.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingBasic

/-!
# Fontaine's crystalline period ring: normalizing divided-power series

Let `w` be a generator of the kernel of Fontaine's map `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]`. The
coefficients of a series `Σ aₙ w^n/n!` with `aₙ → 0` `p`-adically can be chosen such that
`θ(aₙ) ≠ 0` whenever `aₙ ≠ 0`, without changing the partial sums modulo `p^k` from some point
on (`PadicComplexInt.exists_normalized`): write each coefficient as `r + w u` and move `w u` to
the next index, using `w u · w^n/n! = (n + 1) u · w^{n+1}/(n+1)!`. For a series normalized in
this way, if every partial sum below `m` lies in the `m`-th power of the kernel of `θ` with `p`
inverted, then every coefficient vanishes (`PadicComplexInt.eq_zero_of_normalized`). This gives
the injectivity of the map `A_cris → B_dR^+` (Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223 (1994), Exposé II, §4.1.2, p. 83).
-/

@[expose] public noncomputable section

open Ideal PowerSeries
open WittVector (fontaineTheta)

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

variable {p} {w : WittVector p (PreTilt 𝓞_ℂ_[p] p)}

/-! ### The carry construction

Every `x ∈ W(𝓞_ℂ_[p]♭)` is split as `x = r + w u`: on `w W(𝓞_ℂ_[p]♭)` take `r = 0` and `u` a
chosen quotient by `w`, off `w W(𝓞_ℂ_[p]♭)` take `r = x` and `u = 0`. With `t₀ = a₀` and
`t_{n+1} = a_{n+1} + (n+1) uₙ` (where `tₙ = rₙ + w uₙ`), the normalized coefficients are the
`rₙ`. -/

/-- `a → 0` `p`-adically: for every `k`, `p ^ k` divides all but finitely many terms. -/
private def IsPadicNull (a : ℕ → 𝔸) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, (p : 𝔸) ^ k ∣ a n

open Classical in
/-- A quotient of `x` by `w` when `x ∈ w W(𝓞_ℂ_[p]♭)`, and `0` otherwise. -/
private def wQuot (w x : 𝔸) : 𝔸 :=
  if h : ∃ b, x = w * b then h.choose else 0

open Classical in
/-- The part of `x` kept as a coefficient: `0` when `x ∈ w W(𝓞_ℂ_[p]♭)`, and `x` otherwise. -/
private def wRem (w x : 𝔸) : 𝔸 :=
  if ∃ b, x = w * b then 0 else x

private theorem wRem_add_wQuot (w x : 𝔸) : x = wRem w x + w * wQuot w x := by
  unfold wRem wQuot
  split_ifs with h
  · rw [zero_add]
    exact h.choose_spec
  · rw [mul_zero, add_zero]

private theorem wRem_normalized
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (x : 𝔸) :
    wRem w x = 0 ∨ fontaineTheta 𝓞_ℂ_[p] p (wRem w x) ≠ 0 := by
  unfold wRem
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr fun hx => h (dvd_of_fontaineTheta_eq_zero hgen hx)

private theorem dvd_wQuot
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (k : ℕ) {x : 𝔸}
    (h : (p : 𝔸) ^ k ∣ x) : (p : 𝔸) ^ k ∣ wQuot w x := by
  unfold wQuot
  split_ifs with hx
  · apply p_pow_dvd_of_dvd_mul hgen k
    rw [← hx.choose_spec]
    exact h
  · exact dvd_zero _

private theorem dvd_wRem (k : ℕ) {x : 𝔸} (h : (p : 𝔸) ^ k ∣ x) :
    (p : 𝔸) ^ k ∣ wRem w x := by
  unfold wRem
  split_ifs
  · exact dvd_zero _
  · exact h

/-- The carried coefficients: `t₀ = a₀` and `t_{n+1} = a_{n+1} + (n+1) uₙ`, where
`uₙ = tₙ / w` when `tₙ ∈ w W(𝓞_ℂ_[p]♭)`, and `uₙ = 0` otherwise. -/
private def carrySeq (w : 𝔸) (a : ℕ → 𝔸) : ℕ → 𝔸
  | 0 => a 0
  | n + 1 => a (n + 1) + ((n + 1 : ℕ) : 𝔸) * wQuot w (carrySeq w a n)

private theorem carrySeq_zero (w : 𝔸) (a : ℕ → 𝔸) : carrySeq w a 0 = a 0 := rfl

private theorem carrySeq_succ (w : 𝔸) (a : ℕ → 𝔸) (n : ℕ) :
    carrySeq w a (n + 1) = a (n + 1) + ((n + 1 : ℕ) : 𝔸) * wQuot w (carrySeq w a n) :=
  rfl

/-- The normalized series: its `n`-th coefficient is the kept part of `tₙ`. -/
private def normSeries (w : 𝔸) (f : 𝔸⟦X⟧) : 𝔸⟦X⟧ :=
  PowerSeries.mk fun n => wRem w (carrySeq w (fun m => PowerSeries.coeff m f) n)

private theorem coeff_normSeries (w : 𝔸) (f : 𝔸⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (normSeries w f) =
      wRem w (carrySeq w (fun m => PowerSeries.coeff m f) n) := by
  rw [normSeries, PowerSeries.coeff_mk]

/-- The partial sums of `f` and of its normalization differ by a single carry term: using
`w u · w^N/N! = (N+1) u · w^{N+1}/(N+1)!`, the `w`-divisible part of `t_N` moves to the next
index. -/
private theorem dividedPowerSum_sub_dividedPowerSum_normSeries (f : 𝔸⟦X⟧) (N : ℕ) :
    dividedPowerSum w f (N + 1) - dividedPowerSum w (normSeries w f) (N + 1) =
      algebraMap 𝔸 𝔸ₚ
          (((N + 1 : ℕ) : 𝔸) * wQuot w (carrySeq w (fun m => PowerSeries.coeff m f) N)) *
        dividedPower w (N + 1) := by
  induction N with
  | zero =>
    have hs := congrArg (algebraMap 𝔸 𝔸ₚ)
      (wRem_add_wQuot w (PowerSeries.coeff 0 f))
    have hγ := succ_mul_dividedPower_succ w 0
    rw [map_add, map_mul] at hs
    rw [map_mul, map_natCast, dividedPowerSum_succ, dividedPowerSum_succ,
      dividedPowerSum_zero_right, dividedPowerSum_zero_right, coeff_normSeries, carrySeq_zero]
    linear_combination dividedPower w 0 * hs -
      algebraMap 𝔸 𝔸ₚ (wQuot w (PowerSeries.coeff 0 f)) * hγ
  | succ N ih =>
    have hs := congrArg (algebraMap 𝔸 𝔸ₚ)
      (wRem_add_wQuot w (carrySeq w (fun m => PowerSeries.coeff m f) (N + 1)))
    have ht := congrArg (algebraMap 𝔸 𝔸ₚ)
      (carrySeq_succ w (fun m => PowerSeries.coeff m f) N)
    have hγ := succ_mul_dividedPower_succ w (N + 1)
    rw [map_add, map_mul] at hs
    rw [map_add, map_mul, map_natCast] at ht
    rw [map_mul, map_natCast] at ih ⊢
    rw [dividedPowerSum_succ w f (N + 1), dividedPowerSum_succ w (normSeries w f) (N + 1),
      coeff_normSeries]
    linear_combination ih - dividedPower w (N + 1) * ht + dividedPower w (N + 1) * hs -
      algebraMap 𝔸 𝔸ₚ
        (wQuot w (carrySeq w (fun m => PowerSeries.coeff m f) (N + 1))) * hγ

/-- The carried coefficients tend to `0`. Fix `k` and `M` with `p^k ∣ aₙ` for `n ≥ M`. For
`q ≤ k`, `p^q ∣ tₙ` for all `n ≥ M + p q`: among `p` consecutive indices there is a multiple
`m + 1` of `p`, where `t_{m+1} = a_{m+1} + (m+1) u_m` gains a factor `p` (`p^q ∣ t_m` gives
`p^q ∣ u_m`, since `w` is a non-zero-divisor modulo `p^q`), and the divisibility then propagates
to all later indices. -/
private theorem isPadicNull_carrySeq
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {a : ℕ → 𝔸}
    (ha : IsPadicNull a) : IsPadicNull (carrySeq w a) := by
  unfold IsPadicNull at ha ⊢
  intro k
  obtain ⟨M, hM⟩ := ha k
  have hstep : ∀ q ≤ k, ∀ m, M ≤ m → (p : 𝔸) ^ q ∣ carrySeq w a m →
      (p : 𝔸) ^ q ∣ carrySeq w a (m + 1) := by
    intro q hq m hm h
    rw [carrySeq_succ]
    exact dvd_add ((pow_dvd_pow _ hq).trans (hM (m + 1) (by omega)))
      (dvd_mul_of_dvd_right (dvd_wQuot hgen q h) _)
  have hjump : ∀ q < k, ∀ m, M ≤ m → (p : 𝔸) ^ q ∣ carrySeq w a m → p ∣ m + 1 →
      (p : 𝔸) ^ (q + 1) ∣ carrySeq w a (m + 1) := by
    intro q hq m hm h hdvd
    rw [carrySeq_succ]
    refine dvd_add ((pow_dvd_pow _ (by omega : q + 1 ≤ k)).trans (hM (m + 1) (by omega))) ?_
    rw [pow_succ']
    exact mul_dvd_mul (Nat.cast_dvd_cast hdvd) (dvd_wQuot hgen q h)
  have hmain : ∀ q ≤ k, ∀ n, M + p * q ≤ n → (p : 𝔸) ^ q ∣ carrySeq w a n := by
    intro q
    induction q with
    | zero =>
      intro _ n _
      rw [pow_zero]
      exact one_dvd _
    | succ q ih =>
      intro hq n hn
      rw [mul_add_one] at hn
      have hp0 : 0 < p := hp.out.pos
      obtain ⟨n₁, h1, h2, hdiv⟩ : ∃ n₁, M + p * q < n₁ ∧ n₁ ≤ M + p * q + p ∧ p ∣ n₁ := by
        refine ⟨p * ((M + p * q) / p + 1), Nat.lt_mul_div_succ _ hp0, ?_, Dvd.intro _ rfl⟩
        rw [mul_add_one]
        have := Nat.mul_div_le (M + p * q) p
        omega
      have hbase : (p : 𝔸) ^ (q + 1) ∣ carrySeq w a n₁ := by
        obtain ⟨m, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega⟩
        exact hjump q (by omega) m (by omega) (ih (by omega) m (by omega)) hdiv
      have hprop : ∀ j, (p : 𝔸) ^ (q + 1) ∣ carrySeq w a (n₁ + j) := by
        intro j
        induction j with
        | zero => exact hbase
        | succ j ihj => exact hstep (q + 1) hq (n₁ + j) (by omega) ihj
      obtain ⟨j, rfl⟩ : ∃ j, n = n₁ + j := ⟨n - n₁, by omega⟩
      exact hprop j
  exact ⟨M + p * k, fun n hn => hmain k le_rfl n hn⟩

/-- Normalization. For a generator `w` of the kernel of `θ` and a restricted series `f`, there
is a restricted series `g` each of whose coefficients is either `0` or has nonzero image under
`θ`, such that for every `k` the partial sums `Σ_{n<N} aₙ w^n/n!` of `f` and of `g` differ by an
element of `p^k W(𝓞_ℂ_[p]♭)[w^n/n!]` for all large `N`. -/
theorem exists_normalized
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w})
    {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) :
    ∃ g ∈ restrictedPowerSeries p,
      (∀ n, PowerSeries.coeff n g = 0 ∨ fontaineTheta 𝓞_ℂ_[p] p (PowerSeries.coeff n g) ≠ 0) ∧
      ∀ k, ∃ N₀, ∀ N, N₀ ≤ N → ∃ e ∈ finiteDividedPowers p w,
        dividedPowerSum w f N - dividedPowerSum w g N = (p : 𝔸ₚ) ^ k * e := by
  have hf' : IsPadicNull fun n => PowerSeries.coeff n f := hf
  have ht : IsPadicNull (carrySeq w fun m => PowerSeries.coeff m f) :=
    isPadicNull_carrySeq hgen hf'
  refine ⟨normSeries w f, ?_, fun n => ?_, fun k => ?_⟩
  · change IsPadicNull fun n => PowerSeries.coeff n (normSeries w f)
    intro k
    have htk := ht k
    obtain ⟨N, hN⟩ := htk
    refine ⟨N, fun n hn => ?_⟩
    change (p : 𝔸) ^ k ∣ PowerSeries.coeff n (normSeries w f)
    rw [coeff_normSeries]
    exact dvd_wRem k (hN n hn)
  · rw [coeff_normSeries]
    exact wRem_normalized hgen _
  · have htk := ht k
    obtain ⟨N₁, hN₁⟩ := htk
    refine ⟨N₁ + 1, fun N hN => ?_⟩
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hdvd := dvd_mul_of_dvd_right (dvd_wQuot hgen k (hN₁ M (by omega)))
      ((M + 1 : ℕ) : 𝔸)
    obtain ⟨d, hd⟩ := hdvd
    refine ⟨algebraMap 𝔸 𝔸ₚ d * dividedPower w (M + 1),
      Subring.mul_mem _ (algebraMap_mem_finiteDividedPowers w d) (dividedPower_mem w _), ?_⟩
    rw [dividedPowerSum_sub_dividedPowerSum_normSeries, hd, map_mul, map_pow, map_natCast,
      mul_assoc]

/-- For a generator `w` of the kernel of `θ`, let `g` be a series each of whose coefficients is
either `0` or has nonzero image under `θ`. If for every `m` the partial sum
`Σ_{n<m} aₙ w^n/n!` of `g` lies in the `m`-th power of the kernel of `θ` with `p` inverted, then
`g = 0`. -/
theorem eq_zero_of_normalized
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {g : 𝔸⟦X⟧}
    (hg : ∀ n, PowerSeries.coeff n g = 0 ∨ fontaineTheta 𝓞_ℂ_[p] p (PowerSeries.coeff n g) ≠ 0)
    (h0 : ∀ m, dividedPowerSum w g m ∈ 𝕀 ^ m) : g = 0 := by
  have hw : algebraMap 𝔸 𝔸ₚ w ≠ 0 := by
    obtain ⟨c, hc⟩ := exists_eq_xi_mul_unit hgen
    have hw0 : w ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (xi_ne_zero p) c.ne_zero
    intro h
    exact hw0 (injective_algebraMap_localizationAway (h.trans (map_zero _).symm))
  have hcoeff : ∀ n, PowerSeries.coeff n g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hlow : dividedPowerSum w g n = 0 :=
        Finset.sum_eq_zero fun m hm => by
          rw [ih m (Finset.mem_range.mp hm), map_zero, zero_mul]
      have h1 := h0 (n + 1)
      rw [dividedPowerSum_succ, hlow, zero_add,
        ker_fontaineThetaInvertP_pow_eq_span_pow hgen] at h1
      have h2 := Ideal.mul_mem_left _ ((n.factorial : ℕ) : 𝔸ₚ) h1
      rw [mul_left_comm, factorial_mul_dividedPower] at h2
      obtain ⟨c, hc⟩ := mem_span_singleton'.mp h2
      have h3 : algebraMap 𝔸 𝔸ₚ (PowerSeries.coeff n g) = c * algebraMap 𝔸 𝔸ₚ w := by
        apply mul_right_cancel₀ (pow_ne_zero n hw)
        rw [← hc]
        ring
      have h4 : algebraMap 𝔸 𝔸ₚ (PowerSeries.coeff n g) ∈ 𝕀 ^ 1 := by
        rw [ker_fontaineThetaInvertP_pow_eq_span_pow hgen, pow_one, h3]
        exact Ideal.mul_mem_left _ _ (mem_span_singleton_self _)
      have h5 := mem_span_pow_of_algebraMap_mem hgen 1 h4
      rw [pow_one, ← hgen, RingHom.mem_ker] at h5
      exact (hg n).resolve_right (not_not.mpr h5)
  ext n
  rw [hcoeff n, map_zero]

end PadicComplexInt

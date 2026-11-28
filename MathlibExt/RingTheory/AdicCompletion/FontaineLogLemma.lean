/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/FontaineLogCore.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source file at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.PowerSeriesEvalMap
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Fontaine's lemma on `log(1 - β)`

This file proves, in an abstract setting, the key step of the proof of Fontaine's lemma that
`log([p̃]/p)` is not in the fraction field of `B_cris` (J.-M. Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223 (1994), Exposé II, Lemme 4.3.1 p. 87, proved in §4.3.2 pp. 87–88).

Let `A` be a commutative ring, `P` an `A`-algebra and `I` an ideal of `P`; in the application,
`A = W(𝓞_ℂ_[p]♭)`, `P = A[1/p]`, `I` is the kernel of `θ` and the `I`-adic completion of `P` is
`B_dR^+`. Let `ξ ∈ A` and `β ∈ I` with `p β = ξ`, and let `S = A⟦β⟧` be the subring of the
completion of the values `Σ aₙ βⁿ` with `aₙ ∈ A` (`AdicCompletion.evalPowerSeriesRange`). Assume
that `p` and the positive integers `n` are invertible in `P`, with `p^{v_p(n)}/n ∈ A`, that
`A ∩ I^k = ξ^k A`, that `⋂_k (p^k A + ξ^m A) = ξ^m A`, and that `ξ` is a non-zero-divisor of the
completion. Then for every nonzero `a ∈ S`, `a · log(1 - β) ∉ S`, where
`log(1 - β) = -Σ_{n ≥ 1} βⁿ/n` (`AdicCompletion.mul_evalPowerSeries_logOneSubSeries_notMem`).

The series `log(1 - X)` is written over `P` with given inverses of the positive integers
(`AdicCompletion.logOneSubSeries`), as `P` is not assumed to be a `ℚ`-algebra; when these inverses
come from a field `K` with `[Algebra ℚ K]`, it is the image of Mathlib's `PowerSeries.log K` at
`-X` (`AdicCompletion.logOneSubSeries_eq_map_rescale_log`).

## Proof

Following Fontaine: `S` is `p`-adically separated (`AdicCompletion.eq_zero_of_forall_mem_pow_mul`)
and `S ∩ Fil^i = β^i S`, where `Fil^i` is the kernel of the projection to `P ⧸ I^i`. Write
`a = p^r a'` with `a' ∉ pS`, and `a' = p s + β^i (b_i + β h)` with `b_i ∉ (p, ξ)`. For `p^j > i`
with `j > r`, `p^(j-1) log(1 - β)` is congruent to `-β^{p^j}/p` modulo `S` and `Fil^{2p^j}`; if
`a · log(1 - β) ∈ S`, then `b_i β^{i + p^j}/p ∈ S + Fil^{i + p^j + 1}`, and reducing modulo `I`
after dividing by `β^{i+p^j}` gives `b_i ∈ (p, ξ)`, a contradiction.
-/

@[expose] public noncomputable section

open PowerSeries

namespace AdicCompletion

variable (A : Type*) {P : Type*} [CommRing A] [CommRing P] [Algebra A P] (I : Ideal P)

/-- The subring `A⟦β⟧` of the `I`-adic completion of `P`: the values at `β ∈ I` of the power series
with coefficients in `A`. -/
def evalPowerSeriesRange {β : P} (hβ : β ∈ I) : Subring (AdicCompletion I P) :=
  ((evalPowerSeries I hβ).comp (PowerSeries.map (algebraMap A P))).range

/-- An element lies in `A⟦β⟧` if and only if it is the value at `β` of a series with coefficients
in `A`. -/
theorem mem_evalPowerSeriesRange {β : P} (hβ : β ∈ I) {y : AdicCompletion I P} :
    y ∈ evalPowerSeriesRange A I hβ ↔
      ∃ f : A⟦X⟧, evalPowerSeries I hβ (PowerSeries.map (algebraMap A P) f) = y :=
  RingHom.mem_range

/-- The series `log(1 - X) = -Σ_{n ≥ 1} Xⁿ/n` over a commutative ring `P`, written with given
elements `inv n` for `1/n`: its coefficient in degree `n ≥ 1` is `-inv n`, and in degree `0` it
is `0`. It is not built from Mathlib's `PowerSeries.log`, which needs a `ℚ`-algebra, as `P` is not
assumed to be one (in the application, `P = W(𝓞_ℂ_[p]♭)[1/p]` has no `ℚ`-algebra instance and
`inv n` is the image of `(n : ℚ_[p])⁻¹`); when the `inv n` are the images of the `(n : K)⁻¹` of a
field `K` with `[Algebra ℚ K]`, it is the image of `PowerSeries.log K` at `-X`
(`AdicCompletion.logOneSubSeries_eq_map_rescale_log`). -/
def logOneSubSeries (inv : ℕ → P) : P⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else -inv n

/-- For a field `K` with `[Algebra ℚ K]` and a commutative `K`-algebra `P`, the series
`logOneSubSeries` with `inv n` the image of `(n : K)⁻¹` is the image in `P⟦X⟧` of Mathlib's
`log(1 + X)` over `K` (`PowerSeries.log K`) at `-X`, i.e. of the series `log(1 - X)` over `K`. -/
theorem logOneSubSeries_eq_map_rescale_log {K : Type*} [Field K] [Algebra ℚ K] [Algebra K P] :
    logOneSubSeries (fun n => algebraMap K P (n : K)⁻¹) =
      PowerSeries.map (algebraMap K P) (rescale (-1) (PowerSeries.log K)) := by
  ext n
  rw [logOneSubSeries, coeff_mk, coeff_map, coeff_rescale, coeff_log]
  split_ifs with hn
  · rw [mul_zero, map_zero]
  · have h1 : ((-1 : K) ^ n) * (-1) ^ (n + 1) = -1 := by
      rw [← pow_add]
      exact Odd.neg_one_pow ⟨n, by ring⟩
    rw [map_div₀, map_pow, map_neg, map_one, map_natCast, ← map_neg (algebraMap K P)]
    congr 1
    rw [div_eq_mul_inv, ← mul_assoc, h1, neg_one_mul]

/-- The image of `y ∈ P` in the completion is its image under the algebra map. -/
private theorem of_eq_algebraMap (y : P) : of I P y = algebraMap P (AdicCompletion I P) y := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- Modulo `I ^ n`, the image of `y ∈ P` in the completion is the class of `y`. -/
private theorem evalₐ_algebraMap (n : ℕ) (y : P) :
    evalₐ I n (algebraMap P (AdicCompletion I P) y) = Ideal.Quotient.mk (I ^ n) y := by
  rw [← of_eq_algebraMap, evalₐ_of]

/-- The value of a constant series `C y` is the image of `y` under the algebra map. -/
private theorem evalPowerSeries_C' {x : P} (hx : x ∈ I) (y : P) :
    evalPowerSeries I hx (C y) = algebraMap P (AdicCompletion I P) y := by
  rw [evalPowerSeries_C, of_eq_algebraMap]

/-- The value of `X` at `x` is the image of `x` under the algebra map. -/
private theorem evalPowerSeries_X' {x : P} (hx : x ∈ I) :
    evalPowerSeries I hx X = algebraMap P (AdicCompletion I P) x := by
  rw [evalPowerSeries_X, of_eq_algebraMap]

/-- The value at `x` of a polynomial `Q` is the image of `Q.eval x` under the algebra map. -/
private theorem evalPowerSeries_coe' {x : P} (hx : x ∈ I) (Q : Polynomial P) :
    evalPowerSeries I hx (Q : P⟦X⟧) = algebraMap P (AdicCompletion I P) (Q.eval x) := by
  rw [evalPowerSeries_coe, of_eq_algebraMap]

/-- The value at `β` of a series with coefficients in `A` lies in `A⟦β⟧`. -/
private theorem evalPowerSeries_map_mem {β : P} (hβI : β ∈ I) (f : A⟦X⟧) :
    evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f) ∈ evalPowerSeriesRange A I hβI :=
  (mem_evalPowerSeriesRange A I hβI).mpr ⟨f, rfl⟩

variable (p : ℕ)

/-- If `p β = ξ`, then `p ^ m` times the value at `β` of the truncation below degree `m` of a
series `Σ aₙ Xⁿ` with coefficients in `A` is the image of `Σ_{n<m} aₙ ξⁿ p^{m-n} ∈ A`. -/
private theorem natCast_pow_mul_eval_trunc {β : P} (ξ : A) (hpβ : (p : P) * β = algebraMap A P ξ)
    (f : A⟦X⟧) (m : ℕ) :
    (p : P) ^ m * (trunc m (PowerSeries.map (algebraMap A P) f)).eval β =
      algebraMap A P (∑ i ∈ Finset.range m, coeff i f * ξ ^ i * (p : A) ^ (m - i)) := by
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := (Finset.mem_range.mp hi).le
  simp only [RingHom.id_apply, PowerSeries.coeff_map, map_mul, map_pow, map_natCast]
  have hm : (p : P) ^ m = (p : P) ^ (m - i) * (p : P) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hm, ← hpβ]
  ring

/-- Modulo `I ^ m`, `p ^ m` times an element of `A⟦β⟧` is the class of an element of `A`. -/
private theorem exists_evalₐ_natCast_pow_mul {β : P} (hβI : β ∈ I) (ξ : A)
    (hpβ : (p : P) * β = algebraMap A P ξ) (f : A⟦X⟧) (m : ℕ) :
    ∃ w : A, evalₐ I m ((p : AdicCompletion I P) ^ m *
      evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f)) =
        Ideal.Quotient.mk (I ^ m) (algebraMap A P w) := by
  refine ⟨∑ i ∈ Finset.range m, coeff i f * ξ ^ i * (p : A) ^ (m - i), ?_⟩
  rw [map_mul, evalₐ_evalPowerSeries, map_pow, map_natCast,
    ← map_natCast (Ideal.Quotient.mk (I ^ m)), ← map_pow, ← map_mul,
    natCast_pow_mul_eval_trunc A p ξ hpβ f m]

/-- **`A⟦β⟧` is `p`-adically separated**: let `A` be a commutative ring, `P` a commutative
`A`-algebra, `I` an ideal of `P`, `p` a natural number with `p · pinv = 1` in `P`, and `β ∈ I`
with `p β = ξ` for some `ξ ∈ A`. Assume that, for every `k`, every `a ∈ A` whose image lies in
`I^k` lies in `ξ^k A`, and that `⋂_k (p^k A + ξ^m A) = ξ^m A` for every `m`. Then an element `x`
of the completion such that, for every `k`, `x = p^k y` for some `y ∈ A⟦β⟧`, is zero. -/
theorem eq_zero_of_forall_mem_pow_mul {β : P} (hβI : β ∈ I) (ξ : A) {pinv : P}
    (hpβ : (p : P) * β = algebraMap A P ξ) (hpinv : (p : P) * pinv = 1)
    (hξpow : ∀ (k : ℕ) (a : A), algebraMap A P a ∈ I ^ k → a ∈ Ideal.span {ξ ^ k})
    (hsepA : ∀ (m : ℕ) (w : A), (∀ k : ℕ, ∃ a b : A, w = (p : A) ^ k * a + ξ ^ m * b) →
      w ∈ Ideal.span {ξ ^ m})
    (x : AdicCompletion I P)
    (h : ∀ k : ℕ, ∃ y ∈ evalPowerSeriesRange A I hβI, x = (p : AdicCompletion I P) ^ k * y) :
    x = 0 := by
  have hξI : algebraMap A P ξ ∈ I := hpβ ▸ I.mul_mem_left (p : P) hβI
  refine ext_evalₐ fun m => ?_
  rw [map_zero]
  choose y hy hxy using h
  choose f hf using fun k => (mem_evalPowerSeriesRange A I hβI).mp (hy k)
  choose w hw using fun k => exists_evalₐ_natCast_pow_mul A I p hβI ξ hpβ (f k) m
  have hk : ∀ k, evalₐ I m ((p : AdicCompletion I P) ^ m * x) =
      Ideal.Quotient.mk (I ^ m) (algebraMap A P ((p : A) ^ k * w k)) := by
    intro k
    rw [hxy k, mul_left_comm, map_mul, ← hf k, hw k]
    simp only [map_mul, map_pow, map_natCast]
  have hw0 : w 0 ∈ Ideal.span {ξ ^ m} := by
    refine hsepA m (w 0) fun k => ?_
    have e := (hk 0).symm.trans (hk k)
    rw [Ideal.Quotient.eq, ← map_sub] at e
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hξpow m _ e)
    exact ⟨w k, b, by rw [pow_zero, one_mul] at hb; linear_combination -hb⟩
  have h0 : evalₐ I m ((p : AdicCompletion I P) ^ m * x) = 0 := by
    rw [hk 0, pow_zero, one_mul, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hw0
    rw [← hc, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hξI m)
  rw [map_mul, map_pow, map_natCast] at h0
  have hu : IsUnit ((p : P ⧸ I ^ m) ^ m) := by
    refine (IsUnit.of_mul_eq_one (Ideal.Quotient.mk (I ^ m) pinv) ?_).pow m
    rw [← map_natCast (Ideal.Quotient.mk (I ^ m)), ← map_mul, hpinv, map_one]
  exact hu.mul_right_eq_zero.mp h0

/-- **`A⟦β⟧ ∩ Fil^i = β^i A⟦β⟧`**: an element of `A⟦β⟧` whose image in `P ⧸ I ^ i` vanishes is
`β ^ i` times an element of `A⟦β⟧`. -/
private theorem exists_eq_pow_mul_of_evalₐ_eq_zero {β : P} (hβI : β ∈ I) (ξ : A) {pinv : P}
    (hpβ : (p : P) * β = algebraMap A P ξ) (hpinv : (p : P) * pinv = 1)
    (hξpow : ∀ (k : ℕ) (a : A), algebraMap A P a ∈ I ^ k → a ∈ Ideal.span {ξ ^ k})
    (f : A⟦X⟧) (i : ℕ)
    (h : evalₐ I i (evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f)) = 0) :
    ∃ g : A⟦X⟧, evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f) =
      algebraMap P (AdicCompletion I P) β ^ i *
        evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) g) := by
  have hdec : PowerSeries.map (algebraMap A P) f =
      ((trunc i (PowerSeries.map (algebraMap A P) f) : Polynomial P) : P⟦X⟧) +
        X ^ i * PowerSeries.map (algebraMap A P) (PowerSeries.mk fun k => coeff (k + i) f) := by
    ext n
    rw [map_add, Polynomial.coeff_coe, coeff_trunc, coeff_X_pow_mul']
    by_cases hn : n < i
    · rw [ite_eq_left hn, ite_eq_right (by omega), add_zero]
    · rw [ite_eq_right hn, ite_eq_left (by omega), zero_add, PowerSeries.coeff_map,
        PowerSeries.coeff_map, PowerSeries.coeff_mk, Nat.sub_add_cancel (by omega)]
  have hsplit : evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f) =
      algebraMap P (AdicCompletion I P) ((trunc i (PowerSeries.map (algebraMap A P) f)).eval β) +
        algebraMap P (AdicCompletion I P) β ^ i * evalPowerSeries I hβI
          (PowerSeries.map (algebraMap A P) (PowerSeries.mk fun k => coeff (k + i) f)) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_mul, map_pow, evalPowerSeries_X', evalPowerSeries_coe']
  have hβi : (Ideal.Quotient.mk (I ^ i) β) ^ i = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hβI i
  have hQ : (trunc i (PowerSeries.map (algebraMap A P) f)).eval β ∈ I ^ i := by
    have h2 := congrArg (evalₐ I i) hsplit
    rw [h, map_add, map_mul, map_pow, evalₐ_algebraMap I, evalₐ_algebraMap I, hβi, zero_mul,
      add_zero] at h2
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h2.symm
  have hw : algebraMap A P (∑ n ∈ Finset.range i, coeff n f * ξ ^ n * (p : A) ^ (i - n)) ∈
      I ^ i := by
    rw [← natCast_pow_mul_eval_trunc A p ξ hpβ f i]
    exact Ideal.mul_mem_left _ _ hQ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hξpow i _ hw)
  have hQc : (trunc i (PowerSeries.map (algebraMap A P) f)).eval β = β ^ i * algebraMap A P c := by
    refine ((IsUnit.of_mul_eq_one _ hpinv).pow i).mul_left_cancel ?_
    rw [natCast_pow_mul_eval_trunc A p ξ hpβ f i, ← hc, map_mul, map_pow, ← hpβ]
    ring
  refine ⟨C c + PowerSeries.mk fun k => coeff (k + i) f, ?_⟩
  rw [hsplit, hQc, map_add, map_add, PowerSeries.map_C, evalPowerSeries_C', map_mul, map_pow]
  ring

/-- If every coefficient of `f` lies in the ideal `(p, ξ)` of `A`, the value of `f` at `β` lies
in `p A⟦β⟧`. -/
private theorem exists_eq_natCast_mul_of_coeff_mem {β : P} (hβI : β ∈ I) (ξ : A)
    (hpβ : (p : P) * β = algebraMap A P ξ) (f : A⟦X⟧)
    (hf : ∀ n, coeff n f ∈ Ideal.span {(p : A), ξ}) :
    ∃ y ∈ evalPowerSeriesRange A I hβI,
      evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f) =
        (p : AdicCompletion I P) * y := by
  choose d e hde using fun n => Ideal.mem_span_pair.mp (hf n)
  refine ⟨evalPowerSeries I hβI (PowerSeries.map (algebraMap A P)
    (PowerSeries.mk d + X * PowerSeries.mk e)), evalPowerSeries_map_mem A I hβI _, ?_⟩
  have hf' : f = C (p : A) * PowerSeries.mk d + C ξ * PowerSeries.mk e := by
    ext n
    rw [map_add, coeff_C_mul, coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← hde n]
    ring
  rw [hf']
  simp only [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_X, evalPowerSeries_C',
    evalPowerSeries_X', map_natCast]
  rw [← hpβ, map_mul, map_natCast]
  ring

/-- If the coefficients of `f` of degree `< i` lie in `(p, ξ)`, then the value of `f` at `β` is
`p s + β ^ i h`, with `s ∈ A⟦β⟧` and `h` the value of `Σ_k a_{k+i} Xᵏ`. -/
private theorem exists_eq_natCast_mul_add_pow_mul {β : P} (hβI : β ∈ I) (ξ : A)
    (hpβ : (p : P) * β = algebraMap A P ξ) (f : A⟦X⟧) (i : ℕ)
    (hi : ∀ n < i, coeff n f ∈ Ideal.span {(p : A), ξ}) :
    ∃ s ∈ evalPowerSeriesRange A I hβI,
      evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) f) =
        (p : AdicCompletion I P) * s + algebraMap P (AdicCompletion I P) β ^ i *
          evalPowerSeries I hβI (PowerSeries.map (algebraMap A P)
            (PowerSeries.mk fun k => coeff (k + i) f)) := by
  have hgJ : ∀ n, coeff n (PowerSeries.mk fun n => if n < i then coeff n f else 0) ∈
      Ideal.span {(p : A), ξ} := by
    intro n
    rw [PowerSeries.coeff_mk]
    split_ifs with hn
    · exact hi n hn
    · exact Ideal.zero_mem _
  obtain ⟨s, hs, hgs⟩ := exists_eq_natCast_mul_of_coeff_mem A I p hβI ξ hpβ _ hgJ
  refine ⟨s, hs, ?_⟩
  have hdec : f = (PowerSeries.mk fun n => if n < i then coeff n f else 0) +
      X ^ i * PowerSeries.mk fun k => coeff (k + i) f := by
    ext n
    rw [map_add, coeff_X_pow_mul']
    simp only [PowerSeries.coeff_mk]
    by_cases hn : n < i
    · rw [ite_eq_left hn, ite_eq_right (by omega), add_zero]
    · rw [ite_eq_right hn, ite_eq_left (by omega), zero_add, Nat.sub_add_cancel (by omega)]
  conv_lhs => rw [hdec]
  rw [map_add, map_add, hgs, map_mul, map_mul, map_pow, map_pow, PowerSeries.map_X,
    evalPowerSeries_X']

/-- **Fontaine's splitting of `log(1 - X)`**: for `j ≥ 1`, `p^{j-1} log(1 - X)` is the sum of a
series with coefficients in `A`, of `-X^{p^j}/p` and of a multiple of `X^{2p^j}`. -/
private theorem exists_C_pow_mul_logOneSubSeries_eq [Fact p.Prime] {pinv : P}
    (hpinv : (p : P) * pinv = 1) (inv : ℕ → P) (hinv : ∀ n : ℕ, n ≠ 0 → (n : P) * inv n = 1)
    (hint : ∀ n : ℕ, n ≠ 0 → ∃ w : A, algebraMap A P w * (n : P) = (p : P) ^ padicValNat p n)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ (q : A⟦X⟧) (T : P⟦X⟧), C ((p : P) ^ (j - 1)) * logOneSubSeries inv =
      PowerSeries.map (algebraMap A P) q - C pinv * X ^ (p ^ j) + X ^ (2 * p ^ j) * T := by
  have hp : p.Prime := Fact.out
  have hN : 0 < p ^ j := pow_pos hp.pos j
  have hwex : ∀ n : ℕ, ∃ w : A, (n ≠ 0 → ¬ p ^ j ∣ n →
      algebraMap A P w = (p : P) ^ (j - 1) * inv n) := by
    intro n
    by_cases hn : n ≠ 0 ∧ ¬ p ^ j ∣ n
    · obtain ⟨w0, hw0⟩ := hint n hn.1
      have hv : padicValNat p n < j := by
        by_contra hc
        exact hn.2 ((multiplicity_dvd_iff_le hn.1).mpr (by rw [← Nat.padicValNat_def]; omega))
      refine ⟨w0 * (p : A) ^ (j - 1 - padicValNat p n), fun _ _ => ?_⟩
      have hle : padicValNat p n ≤ j - 1 := by omega
      have e1 : (p : P) ^ (j - 1) =
          (p : P) ^ padicValNat p n * (p : P) ^ (j - 1 - padicValNat p n) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      have e2 := hinv n hn.1
      rw [map_mul, map_pow, map_natCast, e1, ← hw0]
      linear_combination (-(algebraMap A P w0) * (p : P) ^ (j - 1 - padicValNat p n)) * e2
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose w hw using hwex
  refine ⟨PowerSeries.mk fun n => if n = 0 ∨ n = p ^ j ∨ 2 * p ^ j ≤ n then 0 else -w n,
    PowerSeries.mk fun n => -((p : P) ^ (j - 1) * inv (n + 2 * p ^ j)), ?_⟩
  ext n
  rw [coeff_C_mul, map_add, map_sub, PowerSeries.coeff_map, coeff_C_mul, coeff_X_pow,
    coeff_X_pow_mul', logOneSubSeries]
  simp only [PowerSeries.coeff_mk]
  by_cases h0 : n = 0
  · subst h0
    have h1 : (0 : ℕ) ≠ p ^ j := by omega
    have h2 : ¬ 2 * p ^ j ≤ 0 := by omega
    simp [h1, h2]
  · by_cases hNn : n = p ^ j
    · subst hNn
      have h2 : ¬ 2 * p ^ j ≤ p ^ j := by omega
      have e3 : ((p ^ j : ℕ) : P) * inv (p ^ j) = 1 := hinv _ (by omega)
      have e4 : pinv ^ j * (p : P) ^ j = 1 := by rw [← mul_pow, mul_comm pinv, hpinv, one_pow]
      have e5 : inv (p ^ j) = pinv ^ j := by
        calc inv (p ^ j) = (pinv ^ j * (p : P) ^ j) * inv (p ^ j) := by rw [e4, one_mul]
          _ = pinv ^ j * (((p ^ j : ℕ) : P) * inv (p ^ j)) := by push_cast; ring
          _ = pinv ^ j := by rw [e3, mul_one]
      have e7 : pinv ^ j = pinv ^ (j - 1) * pinv := by rw [← pow_succ, Nat.sub_add_cancel hj]
      have e6 : (p : P) ^ (j - 1) * pinv ^ j = pinv := by
        rw [e7, ← mul_assoc, ← mul_pow, hpinv, one_pow, one_mul]
      have hor : p ^ j = 0 ∨ p ^ j = p ^ j ∨ 2 * p ^ j ≤ p ^ j := Or.inr (Or.inl rfl)
      rw [ite_eq_right h0, ite_eq_left hor, map_zero, ite_eq_left rfl, ite_eq_right h2, add_zero,
        zero_sub, mul_one, e5]
      linear_combination -e6
    · by_cases hbig : 2 * p ^ j ≤ n
      · have hor : n = 0 ∨ n = p ^ j ∨ 2 * p ^ j ≤ n := Or.inr (Or.inr hbig)
        rw [ite_eq_right h0, ite_eq_left hor, map_zero, ite_eq_right hNn, ite_eq_left hbig,
          mul_zero, sub_zero, zero_add, Nat.sub_add_cancel hbig]
        ring
      · have hndvd : ¬ p ^ j ∣ n := by
          rintro ⟨c, hc⟩
          rcases c with _ | _ | c
          · exact h0 (by simpa using hc)
          · exact hNn (by simpa using hc)
          · apply hbig
            rw [hc]
            nlinarith
        have hor : ¬ (n = 0 ∨ n = p ^ j ∨ 2 * p ^ j ≤ n) := by omega
        rw [ite_eq_right h0, ite_eq_right hor, ite_eq_right hNn, ite_eq_right hbig, map_neg,
          hw n h0 hndvd, mul_zero, sub_zero, add_zero]
        ring

/-- **Fontaine's lemma, abstract form**: let `A` be a commutative ring, `P` a commutative
`A`-algebra, `I` an ideal of `P`, `p` a prime with `p · pinv = 1` in `P`, and `β ∈ I` with
`p β = ξ` for some `ξ ∈ A`. Let `inv n ∈ P` satisfy `n · inv n = 1` for every `n ≠ 0`. Assume
that `p^{v_p(n)}/n ∈ A` for every `n ≠ 0` (the image of some `w ∈ A`, times `n`, is `p^{v_p(n)}`
in `P`), that, for every `k`, every `a ∈ A` whose image lies in `I^k` lies in `ξ^k A`, that
`⋂_k (p^k A + ξ^m A) = ξ^m A` for every `m`, and that `ξ` is a non-zero-divisor of the completion.
Then `a · log(1 - β) ∉ A⟦β⟧` for every nonzero `a ∈ A⟦β⟧`, where `log(1 - β) = -Σ_{n ≥ 1} βⁿ/n`
is the value at `β` of `logOneSubSeries inv`. -/
theorem mul_evalPowerSeries_logOneSubSeries_notMem [Fact p.Prime] {β : P} (hβI : β ∈ I) (ξ : A)
    {pinv : P} (hpβ : (p : P) * β = algebraMap A P ξ) (hpinv : (p : P) * pinv = 1)
    (inv : ℕ → P) (hinv : ∀ n : ℕ, n ≠ 0 → (n : P) * inv n = 1)
    (hint : ∀ n : ℕ, n ≠ 0 → ∃ w : A, algebraMap A P w * (n : P) = (p : P) ^ padicValNat p n)
    (hξpow : ∀ (k : ℕ) (a : A), algebraMap A P a ∈ I ^ k → a ∈ Ideal.span {ξ ^ k})
    (hsepA : ∀ (m : ℕ) (w : A), (∀ k : ℕ, ∃ a b : A, w = (p : A) ^ k * a + ξ ^ m * b) →
      w ∈ Ideal.span {ξ ^ m})
    (hreg : ∀ x : AdicCompletion I P,
      algebraMap P (AdicCompletion I P) (algebraMap A P ξ) * x = 0 → x = 0)
    {a : AdicCompletion I P} (ha : a ∈ evalPowerSeriesRange A I hβI) (ha0 : a ≠ 0) :
    a * evalPowerSeries I hβI (logOneSubSeries inv) ∉ evalPowerSeriesRange A I hβI := by
  classical
  intro hb
  have hp : p.Prime := Fact.out
  set S := evalPowerSeriesRange A I hβI
  obtain ⟨b, hbdef⟩ : ∃ b : AdicCompletion I P, b = algebraMap P (AdicCompletion I P) β :=
    ⟨_, rfl⟩
  obtain ⟨π, hπdef⟩ : ∃ π : AdicCompletion I P, π = algebraMap P (AdicCompletion I P) pinv :=
    ⟨_, rfl⟩
  have hpp : (p : AdicCompletion I P) * π = 1 := by
    rw [hπdef, ← map_natCast (algebraMap P (AdicCompletion I P)), ← map_mul, hpinv, map_one]
  -- `β` is a non-zero-divisor of the completion, since `ξ = p β` is one and `p` is a unit.
  have hbreg : ∀ x : AdicCompletion I P, b * x = 0 → x = 0 := by
    intro x hx
    have h1 : algebraMap P (AdicCompletion I P) (algebraMap A P ξ) * (π * x) = 0 := by
      rw [← hpβ, map_mul, map_natCast, ← hbdef]
      have e : (p : AdicCompletion I P) * b * (π * x) =
          π * (p : AdicCompletion I P) * (b * x) := by
        ring
      rw [e, hx, mul_zero]
    have h2 := hreg _ h1
    calc x = (p : AdicCompletion I P) * π * x := by rw [hpp, one_mul]
      _ = (p : AdicCompletion I P) * (π * x) := by ring
      _ = 0 := by rw [h2, mul_zero]
  have hbpow : ∀ (k : ℕ) (x y : AdicCompletion I P), b ^ k * x = b ^ k * y → x = y := by
    intro k
    induction k with
    | zero =>
      intro x y h
      simpa using h
    | succ k ih =>
      intro x y h
      apply ih
      have h' : b * (b ^ k * x - b ^ k * y) = 0 := by
        have e : b * (b ^ k * x - b ^ k * y) = b ^ (k + 1) * x - b ^ (k + 1) * y := by ring
        rw [e, h, sub_self]
      exact sub_eq_zero.mp (hbreg _ h')
  have hbS : b ∈ S := by
    refine (mem_evalPowerSeriesRange A I hβI).mpr ⟨X, ?_⟩
    rw [PowerSeries.map_X, evalPowerSeries_X' I hβI, hbdef]
  have hpS : ∀ k : ℕ, ((p : AdicCompletion I P) ^ k) ∈ S := fun k =>
    Subring.pow_mem _ (natCast_mem _ p) k
  -- Step 1: `a = p^r a'` with `a' ∉ p A⟦β⟧`.
  have hex : ∃ k : ℕ, ¬ ∃ y ∈ S, a = (p : AdicCompletion I P) ^ k * y := by
    by_contra hc
    exact ha0 (eq_zero_of_forall_mem_pow_mul A I p hβI ξ hpβ hpinv hξpow hsepA a
      fun k => not_not.mp (not_exists.mp hc k))
  have hK0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact this ⟨a, ha, by rw [pow_zero, one_mul]⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.find hex = r + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hra : ∃ y ∈ S, a = (p : AdicCompletion I P) ^ r * y :=
    not_not.mp (Nat.find_min hex (show r < Nat.find hex by omega))
  obtain ⟨a', ha'S, haa'⟩ := hra
  have ha'p : ¬ ∃ y ∈ S, a' = (p : AdicCompletion I P) * y := by
    rintro ⟨y, hy, hy'⟩
    have := Nat.find_spec hex
    rw [hr] at this
    exact this ⟨y, hy, by rw [haa', hy']; ring⟩
  -- Step 2: the first coefficient outside `(p, ξ)`.
  obtain ⟨f, hf⟩ := (mem_evalPowerSeriesRange A I hβI).mp ha'S
  have hcex : ∃ n, coeff n f ∉ Ideal.span {(p : A), ξ} := by
    by_contra hc
    obtain ⟨y, hy, hy'⟩ := exists_eq_natCast_mul_of_coeff_mem A I p hβI ξ hpβ f
      fun n => not_not.mp (not_exists.mp hc n)
    exact ha'p ⟨y, hy, by rw [← hf, hy']⟩
  have hci : coeff (Nat.find hcex) f ∉ Ideal.span {(p : A), ξ} := Nat.find_spec hcex
  have hlow : ∀ n < Nat.find hcex, coeff n f ∈ Ideal.span {(p : A), ξ} :=
    fun n hn => not_not.mp (Nat.find_min hcex hn)
  obtain ⟨i, hi⟩ : ∃ i, i = Nat.find hcex := ⟨_, rfl⟩
  rw [← hi] at hci hlow
  obtain ⟨s, hsS, hsdec⟩ := exists_eq_natCast_mul_add_pow_mul A I p hβI ξ hpβ f i hlow
  rw [← hbdef, hf] at hsdec
  -- `H = c₀ + β h'`, where `H` is the value of `Σ_k a_{k+i} Xᵏ`.
  obtain ⟨H, hHdef⟩ : ∃ H : AdicCompletion I P, H = evalPowerSeries I hβI
      (PowerSeries.map (algebraMap A P) (PowerSeries.mk fun k => coeff (k + i) f)) := ⟨_, rfl⟩
  obtain ⟨h', hh'def⟩ : ∃ h' : AdicCompletion I P, h' = evalPowerSeries I hβI
      (PowerSeries.map (algebraMap A P) (PowerSeries.mk fun k => coeff (k + 1 + i) f)) :=
    ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0 : AdicCompletion I P,
      c0 = algebraMap P (AdicCompletion I P) (algebraMap A P (coeff i f)) := ⟨_, rfl⟩
  have hHdec : H = c0 + b * h' := by
    have hd : (PowerSeries.mk fun k => coeff (k + i) f) =
        C (coeff i f) + X * PowerSeries.mk fun k => coeff (k + 1 + i) f := by
      ext n
      rcases n with _ | n
      · rw [PowerSeries.coeff_mk, map_add, coeff_C, ite_eq_left rfl, coeff_zero_X_mul, add_zero,
          zero_add]
      · rw [PowerSeries.coeff_mk, map_add, coeff_C, ite_eq_right (Nat.succ_ne_zero n), zero_add,
          coeff_succ_X_mul, PowerSeries.coeff_mk]
    rw [hHdef, hd, map_add, map_add, PowerSeries.map_C, evalPowerSeries_C' I hβI, map_mul,
      map_mul, PowerSeries.map_X, evalPowerSeries_X' I hβI, hc0def, hbdef, hh'def]
  rw [← hHdef] at hsdec
  -- Step 3: the splitting of `log(1 - β)` at `N = p^j`.
  obtain ⟨j, hjdef⟩ : ∃ j, j = i + r + 1 := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by omega
  have hiN : i < p ^ j :=
    lt_of_lt_of_le (show i < j by omega) (Nat.lt_pow_self hp.one_lt).le
  obtain ⟨q, T, hqT⟩ := exists_C_pow_mul_logOneSubSeries_eq A p hpinv inv hinv hint j hj1
  obtain ⟨T', hT'def⟩ : ∃ T' : AdicCompletion I P, T' = evalPowerSeries I hβI T := ⟨_, rfl⟩
  obtain ⟨Q', hQ'def⟩ : ∃ Q' : AdicCompletion I P,
      Q' = evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) q) := ⟨_, rfl⟩
  have hU : (p : AdicCompletion I P) ^ (j - 1) * evalPowerSeries I hβI (logOneSubSeries inv) =
      Q' - π * b ^ (p ^ j) + b ^ (2 * p ^ j) * T' := by
    have := congrArg (evalPowerSeries I hβI) hqT
    rw [map_mul, evalPowerSeries_C' I hβI, map_pow, map_natCast, map_add, map_sub, map_mul,
      map_mul, evalPowerSeries_C' I hβI, map_pow, map_pow, evalPowerSeries_X' I hβI] at this
    rw [this, hQ'def, hπdef, hbdef, hT'def]
  have hle : r ≤ j - 1 := by omega
  have hpr : (p : AdicCompletion I P) ^ (j - 1) =
      (p : AdicCompletion I P) ^ (j - 1 - r) * (p : AdicCompletion I P) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hmem1 : (p : AdicCompletion I P) ^ (j - 1) *
      (a' * evalPowerSeries I hβI (logOneSubSeries inv)) ∈ S := by
    have e : (p : AdicCompletion I P) ^ (j - 1) *
        (a' * evalPowerSeries I hβI (logOneSubSeries inv)) =
        (p : AdicCompletion I P) ^ (j - 1 - r) *
          (a * evalPowerSeries I hβI (logOneSubSeries inv)) := by
      rw [hpr, haa']
      ring
    rw [e]
    exact Subring.mul_mem _ (hpS _) hb
  obtain ⟨s1, hs1def⟩ : ∃ s1 : AdicCompletion I P, s1 = a' * Q' -
      (p : AdicCompletion I P) ^ (j - 1) * (a' * evalPowerSeries I hβI (logOneSubSeries inv)) :=
    ⟨_, rfl⟩
  have hs1S : s1 ∈ S := by
    rw [hs1def, hQ'def]
    exact Subring.sub_mem _ (Subring.mul_mem _ ha'S (evalPowerSeries_map_mem A I hβI q)) hmem1
  have hkey : a' * π * b ^ (p ^ j) = s1 + b ^ (2 * p ^ j) * (a' * T') := by
    have e : (p : AdicCompletion I P) ^ (j - 1) *
        (a' * evalPowerSeries I hβI (logOneSubSeries inv)) =
        a' * ((p : AdicCompletion I P) ^ (j - 1) *
          evalPowerSeries I hβI (logOneSubSeries inv)) := by
      ring
    rw [hs1def, e, hU]
    ring
  -- `σ = β^{i+N} Z` with `σ ∈ A⟦β⟧`.
  have hσS : s1 - s * b ^ (p ^ j) ∈ S :=
    Subring.sub_mem _ hs1S (Subring.mul_mem _ hsS (Subring.pow_mem _ hbS _))
  have e2N : b ^ (2 * p ^ j) = b ^ (i + p ^ j) * b ^ (p ^ j - i) := by
    rw [← pow_add]
    congr 1
    omega
  have eiN : b ^ (i + p ^ j) = b ^ i * b ^ (p ^ j) := pow_add b i (p ^ j)
  have hσZ : s1 - s * b ^ (p ^ j) =
      b ^ (i + p ^ j) * (π * c0 - b ^ (p ^ j - i) * (a' * T') + b * (π * h')) := by
    have ha'dec : a' = (p : AdicCompletion I P) * s + b ^ i * H := hsdec
    linear_combination (-1 : AdicCompletion I P) * hkey + (π * b ^ (p ^ j)) * ha'dec +
      (s * b ^ (p ^ j)) * hpp + (b ^ (i + p ^ j) * π) * hHdec - (π * H) * eiN - (a' * T') * e2N
  -- `σ ∈ β^{i+N} A⟦β⟧`, then cancel `β^{i+N}`.
  obtain ⟨g0, hg0⟩ := (mem_evalPowerSeriesRange A I hβI).mp hσS
  have hev0 : evalₐ I (i + p ^ j)
      (evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) g0)) = 0 := by
    rw [hg0, hσZ, map_mul, map_pow, hbdef, evalₐ_algebraMap I, ← map_pow,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.pow_mem_pow hβI _), zero_mul]
  obtain ⟨g, hg⟩ := exists_eq_pow_mul_of_evalₐ_eq_zero A I p hβI ξ hpβ hpinv hξpow g0
    (i + p ^ j) hev0
  rw [hg0, hσZ, ← hbdef] at hg
  have hZ := hbpow _ _ _ hg
  -- Reduce modulo `I`.
  have hZ1 := congrArg (evalₐ I 1) hZ
  have hβ1 : evalₐ I 1 b = 0 := by
    rw [hbdef, evalₐ_algebraMap I, Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hβI
  have hNi0 : p ^ j - i ≠ 0 := by omega
  have htr : evalₐ I 1 (evalPowerSeries I hβI (PowerSeries.map (algebraMap A P) g)) =
      Ideal.Quotient.mk (I ^ 1) (algebraMap A P (coeff 0 g)) := by
    rw [evalₐ_evalPowerSeries, Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.sum_range_one,
      pow_zero, mul_one, RingHom.id_apply, PowerSeries.coeff_map]
  simp only [map_add, map_sub, map_mul, map_pow, hβ1, zero_pow hNi0, zero_mul, sub_zero,
    add_zero, htr] at hZ1
  rw [hπdef, hc0def, evalₐ_algebraMap I, evalₐ_algebraMap I, ← map_mul, Ideal.Quotient.eq,
    pow_one] at hZ1
  have hmem : algebraMap A P (coeff i f - (p : A) * coeff 0 g) ∈ I ^ 1 := by
    have e : algebraMap A P (coeff i f - (p : A) * coeff 0 g) =
        (p : P) * (pinv * algebraMap A P (coeff i f) - algebraMap A P (coeff 0 g)) := by
      rw [map_sub, map_mul, map_natCast]
      linear_combination (-(algebraMap A P (coeff i f))) * hpinv
    rw [e, pow_one]
    exact Ideal.mul_mem_left _ _ hZ1
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hξpow 1 _ hmem)
  apply hci
  refine Ideal.mem_span_pair.mpr ⟨coeff 0 g, d, ?_⟩
  rw [pow_one] at hd
  linear_combination hd

end AdicCompletion

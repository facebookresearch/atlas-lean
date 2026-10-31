/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import MathlibExt.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Rankin–Selberg product in the Selberg class

For `F, G` in the Selberg class with Euler logarithms `log F = ∑ b(n) n^{-s}` and
`log G = ∑ c(n) n^{-s}`, the *Rankin–Selberg product* `F ⊗ G` is defined through its logarithm:
`log (F ⊗ G) = ∑ k b(pᵏ) c(pᵏ) p^{-ks}`. A function `F ∈ 𝒮` is *`⊗`-simple* if `F ⊗ F̄`
continues analytically to `Re s ≥ 1/2` except for a simple pole at `s = 1`.

## Main definitions

* `SelbergClass.tensorLog b c`: the coefficients `k · b(pᵏ) · c(pᵏ)` of `log (F ⊗ G)`.
* `SelbergClass.tensor b c`: the Rankin–Selberg product `(F ⊗ G)(s) = exp L(tensorLog b c, s)`.
* `ArithmeticFunction.IsTensorSimple a`: `a ∈ 𝒮` is `⊗`-simple.

## Main statements

* `ArithmeticFunction.IsEulerLog.norm_apply_prime_pow_le`: a bound `|a n| ≤ c n^ε` on the
  coefficients gives `|b(pᵏ)| ≤ ((1 + c)^k - 1) p^{kε} / k` on the Euler logarithm.
* `SelbergClass.LSeriesSummable_tensorLog`: for `F, G ∈ 𝒮` the Dirichlet series of
  `log (F ⊗ G)` converges absolutely on `Re s > 1`.
* `ArithmeticFunction.IsTensorSimple.neg_one_le_meromorphicOrderAt`: a `⊗`-simple `F` has at
  most a simple pole at `s = 1`.
-/

open Complex Filter Topology

@[expose] public section

namespace ArithmeticFunction

/-- **Bounds for Euler logarithms at prime powers.** If `a 1 = 1`, `L(a, s)` converges absolutely
on `Re s > 1`, `b` is an Euler logarithm of `a` and `|a n| ≤ c n^ε` for `n > 0`, then
`|b(pᵏ)| ≤ ((1 + c)^k - 1) p^{kε} / k` for every prime `p` and `k ≥ 1`. -/
theorem IsEulerLog.norm_apply_prime_pow_le {a : ArithmeticFunction ℂ} {b : ℕ → ℂ}
    (hb : IsEulerLog a b) (ha1 : a 1 = 1)
    (haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s) {c ε : ℝ}
    (hc : ∀ n : ℕ, 0 < n → ‖a n‖ ≤ c * (n : ℝ) ^ ε) {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : 1 ≤ k) :
    ‖b (p ^ k)‖ ≤ ((1 + c) ^ k - 1) * (p : ℝ) ^ ((k : ℝ) * ε) / k := by
  have hrec := hb.natCast_mul_apply_prime_pow haS hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set P : ℝ := (p : ℝ) ^ ε with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hp0 ε
  have hpow : ∀ m : ℕ, (p : ℝ) ^ ((m : ℝ) * ε) = P ^ m := by
    intro m
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_natCast]
  have haP : ∀ m : ℕ, ‖a (p ^ m)‖ ≤ c * P ^ m := by
    intro m
    have := hc (p ^ m) (pow_pos hp.pos m)
    rwa [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, hpow] at this
  have main : ∀ k : ℕ, (k : ℝ) * ‖b (p ^ k)‖ ≤ ((1 + c) ^ k - 1) * P ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    have hk' := hrec k
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, ha1] at hk'
    have hkb : (k : ℂ) * b (p ^ k) = (k : ℂ) * a (p ^ k) -
        ∑ i ∈ Finset.range k, (i : ℂ) * b (p ^ i) * a (p ^ (k - i)) := by
      linear_combination -hk'
    have hnorm : (k : ℝ) * ‖b (p ^ k)‖ ≤ (k : ℝ) * ‖a (p ^ k)‖ +
        ∑ i ∈ Finset.range k, (i : ℝ) * ‖b (p ^ i)‖ * ‖a (p ^ (k - i))‖ := by
      have h1 : (k : ℝ) * ‖b (p ^ k)‖ = ‖(k : ℂ) * b (p ^ k)‖ := by simp
      rw [h1, hkb]
      refine (norm_sub_le _ _).trans (add_le_add (by simp) ?_)
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      simp
    have hterm : ∀ i ∈ Finset.range k, (i : ℝ) * ‖b (p ^ i)‖ * ‖a (p ^ (k - i))‖ ≤
        c * P ^ k * ((1 + c) ^ i - 1) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have h1 := ih i hik
      have h2 := haP (k - i)
      have hc1 : 1 ≤ c := by simpa [ha1] using hc 1 one_pos
      have hnn : 0 ≤ ((1 + c) ^ i - 1) * P ^ i := by
        apply mul_nonneg _ (pow_nonneg hP.le _)
        have : 1 ≤ (1 + c) ^ i := one_le_pow₀ (by linarith)
        linarith
      calc (i : ℝ) * ‖b (p ^ i)‖ * ‖a (p ^ (k - i))‖
          ≤ ((1 + c) ^ i - 1) * P ^ i * (c * P ^ (k - i)) :=
            mul_le_mul h1 h2 (norm_nonneg _) hnn
        _ = c * (P ^ i * P ^ (k - i)) * ((1 + c) ^ i - 1) := by ring
        _ = c * P ^ k * ((1 + c) ^ i - 1) := by rw [pow_mul_pow_sub _ hik.le]
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at hsum
    have hgeom := geom_sum_mul (1 + c) k
    have hak := haP k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc (k : ℝ) * ‖b (p ^ k)‖ ≤ k * (c * P ^ k) + c * P ^ k *
          (∑ i ∈ Finset.range k, (1 + c) ^ i - k) :=
          hnorm.trans (add_le_add (mul_le_mul_of_nonneg_left hak hk0) hsum)
      _ = (∑ i ∈ Finset.range k, (1 + c) ^ i) * (1 + c - 1) * P ^ k := by ring
      _ = ((1 + c) ^ k - 1) * P ^ k := by rw [hgeom]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [hpow, le_div_iff₀ hkpos, mul_comm]
  exact main k

end ArithmeticFunction

namespace SelbergClass

open ArithmeticFunction

/-- The coefficients of `log (F ⊗ G)` for Euler logarithms `b` of `F` and `c` of `G`:
`tensorLog b c (pᵏ) = k · b(pᵏ) · c(pᵏ)` on prime powers, and `0` elsewhere. (For `n = pᵏ`,
`n.minFac = p` and `n.factorization p = k`.) -/
def tensorLog (b c : ℕ → ℂ) : ℕ → ℂ := fun n =>
  if IsPrimePow n then (n.factorization n.minFac : ℂ) * b n * c n else 0

/-- The **Rankin–Selberg product** `(F ⊗ G)(s) = exp (∑ tensorLog b c n · n^{-s})`, for Euler
logarithms `b` of `F` and `c` of `G`. -/
noncomputable def tensor (b c : ℕ → ℂ) (s : ℂ) : ℂ :=
  exp (LSeries (tensorLog b c) s)

/-- The Rankin–Selberg logarithm at a prime power `pᵏ`, `k ≠ 0`:
`tensorLog b c (pᵏ) = k b(pᵏ) c(pᵏ)`. -/
theorem tensorLog_prime_pow (b c : ℕ → ℂ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    tensorLog b c (p ^ k) = (k : ℂ) * b (p ^ k) * c (p ^ k) := by
  unfold tensorLog
  rw [ite_eq_left (hp.isPrimePow.pow hk), hp.pow_minFac hk, hp.factorization_pow]
  simp

/-- `tensorLog b c` vanishes off the prime powers. -/
theorem tensorLog_of_not_isPrimePow (b c : ℕ → ℂ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    tensorLog b c n = 0 := by
  simp [tensorLog, hn]

end SelbergClass

namespace ArithmeticFunction

open SelbergClass

/-- `a ∈ 𝒮` is **`⊗`-simple**: for its Euler logarithm `b`, `F ⊗ F̄ = tensor b b̄` continues
from `Re s > 1` to a function analytic at every point of `Re s ≥ 1/2` other than `s = 1`, with a
simple pole at `s = 1`. -/
def IsTensorSimple (a : ArithmeticFunction ℂ) : Prop :=
  a ∈ selbergClass ∧ ∃ b, IsEulerLog a b ∧ ∃ H : ℂ → ℂ,
    (∀ s, 1 < s.re → H s = tensor b (fun n => starRingEnd ℂ (b n)) s) ∧
    AnalyticOnNhd ℂ H {s | 1 / 2 ≤ s.re ∧ s ≠ 1} ∧ meromorphicOrderAt H 1 = -1

end ArithmeticFunction

namespace SelbergClass

open ArithmeticFunction

/-- **Absolute convergence of the Rankin–Selberg logarithm.** For `F, G ∈ 𝒮` with Euler
logarithms `bF`, `bG`, the Dirichlet series of `log (F ⊗ G)`, with coefficients
`tensorLog bF bG`, converges absolutely for `Re s > 1`. -/
theorem LSeriesSummable_tensorLog {a b : ArithmeticFunction ℂ} {bF bG : ℕ → ℂ}
    (ha : a ∈ selbergClass) (hb : b ∈ selbergClass)
    (hbF : IsEulerLog a bF) (hbG : IsEulerLog b bG) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (tensorLog bF bG) s := by
  obtain ⟨ha1, -, ⟨b₁, θ₁, hθ₁, hb₁, C₁, hC₁⟩, -⟩ := id ha
  obtain ⟨hb1, -, ⟨b₂, θ₂, hθ₂, hb₂, C₂, hC₂⟩, hbO⟩ := id hb
  have hF : bF = b₁ := IsEulerLog.unique ha1 (fun s hs => LSeriesSummable_of_mem ha hs) hbF hb₁
  have hG : bG = b₂ := IsEulerLog.unique hb1 (fun s hs => LSeriesSummable_of_mem hb hs) hbG hb₂
  have hCF : ∀ n, ‖bF n‖ ≤ C₁ * (n : ℝ) ^ θ₁ := hF ▸ hC₁
  have hCG : ∀ n, ‖bG n‖ ≤ C₂ * (n : ℝ) ^ θ₂ := hG ▸ hC₂
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (by simpa using hCF 1)
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (by simpa using hCG 1)
  set σ := s.re with hσ
  set δ : ℝ := (σ - 1) / 2 with hδ
  set ε : ℝ := δ / 2 with hε
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨c, hc⟩ := hbO ε hε0
  have h829 := fun (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) =>
    hbG.norm_apply_prime_pow_le hb1 (fun s hs => LSeriesSummable_of_mem hb hs)
      (fun n _ => hc n) hp hk
  set P : ℕ := ⌈(1 + c) ^ ε⁻¹⌉₊ with hP
  have hc1 : 1 ≤ c := by
    have := hc 1; simpa [hb1] using this
  have hlarge : ∀ p : ℕ, p.Prime → P ≤ p → ∀ k : ℕ, 0 < k →
      (k : ℝ) * ‖bG (p ^ k)‖ ≤ (((p ^ k : ℕ) : ℝ)) ^ δ := by
    intro p hp hpP k hk
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have h := h829 p hp k hk
    rw [le_div_iff₀ hkpos] at h
    have hpe : 1 + c ≤ (p : ℝ) ^ ε := by
      have h1 : (1 + c) ^ ε⁻¹ ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hpP)
      calc 1 + c = ((1 + c) ^ ε⁻¹) ^ ε := (Real.rpow_inv_rpow (by linarith) hε0.ne').symm
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 hε0.le
    have hpow : (p : ℝ) ^ ((k : ℝ) * ε) = ((p : ℝ) ^ ε) ^ k := by
      rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_natCast]
    have hN : (((p ^ k : ℕ) : ℝ)) ^ δ = ((p : ℝ) ^ ε) ^ k * ((p : ℝ) ^ ε) ^ k := by
      rw [← mul_pow, ← Real.rpow_add hp0, Nat.cast_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul hp0.le, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1; rw [hε]; ring
    rw [hN, mul_comm (k : ℝ), ← hpow]
    have hP0 : 0 ≤ (p : ℝ) ^ ((k : ℝ) * ε) := Real.rpow_nonneg hp0.le _
    have hck : (1 + c) ^ k ≤ ((p : ℝ) ^ ε) ^ k := pow_le_pow_left₀ (by linarith) hpe k
    nlinarith
  set f : ℕ → ℝ := fun n => ‖LSeries.term (tensorLog bF bG) s n‖ with hf
  have hfpow : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k →
      f (p ^ k) = (k : ℝ) * ‖bF (p ^ k)‖ * ‖bG (p ^ k)‖ / (((p ^ k : ℕ) : ℝ)) ^ σ := by
    intro p hp k hk
    simp only [hf, LSeries.norm_term_eq, ite_eq_right (pow_ne_zero k hp.ne_zero),
      tensorLog_prime_pow bF bG hp hk.ne', norm_mul, Complex.norm_natCast]
    rfl
  set s' : ℂ := ((σ - δ : ℝ) : ℂ) with hs'
  have hs're : s'.re = σ - δ := by rw [hs']; exact Complex.ofReal_re _
  have hsum1 : Summable fun n => ‖LSeries.term bF s' n‖ :=
    (hbF.2 s' (by rw [hs're, hδ]; linarith)).1.norm
  set Ps := (Finset.range P).filter Nat.Prime with hPs
  set g : ℕ → ℕ → ℝ := fun p => (Set.range fun k : ℕ => p ^ (k + 1)).indicator f with hg
  have hsmall : ∀ p ∈ Ps, Summable (g p) := by
    intro p hpPs
    have hp : p.Prime := (Finset.mem_filter.1 hpPs).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hinj : Function.Injective fun k : ℕ => p ^ (k + 1) := fun i j hij => by
      have := Nat.pow_right_injective hp.two_le hij
      simpa using this
    refine (hinj.summable_iff (fun x hx => Set.indicator_of_notMem hx _)).1 ?_
    set x : ℝ := (p : ℝ) ^ (θ₁ + θ₂ - σ) with hx
    have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
    have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hgeo0 : Summable fun n : ℕ => (n : ℝ) ^ 1 * x ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hx0])
    have hgeo : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 1 * x ^ (k + 1) :=
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 1 * x ^ n) 1).2 hgeo0
    refine Summable.of_nonneg_of_le (fun k => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
      (fun k => ?_) (hgeo.mul_left (C₁ * C₂))
    simp only [Function.comp]
    rw [Set.indicator_of_mem (show p ^ (k + 1) ∈ Set.range (fun k : ℕ => p ^ (k + 1)) from
      ⟨k, rfl⟩), hfpow p hp (k + 1) k.succ_pos]
    set N : ℝ := ((p ^ (k + 1) : ℕ) : ℝ) with hN
    have hN0 : 0 < N := by rw [hN]; exact_mod_cast pow_pos hp.pos _
    have hxN : x ^ (k + 1) = N ^ (θ₁ + θ₂ - σ) := by
      rw [hN, hx, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, mul_comm]
    rw [hxN, Real.rpow_sub hN0, Real.rpow_add hN0, div_le_iff₀ (Real.rpow_pos_of_pos hN0 _)]
    have h1 := hCF (p ^ (k + 1))
    have h2 := hCG (p ^ (k + 1))
    rw [← hN] at h1 h2
    have hsn : (0 : ℝ) ≤ N ^ σ := (Real.rpow_pos_of_pos hN0 _).le
    have e : ((k + 1 : ℕ) : ℝ) ^ 1 * (C₁ * C₂) * (N ^ θ₁ * N ^ θ₂ / N ^ σ) * N ^ σ =
        ((k + 1 : ℕ) : ℝ) * (C₁ * N ^ θ₁) * (C₂ * N ^ θ₂) := by
      field_simp
    calc ((k + 1 : ℕ) : ℝ) * ‖bF (p ^ (k + 1))‖ * ‖bG (p ^ (k + 1))‖
        ≤ ((k + 1 : ℕ) : ℝ) * (C₁ * N ^ θ₁) * (C₂ * N ^ θ₂) := by
          gcongr
      _ = C₁ * C₂ * (((k + 1 : ℕ) : ℝ) ^ 1 * (N ^ θ₁ * N ^ θ₂ / N ^ σ)) * N ^ σ := by
          rw [← e]; ring
  have hbound : ∀ n, f n ≤ ‖LSeries.term bF s' n‖ + ∑ p ∈ Ps, g p n := by
    intro n
    have hg0 : 0 ≤ ∑ p ∈ Ps, g p n :=
      Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    by_cases hn : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
      by_cases hpP : P ≤ p
      · refine le_add_of_le_of_nonneg ?_ hg0
        rw [hfpow p hp k hk, LSeries.norm_term_eq, ite_eq_right (pow_ne_zero k hp.ne_zero),
          hs're]
        set N : ℝ := ((p ^ k : ℕ) : ℝ) with hN
        have hN0 : 0 < N := by rw [hN]; exact_mod_cast pow_pos hp.pos k
        have hl := hlarge p hp hpP k hk
        rw [← hN] at hl
        rw [Real.rpow_sub hN0, div_div_eq_mul_div]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
        calc (k : ℝ) * ‖bF (p ^ k)‖ * ‖bG (p ^ k)‖
            = ‖bF (p ^ k)‖ * ((k : ℝ) * ‖bG (p ^ k)‖) := by ring
          _ ≤ ‖bF (p ^ k)‖ * N ^ δ := mul_le_mul_of_nonneg_left hl (norm_nonneg _)
      · refine le_add_of_nonneg_of_le (norm_nonneg _) ?_
        have hpPs : p ∈ Ps := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun q => g q (p ^ k))
          (fun q _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _) hpPs)
        simp only [hg]
        rw [Set.indicator_of_mem (show p ^ k ∈ Set.range (fun k : ℕ => p ^ (k + 1)) from
          ⟨k - 1, by simp only [Nat.sub_add_cancel hk]⟩)]
    · have h0 : f n = 0 := by
        simp only [hf, LSeries.norm_term_eq]
        split_ifs
        · rfl
        · simp [tensorLog, ite_eq_right hn]
      rw [h0]
      exact add_nonneg (norm_nonneg _) hg0
  have hsumf : Summable f :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hsum1.add (summable_sum hsmall))
  exact hsumf.of_norm

/-- The pointwise inequality `2 Re z ≤ k |z|² + 1/k` behind `|F|² ≤ |F ⊗ F̄| ζ`, written for the
coefficients: `2 Re b(n) ≤ Re (tensorLog b b̄)(n) + Λ(n) / log n`. -/
private lemma two_mul_re_le_re_tensorLog_add (b : ℕ → ℂ) (hb : ∀ n, b n ≠ 0 → IsPrimePow n)
    (n : ℕ) :
    2 * (b n).re ≤ (tensorLog b (fun n => starRingEnd ℂ (b n)) n).re +
      (((vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)).re := by
  have hZ : 0 ≤ (((vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ)).re := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    exact div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
    rw [tensorLog_prime_pow _ _ hp hk.ne', vonMangoldt_apply_pow hk.ne',
      vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow, ← Complex.ofReal_div]
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have e : Real.log p / (k * Real.log p) = 1 / k := by field_simp
    rw [e, Complex.ofReal_re]
    set z := b (p ^ k)
    have hre : ((k : ℂ) * z * starRingEnd ℂ z).re = k * ‖z‖ ^ 2 := by
      rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hre]
    have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have h2 : 0 ≤ (k * ‖z‖ - 1) ^ 2 / k := by positivity
    have h3 : (k * ‖z‖ - 1) ^ 2 / k = k * ‖z‖ ^ 2 + 1 / k - 2 * ‖z‖ := by field_simp; ring
    linarith
  · have hb0 : b n = 0 := by by_contra h; exact hn (hb n h)
    rw [hb0, tensorLog_of_not_isPrimePow _ _ hn]
    simpa using hZ

/-- For real `σ > 1`, `|F(σ)|² ≤ |(F ⊗ F̄)(σ)| · |ζ(σ)|`. -/
private lemma norm_sq_le_norm_tensor_mul_norm_riemannZeta {a : ArithmeticFunction ℂ}
    (ha : a ∈ selbergClass) {b : ℕ → ℂ} (hb : IsEulerLog a b) {F H : ℂ → ℂ}
    (hF : IsLSeriesContinuation a F)
    (hH : ∀ s, 1 < s.re → H s = tensor b (fun n => starRingEnd ℂ (b n)) s)
    {σ : ℝ} (hσ : 1 < σ) :
    ‖F σ‖ ^ 2 ≤ ‖H σ‖ * ‖riemannZeta σ‖ := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  obtain ⟨hbS, hFb⟩ := hb.2 _ hs
  set T : ℕ → ℂ := tensorLog b (fun n => starRingEnd ℂ (b n)) with hTdef
  set Z : ℕ → ℂ := fun n =>
    ((vonMangoldt n : ℝ) : ℂ) / ((Real.log n : ℝ) : ℂ) with hZdef
  have hTS : LSeriesSummable T σ := by
    have h := LSeriesSummable_tensorLog ha ha hb hb hs
    refine Summable.of_norm_bounded h.norm (fun n => LSeries.norm_term_le _ (le_of_eq ?_))
    by_cases hn : IsPrimePow n
    · simp [hTdef, tensorLog, hn]
    · simp [hTdef, tensorLog, hn]
  have hZS : LSeriesSummable Z σ := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := (1 + σ) / 2) (by simp; linarith)
      ⟨1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 + σ) / 2 - 1) :=
      Real.one_le_rpow hn1 (by linarith)
    have h2 : ‖Z n‖ ≤ 1 := by
      rw [hZdef]
      simp only
      rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n))]
      exact div_le_one_of_le₀ vonMangoldt_le_log (Real.log_natCast_nonneg n)
    linarith
  have hzeta := riemannZeta_eq_exp_LSeries hs
  have hre : 2 * (LSeries b σ).re ≤ (LSeries T σ).re + (LSeries Z σ).re := by
    have h1 := (Complex.hasSum_re hbS.LSeriesHasSum).mul_left 2
    have h2 := (Complex.hasSum_re hTS.LSeriesHasSum).add (Complex.hasSum_re hZS.LSeriesHasSum)
    refine hasSum_le (fun n => ?_) h1 h2
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hc : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
      have hpos : 0 < (n : ℝ) ^ σ := by positivity
      simp only [LSeries.term_of_ne_zero hn, hc, Complex.div_ofReal_re]
      rw [← add_div, mul_div_assoc']
      exact div_le_div_of_nonneg_right (two_mul_re_le_re_tensorLog_add b hb.1 n) hpos.le
  rw [hF.1 _ hs, hFb, hH _ hs, tensor, ← hzeta, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_exp, sq, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

end SelbergClass

namespace ArithmeticFunction

open SelbergClass

/-- **A `⊗`-simple function has at most a simple pole at `s = 1`.** If `a ∈ 𝒮` is `⊗`-simple
and `F` is the continuation of `L(a, s)`, then `meromorphicOrderAt F 1 ≥ -1`. The proof compares
`|F(σ)|² ≤ |(F ⊗ F̄)(σ)| ζ(σ)` as `σ → 1⁺`. -/
theorem IsTensorSimple.neg_one_le_meromorphicOrderAt {a : ArithmeticFunction ℂ} {F : ℂ → ℂ}
    (ha : IsTensorSimple a) (hF : IsLSeriesContinuation a F) :
    -1 ≤ meromorphicOrderAt F 1 := by
  obtain ⟨ha𝒮, b, hb, H, hHeq, -, hHord⟩ := ha
  have hFm : MeromorphicAt F 1 := SelbergClass.meromorphicAt_one ha𝒮 hF
  have hHm : MeromorphicAt H 1 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hHord]; decide)
  have hZm := meromorphicAt_riemannZeta_one
  have hZord := meromorphicOrderAt_riemannZeta_one
  by_contra hlt
  push Not at hlt
  have hFne : ∀ σ : ℝ, 1 < σ → F σ ≠ 0 := by
    intro σ hσ
    have hs : 1 < (σ : ℂ).re := by simpa using hσ
    rw [hF.1 _ hs, (hb.2 _ hs).2]
    exact Complex.exp_ne_zero _
  set Ψ : ℂ → ℂ := H * riemannZeta * F⁻¹ * F⁻¹ with hΨ
  have hord : 0 < meromorphicOrderAt Ψ 1 := by
    rw [hΨ, meromorphicOrderAt_mul ((hHm.mul hZm).mul hFm.inv) hFm.inv,
      meromorphicOrderAt_mul (hHm.mul hZm) hFm.inv, meromorphicOrderAt_mul hHm hZm,
      meromorphicOrderAt_inv, hHord, hZord]
    cases h : meromorphicOrderAt F 1 with
    | top => rw [h] at hlt; exact absurd hlt (by simp)
    | coe n =>
      rw [h] at hlt
      have hn : n < -1 := by
        have h2 : ((n : ℤ) : WithTop ℤ) < ((-1 : ℤ) : WithTop ℤ) := hlt
        exact WithTop.coe_lt_coe.mp h2
      have : ((-1 + -1 + -n + -n : ℤ) : WithTop ℤ) =
          -1 + -1 + -(n : WithTop ℤ) + -(n : WithTop ℤ) := by
        rfl
      rw [← this]
      exact_mod_cast (by omega : (0 : ℤ) < -1 + -1 + -n + -n)
  have ht := tendsto_zero_of_meromorphicOrderAt_pos hord
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simpa using (ne_of_gt (Set.mem_Ioi.mp hσ))
  have hev := (ht.comp hpath).eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  have hgt : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 < σ := self_mem_nhdsWithin
  obtain ⟨σ, h1, h2⟩ := (hev.and hgt).exists
  have hk := norm_sq_le_norm_tensor_mul_norm_riemannZeta ha𝒮 hb hF hHeq h2
  have hFσ : 0 < ‖F σ‖ := norm_pos_iff.2 (hFne σ h2)
  have h1' : ‖Ψ σ‖ < 1 := by simpa using h1
  have : ‖Ψ σ‖ = ‖H σ‖ * ‖riemannZeta σ‖ / ‖F σ‖ ^ 2 := by
    simp only [hΨ, Pi.mul_apply, Pi.inv_apply, norm_mul, norm_inv]
    field_simp
  rw [this, div_lt_one (by positivity)] at h1'
  linarith

end ArithmeticFunction

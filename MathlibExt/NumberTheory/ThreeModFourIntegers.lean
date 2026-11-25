/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Integers whose prime factors are all `≡ 3 (mod 4)`

This file proves the asymptotic formula of Gareth A. Jones and Alexander K. Zvonkin,
*A Number-Theoretic Problem Concerning Pseudo-Real Riemann Surfaces*, INTEGERS 25 (2025),
Article A75 (arXiv:2401.00270), for the number `g(x)` of integers `n ≤ x` all of whose prime
factors are `≡ 3 (mod 4)`:
`g(x) ~ √(e^γ / π) · (C / 2) · x / √(ln x)`
(`MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four`).

`g(x)` counts the `n ≤ x` all of whose prime factors are `≡ -1 (mod 4)` (including
`n = 1`). The constant `C = C(4, 1)` of Languasco and Zaccagnini is defined in the paper
by `∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q) = C / (ln x)^{1/2} + O((ln x)^{-3/2})`; it enters
here as the limit of `(ln x)^{1/2} ∏_{q ≤ x, q ≡ 1 (4)} (1 - 1/q)`.

## Proof

The paper derives the formula from Raikov's Tauberian theorem. This file uses only real-variable
arguments instead. Write `G(s) = ∑ g(n) n^{-s}` and `H(s) = ∑ h(n) n^{-s}` for `s > 1`, where `h`
is the indicator of the integers with no prime factor `≡ 3 (mod 4)`.

1. The elementary mean-value argument of `MathlibExt.NumberTheory.PrimeCounting.LandauRamanujan`
   (there for `h`), run with the prime number theorem for the progression `3 mod 4`, gives
   `∑_{n ≤ x} g(n) / n ~ α √(ln x)` for some `α > 0`, and then `g(x) ~ (α / 2) x / √(ln x)`.
2. An Abelian argument turns the first asymptotic into `√ε · G(1 + ε) → α Γ(3/2) = α √π / 2`
   as `ε → 0⁺`.
3. The Euler products give `G(s) H(s) = ζ(s)`; with `(s - 1) ζ(s) → 1` this yields the limit of
   `√ε · H(1 + ε)`.
4. A log-log Abelian argument, through the integral formula
   `γ = -log ε - ε ∫_1^∞ log (log t) t^{-1-ε} dt`, compares `log H(1 + ε)` with the partial
   products in the hypothesis on `C`. This identifies `α = e^{γ/2} C / √π`.
-/

namespace MetaMathlibExt

namespace isEquivalent_card_primeFactors_three_mod_four

/-! ### A mean-value argument for the integers with all prime factors `≡ 3 (mod 4)` -/

section Elementary

open Asymptotics Filter Finset Nat Chebyshev ArithmeticFunction
open scoped Topology

/-- Indicator of positive integers all of whose prime factors are `≡ 3 mod 4`. -/
private noncomputable def tmG (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 = 3 then 1 else 0

private lemma tmG_zero : tmG 0 = 0 := by simp [tmG]

private lemma tmG_one : tmG 1 = 1 := by simp [tmG]

private lemma tmG_nonneg (n : ℕ) : 0 ≤ tmG n := by
  unfold tmG
  split_ifs <;> norm_num

private lemma tmG_le_one (n : ℕ) : tmG n ≤ 1 := by
  unfold tmG
  split_ifs <;> norm_num

private lemma tmG_mul (m n : ℕ) : tmG (m * n) = tmG m * tmG n := by
  by_cases hm : m = 0
  · subst hm
    simp [tmG_zero]
  · by_cases hn : n = 0
    · subst hn
      simp [tmG_zero]
    · have hU : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
        Nat.primeFactors_mul hm hn
      have hIff : (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, p % 4 = 3) ↔
          (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p % 4 = 3) ∧
          (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 = 3) := by
        rw [hU]
        constructor
        · rintro ⟨_, hH⟩
          exact ⟨⟨hm, fun p hp => hH p (Finset.mem_union.mpr (Or.inl hp))⟩,
            ⟨hn, fun p hp => hH p (Finset.mem_union.mpr (Or.inr hp))⟩⟩
        · rintro ⟨⟨hm', hHm⟩, ⟨hn', hHn⟩⟩
          refine ⟨mul_ne_zero hm' hn', fun p hp => ?_⟩
          rcases Finset.mem_union.mp hp with h | h
          · exact hHm p h
          · exact hHn p h
      simp only [tmG, hIff]
      split_ifs with h1 h2 h3 <;> simp_all

private lemma tmG_log_eq {n : ℕ} (hn : 1 ≤ n) :
    tmG n * Real.log n
      = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * tmG d * tmG (n / d) := by
  have hn0 : n ≠ 0 := by omega
  have hterm : ∀ d ∈ n.divisors,
      ArithmeticFunction.vonMangoldt d * tmG d * tmG (n / d)
        = ArithmeticFunction.vonMangoldt d * tmG n := by
    intro d hd
    have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
    have hmul : tmG d * tmG (n / d) = tmG n := by
      rw [← tmG_mul, hdeq]
    calc ArithmeticFunction.vonMangoldt d * tmG d * tmG (n / d)
        = ArithmeticFunction.vonMangoldt d * (tmG d * tmG (n / d)) := by ring
      _ = ArithmeticFunction.vonMangoldt d * tmG n := by rw [hmul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ArithmeticFunction.vonMangoldt_sum, mul_comm]

private lemma tmG_log_div_eq {n : ℕ} (hn : 1 ≤ n) :
    tmG n * Real.log n / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)) *
        (tmG (n / d) / ((n / d : ℕ) : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  rw [tmG_log_eq hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
  have hcast : (d : ℝ) * (((n / d : ℕ)) : ℝ) = (n : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdeq
    rwa [Nat.cast_mul] at h
  have e : (ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)) *
      (tmG (n / d) / (((n / d : ℕ)) : ℝ))
      = (ArithmeticFunction.vonMangoldt d * tmG d * tmG (n / d)) /
        ((d : ℝ) * (((n / d : ℕ)) : ℝ)) := by
    ring
  rw [e, hcast]

private lemma tm_sum_swap (F G : ℕ → ℝ) (hF : F 0 = 0) (hG : G 0 = 0)
    (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, F d * G (n / d)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, G m * ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, F d := by
  classical
  let F' : ArithmeticFunction ℝ := ⟨F, hF⟩
  let G' : ArithmeticFunction ℝ := ⟨G, hG⟩
  have hFG : ∀ n : ℕ, (F' * G') n = ∑ d ∈ n.divisors, F d * G (n / d) := by
    intro n
    calc (F' * G') n = ∑ x ∈ n.divisorsAntidiagonal, F x.1 * G x.2 := by
          rw [ArithmeticFunction.mul_apply]
          apply Finset.sum_congr rfl
          intro x _
          rfl
      _ = ∑ d ∈ n.divisors, F d * G (n / d) :=
          Nat.sum_divisorsAntidiagonal (fun a b => F a * G b)
  have hGF : ∀ n : ℕ, (G' * F') n = ∑ d ∈ n.divisors, F d * G (n / d) := by
    intro n
    have hcomm : G' * F' = F' * G' := mul_comm _ _
    rw [hcomm]
    exact hFG n
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, F d * G (n / d)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (G' * F') n := by
        apply Finset.sum_congr rfl
        intro n _
        exact (hGF n).symm
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, G' n * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / n), F' m :=
        ArithmeticFunction.sum_Ioc_mul_eq_sum_sum G' F' ⌊x⌋₊
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, G m * ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, F d := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Nat.floor_div_natCast]
        rfl

/-- `N(x)`: count of `n ≤ x` with `tmG n = 1`. -/
private noncomputable def tmCount (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n

/-- `A(x)`: reciprocal sum of `tmG` over `n ≤ x`. -/
private noncomputable def tmA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ)

/-- `ψ_g(y)`: von Mangoldt sum restricted by `tmG`. -/
private noncomputable def tmPsi (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * tmG d

/-- `M(y)`: reciprocal Mertens sum restricted by `tmG`. -/
private noncomputable def tmMert (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)

/-- `J(x)`: log-weighted reciprocal sum. -/
private noncomputable def tmJ (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG n / (n : ℝ)) * Real.log (x / (n : ℝ))

private lemma tm_L_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m * tmPsi (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * tmG d) 0 = 0 := by
    simp [tmG_zero]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * tmG d) * tmG (n / d) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [tmG_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact tmG_log_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * tmG d) * tmG (n / d) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, ArithmeticFunction.vonMangoldt d * tmG d :=
        tm_sum_swap _ _ hF tmG_zero x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m * tmPsi (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [tmPsi]

private lemma tm_logA_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ) / (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) * tmMert (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)) 0 = 0 := by
    simp [tmG_zero]
  have hG : (fun m : ℕ => tmG m / (m : ℝ)) 0 = 0 := by
    simp [tmG_zero]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)) *
        (tmG (n / d) / (((n / d : ℕ)) : ℝ)) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [tmG_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact tmG_log_div_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)) *
        (tmG (n / d) / (((n / d : ℕ)) : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ) :=
        tm_sum_swap (fun d : ℕ => ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ))
          (fun m : ℕ => tmG m / (m : ℝ)) hF hG x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) * tmMert (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [tmMert]

private lemma tmCount_nonneg (x : ℝ) : 0 ≤ tmCount x :=
  Finset.sum_nonneg fun n _ => tmG_nonneg n

private lemma tmA_nonneg (x : ℝ) : 0 ≤ tmA x := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n)

private lemma tmPsi_nonneg (y : ℝ) : 0 ≤ tmPsi y := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (tmG_nonneg d)

private lemma tmA_mono : Monotone tmA := by
  intro x y hxy
  simp only [tmA]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · intro n _ _
    exact div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n)

private lemma tmA_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ tmA x := by
  have h1 : 1 ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    rw [Finset.mem_Ioc]
    exact ⟨by omega, (Nat.one_le_floor_iff x).mpr hx⟩
  have h := Finset.single_le_sum
    (fun n _ => div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n)) h1
  simpa [tmG_one, tmA] using h

private lemma tmCount_le {y : ℝ} (hy : 0 ≤ y) : tmCount y ≤ y := by
  calc tmCount y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, tmG n := rfl
    _ ≤ ∑ _n ∈ Finset.Ioc 0 ⌊y⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => tmG_le_one n
    _ = (⌊y⌋₊ : ℝ) := by simp [Finset.sum_const, Nat.card_Ioc]
    _ ≤ y := Nat.floor_le hy

private lemma tmPsi_le_psi (y : ℝ) : tmPsi y ≤ Chebyshev.psi y := by
  simp only [tmPsi, Chebyshev.psi]
  apply Finset.sum_le_sum
  intro d _
  calc ArithmeticFunction.vonMangoldt d * tmG d
      ≤ ArithmeticFunction.vonMangoldt d * 1 :=
        mul_le_mul_of_nonneg_left (tmG_le_one d)
          ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt d := mul_one _

private lemma tmPsi_le_mul_self {y : ℝ} (hy : 0 ≤ y) :
    tmPsi y ≤ (Real.log 4 + 4) * y :=
  le_trans (tmPsi_le_psi y) (Chebyshev.psi_le_const_mul_self hy)

/-- `tmG` on a prime is determined by the residue of the prime mod 4. -/
private lemma tmG_prime_eq {p : ℕ} (hp : p.Prime) :
    tmG p = if p % 4 = 3 then 1 else 0 := by
  have hmem : ∀ q : ℕ, q ∈ p.primeFactors ↔ q = p := by
    intro q
    constructor
    · intro hq
      have hqP := Nat.prime_of_mem_primeFactors hq
      have hqdvd := Nat.dvd_of_mem_primeFactors hq
      exact (Nat.prime_dvd_prime_iff_eq hqP hp).mp hqdvd
    · intro hq
      rw [hq]
      exact hp.mem_primeFactors_self
  unfold tmG
  by_cases h : p % 4 = 3
  · rw [ite_eq_left h, ite_eq_left]
    exact ⟨hp.ne_zero, fun q hq => by rw [(hmem q).mp hq]; exact h⟩
  · rw [ite_eq_right h, ite_eq_right]
    intro hc
    exact h (hc.2 p ((hmem p).mpr rfl))

/-- The residue `3` is a unit modulo `4`. -/
private lemma tm_isUnit_three : IsUnit (3 : ZMod 4) :=
  ⟨⟨3, 3, by decide, by decide⟩, rfl⟩

/-- The residue-class von Mangoldt function as an `if`. -/
private lemma tm_residueClass_eq (d : ℕ) :
    ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d
      = if (d : ZMod 4) = 3 then ArithmeticFunction.vonMangoldt d else 0 := by
  change Set.indicator {n : ℕ | (n : ZMod 4) = (3 : ZMod 4)} _ _ = _
  split_ifs with h
  · have hm : d ∈ {n : ℕ | (n : ZMod 4) = (3 : ZMod 4)} := h
    exact Set.indicator_of_mem hm _
  · have hm : d ∉ {n : ℕ | (n : ZMod 4) = (3 : ZMod 4)} := h
    exact Set.indicator_of_notMem hm _

/-- Pointwise comparison of `Λ · tmG ·` with the residue class of `3 mod 4`. -/
private lemma tm_resid_diff_le (d : ℕ) :
    |ArithmeticFunction.vonMangoldt d * tmG d -
      ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d|
      ≤ (if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d) := by
  by_cases h2 : d = 2
  · subst h2
    have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hH : tmG 2 = 0 := by
      rw [tmG_prime_eq Nat.prime_two, ite_eq_right (by decide)]
    have hr : ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) 2 = 0 := by
      rw [tm_residueClass_eq, ite_eq_right (by decide)]
    rw [hΛ, hH, hr, ite_eq_left rfl, ite_eq_left Nat.prime_two, mul_zero, sub_zero,
      abs_zero, add_zero]
    exact Real.log_nonneg (by norm_num)
  · by_cases hp : d.Prime
    · -- `d` is an odd prime: both sides agree.
      obtain rfl | hodd := hp.eq_two_or_odd'
      · exact absurd rfl h2
      · have hmod : d % 4 = 1 ∨ d % 4 = 3 := by
          have hlt : d % 4 < 4 := Nat.mod_lt d (by norm_num)
          have h2mod : d % 2 = 1 := Nat.odd_iff.mp hodd
          omega
        have hcast : (d : ZMod 4) = ((d % 4 : ℕ) : ZMod 4) :=
          (ZMod.natCast_mod d 4).symm
        have hΛr : ArithmeticFunction.vonMangoldt d * tmG d
            = ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d := by
          rw [tm_residueClass_eq, tmG_prime_eq hp]
          rcases hmod with h1 | h3
          · have hc : (d : ZMod 4) ≠ 3 := by
              rw [hcast, h1]
              decide
            rw [ite_eq_right (by omega : d % 4 ≠ 3), ite_eq_right hc, mul_zero]
          · have hc : (d : ZMod 4) = 3 := by
              rw [hcast, h3]
              rfl
            rw [ite_eq_left h3, ite_eq_left hc, mul_one]
        rw [hΛr, sub_self, abs_zero, ite_eq_right h2, ite_eq_left hp]
        norm_num
    · -- `d` is not prime: both terms lie in `[0, Λ d]`.
      rw [ite_eq_right h2, ite_eq_right hp]
      have ha0 : 0 ≤ ArithmeticFunction.vonMangoldt d * tmG d :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (tmG_nonneg d)
      have ha1 : ArithmeticFunction.vonMangoldt d * tmG d
          ≤ ArithmeticFunction.vonMangoldt d := by
        calc ArithmeticFunction.vonMangoldt d * tmG d
            ≤ ArithmeticFunction.vonMangoldt d * 1 :=
              mul_le_mul_of_nonneg_left (tmG_le_one d)
                ArithmeticFunction.vonMangoldt_nonneg
          _ = ArithmeticFunction.vonMangoldt d := mul_one _
      have hb0 : 0 ≤ ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d :=
        ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _
      have hb1 : ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d
          ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt.residueClass_le _ _
      rw [abs_le]
      constructor <;> linarith

/-- For `t ≥ 1`, `log t` is at most four times `t ^ (1/4 : ℝ)`. -/
private lemma tm_log_le_four_rpow (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ≤ 4 * t ^ (1/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : Real.log (t ^ (1/4 : ℝ)) ≤ t ^ (1/4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos (1/4 : ℝ))
    linarith
  have h2 : Real.log t = 4 * Real.log (t ^ (1/4 : ℝ)) := by
    have hlog := Real.log_rpow htpos (1/4 : ℝ)
    linarith
  linarith

/-- For `t ≥ 1`, `2 * √t * log t` is at most `8 * t ^ (3/4 : ℝ)`. -/
private lemma tm_two_sqrt_mul_log_le (t : ℝ) (ht : 1 ≤ t) :
    2 * Real.sqrt t * Real.log t ≤ 8 * t ^ (3/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog := tm_log_le_four_rpow t ht
  have h2nn : (0 : ℝ) ≤ 2 * t ^ (1/2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg htpos.le _)
  have hmul := mul_le_mul_of_nonneg_left hlog h2nn
  have e_add : t ^ (1/2 : ℝ) * t ^ (1/4 : ℝ) = t ^ (3/4 : ℝ) := by
    rw [← Real.rpow_add htpos]
    congr 1
    norm_num
  rw [Real.sqrt_eq_rpow]
  calc 2 * t ^ (1/2 : ℝ) * Real.log t
      ≤ 2 * t ^ (1/2 : ℝ) * (4 * t ^ (1/4 : ℝ)) := hmul
    _ = 8 * t ^ (3/4 : ℝ) := by rw [← e_add]; ring

/-- Pointwise bound for the non-prime Abel integrand. -/
private lemma tm_psi_sub_theta_div_le (t : ℝ) (ht : 1 ≤ t) :
    (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 ≤ 8 * t ^ (-5/4 : ℝ) := by
  have hnn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hle := Chebyshev.psi_sub_theta_le ht
  have hnum := tm_two_sqrt_mul_log_le t ht
  calc (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
      ≤ (8 * t ^ (3/4 : ℝ)) / t ^ 2 :=
        div_le_div_of_nonneg_right (le_trans hle hnum) (sq_nonneg t)
    _ = 8 * t ^ (-5/4 : ℝ) := by
      rw [← Real.rpow_natCast t 2, mul_div_assoc,
        ← Real.rpow_sub (lt_of_lt_of_le zero_lt_one ht)]
      congr 1
      norm_num

/-- Monotonicity of `ψ - θ` (a sum of nonnegative terms over a growing set). -/
private lemma tm_psi_sub_theta_mono :
    Monotone (fun t => Chebyshev.psi t - Chebyshev.theta t) := by
  intro a b hab
  dsimp only
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hab) hn.1, hn.2⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The reciprocal sum of `Λ` over non-primes is uniformly bounded. -/
private lemma tm_sum_not_prime_le :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ≤ C := by
  refine ⟨40, fun y hy => ?_⟩
  set c : ℕ → ℝ := fun n =>
    if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n with hc
  have hcn : ∀ n : ℕ, c n =
      (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n) :=
    fun n => rfl
  have hc0 : c 0 = 0 := by
    rw [hcn, ite_eq_right Nat.not_prime_zero,
      ArithmeticFunction.vonMangoldt_apply, ite_eq_right not_isPrimePow_zero]
  have hpart : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
      = Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc0, zero_add,
      Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcn]
    by_cases h : n.Prime
    · rw [ite_eq_left h, ite_eq_right (show ¬¬n.Prime from fun hn => hn h)]
    · rw [ite_eq_right h, ite_eq_left h]
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) y,
      DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    exact (hasDerivAt_inv
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).differentiableAt
  have hint : MeasureTheory.IntegrableOn (deriv fun t : ℝ => t⁻¹)
      (Set.Icc 1 y) MeasureTheory.volume := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuous_pow 2).continuousOn
    intro t ht
    rw [Set.mem_Icc] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hA := sum_mul_eq_sub_integral_mul₀ (f := fun t : ℝ => t⁻¹) c hc0 y hdiff hint
  beta_reduce at hA
  simp only [hpart] at hA
  have hLHS : (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (k : ℝ)⁻¹ * c k)
      = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcn, div_eq_mul_inv]
    by_cases h : n.Prime
    · rw [ite_eq_left h, ite_eq_left h, mul_zero]
    · rw [ite_eq_right h, ite_eq_right h, mul_comm]
  have hderiv : ∀ t ∈ Set.Ioc (1 : ℝ) y,
      deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t)
      = -((Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) := by
    intro t _
    rw [deriv_inv, neg_mul, inv_mul_eq_div]
  have hint2 : (∫ t in Set.Ioc (1 : ℝ) y,
      deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t))
      = - ∫ t in Set.Ioc (1 : ℝ) y,
        (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    rw [Set.mem_Ioc] at ht
    exact hderiv t ht
  rw [hLHS, hint2, sub_neg_eq_add] at hA
  have hB : y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y) ≤ 8 := by
    have hle := Chebyshev.psi_sub_theta_le hy
    have hnum := tm_two_sqrt_mul_log_le y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have hle1 : y ^ (3/4 : ℝ) ≤ y := by
      calc y ^ (3/4 : ℝ) ≤ y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
        _ = y := Real.rpow_one y
    have hle2 : y ^ (3/4 : ℝ) / y ≤ 1 := (div_le_one hypos).mpr hle1
    calc y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y)
        ≤ y⁻¹ * (8 * y ^ (3/4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans hle hnum) (inv_nonneg.mpr hypos.le)
      _ = 8 * (y ^ (3/4 : ℝ) / y) := by ring
      _ ≤ 8 * 1 :=
          mul_le_mul_of_nonneg_left hle2 (by norm_num)
      _ = 8 := mul_one 8
  have h_int : MeasureTheory.IntegrableOn
      (fun t => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      (Set.Ioc 1 y) MeasureTheory.volume := by
    have hfin : MeasureTheory.volume (Set.Ioc (1 : ℝ) y) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ 8 ?_
    · exact ((tm_psi_sub_theta_mono.measurable.div
        (measurable_id.pow_const 2)).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.mem_Ioc] at ht
      have ht1 : 1 ≤ t := le_of_lt ht.1
      have hnn : 0 ≤ (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
        apply div_nonneg _ (sq_nonneg t)
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
        exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
      have hle := tm_psi_sub_theta_div_le t ht1
      have h54 : t ^ (-5/4 : ℝ) ≤ 1 := by
        calc t ^ (-5/4 : ℝ) ≤ t ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          _ = 1 := Real.rpow_zero t
      calc ‖(Chebyshev.psi t - Chebyshev.theta t) / t ^ 2‖
          = (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ 8 * t ^ (-5/4 : ℝ) := hle
        _ ≤ 8 := by
            calc 8 * t ^ (-5/4 : ℝ) ≤ 8 * 1 :=
                  mul_le_mul_of_nonneg_left h54 (by norm_num)
              _ = 8 := mul_one 8
  have h_major : MeasureTheory.IntegrableOn (fun t => 8 * t ^ (-5/4 : ℝ))
      (Set.Ioc 1 y) MeasureTheory.volume :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).mono_set
      Set.Ioc_subset_Ioi_self).const_mul 8
  have hIval : (∫ t in Set.Ioc (1 : ℝ) y,
      (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      ≤ ∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ) :=
    MeasureTheory.setIntegral_mono_on h_int h_major measurableSet_Ioc
      (fun t ht => tm_psi_sub_theta_div_le t (le_of_lt (Set.mem_Ioc.mp ht).1))
  have hIoi_val : (∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ)) = 32 := by
    have e : (-5/4 : ℝ) + 1 = -1/4 := by norm_num
    have hval : (∫ t in Set.Ioi (1 : ℝ), t ^ (-5/4 : ℝ)) = 4 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one, e]
      simp only [Real.one_rpow]
      norm_num
    calc (∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ))
        = 8 * ∫ t in Set.Ioi (1 : ℝ), t ^ (-5/4 : ℝ) := by
          simp only [← smul_eq_mul]
          exact MeasureTheory.integral_const_mul _ _
      _ = 32 := by rw [hval]; norm_num
  have hImono : (∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ)) ≤ 32 := by
    calc (∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ))
        ≤ ∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ) := by
          have hIoi_int : MeasureTheory.IntegrableOn
              (fun t : ℝ => 8 * t ^ (-5/4 : ℝ))
              (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
            (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 8
          apply MeasureTheory.setIntegral_mono_set hIoi_int _ _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
              with t ht
            exact mul_nonneg (by norm_num)
              (Real.rpow_nonneg
                (le_trans zero_le_one (le_of_lt (Set.mem_Ioi.mp ht))) _)
          · exact MeasureTheory.ae_of_all _ fun t ht =>
              Set.Ioc_subset_Ioi_self ht
      _ = 32 := hIoi_val
  have hfinal : y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y) +
      (∫ t in Set.Ioc (1 : ℝ) y, (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      ≤ 40 := by
    calc _ ≤ 8 + ∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ) :=
          add_le_add hB hIval
      _ ≤ 8 + 32 := add_le_add (le_refl 8) hImono
      _ = 40 := by norm_num
  rw [hA]
  exact hfinal

/-- Mertens bound for the `tmG`-restricted reciprocal sum. -/
private lemma tm_mertens :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → |tmMert y - 1 / 2 * Real.log y| ≤ C := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  obtain ⟨C₁, hC₁⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le
    (q := 4) (3 : ZMod 4) tm_isUnit_three
  obtain ⟨C₂, hC₂⟩ := tm_sum_not_prime_le
  have hφ : Nat.totient 4 = 2 := by decide
  refine ⟨C₁ + (Real.log 2 / 2 + C₂), fun y hy => ?_⟩
  have hmain : ∀ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * tmG d -
        ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d) / (d : ℝ)|
      ≤ (if d = 2 then Real.log 2 / 2 else 0) +
        (if d.Prime then (0 : ℝ)
          else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Ioc.mp hd).1
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have h := tm_resid_diff_le d
    have hdiv : |(ArithmeticFunction.vonMangoldt d * tmG d -
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d) / (d : ℝ)|
        = |ArithmeticFunction.vonMangoldt d * tmG d -
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d| / (d : ℝ) := by
      rw [abs_div, abs_of_nonneg hdpos.le]
    have e : ((if d = 2 then Real.log 2 else 0) +
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) / (d : ℝ)
        = (if d = 2 then Real.log 2 / 2 else 0) +
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
      by_cases h : d.Prime
      · rw [ite_eq_left h, ite_eq_left h]
        by_cases h2 : d = 2
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left rfl]
          ring
        · rw [ite_eq_right h2, ite_eq_right h2, zero_add, zero_div]
      · rw [ite_eq_right h, ite_eq_right h]
        by_cases h2 : d = 2
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left rfl]
          ring
        · rw [ite_eq_right h2, ite_eq_right h2, zero_add, zero_add]
    rw [hdiv]
    exact le_trans (div_le_div_of_nonneg_right h hdpos.le) (le_of_eq e)
  have hsum : ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * tmG d -
        ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d) / (d : ℝ)|
      ≤ Real.log 2 / 2 + C₂ := by
    calc _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          ((if d = 2 then Real.log 2 / 2 else 0) +
           (if d.Prime then (0 : ℝ)
             else ArithmeticFunction.vonMangoldt d / (d : ℝ))) :=
          Finset.sum_le_sum fun d hd => hmain d hd
      _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 / 2 else 0)) +
          (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
            (if d.Prime then (0 : ℝ)
              else ArithmeticFunction.vonMangoldt d / (d : ℝ))) :=
          Finset.sum_add_distrib
      _ ≤ Real.log 2 / 2 + C₂ := by
          apply add_le_add _ (hC₂ y hy)
          simp only [Finset.sum_ite_eq']
          split_ifs with hmem
          · exact le_refl _
          · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hrfl : tmMert y =
      ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ) := rfl
  have hdiff_sum : (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * tmG d / (d : ℝ)) -
      (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ))
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        (ArithmeticFunction.vonMangoldt d * tmG d -
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d) / (d : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [sub_div]
  have hM : |tmMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ))|
      ≤ Real.log 2 / 2 + C₂ := by
    rw [hrfl, hdiff_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) hsum
  have hN5a : |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ)) -
      1 / 2 * Real.log y| ≤ C₁ := by
    have h := hC₁ y hy
    rw [hφ, Nat.cast_two] at h
    rwa [show Real.log y / 2 = 1 / 2 * Real.log y from by ring] at h
  calc |tmMert y - 1 / 2 * Real.log y|
      = |(tmMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ))) +
        ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ)) -
          1 / 2 * Real.log y)| := by
        congr 1
        ring
    _ ≤ |tmMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ))| +
        |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) n / (n : ℝ)) -
          1 / 2 * Real.log y| := abs_add_le _ _
    _ ≤ (Real.log 2 / 2 + C₂) + C₁ := add_le_add hM hN5a
    _ = C₁ + (Real.log 2 / 2 + C₂) := by ring

/-- The difference between `tmPsi` and the residue-class psi is at most
`log 2 + (ψ - θ)`. -/
private lemma tm_psi_diff_le (y : ℝ) :
    |tmPsi y - Chebyshev.psiResidueClass (3 : ZMod 4) y|
      ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) := by
  have e : tmPsi y - Chebyshev.psiResidueClass (3 : ZMod 4) y
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * tmG d -
        ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d) := by
    unfold tmPsi Chebyshev.psiResidueClass
    rw [← Finset.sum_sub_distrib]
  have hnp : ∀ z : ℝ, ∑ d ∈ Finset.Ioc 0 ⌊z⌋₊,
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)
      = Chebyshev.psi z - Chebyshev.theta z := by
    intro z
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d.Prime
    · rw [ite_eq_left h, ite_eq_right (show ¬¬d.Prime from fun hn => hn h)]
    · rw [ite_eq_right h, ite_eq_left h]
  have h2part : ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)
      ≤ Real.log 2 := by
    simp only [Finset.sum_ite_eq']
    split_ifs with hmem
    · exact le_refl _
    · exact Real.log_nonneg (by norm_num)
  rw [e]
  calc |∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * tmG d -
        ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d)|
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, |ArithmeticFunction.vonMangoldt d * tmG d -
        ArithmeticFunction.vonMangoldt.residueClass (3 : ZMod 4) d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ((if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_le_sum fun d _ => tm_resid_diff_le d
    _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)) +
        (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_add_distrib
    _ ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) :=
        add_le_add h2part (le_of_eq (hnp y))

/-- The normalized error between `tmPsi` and the residue-class psi tends to zero. -/
private lemma tm_psi_err_tendsto :
    Filter.Tendsto (fun y => (tmPsi y -
      Chebyshev.psiResidueClass (3 : ZMod 4) y) / y)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ y in Filter.atTop,
      ‖(tmPsi y - Chebyshev.psiResidueClass (3 : ZMod 4) y) / y‖
        ≤ Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have h1 := tm_psi_diff_le y
    have h2 := Chebyshev.psi_sub_theta_le hy
    have h3 := tm_two_sqrt_mul_log_le y hy
    have e1 : y ^ (3/4 : ℝ) / y = y ^ (-1/4 : ℝ) := by
      have h3 : (3/4 : ℝ) - 1 = -1/4 := by norm_num
      rw [← h3, Real.rpow_sub hypos, Real.rpow_one]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hypos.le]
    calc |tmPsi y - Chebyshev.psiResidueClass (3 : ZMod 4) y| / y
        ≤ (Real.log 2 + 8 * y ^ (3/4 : ℝ)) / y := by
          apply div_le_div_of_nonneg_right _ hypos.le
          linarith [h1, h2, h3]
      _ = Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
          rw [add_div, mul_div_assoc, e1]
  have hg : Filter.Tendsto (fun y : ℝ => Real.log 2 / y + 8 * y ^ (-1/4 : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => Real.log 2 / y) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero.const_mul (Real.log 2))
    have h2 : Filter.Tendsto (fun y : ℝ => 8 * y ^ (-1/4 : ℝ))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop
        (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul 8
      have e : ((-1/4 : ℝ)) = -((1/4 : ℝ)) := by norm_num
      rw [e]
      simpa using h
    simpa using h1.add h2
  exact squeeze_zero_norm' hbound hg

/-- `tmPsi y / y` tends to `1 / 2`. -/
private lemma tm_psi_tendsto :
    Filter.Tendsto (fun y => tmPsi y / y) Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  have hPNT := Chebyshev.tendsto_psiResidueClass_div_self (3 : ZMod 4) tm_isUnit_three
  have hφ : Nat.totient 4 = 2 := by decide
  have eφ : ((Nat.totient 4 : ℝ))⁻¹ = 1 / 2 := by
    rw [hφ]
    norm_num
  rw [eφ] at hPNT
  have heq : (fun y => tmPsi y / y) =ᶠ[Filter.atTop]
      (fun y => (tmPsi y - Chebyshev.psiResidueClass (3 : ZMod 4) y) / y +
        Chebyshev.psiResidueClass (3 : ZMod 4) y / y) := by
    filter_upwards with y
    rw [sub_div]
    ring
  have hlim := tm_psi_err_tendsto.add hPNT
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 from by ring] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

/-- `J` is close to `(2/3) A log`: the Mertens error propagates. -/
private lemma tm_J_near :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |tmJ x - 2 / 3 * tmA x * Real.log x| ≤ 2 / 3 * C * tmA x := by
  obtain ⟨C, hC⟩ := tm_mertens
  refine ⟨C, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hm : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      |tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| ≤ C := by
    intro m hmem
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmem).1
    have hmx : (m : ℝ) ≤ x := by
      have h1 : m ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ x))
    have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hge : 1 ≤ x / (m : ℝ) := by
      rw [le_div_iff₀ hpos]
      simpa using hmx
    exact hC _ hge
  have hR : |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
      (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| ≤ C * tmA x := by
    calc _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          |(tmG m / (m : ℝ)) *
            (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          (tmG m / (m : ℝ)) * C := by
          apply Finset.sum_le_sum
          intro m hmem
          calc |(tmG m / (m : ℝ)) *
              (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))|
              = (tmG m / (m : ℝ)) *
                |tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| := by
                rw [abs_mul, abs_of_nonneg
                  (div_nonneg (tmG_nonneg m) (Nat.cast_nonneg m))]
            _ ≤ (tmG m / (m : ℝ)) * C :=
                mul_le_mul_of_nonneg_left (hm m hmem)
                  (div_nonneg (tmG_nonneg m) (Nat.cast_nonneg m))
      _ = C * tmA x := by
          have hrfl : tmA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m / (m : ℝ) := rfl
          rw [← Finset.sum_mul, ← hrfl]
          ring
  have hsplit : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      (tmG m / (m : ℝ)) * tmMert (x / (m : ℝ)))
      = 1 / 2 * tmJ x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
        (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have hJ2 : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
        (tmG m / (m : ℝ)) * (1 / 2 * Real.log (x / (m : ℝ)))) = 1 / 2 * tmJ x := by
      have hJ : tmJ x =
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) * Real.log (x / (m : ℝ)) := rfl
      rw [hJ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    calc (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) * tmMert (x / (m : ℝ)))
        = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ((tmG m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ))) + (tmG m / (m : ℝ)) *
          (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))) :=
          Finset.sum_congr rfl fun m _ => by ring
      _ = (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ)))) +
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
          (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) :=
          Finset.sum_add_distrib
      _ = 1 / 2 * tmJ x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
          (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
          rw [hJ2]
  have hAJ : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ) / (n : ℝ))
      = tmA x * Real.log x - tmJ x := by
    have hJ : tmJ x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (tmG n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
    have hA : tmA x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ) := rfl
    rw [hJ, hA, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hmem
    by_cases hn : n = 0
    · subst hn
      simp [tmG_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
      ring
  have hRe : (tmA x * Real.log x - tmJ x) - 1 / 2 * tmJ x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m / (m : ℝ)) *
        (tmMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have h1 := tm_logA_eq x
    rw [hAJ] at h1
    rw [h1, hsplit]
    ring
  rw [← hRe] at hR
  have hRw : tmJ x - 2 / 3 * tmA x * Real.log x
      = -((2 / 3) * ((tmA x * Real.log x - tmJ x) - 1 / 2 * tmJ x)) := by
    ring
  rw [hRw, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  calc 2 / 3 * |(tmA x * Real.log x - tmJ x) - 1 / 2 * tmJ x|
      ≤ 2 / 3 * (C * tmA x) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = 2 / 3 * C * tmA x := by ring

/-- Increment bounds for `J`: splitting the sum at `⌊x⌋₊`. -/
private lemma tm_J_increment {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    tmA x * Real.log (y / x) ≤ tmJ y - tmJ x ∧
      tmJ y - tmJ x ≤ tmA y * Real.log (y / x) := by
  have hy : 1 ≤ y := le_trans hx hxy
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hle : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hJx : tmJ x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (tmG n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
  have hJy : tmJ y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)) := rfl
  have hAx : tmA x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ) := rfl
  have hAy : tmA y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, tmG n / (n : ℝ) := rfl
  have hsplitJ : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ))) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hsplitA : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, tmG n / (n : ℝ))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ)) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, tmG n / (n : ℝ) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hlogyx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hypos) (ne_of_gt hxpos)
  have hmain : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
        (tmG n / (n : ℝ)) * Real.log (x / (n : ℝ))
      = (tmG n / (n : ℝ)) * Real.log (y / x) := by
    intro n hmem
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hmem).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Real.log_div (ne_of_gt hypos) (ne_of_gt hnpos),
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos), hlogyx]
    ring
  have hRnn : 0 ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    apply Finset.sum_nonneg
    intro n hmem
    have hn1 : 1 ≤ n := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have h2 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hny : (n : ℝ) ≤ y := by
      have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    have hlog : 0 ≤ Real.log (y / (n : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hnpos]
      simpa using hny
    exact mul_nonneg (div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n)) hlog
  have hRle : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, tmG n / (n : ℝ)) * Real.log (y / x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hmem
    have hn1 : 1 ≤ n := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have h2 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnx : x < (n : ℝ) := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have hN : ⌊x⌋₊ + 1 ≤ n := h1
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hN
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    have hny : (n : ℝ) ≤ y := by
      have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    have hfrac : y / (n : ℝ) ≤ y / x :=
      (div_le_div_iff_of_pos_left hypos hnpos hxpos).mpr hnx.le
    have hlog : Real.log (y / (n : ℝ)) ≤ Real.log (y / x) :=
      Real.log_le_log (div_pos hypos hnpos) hfrac
    exact mul_le_mul_of_nonneg_left hlog
      (div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n))
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ))) -
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG n / (n : ℝ)) * Real.log (x / (n : ℝ)))
      = tmA x * Real.log (y / x) := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
          (tmG n / (n : ℝ)) * Real.log (x / (n : ℝ))))
        = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG n / (n : ℝ)) * Real.log (y / x) :=
      Finset.sum_congr rfl fun n hmem => hmain n hmem
    rw [hcongr, ← Finset.sum_mul, hAx]
  have hR_eq : tmA y - tmA x
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, tmG n / (n : ℝ) := by
    rw [hAy, hAx, hsplitA, add_sub_cancel_left]
  have hJyJx : tmJ y - tmJ x = tmA x * Real.log (y / x) +
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    rw [hJy, hJx, hsplitJ]
    linear_combination hdiff
  rw [hJyJx]
  constructor
  · exact le_add_of_nonneg_right hRnn
  · have hRR : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ (tmA y - tmA x) * Real.log (y / x) := by
      rw [hR_eq]
      calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)))
          ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, tmG n / (n : ℝ)) * Real.log (y / x) :=
            hRle
        _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, tmG n / (n : ℝ)) * Real.log (y / x) :=
            rfl
    calc tmA x * Real.log (y / x) +
        (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (tmG n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ tmA x * Real.log (y / x) + (tmA y - tmA x) * Real.log (y / x) :=
          add_le_add (le_refl _) hRR
      _ = tmA y * Real.log (y / x) := by ring

/-- For `|t| ≤ 1/2`, `|log (1 + t) - t| ≤ 2 t²`. -/
private lemma tm_log_one_add_le (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |(-t)| < 1 := by
    rw [abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one,
    sub_neg_eq_add] at h
  have h2 : |-t + Real.log (1 + t)| = |Real.log (1 + t) - t| := by
    congr 1
    ring
  rw [h2] at h
  have ht2 : |-t| ^ 2 = t ^ 2 := by rw [abs_neg, sq_abs]
  have hden : (1 : ℝ) / 2 ≤ 1 - |-t| := by
    rw [abs_neg]
    have := abs_nonneg t
    linarith
  have hpos : (0 : ℝ) < 1 - |-t| := by linarith
  have hle : t ^ 2 / (1 - |-t|) ≤ t ^ 2 / (1 / 2) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)
    simpa using one_div_le_one_div_of_le (by norm_num) hden
  have hexp : |-t| ^ (1 + 1) = t ^ 2 := ht2
  rw [hexp] at h
  calc |Real.log (1 + t) - t| ≤ t ^ 2 / (1 - |-t|) := h
    _ ≤ t ^ 2 / (1 / 2) := hle
    _ = 2 * t ^ 2 := by ring

/-- From a uniform increment bound, the log-scale sequence is Cauchy and
`u k / k ^ (3/2 : ℝ)` converges to a positive limit. -/
private lemma tm_growth_limit (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
    (K : ℝ) (hK : 0 ≤ K) (k₂ : ℕ)
    (hincr : ∀ k : ℕ, k₂ ≤ k →
      |Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))|
      ≤ (4 * K ^ 2 + K + 12) / (k : ℝ) ^ 2) :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ))
        Filter.atTop (nhds L) := by
  -- The log-scale sequence `v` is Cauchy via summable increments.
  set v : ℕ → ℝ := fun k => Real.log (u k) - 3 / 2 * Real.log (k : ℝ) with hvdef
  have hK' : (0 : ℝ) ≤ 4 * K ^ 2 + K + 12 := by nlinarith [sq_nonneg K, hK]
  have hF : Summable (fun n : ℕ => (4 * K ^ 2 + K + 12 : ℝ) / (n : ℝ) ^ 2) := by
    have hS : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hM := hS.mul_left (4 * K ^ 2 + K + 12)
    refine hM.congr fun n => ?_
    rw [mul_one_div]
  have hG : Summable (fun j : ℕ => (4 * K ^ 2 + K + 12 : ℝ) / (((j + k₂ : ℕ)) : ℝ) ^ 2) :=
    (summable_nat_add_iff k₂).mpr hF
  have hdist : Summable (fun j : ℕ => dist (v (j + k₂)) (v (j + k₂ + 1))) := by
    refine hG.of_nonneg_of_le (fun j => dist_nonneg) fun j => ?_
    have hk : k₂ ≤ j + k₂ := Nat.le_add_left _ _
    have h := hincr (j + k₂) hk
    rw [dist_eq_norm, Real.norm_eq_abs]
    have e : v (j + k₂) - v (j + k₂ + 1)
        = -(Real.log (u (j + k₂ + 1)) - Real.log (u (j + k₂))
          - 3 / 2 * (Real.log (((j + k₂ + 1 : ℕ)) : ℝ)
            - Real.log (((j + k₂ : ℕ)) : ℝ))) := by
      simp only [hvdef]
      ring
    rw [e, abs_neg]
    have hcast2 : ((j + k₂ + 1 : ℕ)) = (j + k₂) + 1 := rfl
    rw [hcast2]
    exact h
  have hshift : CauchySeq (fun j : ℕ => v (j + k₂)) := by
    have hD : Summable (fun j : ℕ => dist ((fun j => v (j + k₂)) j)
        ((fun j => v (j + k₂)) j.succ)) := by
      have e : (fun j : ℕ => dist ((fun j => v (j + k₂)) j)
            ((fun j => v (j + k₂)) j.succ))
            = (fun j : ℕ => dist (v (j + k₂)) (v (j + k₂ + 1))) := by
        funext j
        simp only [Nat.succ_eq_add_one]
        rw [Nat.add_right_comm j 1 k₂]
      rw [e]
      exact hdist
    exact cauchySeq_of_summable_dist hD
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hshift
  have hv_lim : Filter.Tendsto v Filter.atTop (nhds ℓ) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds ℓ) (f := v) k₂
    exact hiff.mp hℓ
  -- Exponentiate back.
  have hexp_lim : Filter.Tendsto (fun k : ℕ => Real.exp (v k))
      Filter.atTop (nhds (Real.exp ℓ)) :=
    (Real.continuous_exp.tendsto ℓ).comp hv_lim
  have heq : (fun k : ℕ => Real.exp (v k)) =ᶠ[Filter.atTop]
      (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have huk : 0 < u k := hpos k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have eexp : Real.exp (3 / 2 * Real.log (k : ℝ)) = (k : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hsk]
      congr 1
      ring
    simp only [hvdef]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log huk, Real.exp_neg, eexp]
    simp only [div_eq_mul_inv]
  refine ⟨Real.exp ℓ, Real.exp_pos ℓ, ?_⟩
  exact hexp_lim.congr' heq

/-- Abstract growth lemma: ratios `1 + 3/(2k)` up to `K/k²` force
`u k / k ^ (3/2 : ℝ)` to converge to a positive limit. -/
private lemma tm_growth (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
    (K : ℝ) (hK : 0 ≤ K) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hstep : ∀ k : ℕ, k₀ ≤ k →
      |u (k + 1) / u k - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2) :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ))
        Filter.atTop (nhds L) := by
  have hbase1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) ^ (-1 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hbase2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) ^ (-2 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun k : ℕ => 3 / (2 * (k : ℝ)))
      Filter.atTop (nhds 0) := by
    have e : (fun k : ℕ => 3 / (2 * (k : ℝ)))
        = (fun k : ℕ => (3 / 2 : ℝ) * (k : ℝ) ^ (-1 : ℝ)) := by
      funext k
      rw [Real.rpow_neg_one]
      ring
    rw [e]
    simpa using hbase1.const_mul (3 / 2 : ℝ)
  have h2 : Filter.Tendsto (fun k : ℕ => K / (k : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    have e : (fun k : ℕ => K / (k : ℝ) ^ 2)
        = (fun k : ℕ => K * (k : ℝ) ^ (-2 : ℝ)) := by
      funext k
      rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_two, div_eq_mul_inv]
    rw [e]
    simpa using hbase2.const_mul K
  have hzev : Filter.Tendsto (fun k : ℕ => 3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using h1.add h2
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp
    (hzev.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  set k₂ := max k₁ (max k₀ 2) with hk₂
  have hk₂₀ : k₀ ≤ k₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hk₂₁ : k₁ ≤ k₂ := le_max_left _ _
  have hk₂pos : 1 ≤ k₂ := le_trans hk₀ hk₂₀
  have hk₂two : 2 ≤ k₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsmall : ∀ k : ℕ, k₂ ≤ k →
      3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2 < 1 / 2 :=
    fun k hk => hk₁ k (le_trans hk₂₁ hk)
  have hkr : ∀ k : ℕ, k₂ ≤ k → (0 : ℝ) < (k : ℝ) := by
    intro k hk
    have h1k : 1 ≤ k := le_trans hk₂pos hk
    exact_mod_cast lt_of_lt_of_le zero_lt_one h1k
  have h1k : ∀ k : ℕ, k₂ ≤ k → (1 : ℝ) ≤ (k : ℝ) := by
    intro k hk
    exact_mod_cast le_trans hk₂pos hk
  have hudev : ∀ k : ℕ, k₂ ≤ k →
      |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 := by
    intro k hk
    have h := hstep k (le_trans hk₂₀ hk)
    have e : u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))
        = u (k + 1) / u k - (1 + 3 / (2 * (k : ℝ))) := by ring
    rw [e]
    exact h
  have htnn : ∀ k : ℕ, k₂ ≤ k → 0 ≤ 3 / (2 * (k : ℝ)) := by
    intro k hk
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (le_of_lt (hkr k hk)))
  have htbound : ∀ k : ℕ, k₂ ≤ k → |u (k + 1) / u k - 1| ≤ 1 / 2 := by
    intro k hk
    have e : u (k + 1) / u k - 1
        = (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) + 3 / (2 * (k : ℝ)) := by
      ring
    calc |u (k + 1) / u k - 1|
        = |(u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) + 3 / (2 * (k : ℝ))| := by
          rw [← e]
      _ ≤ |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| + |3 / (2 * (k : ℝ))| :=
          abs_add_le _ _
      _ = |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| + 3 / (2 * (k : ℝ)) := by
          rw [abs_of_nonneg (htnn k hk)]
      _ ≤ K / (k : ℝ) ^ 2 + 3 / (2 * (k : ℝ)) := by
          exact add_le_add (hudev k hk) le_rfl
      _ = 3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2 := by ring
      _ ≤ 1 / 2 := le_of_lt (hsmall k hk)
  have hinvbound : ∀ k : ℕ, k₂ ≤ k → |1 / (k : ℝ)| ≤ 1 / 2 := by
    intro k hk
    have hsk := hkr k hk
    have h2k : (2 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast le_trans hk₂two hk
    rw [abs_of_nonneg (le_of_lt (div_pos one_pos hsk))]
    calc 1 / (k : ℝ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) h2k
      _ = 1 / 2 := rfl
  have hsq2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    intro a b
    nlinarith [sq_nonneg (a - b)]
  have htsq : ∀ k : ℕ, k₂ ≤ k →
      (u (k + 1) / u k - 1) ^ 2 ≤ (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by
    intro k hk
    have hB := hudev k hk
    have hsk := hkr k hk
    have hs1 := h1k k hk
    have hsq : (u (k + 1) / u k - 1) ^ 2
        ≤ 2 * (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) ^ 2
          + 2 * (3 / (2 * (k : ℝ))) ^ 2 := by
      have h := hsq2 (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
        (3 / (2 * (k : ℝ)))
      have e : (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          + 3 / (2 * (k : ℝ)) = u (k + 1) / u k - 1 := by ring
      rwa [e] at h
    have hKnn : 0 ≤ K / (k : ℝ) ^ 2 := div_nonneg hK (sq_nonneg _)
    have hB2 : (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) ^ 2
        ≤ (K / (k : ℝ) ^ 2) ^ 2 := by
      have h2 : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
          ≤ |K / (k : ℝ) ^ 2| := by
        rw [abs_of_nonneg hKnn]
        exact hB
      exact sq_le_sq.mpr h2
    have h44 : (K / (k : ℝ) ^ 2) ^ 2 ≤ K ^ 2 / (k : ℝ) ^ 2 := by
      have h1sq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((k : ℝ) - 1), hs1]
      have hKs : K / (k : ℝ) ^ 2 ≤ K := div_le_self hK h1sq
      calc (K / (k : ℝ) ^ 2) ^ 2
          = (K / (k : ℝ) ^ 2) * (K / (k : ℝ) ^ 2) := pow_two _
        _ ≤ (K / (k : ℝ) ^ 2) * K :=
            mul_le_mul_of_nonneg_left hKs hKnn
        _ = K ^ 2 / (k : ℝ) ^ 2 := by ring
    have h32 : (3 / (2 * (k : ℝ))) ^ 2 = (9 / 4) / (k : ℝ) ^ 2 := by
      rw [div_pow, show (3 : ℝ) ^ 2 = 9 by norm_num,
        show (2 * (k : ℝ)) ^ 2 = 4 * (k : ℝ) ^ 2 by ring]
      ring
    have hfin : 2 * ((K / (k : ℝ) ^ 2) ^ 2) + 2 * ((9 / 4) / (k : ℝ) ^ 2)
        ≤ (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by
      have h2a := mul_le_mul_of_nonneg_left h44 (show (0 : ℝ) ≤ 2 by norm_num)
      have e : 2 * (K ^ 2 / (k : ℝ) ^ 2) + 2 * ((9 / 4) / (k : ℝ) ^ 2)
          = (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by ring
      linarith
    linarith [hsq, hB2, h32, hfin]
  have htri : ∀ a b c : ℝ, |a + b - c| ≤ |a| + |b| + |c| := by
    intro a b c
    calc |a + b - c| = |(a + b) + (-c)| := by rw [sub_eq_add_neg]
      _ ≤ |a + b| + |-c| := abs_add_le _ _
      _ = |a + b| + |c| := by rw [abs_neg]
      _ ≤ (|a| + |b|) + |c| := by
          have h := abs_add_le a b
          linarith
      _ = |a| + |b| + |c| := by ring
  have hincr : ∀ k : ℕ, k₂ ≤ k →
      |Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))|
      ≤ (4 * K ^ 2 + K + 12) / (k : ℝ) ^ 2 := by
    intro k hk
    have huk : 0 < u k := hpos k (le_trans hk₂pos hk)
    have huk1 : 0 < u (k + 1) :=
      hpos (k + 1) (by omega)
    have hsk := hkr k hk
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have e1 : Real.log (u (k + 1)) - Real.log (u k)
        = Real.log (u (k + 1) / u k) :=
      (Real.log_div (ne_of_gt huk1) (ne_of_gt huk)).symm
    have e2 : Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ)
        = Real.log (1 + 1 / (k : ℝ)) := by
      have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith [hsk]
      rw [hcast, ← Real.log_div (ne_of_gt hpos1) (ne_of_gt hsk)]
      congr 1
      rw [add_div, div_self (ne_of_gt hsk)]
    have e3 : Real.log (u (k + 1) / u k)
        = Real.log (1 + (u (k + 1) / u k - 1)) := by
      congr 1
      ring
    have key : Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))
        = (Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)) := by
      rw [e1, e2, e3]
      ring
    have hA : |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
        ≤ 2 * (u (k + 1) / u k - 1) ^ 2 :=
      tm_log_one_add_le _ (htbound k hk)
    have hB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 :=
      hudev k hk
    have hC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
        ≤ 2 * (1 / (k : ℝ)) ^ 2 :=
      tm_log_one_add_le _ (hinvbound k hk)
    have hC2 : (1 / (k : ℝ)) ^ 2 = 1 / (k : ℝ) ^ 2 := by
      rw [div_pow, one_pow]
    have htsqk := htsq k hk
    rw [key]
    have hmul : |3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))|
        = 3 / 2 * |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hle : |(Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))|
        ≤ |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
          + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
          + |3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))| :=
      htri _ _ _
    rw [hmul] at hle
    -- Clear denominators by multiplying with `S = (k:ℝ)^2 > 0`.
    have hS : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hsk 2
    have hSne : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hS
    have gA : |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
          * (k : ℝ) ^ 2
        ≤ 2 * ((u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hA hS.le
      linarith [h]
    have gB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| * (k : ℝ) ^ 2 ≤ K := by
      have h := mul_le_mul_of_nonneg_right hB hS.le
      rwa [div_mul_cancel₀ _ hSne] at h
    have gC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)| * (k : ℝ) ^ 2 ≤ 2 := by
      have h := mul_le_mul_of_nonneg_right hC hS.le
      have e : (2 * (1 / (k : ℝ)) ^ 2) * (k : ℝ) ^ 2 = 2 := by
        rw [hC2, mul_assoc, div_mul_cancel₀ _ hSne, mul_one]
      rwa [e] at h
    have gt : (u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2 ≤ 2 * K ^ 2 + 9 / 2 := by
      have h := mul_le_mul_of_nonneg_right htsqk hS.le
      rwa [div_mul_cancel₀ _ hSne] at h
    have gV : |(Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))| * (k : ℝ) ^ 2
        ≤ 4 * K ^ 2 + K + 12 := by
      have hstep := mul_le_mul_of_nonneg_right hle hS.le
      have e : (|Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
            + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
            + 3 / 2 * |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|) * (k : ℝ) ^ 2
          = |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
            * (k : ℝ) ^ 2
            + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| * (k : ℝ) ^ 2
            + 3 / 2 * (|Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
              * (k : ℝ) ^ 2) := by
        ring
      have h2 : 2 * ((u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2)
          ≤ 2 * (2 * K ^ 2 + 9 / 2) := by
        linarith [gt]
      linarith [hstep, e, gA, gB, gC, h2]
    exact (le_div_iff₀ hS).mpr gV
  exact tm_growth_limit u hpos K hK k₂ hincr

/-- Ratio bounds for `J` at exponential points: the input for `tm_growth`. -/
private lemma tm_J_ratio :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      |tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := tm_J_near
  obtain ⟨D, hD, hCD⟩ : ∃ D : ℝ, 0 ≤ D ∧ C ≤ D :=
    ⟨|C|, abs_nonneg _, le_abs_self _⟩
  have hC' : ∀ x : ℝ, 1 ≤ x →
      |tmJ x - 2 / 3 * tmA x * Real.log x| ≤ 2 / 3 * D * tmA x := by
    intro x hx
    have h := hC x hx
    have hA := tmA_nonneg x
    have h3 : C * tmA x ≤ D * tmA x :=
      mul_le_mul_of_nonneg_right hCD hA
    calc |tmJ x - 2 / 3 * tmA x * Real.log x| ≤ 2 / 3 * C * tmA x := h
      _ ≤ 2 / 3 * D * tmA x := by linarith [h3]
  have hE : ∀ k : ℕ, (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    intro k
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA1 : tmA 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold tmA
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [tmG_one]
  have hJ1zero : tmJ 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold tmJ
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [tmG_one]
  have hlogR : ∀ k : ℕ,
      Real.log (Real.exp (((k + 1 : ℕ)) : ℝ) / Real.exp (k : ℝ)) = 1 := by
    intro k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp, Real.log_exp, hcast]
    ring
  have hEmono : ∀ k : ℕ,
      Real.exp (k : ℝ) ≤ Real.exp (((k + 1 : ℕ)) : ℝ) := by
    intro k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    apply Real.exp_le_exp_of_le
    linarith
  have hJ1 : 1 ≤ tmJ (Real.exp 1) := by
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := tm_J_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  have hJk : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ tmJ (Real.exp (k : ℝ)) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
      Real.exp_le_exp_of_le hkR
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := tm_J_increment h1e h1k
    have hnn : 0 ≤ tmA (Real.exp 1)
        * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
      apply mul_nonneg (tmA_nonneg _)
      apply Real.log_nonneg
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa using h1k
    linarith [lo, hnn, hJ1]
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * D + 2)
  have hk₀R : 2 * D + 2 < (k₀ : ℝ) := hk₀
  have hk₀pos : 1 ≤ k₀ := by
    have hle : (1 : ℝ) ≤ (k₀ : ℝ) := by linarith [hk₀R, hD]
    exact_mod_cast hle
  refine ⟨3 * (2 * D + 1) / 2, by linarith [hD], k₀, hk₀pos, fun k hk => ?_⟩
  have hs1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hk₀pos hk
  have hsk : (0 : ℝ) < (k : ℝ) := by linarith
  have hsk2 : 2 * D + 2 ≤ (k : ℝ) := le_trans hk₀R.le (by exact_mod_cast hk)
  have hJpos : 0 < tmJ (Real.exp (k : ℝ)) := by
    have h := hJk k (le_trans hk₀pos hk)
    linarith
  have hN6k := hC' (Real.exp (k : ℝ)) (hE k)
  rw [Real.log_exp] at hN6k
  have hN6k1 := hC' (Real.exp (((k + 1 : ℕ)) : ℝ)) (hE (k + 1))
  have hlogk1 : Real.log (Real.exp (((k + 1 : ℕ)) : ℝ)) = ((k + 1 : ℕ) : ℝ) :=
    Real.log_exp _
  rw [hlogk1] at hN6k1
  obtain ⟨hN7lo, hN7hi⟩ := tm_J_increment (hE k) (hEmono k)
  rw [hlogR k, mul_one] at hN7lo hN7hi
  have hposSD : (0 : ℝ) < (k : ℝ) + D := add_pos_of_pos_of_nonneg hsk hD
  have hposT : (0 : ℝ) < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
  have hSDne : (k : ℝ) + D ≠ 0 := ne_of_gt hposSD
  have hTne : ((k : ℝ) + 1) - D ≠ 0 := ne_of_gt hposT
  have hsne : (k : ℝ) ≠ 0 := ne_of_gt hsk
  have hs2ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hsne
  have hAlo : (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ tmA (Real.exp (k : ℝ)) := by
    have hhi := (abs_le.mp hN6k).2
    have hle : tmJ (Real.exp (k : ℝ))
        ≤ (2 / 3) * ((k : ℝ) + D) * tmA (Real.exp (k : ℝ)) := by
      linarith [hhi]
    have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + D) :=
      div_nonneg (by norm_num) hposSD.le
    have h := mul_le_mul_of_nonneg_right hle hpos
    have e1 : ((2 / 3) * ((k : ℝ) + D) * tmA (Real.exp (k : ℝ)))
          * ((3 / 2) / ((k : ℝ) + D))
        = tmA (Real.exp (k : ℝ)) := by
      field_simp
    have e0 : tmJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + D))
        = (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e0, e1] at h
    exact h
  have hA'hi : tmA (Real.exp (((k + 1 : ℕ)) : ℝ))
      ≤ tmJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) := by
    have hlo := (abs_le.mp hN6k1).1
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hle' : (2 / 3) * (((k : ℝ) + 1) - D)
          * tmA (Real.exp (((k + 1 : ℕ)) : ℝ))
        ≤ tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      have e : (2 / 3) * (((k : ℝ) + 1) - D)
            * tmA (Real.exp (((k + 1 : ℕ)) : ℝ))
          = (2 / 3) * tmA (Real.exp (((k + 1 : ℕ)) : ℝ)) * (((k + 1 : ℕ)) : ℝ)
            - (2 / 3) * D * tmA (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
        rw [hcast]
        ring
      rw [e]
      linarith [hlo]
    have hpos : (0 : ℝ) ≤ 3 / (2 * (((k : ℝ) + 1) - D)) :=
      div_nonneg (by norm_num) (mul_nonneg (by norm_num) hposT.le)
    have h := mul_le_mul_of_nonneg_right hle' hpos
    have e1 : ((2 / 3) * (((k : ℝ) + 1) - D)
          * tmA (Real.exp (((k + 1 : ℕ)) : ℝ)))
          * (3 / (2 * (((k : ℝ) + 1) - D)))
        = tmA (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      field_simp
    rw [e1] at h
    exact h
  have h1 : (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - tmJ (Real.exp (k : ℝ)) :=
    le_trans hAlo hN7lo
  have h2 : (3 / 2) / ((k : ℝ) + D)
      ≤ (tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - tmJ (Real.exp (k : ℝ)))
        / tmJ (Real.exp (k : ℝ)) := by
    rw [le_div_iff₀ hJpos]
    have e : ((3 / 2) / ((k : ℝ) + D)) * tmJ (Real.exp (k : ℝ))
        = (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e]
    exact h1
  have eJJ : tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ)) - 1
      = (tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - tmJ (Real.exp (k : ℝ)))
        / tmJ (Real.exp (k : ℝ)) := by
    rw [← div_self (ne_of_gt hJpos), ← sub_div]
  have h3 : 1 + (3 / 2) / ((k : ℝ) + D)
      ≤ tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ)) := by
    linarith [h2, eJJ]
  have e' : (3 / 2) / ((k : ℝ) + D) - 3 / (2 * (k : ℝ))
      = 3 * D ^ 2 / (2 * (k : ℝ) ^ 2 * ((k : ℝ) + D))
        - (3 * D / 2) / (k : ℝ) ^ 2 := by
    field_simp
    ring
  have hdenpos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 * ((k : ℝ) + D) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hsk 2)) hposSD
  have hnn : (0 : ℝ) ≤ 3 * D ^ 2 / (2 * (k : ℝ) ^ 2 * ((k : ℝ) + D)) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg D)) hdenpos.le
  have h4 : -((3 * D / 2) / (k : ℝ) ^ 2)
      ≤ (3 / 2) / ((k : ℝ) + D) - 3 / (2 * (k : ℝ)) := by
    rw [e']
    linarith [hnn]
  have hlow : -((3 * D / 2) / (k : ℝ) ^ 2)
      ≤ tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ))) := by
    linarith [h3, h4]
  have h5 : tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - tmJ (Real.exp (k : ℝ))
      ≤ tmJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) :=
    le_trans hN7hi hA'hi
  have h6 : tmJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      ≤ tmJ (Real.exp (k : ℝ)) := by
    linarith [h5]
  have hTs : (k : ℝ) ≤ 2 * (((k : ℝ) + 1) - D) - 3 := by linarith [hsk2]
  have h2T3pos : (0 : ℝ) < 2 * (((k : ℝ) + 1) - D) - 3 := by
    linarith [hTs, hsk]
  have h2T3ne : 2 * (((k : ℝ) + 1) - D) - 3 ≠ 0 := ne_of_gt h2T3pos
  have h2Tne : 2 * (((k : ℝ) + 1) - D) ≠ 0 :=
    mul_ne_zero (by norm_num) hTne
  have h2sne : 2 * (k : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hsne
  have hδ : 3 / (2 * (((k : ℝ) + 1) - D)) < 1 := by
    have hT32 : (3 : ℝ) / 2 < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
    rw [div_lt_one (by linarith [hposT] : (0 : ℝ) < 2 * (((k : ℝ) + 1) - D))]
    linarith [hT32]
  have h1δ : (0 : ℝ) < 1 - 3 / (2 * (((k : ℝ) + 1) - D)) := by linarith [hδ]
  have h1δne : (1 - 3 / (2 * (((k : ℝ) + 1) - D))) ≠ 0 := ne_of_gt h1δ
  have h7 : tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ))
      ≤ 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    rw [le_div_iff₀ h1δ]
    have e : (tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ)))
          * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
        = (tmJ (Real.exp (((k + 1 : ℕ)) : ℝ))
            * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))) / tmJ (Real.exp (k : ℝ)) := by
      ring
    rw [e, div_le_one hJpos]
    exact h6
  have hfrac : 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) - 1
      = (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    field_simp
    ring
  have hfrac2 : (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      = 3 / (2 * (((k : ℝ) + 1) - D) - 3) := by
    field_simp
  have h10 : 3 / (2 * (((k : ℝ) + 1) - D) - 3) - 3 / (2 * (k : ℝ))
      = 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3)) := by
    field_simp
    ring
  have hden_ge : 2 * (k : ℝ) ^ 2
      ≤ 2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3) := by
    have h := mul_le_mul_of_nonneg_left hTs (show (0 : ℝ) ≤ 2 * (k : ℝ) by
      linarith [hsk])
    linarith [h]
  have hnum_nn : (0 : ℝ) ≤ 3 * (2 * D + 1) := by linarith [hD]
  have hden_pos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by
    have h := pow_pos hsk 2
    linarith [h]
  have h11 : 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
      ≤ 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
        ≤ 1 / (2 * (k : ℝ) ^ 2) :=
      one_div_le_one_div_of_le hden_pos hden_ge
    have e1 : 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
        = 3 * (2 * D + 1) * (1 / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))) := by
      rw [div_eq_mul_inv, inv_eq_one_div]
    have e2 : 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2)
        = 3 * (2 * D + 1) * (1 / (2 * (k : ℝ) ^ 2)) := by
      rw [div_eq_mul_inv, inv_eq_one_div]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 hnum_nn
  have h8 : tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ)) - 1
      ≤ (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    linarith [h7, hfrac]
  have hup : tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))
      ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    have efin : (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2
        = 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by ring
    linarith [h8, hfrac2, h10, h11, efin]
  have hfin : |tmJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / tmJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    rw [abs_le]
    constructor
    · have hKlo : -((3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2)
          ≤ -((3 * D / 2) / (k : ℝ) ^ 2) := by
        have h : (3 * D / 2) ≤ 3 * (2 * D + 1) / 2 := by linarith [hD]
        have h2 : -(3 * (2 * D + 1) / 2) ≤ -(3 * D / 2) := by linarith [h]
        have e1 : -((3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2)
            = (-(3 * (2 * D + 1) / 2)) / (k : ℝ) ^ 2 := by ring
        have e2 : -((3 * D / 2) / (k : ℝ) ^ 2)
            = (-(3 * D / 2)) / (k : ℝ) ^ 2 := by ring
        rw [e1, e2, div_le_div_iff_of_pos_right (pow_pos hsk 2)]
        exact h2
      linarith [hlow, hKlo]
    · exact hup
  exact hfin

/-- `J` at exponential points is positive. -/
private lemma tm_J_exp_pos : ∀ k : ℕ, 1 ≤ k → 0 < tmJ (Real.exp (k : ℝ)) := by
  have hA1 : tmA 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold tmA
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [tmG_one]
  have hJ1zero : tmJ 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold tmJ
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [tmG_one]
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hJ1 : 1 ≤ tmJ (Real.exp 1) := by
    obtain ⟨lo, _⟩ := tm_J_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  intro k hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
    Real.exp_le_exp_of_le hkR
  have hEk : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨lo, _⟩ := tm_J_increment h1e h1k
  have hnn : 0 ≤ tmA (Real.exp 1)
      * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
    apply mul_nonneg (tmA_nonneg _)
    apply Real.log_nonneg
    rw [le_div_iff₀ (Real.exp_pos _)]
    simpa using h1k
  linarith [lo, hnn, hJ1]

/-- Sequential version: `A(e^k) / √k → α` for some `α > 0`. -/
private lemma tm_A_seq_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun k : ℕ => tmA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
        Filter.atTop (nhds α) := by
  obtain ⟨K, hK, k₀, hk₀, hstep⟩ := tm_J_ratio
  obtain ⟨C, hC⟩ := tm_J_near
  have hpos : ∀ k : ℕ, 1 ≤ k → 0 < (fun k => tmJ (Real.exp (k : ℝ))) k :=
    fun k hk => tm_J_exp_pos k hk
  obtain ⟨L, hLpos, hL⟩ := tm_growth _ hpos K hK k₀ hk₀ hstep
  have hrpow : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ (3 / 2 : ℝ)
      = (k : ℝ) * Real.sqrt (k : ℝ) := by
    intro k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [e, Real.rpow_add hsk, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hconv : ∀ k : ℕ, 1 ≤ k → |C| < (k : ℝ) →
      (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + C)
        ≤ tmA (Real.exp (k : ℝ)) ∧
      tmA (Real.exp (k : ℝ))
        ≤ (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by
    intro k hk hCk
    have hEk : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      have h := Real.add_one_le_exp (k : ℝ)
      have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hN6 := hC (Real.exp (k : ℝ)) hEk
    rw [Real.log_exp] at hN6
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have hCab : -(k : ℝ) < C ∧ C < (k : ℝ) := abs_lt.mp hCk
    have hposPC : (0 : ℝ) < (k : ℝ) + C := by linarith [hCab.1]
    have hposMC : (0 : ℝ) < (k : ℝ) - C := by linarith [hCab.2]
    have hSDne : (k : ℝ) + C ≠ 0 := ne_of_gt hposPC
    have hMDne : (k : ℝ) - C ≠ 0 := ne_of_gt hposMC
    have hhi := (abs_le.mp hN6).2
    have hlo := (abs_le.mp hN6).1
    constructor
    · have hle : tmJ (Real.exp (k : ℝ))
          ≤ (2 / 3) * ((k : ℝ) + C) * tmA (Real.exp (k : ℝ)) := by
        linarith [hhi]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + C) :=
        div_nonneg (by norm_num) hposPC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) + C) * tmA (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) + C))
          = tmA (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : tmJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + C))
          = (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + C) := by ring
      rw [e0, e1] at h
      exact h
    · have hle : (2 / 3) * ((k : ℝ) - C) * tmA (Real.exp (k : ℝ))
          ≤ tmJ (Real.exp (k : ℝ)) := by
        linarith [hlo]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) - C) :=
        div_nonneg (by norm_num) hposMC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) - C) * tmA (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) - C))
          = tmA (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : tmJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) - C))
          = (3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by ring
      rw [e0, e1] at h
      exact h
  have hLo : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) + C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (tendsto_natCast_div_add_atTop C)
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    simpa [mul_one] using hmul2
  have hHi : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) - C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (tendsto_natCast_div_add_atTop (-C))
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    have heq : (fun k : ℕ => (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        = (fun k : ℕ => (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C)))) := by
      funext k
      have hsub : ((k : ℝ) - C) = ((k : ℝ) + (-C)) := by ring
      rw [hsub]
    rw [heq] at hmul2
    simpa [mul_one] using hmul2
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (|C| + 1)
  have hk₁R : |C| + 1 < (k₁ : ℝ) := hk₁
  have hk₁pos : 1 ≤ k₁ := by
    have hle : (1 : ℝ) ≤ (k₁ : ℝ) := by
      have hCnn : (0 : ℝ) ≤ |C| := abs_nonneg _
      linarith
    exact_mod_cast hle
  refine ⟨(3 / 2) * L, by linarith [hLpos], ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hHi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop k₁] with k hk
    have hk1 : 1 ≤ k := le_trans hk₁pos hk
    have hCk : |C| < (k : ℝ) := by
      have hle : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hconvk := hconv k hk1 hCk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hsk
    have hsqne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hsk
    have hPCne : (k : ℝ) + C ≠ 0 := ne_of_gt (by
      have hCab : -(k : ℝ) < C := (abs_lt.mp hCk).1
      linarith)
    have e : ((3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) + C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_right hconvk.1 (Real.sqrt_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop k₁] with k hk
    have hk1 : 1 ≤ k := le_trans hk₁pos hk
    have hCk : |C| < (k : ℝ) := by
      have hle : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hconvk := hconv k hk1 hCk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hsk
    have hsqne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hsk
    have hMCne : (k : ℝ) - C ≠ 0 := ne_of_gt (by
      have hCab : C < (k : ℝ) := (abs_lt.mp hCk).2
      linarith)
    have e : tmA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)
        ≤ ((3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right hconvk.2 (Real.sqrt_nonneg _)
    have e2 : ((3 / 2) * tmJ (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((tmJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [e2] at e
    exact e

/-- Shifted end: `A(e^k) / √(k+1) → α`. -/
private lemma tm_A_seq_low (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => tmA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => tmA (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (((k + 1 : ℕ)) : ℝ))
        Filter.atTop (nhds 1) := by
      have h := tendsto_natCast_div_add_atTop (1 : ℝ)
      refine h.congr' ?_
      filter_upwards with k
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
    have h2 := (Real.continuous_sqrt.tendsto 1).comp hbase
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards with k
    exact Real.sqrt_div (Nat.cast_nonneg k) _
  have hmul := hAseq.mul hratio
  have heq : (fun k : ℕ => (tmA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
          * (Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => tmA (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have hsq : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsk)
    have hsq1 : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- Shifted end: `A(e^{k+1}) / √k → α`. -/
private lemma tm_A_seq_high (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => tmA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => tmA (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α) := by
  have hshift : Filter.Tendsto
      (fun k : ℕ => tmA (Real.exp (((k + 1 : ℕ)) : ℝ))
        / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds α)
      (f := fun k : ℕ => tmA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)) 1
    exact hiff.mpr hAseq
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ)) : ℝ) / (k : ℝ))
        Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ))
          Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 1
      have h1 : Filter.Tendsto (fun k : ℕ => 1 + (1 : ℝ) / (k : ℝ))
          Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add h0
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hsk : (k : ℝ) ≠ 0 := by
        have : k ≠ 0 := by omega
        exact_mod_cast this
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_div, div_self hsk]
    have h2 := (Real.continuous_sqrt.tendsto 1).comp hbase
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards with k
    exact Real.sqrt_div (Nat.cast_nonneg _) _
  have hmul := hshift.mul hratio
  have heq : (fun k : ℕ => (tmA (Real.exp (((k + 1 : ℕ)) : ℝ))
          / Real.sqrt (((k + 1 : ℕ)) : ℝ))
          * (Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => tmA (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ)) := by
    filter_upwards with k
    have hS : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- `A(x) / √(log x)` converges to a positive limit. -/
private lemma tm_A_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun x => tmA x / Real.sqrt (Real.log x))
        Filter.atTop (nhds α) := by
  obtain ⟨α, hαpos, hAseq⟩ := tm_A_seq_tendsto
  have hlow := tm_A_seq_low α hAseq
  have hhigh := tm_A_seq_high α hAseq
  have hk_tend : Filter.Tendsto (fun x : ℝ => ⌊Real.log x⌋₊)
      Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop
  have hlowx : Filter.Tendsto
      (fun x : ℝ => tmA (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
        Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := hlow.comp hk_tend
  have hhighx : Filter.Tendsto
      (fun x : ℝ => tmA (Real.exp (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)) /
        Real.sqrt ((⌊Real.log x⌋₊ : ℕ) : ℝ))
      Filter.atTop (nhds α) := hhigh.comp hk_tend
  refine ⟨α, hαpos, ?_⟩
  have key_lo : ∀ᶠ x : ℝ in Filter.atTop,
      tmA (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)
        ≤ tmA x / Real.sqrt (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at h
    have hlognn : (0 : ℝ) ≤ Real.log x := by linarith
    have hkd : ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Nat.floor_le hlognn
    have hku : Real.log x < ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hexpk : Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ x := by
      have h := Real.exp_le_exp.mpr hkd
      rwa [Real.exp_log hxpos] at h
    have hcast1 : ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        = ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hAle1 : tmA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) ≤ tmA x :=
      tmA_mono hexpk
    have hsq2 : Real.sqrt (Real.log x)
        ≤ Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      rw [hcast1]
      exact Real.sqrt_le_sqrt hku.le
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc tmA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) /
            Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        ≤ tmA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_left (tmA_nonneg _) hsqrt_log hsq2
      _ ≤ tmA x / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle1 hsqrt_log.le
  have key_hi : ∀ᶠ x : ℝ in Filter.atTop,
      tmA x / Real.sqrt (Real.log x)
        ≤ tmA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at h
    have hlognn : (0 : ℝ) ≤ Real.log x := by linarith
    have hk1 : 1 ≤ ⌊Real.log x⌋₊ := (Nat.one_le_floor_iff _).mpr hlog1
    have hkd : ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Nat.floor_le hlognn
    have hku : Real.log x < ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hsk : (0 : ℝ) < ((⌊Real.log x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hcast1 : ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        = ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hxexp : x < Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      have h := Real.exp_lt_exp.mpr hku
      rw [Real.exp_log hxpos, ← hcast1] at h
      exact h
    have hAle2 : tmA x ≤ tmA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) :=
      tmA_mono hxexp.le
    have hsq1 : Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ)
        ≤ Real.sqrt (Real.log x) :=
      Real.sqrt_le_sqrt hkd
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc tmA x / Real.sqrt (Real.log x)
        ≤ tmA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle2 hsqrt_log.le
      _ ≤ tmA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_left (tmA_nonneg _)
            (Real.sqrt_pos.mpr hsk) hsq1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowx hhighx key_lo key_hi

/-- `A(x)` tends to infinity. -/
private lemma tm_A_atTop (α : ℝ) (hα : 0 < α)
    (hA : Filter.Tendsto (fun x => tmA x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto tmA Filter.atTop Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x))
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun y : ℝ => y ^ (1/2 : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    have h2 := h1.comp Real.tendsto_log_atTop
    refine h2.congr' ?_
    filter_upwards with x
    exact (Real.sqrt_eq_rpow _).symm
  have hAev : ∀ᶠ x : ℝ in Filter.atTop, α / 2 ≤ tmA x / Real.sqrt (Real.log x) := by
    have hmem : Set.Ioi (α / 2) ∈ nhds α := Ioi_mem_nhds (by linarith)
    filter_upwards [hA.eventually hmem] with x hx
    exact le_of_lt (Set.mem_Ioi.mp hx)
  have hlogev : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.sqrt (Real.log x) * (α / 2) ≤ tmA x := by
    filter_upwards [hAev, hlogev] with x hx1 hx2
    have hpos : (0:ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    have h := (le_div_iff₀ hpos).mp hx1
    linarith [h]
  exact Filter.tendsto_atTop_mono' _ hev
    (hsqrt.atTop_mul_const (by linarith))

/-- The log-weighted sum over the natural density:
`(Σ_{n ≤ x} tmG n · log n) / (x · A(x)) → 1 / 2`. -/
private lemma tm_L_tendsto :
    Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n : ℝ))
        / (x * tmA x))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨α, hαpos, hA⟩ := tm_A_tendsto
  have hAinf := tm_A_atTop α hαpos hA
  have hKpos : (0:ℝ) < Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK1 : (1/2 : ℝ) ≤ Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK : ∀ y : ℝ, 0 ≤ y → |tmPsi y - y / 2| ≤ (Real.log 4 + 4) * y := by
    intro y hy
    have h1 : 0 ≤ tmPsi y := tmPsi_nonneg y
    have h2 : tmPsi y ≤ (Real.log 4 + 4) * y := tmPsi_le_mul_self hy
    have h3 : (0:ℝ) ≤ y / 2 := by linarith
    have h4 : y / 2 ≤ (Real.log 4 + 4) * y := by
      have hnn := mul_nonneg (sub_nonneg.mpr hK1) hy
      linarith
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevY : ∀ᶠ y : ℝ in Filter.atTop, dist (tmPsi y / y) (1/2) ≤ ε/4 :=
    tm_psi_tendsto.eventually
      (Metric.closedBall_mem_nhds (1/2 : ℝ) (show (0:ℝ) < ε/4 by linarith))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevY
  set Y : ℝ := max Y₀ 1 with hYdef
  have hY1 : (1:ℝ) ≤ Y := le_max_right _ _
  have hYpos : (0:ℝ) < Y := by linarith
  have hYrel : ∀ y : ℝ, Y ≤ y → |tmPsi y - y/2| ≤ (ε/4) * y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hYpos hy
    have h := hY₀ y (le_trans (le_max_left _ _) hy)
    rw [Real.dist_eq] at h
    have hyne : y ≠ 0 := ne_of_gt hy0
    have e : tmPsi y - y/2 = y * (tmPsi y / y - 1/2) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg hy0.le]
    calc y * |tmPsi y / y - 1 / 2| ≤ y * (ε/4) :=
        mul_le_mul_of_nonneg_left h hy0.le
      _ = (ε/4) * y := by ring
  have hBpos : (0:ℝ) < 4 * ((Real.log 4 + 4) * Y) / ε :=
    div_pos (mul_pos (by norm_num) (mul_pos hKpos hYpos)) hε
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 4 * ((Real.log 4 + 4) * Y) / ε ≤ tmA x :=
    hAinf.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [Filter.eventually_ge_atTop 1, hB] with x hx1 hBA
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hApos : (0:ℝ) < tmA x := lt_of_lt_of_le hBpos hBA
  have hxA : (0:ℝ) < x * tmA x := mul_pos hxpos hApos
  have hhalf : x / 2 * tmA x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m * (x / (2 * (m:ℝ))) := by
    have hlrA : tmA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m / (m:ℝ) := rfl
    rw [hlrA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) - x/2 * tmA x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ))) := by
    rw [tm_L_eq, hhalf, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hbig : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, Y ≤ x/(m:ℝ) →
      |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (ε/4) * (x * (tmG m/(m:ℝ))) := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have h1 := hYrel _ hYm
    have hnn : (0:ℝ) ≤ tmG m := tmG_nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [abs_mul, abs_of_nonneg hnn]
    calc tmG m * |tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ))|
        = tmG m * |tmPsi (x/(m:ℝ)) - (x/(m:ℝ))/2| := by rw [e]
      _ ≤ tmG m * ((ε/4) * (x/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = (ε/4) * (x * (tmG m/(m:ℝ))) := by ring
  have hsmall : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, ¬ Y ≤ x/(m:ℝ) →
      |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (Real.log 4 + 4) * Y := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have hlt : x/(m:ℝ) < Y := lt_of_not_ge hYm
    have hxm0 : (0:ℝ) ≤ x/(m:ℝ) := div_nonneg hx0 hmpos.le
    have h1 := hK _ hxm0
    have hle1 : tmG m ≤ 1 := tmG_le_one m
    have hnn : (0:ℝ) ≤ tmG m := tmG_nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [← e] at h1
    calc |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        = tmG m * |tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ))| := by
          rw [abs_mul, abs_of_nonneg hnn]
      _ ≤ 1 * ((Real.log 4 + 4) * (x/(m:ℝ))) :=
          mul_le_mul hle1 h1 (abs_nonneg _) (by norm_num)
      _ = (Real.log 4 + 4) * (x/(m:ℝ)) := one_mul _
      _ ≤ (Real.log 4 + 4) * Y :=
          mul_le_mul_of_nonneg_left hlt.le hKpos.le
  have hbig_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
        |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (tmG m/(m:ℝ))) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hbig m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun m _ _ => mul_nonneg (show (0:ℝ) ≤ ε/4 by linarith)
          (mul_nonneg hx0
            (div_nonneg (tmG_nonneg m) (Nat.cast_nonneg m)))))
  have hcardx : (((Finset.Ioc 0 ⌊x⌋₊).filter
      (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ))).card : ℝ) ≤ x := by
    calc (((Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ))).card : ℝ)
        ≤ (((Finset.Ioc 0 ⌊x⌋₊).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_filter_le _ _
      _ = (⌊x⌋₊ : ℝ) := by rw [Nat.card_Ioc, Nat.sub_zero]
      _ ≤ x := Nat.floor_le hx0
  have hsmall_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
        |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ x * ((Real.log 4 + 4) * Y) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hsmall m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (le_trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
        (mul_le_mul_of_nonneg_right hcardx
          (mul_nonneg hKpos.le hYpos.le)))
  have hsum_le : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) - x/2 * tmA x|
      ≤ (ε/4) * (x * tmA x) + x * ((Real.log 4 + 4) * Y) := by
    rw [hdiff]
    calc |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
            |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
              |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|)
          + (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
              |tmG m * (tmPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|) :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (tmG m/(m:ℝ))))
          + x * ((Real.log 4 + 4) * Y) :=
          _root_.add_le_add hbig_sum hsmall_sum
      _ = (ε/4) * (x * tmA x) + x * ((Real.log 4 + 4) * Y) := by
          congr 1
          calc ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (tmG m/(m:ℝ)))
              = (ε/4) * x * ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (tmG m/(m:ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m _
                ring
            _ = (ε/4) * (x * tmA x) := by
                have hlrA : tmA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, tmG m/(m:ℝ) := rfl
                rw [hlrA]
                ring
  have e : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) / (x * tmA x) - 1/2
      = ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) - x/2 * tmA x)
        / (x * tmA x) := by
    have hxAne : x * tmA x ≠ 0 := ne_of_gt hxA
    field_simp
  have hBY : (Real.log 4 + 4) * Y / tmA x ≤ ε/4 := by
    rw [div_le_iff₀ hApos]
    have h2 : 4 * ((Real.log 4 + 4) * Y) ≤ tmA x * ε := by
      rwa [div_le_iff₀ hε] at hBA
    linarith [h2]
  have hfin : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) / (x * tmA x)
      - 1/2| ≤ ε/2 := by
    rw [e, abs_div, abs_of_nonneg hxA.le, div_le_iff₀ hxA]
    have h1 : x * ((Real.log 4 + 4) * Y) ≤ (ε/4) * (x * tmA x) := by
      have e2 : x * ((Real.log 4 + 4) * Y)
          = (x * tmA x) * ((Real.log 4 + 4) * Y / tmA x) := by
        have hAne : tmA x ≠ 0 := ne_of_gt hApos
        field_simp
      rw [e2]
      calc (x * tmA x) * ((Real.log 4 + 4) * Y / tmA x)
          ≤ (x * tmA x) * (ε/4) :=
            mul_le_mul_of_nonneg_left hBY hxA.le
        _ = (ε/4) * (x * tmA x) := by ring
    linarith [hsum_le, h1]
  change dist ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) / (x * tmA x))
    (1/2 : ℝ) < ε
  rw [Real.dist_eq]
  linarith [hfin, hε]

/-- For `x ≥ 1`: `∑_{n ≤ x} log (x / n) ≤ x`, via `N!`. -/
private lemma tm_log_sum_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log (x / (n:ℝ)) ≤ x := by
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNpos : (0:ℝ) < (N:ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNnn : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hlogne : ∀ i ∈ Finset.Ico 1 (N+1), ((i : ℕ):ℝ) ≠ 0 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hi1)
  have hlogfact : ∑ n ∈ Finset.Ico 1 (N+1), Real.log ((n:ℕ):ℝ)
      = Real.log (((Nat.factorial N : ℕ)):ℝ) := by
    have hprod : (∏ i ∈ Finset.Ico 1 (N+1), ((i:ℕ):ℝ)) = (((Nat.factorial N : ℕ)):ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Finset.prod_Ico_id_eq_factorial N
    rw [← hprod]
    exact (Real.log_prod hlogne).symm
  have hS : ∑ n ∈ Finset.Ioc 0 N, Real.log (x/(n:ℝ))
      = (N:ℝ) * Real.log x - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
    rw [hIoc]
    calc ∑ n ∈ Finset.Ico 1 (N+1), Real.log (x/((n:ℕ):ℝ))
        = ∑ n ∈ Finset.Ico 1 (N+1),
            (Real.log x - Real.log ((n:ℕ):ℝ)) :=
          Finset.sum_congr rfl (fun i hi =>
            Real.log_div (ne_of_gt hxpos) (hlogne i hi))
      _ = (Finset.Ico 1 (N+1)).card • Real.log x
          - ∑ n ∈ Finset.Ico 1 (N+1), Real.log ((n:ℕ):ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const]
      _ = (N:ℝ) * Real.log x - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
          have hcard : (Finset.Ico 1 (N+1)).card = N := by simp [Nat.card_Ico]
          rw [hlogfact, hcard, nsmul_eq_mul]
  have hfact : (N:ℝ) * Real.log (N:ℝ) - Real.log (((Nat.factorial N : ℕ)):ℝ) ≤ (N:ℝ) := by
    have hexp : HasSum (fun n : ℕ => (N:ℝ)^n / (((Nat.factorial n : ℕ)):ℝ))
        (Real.exp (N:ℝ)) := by
      have h : HasSum (fun n : ℕ => (N:ℝ)^n / (((Nat.factorial n : ℕ)):ℝ))
          (NormedSpace.exp (N:ℝ)) :=
        NormedSpace.expSeries_div_hasSum_exp _
      rwa [← Real.exp_eq_exp_ℝ] at h
    have hfact_le : (N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ) ≤ Real.exp (N:ℝ) := by
      have hle := hexp.summable.sum_le_tsum {N} (fun i _ =>
        div_nonneg (pow_nonneg hNnn _) (Nat.cast_nonneg _))
      rw [Finset.sum_singleton, hexp.tsum_eq] at hle
      exact hle
    have hpos1 : (0:ℝ) < (N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ) :=
      div_pos (pow_pos hNpos _)
        (Nat.cast_pos.mpr (Nat.factorial_pos _))
    have h2 := Real.log_le_log hpos1 hfact_le
    rw [Real.log_exp] at h2
    have e : Real.log ((N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ))
        = (N:ℝ) * Real.log (N:ℝ) - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
      rw [Real.log_div (ne_of_gt (pow_pos hNpos _))
        (ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))), Real.log_pow]
    rwa [e] at h2
  have hxd : (N:ℝ) * Real.log (x/(N:ℝ)) ≤ x - (N:ℝ) := by
    have h1 : Real.log (x/(N:ℝ)) ≤ x/(N:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hxpos hNpos)
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    have h2 := mul_le_mul_of_nonneg_left h1 hNnn
    have e : (N:ℝ) * (x/(N:ℝ) - 1) = x - (N:ℝ) := by
      rw [mul_sub, mul_one]
      congr 1
      rw [mul_comm]
      exact div_mul_cancel₀ _ hNne
    rwa [e] at h2
  have hsplit : (N:ℝ) * Real.log x
      = (N:ℝ) * Real.log (x/(N:ℝ)) + (N:ℝ) * Real.log (N:ℝ) := by
    have e : Real.log (x/(N:ℝ)) = Real.log x - Real.log (N:ℝ) :=
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)
    rw [e]
    ring
  linarith [hS, hfact, hxd, hsplit]

/-- Natural density: `N(x) · √(log x) / x → α / 2`. -/
private lemma tm_count_tendsto (α : ℝ)
    (hA : Filter.Tendsto (fun x => tmA x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto (fun x => tmCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2)) := by
  obtain ⟨α', hα'pos, hA'⟩ := tm_A_tendsto
  have hAinf := tm_A_atTop α' hα'pos hA'
  -- The `J₂` sum and its bounds.
  have hJ2eq : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ)))
      = tmCount x * Real.log x
        - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) := by
    intro x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hlrC : tmCount x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n := rfl
    rw [hlrC, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
    ring
  have hJ2nn : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ)))
        / (x * tmA x) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < tmA x :=
      lt_of_lt_of_le (by norm_num) (tmA_ge_one hx)
    apply div_nonneg _ (mul_nonneg hxpos.le hApos.le)
    apply Finset.sum_nonneg
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    have hnx : (n:ℝ) ≤ x := by
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
    have hlog : 0 ≤ Real.log (x/(n:ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hnpos]
      simpa using hnx
    exact mul_nonneg (tmG_nonneg n) hlog
  have hJ2le : ∀ᶠ x : ℝ in Filter.atTop,
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ)))
        / (x * tmA x) ≤ 1 / tmA x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < tmA x :=
      lt_of_lt_of_le (by norm_num) (tmA_ge_one hx)
    have hxA : (0:ℝ) < x * tmA x := mul_pos hxpos hApos
    have hJle : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ))) ≤ x := by
      calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ))
          ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log (x/(n:ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
            have hnpos : (0:ℝ) < (n:ℝ) := by
              exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
            have hnx : (n:ℝ) ≤ x := by
              have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
              exact le_trans (by exact_mod_cast h1)
                (Nat.floor_le (by linarith))
            have hlog : 0 ≤ Real.log (x/(n:ℝ)) := by
              apply Real.log_nonneg
              rw [le_div_iff₀ hnpos]
              simpa using hnx
            calc tmG n * Real.log (x/(n:ℝ))
                ≤ 1 * Real.log (x/(n:ℝ)) :=
                  mul_le_mul_of_nonneg_right (tmG_le_one n) hlog
              _ = Real.log (x/(n:ℝ)) := one_mul _
        _ ≤ x := tm_log_sum_le hx
    calc (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ))) / (x * tmA x)
        ≤ x / (x * tmA x) :=
          div_le_div_of_nonneg_right hJle hxA.le
      _ = 1 / tmA x := by
          have hxne : x ≠ 0 := ne_of_gt hxpos
          have hAne : tmA x ≠ 0 := ne_of_gt hApos
          field_simp
  have h1A : Filter.Tendsto (fun x => 1 / tmA x) Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hAinf
    refine h.congr' ?_
    filter_upwards with x
    exact (one_div _).symm
  have hJ2 : Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ)))
        / (x * tmA x))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1A
      hJ2nn hJ2le
  have hHlog : Filter.Tendsto
      (fun x => tmCount x * Real.log x / (x * tmA x))
      Filter.atTop (nhds (1 / 2)) := by
    have heq : (fun x => tmCount x * Real.log x / (x * tmA x)) =ᶠ[Filter.atTop]
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ)))
          / (x * tmA x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) / (x * tmA x)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      rw [hJ2eq x hx]
      ring
    have hsum := hJ2.add tm_L_tendsto
    rw [show (0:ℝ) + 1/2 = 1/2 by ring] at hsum
    have hsum' : Filter.Tendsto
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (x/(n:ℝ)))
          / (x * tmA x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n * Real.log (n:ℝ)) / (x * tmA x))
        Filter.atTop (nhds (1/2)) := hsum
    exact hsum'.congr' heq.symm
  have heq2 : (fun x => (tmCount x * Real.log x / (x * tmA x))
        * (tmA x / Real.sqrt (Real.log x)))
      =ᶠ[Filter.atTop]
      (fun x => tmCount x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsq : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlog)
    have hApos : (0:ℝ) < tmA x :=
      lt_of_lt_of_le (by norm_num) (tmA_ge_one (le_of_lt hx))
    have hxne : x ≠ 0 := ne_of_gt (by linarith)
    have hAne : tmA x ≠ 0 := ne_of_gt hApos
    have hdiv : Real.log x / Real.sqrt (Real.log x)
        = Real.sqrt (Real.log x) := by
      rw [div_eq_iff hsq, Real.mul_self_sqrt hlog.le]
    calc (tmCount x * Real.log x / (x * tmA x))
            * (tmA x / Real.sqrt (Real.log x))
        = (tmCount x / x) * (Real.log x / Real.sqrt (Real.log x)) := by
          field_simp
      _ = (tmCount x / x) * Real.sqrt (Real.log x) := by rw [hdiv]
      _ = tmCount x * Real.sqrt (Real.log x) / x := by ring
  have hprod := hHlog.mul hA
  have eα : (1/2 : ℝ) * α = α / 2 := by ring
  rw [eα] at hprod
  have hprod' : Filter.Tendsto
      (fun x => (tmCount x * Real.log x / (x * tmA x))
        * (tmA x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds (α/2)) := hprod
  exact hprod'.congr' heq2

/-- The elementary mean-value argument for `tmG`: `∑_{n ≤ x} tmG n / n ~ α √(log x)` for some
`α > 0`, and then the count of `n ≤ x` with `tmG n = 1` is `~ (α / 2) x / √(log x)`. -/
private theorem partI : ∃ α : ℝ, 0 < α ∧
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ)) / √(Real.log x))
      atTop (𝓝 α) ∧
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n) * √(Real.log x) / x)
      atTop (𝓝 (α / 2)) := by
  obtain ⟨α, hα, hA⟩ := tm_A_tendsto
  exact ⟨α, hα, hA, tm_count_tendsto α hA⟩

end Elementary

/-! ### An Abelian theorem for `√(log x)` growth -/

section Abelian

open Filter Topology

section AbelSqrtLogHelpers

open MeasureTheory

/-- `∫₀^∞ e^{-v} √v dv = Γ(3/2) = √π / 2`. -/
private theorem abelSqrtLog_integral_exp_neg_mul_sqrt :
    ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * √v = √Real.pi / 2 := by
  have h := Real.Gamma_eq_integral (s := 3 / 2) (by norm_num)
  have h32 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  rw [h32, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
    show (1 / 2 + 1 : ℝ) - 1 = 1 / 2 by norm_num] at h
  calc ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * √v
      = ∫ v in Set.Ioi (0 : ℝ), Real.exp (-v) * v ^ (1 / 2 : ℝ) := by
        simp_rw [Real.sqrt_eq_rpow]
    _ = √Real.pi / 2 := by rw [← h]; ring

/-- `v ↦ e^{-v} √v` is integrable on `(0, ∞)`. -/
private theorem abelSqrtLog_integrableOn_exp_neg_mul_sqrt :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * √v) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := 3 / 2) (by norm_num)
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at h
  simpa only [Real.sqrt_eq_rpow] using h

/-- `v ↦ e^{-v}` is integrable on `(0, ∞)`. -/
private theorem abelSqrtLog_integrableOn_exp_neg :
    IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ioi 0) := by
  simpa using exp_neg_integrableOn_Ioi 0 one_pos

/-- Change of variables `t = exp (v / ε)` in `ε ∫_{(1, ∞)} t ^ (-ε - 1) S(t) dt`. -/
private theorem abelSqrtLog_mul_integral_rpow_eq (S : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi 1, t ^ (-ε - 1) * S t =
      ∫ v in Set.Ioi 0, Real.exp (-v) * S (Real.exp (v / ε)) := by
  have h1 := integral_comp_exp_Ioi (fun t : ℝ => t ^ (-ε - 1) * S t) 0
  rw [Real.exp_zero] at h1
  rw [← h1]
  have h2 := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (-(ε * x)) * S (Real.exp x)) 0 (inv_pos.mpr hε)
  rw [mul_zero, inv_inv, smul_eq_mul] at h2
  have h3 : ∀ x : ℝ, Real.exp x • ((Real.exp x) ^ (-ε - 1) * S (Real.exp x)) =
      Real.exp (-(ε * x)) * S (Real.exp x) := by
    intro x
    rw [smul_eq_mul, ← mul_assoc, ← Real.exp_mul, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h3]
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

/-- A monotone `S` with `S x / √(log x) → α` satisfies `S x ≤ A √(log x) + B` for `x ≥ 1`. -/
private theorem abelSqrtLog_exists_bound {S : ℝ → ℝ} (hSm : Monotone S) {α : ℝ}
    (hA : Tendsto (fun x => S x / √(Real.log x)) atTop (𝓝 α)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → S x ≤ A * √(Real.log x) + B := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((hA.eventually (gt_mem_nhds (lt_add_one α))).and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨|α + 1|, |S T|, abs_nonneg _, abs_nonneg _, fun x hx => ?_⟩
  have hlog : 0 ≤ √(Real.log x) := Real.sqrt_nonneg _
  rcases le_or_gt T x with hTx | hxT
  · obtain ⟨h1, h2⟩ := hT x hTx
    have hpos : 0 < √(Real.log x) :=
      Real.sqrt_pos.mpr (Real.log_pos (by linarith))
    rw [div_lt_iff₀ hpos] at h1
    have : (α + 1) * √(Real.log x) ≤ |α + 1| * √(Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog
    linarith [abs_nonneg (S T)]
  · have h1 : S x ≤ S T := hSm hxT.le
    have h2 : 0 ≤ |α + 1| * √(Real.log x) := mul_nonneg (abs_nonneg _) hlog
    linarith [le_abs_self (S T)]

/-- The partial sums `t ↦ ∑_{0 < n ≤ t} c n` of a nonnegative sequence are monotone. -/
private theorem abelSqrtLog_partialSum_monotone {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) :
    Monotone (fun t : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n) := by
  intro s t hst
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hst)) fun i _ _ => hc i

/-- Dominated convergence: `∫₀^∞ e^{-v} √ε S(e^{v/ε}) dv → ∫₀^∞ e^{-v} α √v dv` as `ε → 0⁺`. -/
private theorem abelSqrtLog_tendsto_integral {S : ℝ → ℝ} (hS0 : ∀ x, 0 ≤ S x) (hSm : Monotone S)
    {α A B : ℝ} (hB : 0 ≤ B)
    (hA : Tendsto (fun x => S x / √(Real.log x)) atTop (𝓝 α))
    (hbound : ∀ x : ℝ, 1 ≤ x → S x ≤ A * √(Real.log x) + B) :
    Tendsto (fun ε : ℝ => ∫ v in Set.Ioi 0, Real.exp (-v) * (√ε * S (Real.exp (v / ε))))
      (𝓝[>] 0) (𝓝 (∫ v in Set.Ioi 0, Real.exp (-v) * (α * √v))) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun v => Real.exp (-v) * (A * √v + B)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hm : Measurable (fun v : ℝ => S (Real.exp (v / ε))) := by
      refine (hSm.comp fun a b hab => ?_).measurable
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hab hε.le)
    exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
      (measurable_const.mul hm)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε ⟨hε0, hε1⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v)
    have hx : 1 ≤ Real.exp (v / ε) := Real.one_le_exp (div_nonneg hv.le hε0.le)
    have h1 := hbound _ hx
    rw [Real.log_exp] at h1
    have h2 : √ε * √(v / ε) = √v := by
      rw [← Real.sqrt_mul hε0.le, mul_div_cancel₀ _ hε0.ne']
    have h3 : √ε ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hε1
    have h4 : 0 ≤ √ε := Real.sqrt_nonneg ε
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg h4 (hS0 _)))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    calc √ε * S (Real.exp (v / ε)) ≤ √ε * (A * √(v / ε) + B) :=
          mul_le_mul_of_nonneg_left h1 h4
      _ = A * (√ε * √(v / ε)) + √ε * B := by ring
      _ = A * √v + √ε * B := by rw [h2]
      _ ≤ A * √v + B := by nlinarith
  · have := (abelSqrtLog_integrableOn_exp_neg_mul_sqrt.const_mul A).add
      (abelSqrtLog_integrableOn_exp_neg.const_mul B)
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v)
    refine Tendsto.const_mul _ ?_
    have hlim : Tendsto (fun ε : ℝ => Real.exp (v / ε)) (𝓝[>] 0) atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      exact (tendsto_inv_nhdsGT_zero.const_mul_atTop hv).congr fun ε =>
        (div_eq_mul_inv v ε).symm
    have := (hA.comp hlim).mul_const (√v)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    simp only [Function.comp, Real.log_exp]
    rw [Real.sqrt_div hv.le]
    have : 0 < √v := Real.sqrt_pos.mpr hv
    have : 0 < √ε := Real.sqrt_pos.mpr hε
    field_simp

/-- Abel summation: if the partial sums are `O(t ^ (ε / 2))`, then
`∑ c n / n ^ ε = ε ∫_{(1, ∞)} t ^ (-ε - 1) S(t) dt`. -/
private theorem abelSqrtLog_hasSum_div_rpow {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ t : ℝ, 1 ≤ t → ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n ≤ C * t ^ (ε / 2)) :
    HasSum (fun n : ℕ => c n / (n : ℝ) ^ ε)
      (ε * ∫ t in Set.Ioi 1, t ^ (-ε - 1) * ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n) := by
  set c' : ℕ → ℝ := fun n => if n = 0 then 0 else c n
  have hc'0 : c' 0 = 0 := by simp [c']
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, c' k = ∑ k ∈ Finset.Ioc 0 m, c k := by
    intro m
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons, hc'0, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [c', (Finset.mem_Ioc.mp hk).1.ne']
  have hS0 : ∀ t : ℝ, 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n := fun t =>
    Finset.sum_nonneg fun i _ => hc i
  have hderiv : deriv (fun t : ℝ => t ^ (-ε)) = fun t => -ε * t ^ (-ε - 1) :=
    Real.deriv_rpow_const' _
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun t : ℝ => t ^ (-ε)) t :=
    fun t ht => Real.differentiableAt_rpow_const_of_ne _
      (zero_lt_one.trans_le (Set.mem_Ici.mp ht)).ne'
  have hf_int : LocallyIntegrableOn (deriv fun t : ℝ => t ^ (-ε)) (Set.Ici 1) := by
    rw [hderiv]
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun x hx =>
      Or.inl (zero_lt_one.trans_le (Set.mem_Ici.mp hx)).ne')
  have h_lim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Icc 0 n, c' k) atTop
      (𝓝 0) := by
    simp_rw [hsum]
    have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(ε / 2))) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < ε / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul C
      rwa [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.sum_nonneg fun i _ => hc i)) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
    have h1 := hC n hn'
    rw [Nat.floor_natCast] at h1
    calc (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Ioc 0 n, c k
        ≤ (n : ℝ) ^ (-ε) * (C * (n : ℝ) ^ (ε / 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = C * ((n : ℝ) ^ (-ε) * (n : ℝ) ^ (ε / 2)) := by ring
      _ = C * (n : ℝ) ^ (-(ε / 2)) := by
        rw [← Real.rpow_add (by linarith)]
        congr 2
        ring
  have hg_dom : (fun t : ℝ => deriv (fun t : ℝ => t ^ (-ε)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c' k) =O[atTop] fun t : ℝ => t ^ (-ε / 2 - 1) := by
    simp_rw [hderiv, hsum]
    refine Asymptotics.IsBigO.of_bound (ε * C) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_mul, abs_mul, abs_neg, abs_of_pos hε, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_of_nonneg (hS0 t)]
    calc ε * t ^ (-ε - 1) * ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k
        ≤ ε * t ^ (-ε - 1) * (C * t ^ (ε / 2)) := by
          gcongr
          exact hC t ht
      _ = ε * C * (t ^ (-ε - 1) * t ^ (ε / 2)) := by ring
      _ = ε * C * t ^ (-ε / 2 - 1) := by
        rw [← Real.rpow_add ht0]
        congr 2
        ring
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-ε / 2 - 1)) atTop :=
    integrableAtFilter_rpow_atTop_iff.mpr (by linarith)
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c' hc'0 hf_diff hf_int h_lim
    hg_dom hg_int
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n => div_nonneg (hc n) (Real.rpow_nonneg (Nat.cast_nonneg n) ε)),
    ← tendsto_add_atTop_iff_nat 1]
  simp_rw [Nat.range_succ_eq_Icc_zero]
  have hval : (0 : ℝ) - ∫ t in Set.Ioi 1, deriv (fun t : ℝ => t ^ (-ε)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c' k =
      ε * ∫ t in Set.Ioi 1, t ^ (-ε - 1) * ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n := by
    simp_rw [hderiv, hsum, mul_assoc]
    rw [integral_const_mul]
    ring
  rw [hval] at key
  refine key.congr fun n => Finset.sum_congr rfl fun k _ => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hc'0, Real.zero_rpow hε.ne']
  · simp only [c', hk, ↓reduceIte]
    rw [Real.rpow_neg (Nat.cast_nonneg k), div_eq_inv_mul]

end AbelSqrtLogHelpers

/-- An Abelian theorem: if the partial sums of a nonnegative sequence `c` grow like
`α √(log x)`, then `√ε ∑ c n / n ^ ε → α Γ(3/2) = α √π / 2` as `ε → 0⁺`. -/
private theorem abel_sqrt_log {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {α : ℝ}
    (hA : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c n) / √(Real.log x))
      atTop (𝓝 α)) :
    Tendsto (fun ε : ℝ => √ε * ∑' n : ℕ, c n / (n : ℝ) ^ ε) (𝓝[>] 0)
      (𝓝 (α * (√Real.pi / 2))) := by
  have hSm := abelSqrtLog_partialSum_monotone hc
  have hS0 : ∀ t : ℝ, 0 ≤ ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n := fun t =>
    Finset.sum_nonneg fun i _ => hc i
  obtain ⟨A, B, hA0, hB0, hbound⟩ := abelSqrtLog_exists_bound hSm hA
  have hlim := abelSqrtLog_tendsto_integral hS0 hSm hB0 hA hbound
  have hval : ∫ v in Set.Ioi 0, Real.exp (-v) * (α * √v) = α * (√Real.pi / 2) := by
    simp_rw [mul_left_comm (Real.exp _) α]
    rw [MeasureTheory.integral_const_mul, abelSqrtLog_integral_exp_neg_mul_sqrt]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hC : ∀ t : ℝ, 1 ≤ t → ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n ≤ (A / √ε + B) * t ^ (ε / 2) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    have h1 : √(Real.log t) ≤ t ^ (ε / 2) / √ε := by
      calc √(Real.log t) ≤ √(t ^ ε / ε) := Real.sqrt_le_sqrt (Real.log_le_rpow_div ht0 hε)
        _ = t ^ (ε / 2) / √ε := by
          rw [Real.sqrt_div (Real.rpow_nonneg ht0 _), Real.sqrt_eq_rpow (t ^ ε),
            ← Real.rpow_mul ht0, show ε * (1 / 2) = ε / 2 by ring]
    have h2 : 1 ≤ t ^ (ε / 2) := Real.one_le_rpow ht (by linarith)
    calc ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n ≤ A * √(Real.log t) + B := hbound t ht
      _ ≤ A * (t ^ (ε / 2) / √ε) + B * t ^ (ε / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hA0) (le_mul_of_one_le_right hB0 h2)
      _ = (A / √ε + B) * t ^ (ε / 2) := by ring
  have hsum := abelSqrtLog_hasSum_div_rpow hc hε hC
  have hcov := abelSqrtLog_mul_integral_rpow_eq
    (fun t => ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, c n) hε
  rw [hsum.tsum_eq, hcov, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  ring

end Abelian

/-! ### Euler products -/

section EulerProducts

open Filter Topology

/-- Indicator of positive integers with no prime factor `≡ 3 mod 4`. -/
private noncomputable def tmH (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 then 1 else 0

/-- Weights `-log (1 - 1/p)` on the primes `p` with `p % 4 ≠ 3`. -/
private noncomputable def tmW (n : ℕ) : ℝ :=
  if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - 1 / (n : ℝ)) else 0

/-! ### Complete multiplicativity of prime-factor indicators -/

/-- The indicator of positive integers all of whose prime factors satisfy `P` is completely
multiplicative. -/
private lemma tmPrimeFactorIndicator_mul (P : ℕ → Prop) [DecidablePred P] (m n : ℕ) :
    (if m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, P p then (1 : ℝ) else 0) =
      (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, P p then (1 : ℝ) else 0) *
        (if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p then (1 : ℝ) else 0) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Nat.primeFactors_mul hm hn]
  simp only [ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    Finset.forall_mem_union]
  split_ifs <;> simp_all

/-- Indicator of the positive integers, written in the same shape as `tmG` and `tmH`. -/
private noncomputable def tmPosIndicator (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, True then 1 else 0

private lemma tmH_mul (m n : ℕ) : tmH (m * n) = tmH m * tmH n :=
  tmPrimeFactorIndicator_mul (fun p => p % 4 ≠ 3) m n

private lemma tmPosIndicator_mul (m n : ℕ) :
    tmPosIndicator (m * n) = tmPosIndicator m * tmPosIndicator n :=
  tmPrimeFactorIndicator_mul (fun _ => True) m n

private lemma tmH_zero : tmH 0 = 0 := by simp [tmH]

private lemma tmPosIndicator_zero : tmPosIndicator 0 = 0 := by simp [tmPosIndicator]

private lemma tmH_one : tmH 1 = 1 := by simp [tmH]

private lemma tmPosIndicator_one : tmPosIndicator 1 = 1 := by simp [tmPosIndicator]

private lemma tmH_prime {p : ℕ} (hp : p.Prime) :
    tmH p = if p % 4 ≠ 3 then 1 else 0 := by
  simp [tmH, hp.primeFactors, hp.ne_zero]

private lemma tmPosIndicator_of_ne_zero {n : ℕ} (hn : n ≠ 0) : tmPosIndicator n = 1 := by
  simp [tmPosIndicator, hn]

/-- The completely multiplicative function `n ↦ a n / n ^ s`. -/
private noncomputable def tmDirichletHom (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n, a (m * n) = a m * a n) (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := a n / (n : ℝ) ^ s
  map_zero' := by simp [h0]
  map_one' := by simp [h1]
  map_mul' m n := by
    simp only [Nat.cast_mul, hmul]
    rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_div_mul_comm]

private lemma tmDirichletHom_apply (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n, a (m * n) = a m * a n) (s : ℝ) (n : ℕ) :
    tmDirichletHom a h0 h1 hmul s n = a n / (n : ℝ) ^ s :=
  rfl

private lemma tmDirichletHom_summable_norm (a : ℕ → ℝ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n, a (m * n) = a m * a n) (ha : ∀ n, |a n| ≤ 1) {s : ℝ} (hs : 1 < s) :
    Summable (fun n => ‖tmDirichletHom a h0 h1 hmul s n‖) := by
  refine (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_)
  rw [tmDirichletHom_apply, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  exact div_le_div_of_nonneg_right (ha n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

private lemma tm_abs_ite_one_zero_le_one {P : Prop} [Decidable P] :
    |(if P then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-- The Euler products give `G(s) H(s) = ζ(s)` for real `s > 1`, where `G` and `H` are the
Dirichlet series of `tmG` and `tmH`. -/
private theorem tsum_tmG_mul_tsum_tmH {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, tmG n / (n : ℝ) ^ s) * (∑' n : ℕ, tmH n / (n : ℝ) ^ s) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  have hG := EulerProduct.eulerProduct_completely_multiplicative
    (tmDirichletHom_summable_norm tmG tmG_zero tmG_one tmG_mul
      (fun _ => tm_abs_ite_one_zero_le_one) hs)
  have hH := EulerProduct.eulerProduct_completely_multiplicative
    (tmDirichletHom_summable_norm tmH tmH_zero tmH_one tmH_mul
      (fun _ => tm_abs_ite_one_zero_le_one) hs)
  have hZ := EulerProduct.eulerProduct_completely_multiplicative
    (tmDirichletHom_summable_norm tmPosIndicator tmPosIndicator_zero tmPosIndicator_one
      tmPosIndicator_mul (fun _ => tm_abs_ite_one_zero_le_one) hs)
  simp only [tmDirichletHom_apply] at hG hH hZ
  have key : ∀ N : ℕ,
      (∏ p ∈ N.primesBelow, (1 - tmG p / (p : ℝ) ^ s)⁻¹) *
          (∏ p ∈ N.primesBelow, (1 - tmH p / (p : ℝ) ^ s)⁻¹) =
        ∏ p ∈ N.primesBelow, (1 - tmPosIndicator p / (p : ℝ) ^ s)⁻¹ := by
    intro N
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primesBelow hp
    rw [tmG_prime_eq hp', tmH_prime hp', tmPosIndicator_of_ne_zero hp'.ne_zero]
    by_cases h4 : p % 4 = 3 <;> simp [h4]
  rw [tendsto_nhds_unique ((hG.mul hH).congr key) hZ]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tmPosIndicator_zero, Real.zero_rpow (by linarith : s ≠ 0)]
  · rw [tmPosIndicator_of_ne_zero hn]

private lemma tmH_div_rpow_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ tmH n / (n : ℝ) ^ s :=
  div_nonneg (by unfold tmH; split_ifs <;> norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

/-- The terms `-log (1 - p ^ (-s))` over primes `p % 4 ≠ 3` are nonnegative. -/
private lemma tm_prime_neg_log_term_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ (if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-s)) else 0) := by
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h.1.one_lt.le
    have h2 : (n : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have h3 : 0 ≤ (n : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have := Real.log_nonpos (by linarith) (by linarith : 1 - (n : ℝ) ^ (-s) ≤ 1)
    linarith
  · exact le_rfl

/-- The logarithm of the Euler product of `H(s)`: a sum of `-log (1 - p ^ (-s))` over the primes
`p` with `p % 4 ≠ 3`. -/
private theorem hasSum_log_tsum_tmH {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-s)) else 0)
      (Real.log (∑' n : ℕ, tmH n / (n : ℝ) ^ s)) := by
  have hsumH := tmDirichletHom_summable_norm tmH tmH_zero tmH_one tmH_mul
    (fun _ => tm_abs_ite_one_zero_le_one) hs
  have hH := EulerProduct.eulerProduct_completely_multiplicative hsumH
  simp only [tmDirichletHom_apply] at hH hsumH
  have hpos : 0 < ∑' n : ℕ, tmH n / (n : ℝ) ^ s := by
    have h1 := (Summable.of_norm hsumH).le_tsum 1 (fun j _ => tmH_div_rpow_nonneg s j)
    simp only [tmH_one, Nat.cast_one, Real.one_rpow, div_one] at h1
    linarith
  have hlog := ((Real.continuousAt_log hpos.ne').tendsto).comp hH
  rw [hasSum_iff_tendsto_nat_of_nonneg (tm_prime_neg_log_term_nonneg (by linarith))]
  refine hlog.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [Real.log_prod (fun p hp => ?_)]
  · simp only [Nat.primesBelow, Finset.sum_filter, ite_and]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hp h4
    · rw [tmH_prime hp, ite_eq_left h4, Real.log_inv, Real.rpow_neg (Nat.cast_nonneg p),
        one_div]
    · rw [tmH_prime hp, ite_eq_right h4]
      simp
    · rfl
  · have hp' := Nat.prime_of_mem_primesBelow hp
    rw [tmH_prime hp']
    split_ifs with h4
    · have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
      have h2 : 1 < (p : ℝ) ^ s := Real.one_lt_rpow h1 (by linarith)
      have h3 : 1 / (p : ℝ) ^ s < 1 := by rw [div_lt_one (by linarith)]; exact h2
      exact inv_ne_zero (by linarith)
    · simp

/-! ### The limit `ε → 0⁺` -/

/-- For `0 ≤ t ≤ 1/2`, `0 ≤ -log (1 - t) - t ≤ 2 t ^ 2`. -/
private lemma tm_neg_log_one_sub_sub_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    0 ≤ -Real.log (1 - t) - t ∧ -Real.log (1 - t) - t ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  refine ⟨by linarith [Real.log_le_sub_one_of_pos hpos], ?_⟩
  have habs : |t| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg h0] at h
  have h2 : t ^ 2 / (1 - t) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg t]
  have h3 := neg_abs_le (t + Real.log (1 - t))
  linarith

/-- For `0 ≤ x ≤ 1/2` and `0 ≤ y ≤ 1`, `|-log (1 - x y) - y (-log (1 - x))| ≤ 2 x ^ 2`. -/
private lemma tm_abs_neg_log_mul_sub_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    |-Real.log (1 - x * y) - -Real.log (1 - x) * y| ≤ 2 * x ^ 2 := by
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ x := mul_le_of_le_one_right hx0 hy1
  obtain ⟨h1, h2⟩ := tm_neg_log_one_sub_sub_bounds hxy0 (by linarith)
  obtain ⟨h3, h4⟩ := tm_neg_log_one_sub_sub_bounds hx0 hx1
  have e : -Real.log (1 - x * y) - -Real.log (1 - x) * y =
      (-Real.log (1 - x * y) - x * y) - y * (-Real.log (1 - x) - x) := by ring
  rw [e]
  refine abs_sub_le_of_nonneg_of_le h1 ?_ (mul_nonneg hy0 h3) ?_
  · nlinarith
  · nlinarith

/-- As `ε → 0⁺`, `log H(1 + ε)` and the Dirichlet series `∑ tmW n / n ^ ε` differ by `o(1)`. -/
private theorem tendsto_tsum_log_sub_tsum_tmW :
    Tendsto (fun ε : ℝ =>
      (∑' n : ℕ, if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) else 0) -
        ∑' n : ℕ, tmW n / (n : ℝ) ^ ε)
      (𝓝[>] 0) (𝓝 0) := by
  set A : ℝ → ℕ → ℝ := fun ε n =>
    if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) else 0 with hA_def
  set B : ℝ → ℕ → ℝ := fun ε n => tmW n / (n : ℝ) ^ ε with hB_def
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ‖A ε n - B ε n‖ ≤ 2 / (n : ℝ) ^ 2 := by
    intro ε hε n
    by_cases h : n.Prime ∧ n % 4 ≠ 3
    · simp only [hA_def, hB_def, tmW]
      rw [ite_eq_left h, ite_eq_left h]
      have hn : (0 : ℝ) < n := by exact_mod_cast h.1.pos
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1.two_le
      have hy1 : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
      have hrpow : (n : ℝ) ^ (-(1 + ε)) = 1 / (n : ℝ) * (1 / (n : ℝ) ^ ε) := by
        rw [Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one]
        field_simp
      rw [hrpow, Real.norm_eq_abs, div_eq_mul_one_div (-Real.log (1 - 1 / (n : ℝ)))]
      have hx1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
      have hy : 1 / (n : ℝ) ^ ε ≤ 1 := by rw [div_le_one (by linarith)]; exact hy1
      calc _ ≤ 2 * (1 / (n : ℝ)) ^ 2 :=
            tm_abs_neg_log_mul_sub_le (by positivity) hx1 (by positivity) hy
        _ = 2 / (n : ℝ) ^ 2 := by ring
    · simp only [hA_def, hB_def, tmW]
      rw [ite_eq_right h, ite_eq_right h]
      simp only [zero_div, sub_zero, norm_zero]
      positivity
  have hsum_bound : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) :=
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2).congr fun n => mul_one_div _ _
  have hA : ∀ ε : ℝ, 0 < ε → Summable (A ε) := fun ε hε =>
    (hasSum_log_tsum_tmH (by linarith : 1 < 1 + ε)).summable
  have hAB : ∀ ε : ℝ, 0 < ε → Summable (fun n => A ε n - B ε n) := fun ε hε =>
    hsum_bound.of_norm_bounded (hbound ε hε)
  have hB : ∀ ε : ℝ, 0 < ε → Summable (B ε) := fun ε hε => by
    simpa using (hA ε hε).sub (hAB ε hε)
  have hpt : ∀ n : ℕ, Tendsto (fun ε => A ε n - B ε n) (𝓝[>] 0) (𝓝 0) := by
    intro n
    by_cases h : n.Prime ∧ n % 4 ≠ 3
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h.1.ne_zero
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1.two_le
      have h1 : (1 : ℝ) - (n : ℝ) ^ (-(1 + 0 : ℝ)) ≠ 0 := by
        rw [add_zero, Real.rpow_neg_one]
        have : (n : ℝ)⁻¹ ≤ 1 / 2 := by
          rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hn2
        linarith
      have hc : ContinuousAt (fun ε : ℝ => -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) -
          -Real.log (1 - 1 / (n : ℝ)) / (n : ℝ) ^ ε) 0 := by
        fun_prop (disch := first | exact hn0 | exact h1 | simp)
      have h0 : -Real.log (1 - (n : ℝ) ^ (-(1 + 0 : ℝ))) -
          -Real.log (1 - 1 / (n : ℝ)) / (n : ℝ) ^ (0 : ℝ) = 0 := by
        simp [Real.rpow_neg_one]
      have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi 0) (h0 ▸ hc.tendsto)
      refine this.congr fun ε => ?_
      simp only [hA_def, hB_def, tmW]
      rw [ite_eq_left h, ite_eq_left h]
    · have : ∀ ε, A ε n - B ε n = 0 := fun ε => by
        simp only [hA_def, hB_def, tmW]
        rw [ite_eq_right h, ite_eq_right h]
        simp
      simp only [this]
      exact tendsto_const_nhds
  have hlim : Tendsto (fun ε => ∑' n, (A ε n - B ε n)) (𝓝[>] 0) (𝓝 (∑' _ : ℕ, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence hsum_bound hpt
      (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
  rw [tsum_zero] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact (hA ε hε).tsum_sub (hB ε hε)

end EulerProducts

/-! ### A log-log Abelian theorem and the constant `C` -/

section LogLog

open Filter Topology

section Helpers

open MeasureTheory Asymptotics

private lemma abelLogLog_tmW_zero : tmW 0 = 0 := by
  simp [tmW, Nat.not_prime_zero]

private lemma abelLogLog_one_sub_one_div_prime_pos {n : ℕ} (hn : n.Prime) :
    0 < 1 - 1 / (n : ℝ) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

private lemma abelLogLog_tmW_nonneg (n : ℕ) : 0 ≤ tmW n := by
  unfold tmW
  split_ifs with h
  · have hpos := abelLogLog_one_sub_one_div_prime_pos h.1
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    exact neg_nonneg.mpr (Real.log_nonpos hpos.le (by linarith))
  · exact le_rfl

private lemma abelLogLog_tmW_le_two_div (n : ℕ) : tmW n ≤ 2 / n := by
  unfold tmW
  split_ifs with h
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h.1.two_le
    have hpos := abelLogLog_one_sub_one_div_prime_pos h.1
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hlog
    refine hlog.trans ?_
    have hn1 : (0 : ℝ) < n - 1 := by linarith
    have e : (1 - 1 / (n : ℝ))⁻¹ - 1 = 1 / (n - 1) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hn1 (by linarith)]
    linarith
  · positivity

private lemma abelLogLog_tmW_eq_ite_two_add_ite (n : ℕ) :
    tmW n = (if n = 2 then Real.log 2 else 0) +
    (if n.Prime ∧ n % 4 = 1 then -Real.log (1 - 1 / (n : ℝ)) else 0) := by
  unfold tmW
  by_cases h2 : n = 2
  · subst h2
    norm_num [Nat.prime_two]
    rw [one_div, Real.log_inv, neg_neg]
  · simp only [h2, ↓reduceIte, zero_add]
    by_cases hp : n.Prime
    · have hodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      have hiff : (n % 4 ≠ 3) ↔ (n % 4 = 1) := by omega
      simp only [hp, true_and, hiff]
    · simp [hp]

private lemma abelLogLog_sum_Icc_tmW_eq {x : ℕ} (hx : 2 ≤ x) :
    ∑ n ∈ Finset.Icc 0 x, tmW n = Real.log 2 +
      ∑ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1),
        -Real.log (1 - 1 / (q : ℝ)) := by
  simp_rw [abelLogLog_tmW_eq_ite_two_add_ite, Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [Finset.sum_filter, Nat.range_succ_eq_Icc_zero]
  simp only [Finset.mem_Icc, zero_le, hx, and_self, ↓reduceIte]

private lemma abelLogLog_sqrt_log_mul_prod_eq {x : ℕ} (hx : 2 ≤ x) :
    √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)) =
      2 * Real.exp (-(∑ n ∈ Finset.Icc 0 x, tmW n - 1 / 2 * Real.log (Real.log x))) := by
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hlog : 0 < Real.log x := Real.log_pos hx1
  set S := (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1)
  have hprod : ∏ q ∈ S, (1 - 1 / (q : ℝ)) = Real.exp (∑ q ∈ S, Real.log (1 - 1 / (q : ℝ))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun q hq => (Real.exp_log ?_).symm
    exact abelLogLog_one_sub_one_div_prime_pos (Finset.mem_filter.mp hq).2.1
  rw [hprod, abelLogLog_sum_Icc_tmW_eq hx, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlog,
    ← Real.exp_add]
  have e : -(Real.log 2 + ∑ q ∈ S, -Real.log (1 - 1 / (q : ℝ)) - 1 / 2 * Real.log (Real.log x))
      = -Real.log 2 + (Real.log (Real.log x) * (1 / 2) + ∑ q ∈ S, Real.log (1 - 1 / (q : ℝ))) := by
    rw [Finset.sum_neg_distrib]
    ring
  rw [e, Real.exp_add (-Real.log 2), Real.exp_neg, Real.exp_log two_pos, ← mul_assoc,
    mul_inv_cancel₀ two_ne_zero, one_mul, Real.exp_add]

private lemma abelLogLog_log_sub_log_le_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  rw [← Real.log_div ha.ne' hb.ne']
  calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
    _ = (a - b) / b := by field_simp

private lemma abelLogLog_tendsto_log_log_sub_log_log_floor :
    Tendsto (fun t : ℝ => Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hup : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) * Real.log 2)⁻¹) atTop (𝓝 0) :=
    ((tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).atTop_mul_const
      hlog2).inv_tendsto_atTop
  have hbounds : ∀ t : ℝ, 2 ≤ t → 0 ≤ Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ∧
      Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ≤ ((⌊t⌋₊ : ℝ) * Real.log 2)⁻¹ := by
    intro t ht
    have hn2 : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast ht)
    have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have htn : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have hn0 : (0 : ℝ) < ⌊t⌋₊ := by linarith
    have hlogn : Real.log 2 ≤ Real.log ⌊t⌋₊ := Real.log_le_log two_pos hn2
    have hlognt : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hn0 hnt
    have hlogn0 : 0 < Real.log ⌊t⌋₊ := lt_of_lt_of_le hlog2 hlogn
    refine ⟨sub_nonneg.mpr (Real.log_le_log hlogn0 hlognt), ?_⟩
    calc Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊)
        ≤ (Real.log t - Real.log ⌊t⌋₊) / Real.log ⌊t⌋₊ :=
          abelLogLog_log_sub_log_le_div (by linarith) hlogn0
      _ ≤ ((t - ⌊t⌋₊) / ⌊t⌋₊) / Real.log ⌊t⌋₊ := by
          gcongr
          exact abelLogLog_log_sub_log_le_div (by linarith) hn0
      _ ≤ (1 / ⌊t⌋₊) / Real.log 2 := by
          gcongr
          linarith
      _ = ((⌊t⌋₊ : ℝ) * Real.log 2)⁻¹ := by
          rw [div_div, one_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with t ht
    exact (hbounds t ht).1
  · filter_upwards [eventually_ge_atTop 2] with t ht
    exact (hbounds t ht).2

private lemma abelLogLog_tendsto_two_mul_exp_neg {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (𝓝 C)) :
    Tendsto (fun t : ℝ => 2 * Real.exp
      (-(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, tmW n - 1 / 2 * Real.log (Real.log t)))) atTop (𝓝 C) := by
  have h1 := hC.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 : Tendsto (fun t : ℝ => Real.exp
      (1 / 2 * (Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊)))) atTop (𝓝 1) := by
    have := (abelLogLog_tendsto_log_log_sub_log_log_floor.const_mul (1 / 2)).rexp
    simpa using this
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with t ht
  have hn : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  simp only [Function.comp_apply]
  rw [abelLogLog_sqrt_log_mul_prod_eq hn, mul_assoc, ← Real.exp_add]
  congr 2
  ring

private lemma abelLogLog_sum_Icc_tmW_nonneg (N : ℕ) : 0 ≤ ∑ k ∈ Finset.Icc 0 N, tmW k :=
  Finset.sum_nonneg fun k _ => abelLogLog_tmW_nonneg k

private lemma abelLogLog_sum_Icc_tmW_le_log {t : ℝ} (ht : 1 ≤ t) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k ≤ 2 * (1 + Real.log t) := by
  calc ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k ≤ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, 2 * ((k : ℝ))⁻¹ :=
        Finset.sum_le_sum fun k _ => (abelLogLog_tmW_le_two_div k).trans_eq (by rw [div_eq_mul_inv])
    _ = 2 * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((k : ℝ))⁻¹ := by
        rw [← Finset.mul_sum]
        congr 1
        refine (Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)).symm
        · simp only [Finset.mem_Icc] at hk ⊢
          omega
        · simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
          have : k = 0 := by omega
          simp [this]
    _ = 2 * (harmonic ⌊t⌋₊ : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ 2 * (1 + Real.log t) := by
        gcongr
        exact harmonic_floor_le_one_add_log t ht

private lemma abelLogLog_sum_Icc_tmW_le_rpow {t δ : ℝ} (ht : 1 ≤ t) (hδ : 0 < δ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k ≤ (2 + 2 / δ) * t ^ δ := by
  have h1 : 1 ≤ t ^ δ := Real.one_le_rpow ht hδ.le
  have h2 : Real.log t ≤ t ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ
  calc _ ≤ 2 * (1 + Real.log t) := abelLogLog_sum_Icc_tmW_le_log ht
    _ ≤ 2 * (t ^ δ + t ^ δ / δ) := by gcongr
    _ = (2 + 2 / δ) * t ^ δ := by ring

private lemma abelLogLog_isBigO_rpow_mul_sum_Icc_tmW {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) =O[atTop]
      (fun t : ℝ => t ^ (-1 - ε / 2)) := by
  refine IsBigO.of_bound (2 + 2 / (ε / 2)) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hW := abelLogLog_sum_Icc_tmW_nonneg ⌊t⌋₊
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (by positivity)]
  calc t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k
      ≤ t ^ (-1 - ε) * ((2 + 2 / (ε / 2)) * t ^ (ε / 2)) := by
        gcongr
        exact abelLogLog_sum_Icc_tmW_le_rpow ht (by positivity)
    _ = (2 + 2 / (ε / 2)) * t ^ (-1 - ε / 2) := by
        rw [mul_left_comm, ← Real.rpow_add ht0]
        congr 2
        ring

private lemma abelLogLog_tendsto_rpow_neg_mul_sum_Icc_tmW {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Icc 0 n, tmW k) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (2 + 2 / (ε / 2)) * (n : ℝ) ^ (-(ε / 2))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by positivity : 0 < ε / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul (2 + 2 / (ε / 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with n
    have := abelLogLog_sum_Icc_tmW_nonneg n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hW := abelLogLog_sum_Icc_tmW_le_rpow hn1 (by positivity : 0 < ε / 2)
    rw [Nat.floor_natCast] at hW
    calc (n : ℝ) ^ (-ε) * ∑ k ∈ Finset.Icc 0 n, tmW k
        ≤ (n : ℝ) ^ (-ε) * ((2 + 2 / (ε / 2)) * (n : ℝ) ^ (ε / 2)) := by gcongr
      _ = (2 + 2 / (ε / 2)) * (n : ℝ) ^ (-(ε / 2)) := by
        rw [mul_left_comm, ← Real.rpow_add (by linarith)]
        congr 2
        ring

private lemma abelLogLog_integrableAtFilter_rpow {a : ℝ} (ha : a < -1) :
    IntegrableAtFilter (fun t : ℝ => t ^ a) atTop :=
  ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt ha one_pos⟩

private lemma abelLogLog_integrableOn_rpow_mul_sum_Icc_tmW {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) (Set.Ioi 1) := by
  have hloc : LocallyIntegrableOn (fun t : ℝ => t ^ (-1 - ε)) (Set.Ici 1) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    exact continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le one_pos ht).ne'
  have := (locallyIntegrableOn_mul_sum_Icc tmW (m := 0) zero_le_one
    hloc).integrableOn_of_isBigO_atTop (abelLogLog_isBigO_rpow_mul_sum_Icc_tmW hε)
    (abelLogLog_integrableAtFilter_rpow (by linarith))
  exact this.mono_set Set.Ioi_subset_Ici_self

private lemma abelLogLog_hasSum_tmW_div_rpow {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => tmW n / (n : ℝ) ^ ε)
      (ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) := by
  have hderiv : ∀ t : ℝ, 0 < t → deriv (fun x : ℝ => x ^ (-ε)) t = -ε * t ^ (-1 - ε) := by
    intro t ht
    rw [(Real.hasDerivAt_rpow_const (Or.inl ht.ne')).deriv]
    congr 2
    ring
  have hdiff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ (fun x : ℝ => x ^ (-ε)) t :=
    fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (lt_of_lt_of_le one_pos ht).ne')).differentiableAt
  have hloc : LocallyIntegrableOn (deriv (fun x : ℝ => x ^ (-ε))) (Set.Ici 1) := by
    have hc : ContinuousOn (fun t : ℝ => -ε * t ^ (-1 - ε)) (Set.Ici 1) :=
      continuousOn_const.mul
        (continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le one_pos ht).ne')
    exact (hc.congr fun t ht => hderiv t (lt_of_lt_of_le one_pos ht)).locallyIntegrableOn
      measurableSet_Ici
  have hO : (fun t : ℝ => deriv (fun x : ℝ => x ^ (-ε)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k)
      =O[atTop] (fun t : ℝ => t ^ (-1 - ε / 2)) := by
    refine ((abelLogLog_isBigO_rpow_mul_sum_Icc_tmW hε).const_mul_left (-ε)).congr' ?_
      EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hderiv t ht, mul_assoc]
  have key := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := tmW) abelLogLog_tmW_zero hdiff hloc
    (abelLogLog_tendsto_rpow_neg_mul_sum_Icc_tmW hε) hO
    (abelLogLog_integrableAtFilter_rpow (by linarith))
  have hI : ∫ t in Set.Ioi 1, deriv (fun x : ℝ => x ^ (-ε)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k
      = -ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hderiv t (lt_trans one_pos ht), mul_assoc]
  rw [hI, zero_sub, neg_mul, neg_neg] at key
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n => div_nonneg (abelLogLog_tmW_nonneg n) (by positivity)), ← tendsto_add_atTop_iff_nat 1]
  refine key.congr fun n => ?_
  rw [Nat.range_succ_eq_Icc_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg k), div_eq_inv_mul]

private lemma abelLogLog_integrableOn_rpow_mul_log_log {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * Real.log (Real.log t)) (Set.Ioi 1) := by
  refine (Real.integrableOn_log_log_mul_rpow (s := 1 + ε) (by linarith)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  rw [show -(1 + ε) = -1 - ε by ring, mul_comm]

private lemma abelLogLog_mul_integral_rpow_mul_log_log {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * Real.log (Real.log t) =
      -Real.eulerMascheroniConstant - Real.log ε := by
  have h := Real.eulerMascheroniConstant_eq_neg_integral_log_log (s := 1 + ε) (by linarith)
  have e : ∫ t in Set.Ioi 1, Real.log (Real.log t) * t ^ (-(1 + ε)) =
      ∫ t in Set.Ioi 1, t ^ (-1 - ε) * Real.log (Real.log t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show -(1 + ε) = -1 - ε by ring, mul_comm]
  rw [e, add_sub_cancel_left] at h
  linarith

private lemma abelLogLog_integrableOn_rpow_mul_D {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - ε) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t))) (Set.Ioi 1) := by
  refine ((abelLogLog_integrableOn_rpow_mul_sum_Icc_tmW hε).sub
    ((abelLogLog_integrableOn_rpow_mul_log_log hε).const_mul (1 / 2))).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  ring

private lemma abelLogLog_mul_integral_rpow_mul_D {ε : ℝ} (hε : 0 < ε) :
    ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t)) =
      1 / 2 * Real.log ε + ∑' n : ℕ, tmW n / (n : ℝ) ^ ε +
        Real.eulerMascheroniConstant / 2 := by
  have h1 := (abelLogLog_hasSum_tmW_div_rpow hε).tsum_eq
  have h2 := abelLogLog_mul_integral_rpow_mul_log_log hε
  have hsplit : ∫ t in Set.Ioi 1, t ^ (-1 - ε) *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t)) =
      (∫ t in Set.Ioi 1, t ^ (-1 - ε) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k) -
        1 / 2 * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * Real.log (Real.log t) := by
    rw [← integral_const_mul, ← integral_sub (abelLogLog_integrableOn_rpow_mul_sum_Icc_tmW hε)
      ((abelLogLog_integrableOn_rpow_mul_log_log hε).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hsplit]
  linear_combination -h1 - (1 / 2 : ℝ) * h2

/-- One-sided Abelian bound: an eventual lower bound `m ≤ f t` passes to the limit `L` of the
means `ε ∫_{t > 1} t ^ (-1 - ε) f t` as `ε → 0+`. -/
private lemma abelLogLog_le_of_tendsto_mean {f : ℝ → ℝ} {m L : ℝ}
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * f t) (Set.Ioi 1))
    (hlim : Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * f t) (𝓝[>] 0) (𝓝 L))
    (hm : ∀ᶠ t in atTop, m ≤ f t) : m ≤ L := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hm
  set T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  set K := T * ∫ t in Set.Ioc 1 T, |t ^ (-1 - 1 : ℝ) * f t|
  have hbound : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      -(ε * K) + m * T ^ (-ε) ≤ ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * f t := by
    rintro ε ⟨hε0, hε1⟩
    have hI := hint ε hε0
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hI.mono_set Set.Ioc_subset_Ioi_self)
      (hI.mono_set (Set.Ioi_subset_Ioi hT1)), mul_add]
    have hA : -(ε * K) ≤ ε * ∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t := by
      have habs : |∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t| ≤ K := by
        calc |∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t|
            ≤ ∫ t in Set.Ioc 1 T, |t ^ (-1 - ε) * f t| := abs_integral_le_integral_abs
          _ ≤ ∫ t in Set.Ioc 1 T, T * |t ^ (-1 - 1 : ℝ) * f t| := by
              refine setIntegral_mono_on (hI.mono_set Set.Ioc_subset_Ioi_self).abs
                (((hint 1 one_pos).mono_set Set.Ioc_subset_Ioi_self).abs.const_mul T)
                measurableSet_Ioc fun t ht => ?_
              obtain ⟨ht1, htT⟩ := ht
              have ht0 : 0 < t := by linarith
              have e : t ^ (-1 - ε) = t ^ (1 - ε) * t ^ (-1 - 1 : ℝ) := by
                rw [← Real.rpow_add ht0]
                congr 1
                ring
              rw [e, mul_assoc, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              calc t ^ (1 - ε) ≤ t ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
                _ = t := Real.rpow_one t
                _ ≤ T := htT
          _ = K := integral_const_mul _ _
      have := neg_abs_le (∫ t in Set.Ioc 1 T, t ^ (-1 - ε) * f t)
      nlinarith
    have hB : m * T ^ (-ε) ≤ ε * ∫ t in Set.Ioi T, t ^ (-1 - ε) * f t := by
      have h1 : ∫ t in Set.Ioi T, t ^ (-1 - ε) * m ≤ ∫ t in Set.Ioi T, t ^ (-1 - ε) * f t := by
        refine setIntegral_mono_on ((integrableOn_Ioi_rpow_of_lt (by linarith) hT0).mul_const m)
          (hI.mono_set (Set.Ioi_subset_Ioi hT1)) measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := lt_trans hT0 ht
        exact mul_le_mul_of_nonneg_left (hT₀ t (le_trans (le_max_left _ _) ht.le))
          (Real.rpow_pos_of_pos ht0 _).le
      have h2 : ∫ t in Set.Ioi T, t ^ (-1 - ε) * m = T ^ (-ε) / ε * m := by
        rw [integral_mul_const, integral_Ioi_rpow_of_lt (by linarith) hT0,
          show -1 - ε + 1 = -ε by ring, neg_div_neg_eq]
      calc m * T ^ (-ε) = ε * (T ^ (-ε) / ε * m) := by field_simp
        _ ≤ ε * ∫ t in Set.Ioi T, t ^ (-1 - ε) * f t := by
            rw [← h2]
            exact mul_le_mul_of_nonneg_left h1 hε0.le
    linarith
  have hlow : Tendsto (fun ε : ℝ => -(ε * K) + m * T ^ (-ε)) (𝓝[>] 0) (𝓝 m) := by
    have hc : Continuous (fun ε : ℝ => -(ε * K) + m * T ^ (-ε)) :=
      (continuous_id.mul continuous_const).neg.add
        (continuous_const.mul (continuous_const.rpow continuous_neg fun _ => Or.inl hT0.ne'))
    have := hc.tendsto 0
    simp only [zero_mul, neg_zero, Real.rpow_zero, mul_one, zero_add] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine le_of_tendsto_of_tendsto hlow hlim ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
  exact hbound ε hε

private lemma abelLogLog_tendsto_mean_le {f : ℝ → ℝ} {m L : ℝ}
    (hint : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * f t) (Set.Ioi 1))
    (hlim : Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * f t) (𝓝[>] 0) (𝓝 L))
    (hm : ∀ᶠ t in atTop, f t ≤ m) : L ≤ m := by
  have := abelLogLog_le_of_tendsto_mean (f := fun t => -f t) (m := -m) (L := -L)
    (fun ε hε => by simpa only [mul_neg, Pi.neg_def] using (hint ε hε).neg)
    (by simpa only [mul_neg, integral_neg] using hlim.neg)
    (hm.mono fun t ht => neg_le_neg ht)
  linarith

end Helpers

/-- The log-log Abelian theorem pins down `C`: if `(1/2) log ε + ∑ tmW n / n ^ ε → log κ` as
`ε → 0⁺`, then `C = 2 e^{-γ/2} / κ`. -/
private theorem partIII {C κ : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (𝓝 C))
    (hκ : 0 < κ)
    (hL : Tendsto (fun ε : ℝ => 1 / 2 * Real.log ε + ∑' n : ℕ, tmW n / (n : ℝ) ^ ε)
      (𝓝[>] 0) (𝓝 (Real.log κ))) :
    C = 2 * Real.exp (-Real.eulerMascheroniConstant / 2) / κ := by
  set L := Real.log κ + Real.eulerMascheroniConstant / 2 with hLdef
  set D : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, tmW k - 1 / 2 * Real.log (Real.log t)
  have hint : ∀ ε : ℝ, 0 < ε → MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-1 - ε) * D t)
      (Set.Ioi 1) := fun ε hε => abelLogLog_integrableOn_rpow_mul_D hε
  have hlim : Tendsto (fun ε : ℝ => ε * ∫ t in Set.Ioi 1, t ^ (-1 - ε) * D t) (𝓝[>] 0)
      (𝓝 L) := by
    refine (hL.add_const (Real.eulerMascheroniConstant / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (abelLogLog_mul_integral_rpow_mul_D hε).symm
  have hG : Tendsto (fun t => 2 * Real.exp (-D t)) atTop (𝓝 C) :=
    abelLogLog_tendsto_two_mul_exp_neg hC
  have key : C = 2 * Real.exp (-L) := by
    apply le_antisymm
    · refine not_lt.mp fun h => ?_
      obtain ⟨c, hc1, hc2⟩ := exists_between h
      have hcpos : 0 < c := lt_trans (by positivity) hc1
      have hev : ∀ᶠ t in atTop, D t ≤ -Real.log (c / 2) := by
        filter_upwards [hG.eventually (lt_mem_nhds hc2)] with t ht
        have h1 : c / 2 < Real.exp (-D t) := by linarith
        have h2 := (Real.log_lt_iff_lt_exp (by positivity)).mpr h1
        linarith
      have hLm := abelLogLog_tendsto_mean_le hint hlim hev
      have : c / 2 ≤ Real.exp (-L) := (Real.log_le_iff_le_exp (by positivity)).mp (by linarith)
      linarith
    · refine not_lt.mp fun h => ?_
      obtain ⟨c, hc1, hc2⟩ :=
        exists_between (max_lt h (by positivity : (0 : ℝ) < 2 * Real.exp (-L)))
      have hcpos : 0 < c := lt_of_le_of_lt (le_max_right _ _) hc1
      have hCc : C < c := lt_of_le_of_lt (le_max_left _ _) hc1
      have hev : ∀ᶠ t in atTop, -Real.log (c / 2) ≤ D t := by
        filter_upwards [hG.eventually (gt_mem_nhds hCc)] with t ht
        have h1 : Real.exp (-D t) < c / 2 := by linarith
        have h2 := (Real.lt_log_iff_exp_lt (by positivity)).mpr h1
        linarith
      have hLm := abelLogLog_le_of_tendsto_mean hint hlim hev
      have : Real.exp (-L) ≤ c / 2 := by
        rw [← Real.exp_log (by positivity : 0 < c / 2)]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
  rw [key, hLdef, neg_add, Real.exp_add, Real.exp_neg (Real.log κ), Real.exp_log hκ, neg_div]
  field_simp

end LogLog

/-! ### Assembly -/

section Assembly

open Filter Topology Asymptotics

/-- The Dirichlet series of `tmG` at a real `s > 1` is summable. -/
private lemma summable_tmG {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => tmG n / (n : ℝ) ^ s) := by
  refine (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact div_nonneg (tmG_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  · exact div_le_div_of_nonneg_right (tmG_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

/-- The Dirichlet series of `tmG` at a real `s > 1` is at least `1`. -/
private lemma one_le_tsum_tmG {s : ℝ} (hs : 1 < s) : 1 ≤ ∑' n : ℕ, tmG n / (n : ℝ) ^ s := by
  have h := (summable_tmG hs).le_tsum 1 (fun n _ =>
    div_nonneg (tmG_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
  simpa [tmG_one] using h

/-- `ε ζ(1 + ε) → 1` as `ε → 0⁺`. -/
private lemma tendsto_mul_zeta_one_add :
    Tendsto (fun ε : ℝ => ε * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝[>] 1) := by
    have hc : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_id (x := 𝓝 (0 : ℝ)))
      simpa using this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε ⊢
    linarith
  have h := tendsto_sub_mul_tsum_nat_rpow.comp hmap
  refine h.congr fun ε => ?_
  change (1 + ε - 1) * _ = _
  rw [add_sub_cancel_left]

/-- The rescaled Dirichlet series of `tmG`. -/
private lemma tendsto_sqrt_mul_tsum_tmG {α : ℝ}
    (hA : Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, tmG n / (n : ℝ)) / √(Real.log x))
      atTop (𝓝 α)) :
    Tendsto (fun ε : ℝ => √ε * ∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) (𝓝[>] 0)
      (𝓝 (α * (√Real.pi / 2))) := by
  have h := abel_sqrt_log (c := fun n => tmG n / (n : ℝ))
    (fun n => div_nonneg (tmG_nonneg n) (Nat.cast_nonneg n)) hA
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Set.mem_Ioi] at hε
  have hterm : ∀ n : ℕ, tmG n / (n : ℝ) / (n : ℝ) ^ ε = tmG n / (n : ℝ) ^ (1 + ε) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, div_zero, zero_div, Real.zero_rpow (by linarith), div_zero]
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [Real.rpow_add hnpos, Real.rpow_one, div_div]
  change √ε * ∑' n : ℕ, tmG n / (n : ℝ) / (n : ℝ) ^ ε = _
  rw [tsum_congr hterm]

/-- The asymptotic formula, assembled from the four parts above; the public theorem
`MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four` restates it. -/
private theorem main {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    IsEquivalent atTop
      (fun x : ℕ => (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ))
      (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x /
        √(Real.log x)) := by
  obtain ⟨α, hα, hA, hN⟩ := partI
  have hG := tendsto_sqrt_mul_tsum_tmG hA
  have hpi : 0 < √Real.pi / 2 := by positivity
  have hαpi : 0 < α * (√Real.pi / 2) := mul_pos hα hpi
  set κ := 1 / (α * (√Real.pi / 2)) with hκdef
  have hκ : 0 < κ := by positivity
  -- `√ε · F_h(1 + ε) → κ`.
  have hH : Tendsto (fun ε : ℝ => √ε * ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε)) (𝓝[>] 0)
      (𝓝 κ) := by
    have hq := tendsto_mul_zeta_one_add.div hG hαpi.ne'
    rw [hκdef]
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have hs : 1 < 1 + ε := by linarith
    have hF := tsum_tmG_mul_tsum_tmH hs
    have hG1 := one_le_tsum_tmG hs
    have hsq : 0 < √ε := Real.sqrt_pos.mpr hε
    simp only [Pi.div_apply]
    rw [← hF]
    have hG0 : (∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) ≠ 0 := by linarith
    rw [div_eq_iff (mul_ne_zero hsq.ne' hG0)]
    calc ε * ((∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) * ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε))
        = (√ε * √ε) * ((∑' n : ℕ, tmG n / (n : ℝ) ^ (1 + ε)) *
            ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε)) := by rw [Real.mul_self_sqrt hε.le]
      _ = _ := by ring
  -- Logarithms.
  have hlog : Tendsto (fun ε : ℝ => 1 / 2 * Real.log ε +
      ∑' n : ℕ, (if n.Prime ∧ n % 4 ≠ 3 then -Real.log (1 - (n : ℝ) ^ (-(1 + ε))) else 0))
      (𝓝[>] 0) (𝓝 (Real.log κ)) := by
    have h1 := hH.log hκ.ne'
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    have hs : 1 < 1 + ε := by linarith
    have hpos : 0 < ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε) := by
      have hF := tsum_tmG_mul_tsum_tmH hs
      have hG1 := one_le_tsum_tmG hs
      have hz : 1 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε) := by
        have h := (Real.summable_one_div_nat_rpow.mpr hs).le_tsum 1 (fun n _ => by positivity)
        simpa using h
      by_contra hneg
      have hneg' : ∑' n : ℕ, tmH n / (n : ℝ) ^ (1 + ε) ≤ 0 := not_lt.mp hneg
      nlinarith
    rw [Real.log_mul (Real.sqrt_pos.mpr hε).ne' hpos.ne', (hasSum_log_tsum_tmH hs).tsum_eq,
      Real.log_sqrt hε.le]
    ring
  have hL : Tendsto (fun ε : ℝ => 1 / 2 * Real.log ε + ∑' n : ℕ, tmW n / (n : ℝ) ^ ε)
      (𝓝[>] 0) (𝓝 (Real.log κ)) := by
    have h := hlog.sub tendsto_tsum_log_sub_tsum_tmW
    rw [sub_zero] at h
    refine h.congr fun ε => ?_
    ring
  have hCeq := partIII hC hκ hL
  -- The constant.
  have hK : √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 = α / 2 := by
    have hsqrt : √(Real.exp Real.eulerMascheroniConstant / Real.pi) =
        Real.exp (Real.eulerMascheroniConstant / 2) / √Real.pi := by
      rw [Real.sqrt_div' _ Real.pi_pos.le, ← Real.exp_half]
    have hpi0 : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have he : Real.exp (-Real.eulerMascheroniConstant / 2) =
        (Real.exp (Real.eulerMascheroniConstant / 2))⁻¹ := by
      rw [neg_div, Real.exp_neg]
    have hE0 : Real.exp (Real.eulerMascheroniConstant / 2) ≠ 0 := (Real.exp_pos _).ne'
    rw [hCeq, hκdef, hsqrt, he]
    field_simp
  -- The count as a sum of `tmG`.
  have hcard : ∀ x : ℕ,
      ((((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℕ) : ℝ) =
        ∑ n ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊, tmG n := by
    intro x
    rw [Nat.floor_natCast, Finset.card_filter, Nat.cast_sum,
      show Finset.Icc 1 x = Finset.Ioc 0 x from rfl]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    unfold tmG
    by_cases h : ∀ q ∈ n.primeFactors, q % 4 = 3
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), ite_eq_left_iff.mpr
        (fun h' => absurd ⟨hn0, h⟩ h'), Nat.cast_one]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), ite_eq_right_iff.mpr
        (fun h' => absurd h'.2 h), Nat.cast_zero]
  have hNnat : Tendsto (fun x : ℕ => (∑ n ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊, tmG n) *
      √(Real.log x) / x) atTop (𝓝 (α / 2)) := hN.comp tendsto_natCast_atTop_atTop
  have hα2 : α / 2 ≠ 0 := by positivity
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun x : ℕ => ((∑ n ∈ Finset.Ioc 0 ⌊(x : ℝ)⌋₊, tmG n) *
      √(Real.log x) / x) / (α / 2)) atTop (𝓝 1) := by
    simpa [div_self hα2] using hNnat.div_const (α / 2)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog : 0 < √(Real.log x) := Real.sqrt_pos.mpr (Real.log_pos hx1)
  simp only [Pi.div_apply]
  rw [hcard x, ← hK]
  have hK0 : √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 ≠ 0 := by rw [hK]; exact hα2
  field_simp

end Assembly

end isEquivalent_card_primeFactors_three_mod_four

@[expose] public section

open Filter Asymptotics

/-- **Counting integers whose prime factors are all $\equiv 3 \pmod 4$.** Let $C$ be a real
number such that $\sqrt{\ln x} \prod_{q \le x} (1 - 1/q) \to C$ as the natural number $x$ tends
to infinity, where $q$ runs over the primes with $q \equiv 1 \pmod 4$. Let $g(x)$ be the number
of integers $n$ with $1 \le n \le x$ all of whose prime factors are $\equiv 3 \pmod 4$ (so
$n = 1$ is counted). Then
$$g(x) \sim \sqrt{e^\gamma / \pi} \cdot \frac{C}{2} \cdot \frac{x}{\sqrt{\ln x}}$$
as the natural number $x$ tends to infinity, where $\gamma$ is the Euler–Mascheroni constant.

In the source $C = C(4, 1)$ is the constant of Languasco and Zaccagnini; for $C = 1.29230\ldots$
the constant in front of $x / \sqrt{\ln x}$ is $0.48651\ldots$.

Source: Jones and Zvonkin, *A Number-Theoretic Problem Concerning Pseudo-Real Riemann
Surfaces*, INTEGERS 25 (2025), Article A75, Theorem 2 (`integers-2025-A75-thm-2`). -/
public theorem isEquivalent_card_primeFactors_three_mod_four {C : ℝ}
    (hC : Tendsto (fun x : ℕ => √(Real.log x) *
      ∏ q ∈ (Finset.range (x + 1)).filter (fun q => q.Prime ∧ q % 4 = 1), (1 - 1 / (q : ℝ)))
      atTop (nhds C)) :
    IsEquivalent atTop
      (fun x : ℕ => (((Finset.Icc 1 x).filter fun n => ∀ q ∈ n.primeFactors, q % 4 = 3).card : ℝ))
      (fun x : ℕ => √(Real.exp Real.eulerMascheroniConstant / Real.pi) * C / 2 * x /
        √(Real.log x)) :=
  _root_.MetaMathlibExt.isEquivalent_card_primeFactors_three_mod_four.main hC

end

end MetaMathlibExt

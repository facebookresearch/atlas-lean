/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Int

@[expose] public section

section
namespace MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted

/-!
# Gronwall's maximal order of σ
This file proves Gronwall's exact maximal-order theorem for the divisor-sum
function.
-/

-- Proof roadmap. Names are chosen to avoid shadowing Mathlib.
-- a(n) = Λ(n) / (n * log n), S, A, P, T as in the vetted blueprint.

/-- Prime-power weight a(n) = Λ(n) / (n * log n). a(0) = a(1) = 0 since Λ vanishes there. -/
private noncomputable def mertensAcoeff (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)

/-- S(x) = ∑ Λ(n)/n over n ∈ [0, ⌊x⌋₊]. -/
private noncomputable def mertensS (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- A(x) = ∑ a(n) over n ∈ [0, ⌊x⌋₊]. Monotone in x (nonnegative terms). -/
private noncomputable def mertensA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, mertensAcoeff n

/-- P(x) = ∏ (1 - 1/p)⁻¹ over p ∈ primesLE ⌊x⌋₊. P(x) ≥ 1 > 0. -/
private noncomputable def mertensP (x : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹

/-- T(p,N) = ∑ 1/(k * p^k) over k ∈ [1, Nat.log p N]. -/
private noncomputable def primeTail (p N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (Nat.log p N), (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k)

/-- f(n): the Wanted function, stated exactly as in the Wanted declaration. -/
private noncomputable def gronwallF (n : ℕ) : ℝ :=
  ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))

-- Trivial ground facts (measurability/monotonicity/positivity infrastructure).

/-- a(n) is nonnegative: Λ ≥ 0 and n * log n ≥ 0 for natural n. -/
private theorem mertensAcoeff_nonneg (n : ℕ) : 0 ≤ mertensAcoeff n := by
  unfold mertensAcoeff
  apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
  by_cases hn : n = 0
  · simp [hn]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg h1)

/-- P(x) is positive: each factor (1 - 1/p)⁻¹ > 0 for prime p ≥ 2. -/
private theorem mertensP_pos (x : ℝ) : 0 < mertensP x := by
  unfold mertensP
  apply Finset.prod_pos
  intro p hp
  rw [Nat.mem_primesLE] at hp
  have hp2 : 2 ≤ p := hp.2.two_le
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have h0 : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by
    have : (p:ℝ)⁻¹ ≤ 1/2 := by
      calc (p:ℝ)⁻¹ ≤ (2:ℝ)⁻¹ := by gcongr
        _ = 1/2 := by norm_num
    linarith
  exact inv_pos.mpr h0

/-- S(x) is nonnegative: each term Λ(n)/n ≥ 0. -/
private theorem mertensS_nonneg (x : ℝ) : 0 ≤ mertensS x := by
  unfold mertensS
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

/-- A(x) is monotone: terms are nonnegative and the index set grows with x. -/
private theorem mertensA_mono : Monotone mertensA := by
  intro x y hxy
  unfold mertensA
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc (le_refl 0) (Nat.floor_mono hxy)
  · intro i _ _
    exact mertensAcoeff_nonneg i

/-- A(x) is measurable, for free from monotonicity. -/
private theorem mertensA_measurable : Measurable mertensA :=
  mertensA_mono.measurable

/-- P(x) ≥ 1: each factor (1 - 1/p)⁻¹ ≥ 1 for prime p ≥ 2 . -/
private theorem mertensP_ge_one (x : ℝ) : 1 ≤ mertensP x := by
  have hfactor : ∀ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hq1 : (p : ℝ)⁻¹ < 1 := by
      apply inv_lt_one_of_one_lt₀
      linarith
    have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg p)
    have h0 : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
    have hle : 1 - (p : ℝ)⁻¹ ≤ 1 := by linarith
    calc (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
      _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ := (inv_le_inv₀ zero_lt_one h0).mpr hle
  unfold mertensP
  suffices h : ∀ s : Finset ℕ, s ⊆ Nat.primesLE ⌊x⌋₊ →
      1 ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹ by
    exact h _ (Finset.Subset.refl _)
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a t hat ih hsub
    have ha : (1 : ℝ) ≤ (1 - (a : ℝ)⁻¹)⁻¹ :=
      hfactor a (hsub (Finset.mem_insert_self a t))
    have ht : (1 : ℝ) ≤ ∏ p ∈ t, (1 - (p : ℝ)⁻¹)⁻¹ :=
      ih (fun y hy => hsub (Finset.mem_insert_of_mem hy))
    rw [Finset.prod_insert hat]
    calc (1 : ℝ) ≤ ∏ p ∈ t, (1 - (p : ℝ)⁻¹)⁻¹ := ht
      _ ≤ (1 - (a : ℝ)⁻¹)⁻¹ * ∏ p ∈ t, (1 - (p : ℝ)⁻¹)⁻¹ :=
        le_mul_of_one_le_left (by linarith [ht]) ha

-- Shared helpers.
/-- Each Mertens factor is at least 1 for prime `p`. -/
private theorem one_le_inv_one_sub_inv_prime (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hq1 : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have h0 : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
  have hle : 1 - (p : ℝ)⁻¹ ≤ 1 := by linarith
  calc (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
    _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ := (inv_le_inv₀ zero_lt_one h0).mpr hle

-- Mertens' first theorem, weak form.
/-- Factorial as a product over `Ioc 0 N`. -/
private theorem prod_Ioc_eq_factorial (N : ℕ) :
    ∏ n ∈ Finset.Ioc 0 N, n = Nat.factorial N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Ioc_succ_top (Nat.zero_le n) _, ih, Nat.factorial_succ]
    exact mul_comm _ _

/-- `S` at a natural cast as a sum over `Ioc`. -/
private theorem mertensS_natCast (N : ℕ) :
    mertensS (N : ℝ) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  unfold mertensS
  rw [Nat.floor_natCast]
  symm
  apply Finset.sum_subset Finset.Ioc_subset_Icc_self
  intro x hx hx0
  rw [Finset.mem_Icc] at hx
  rw [Finset.mem_Ioc] at hx0
  push Not at hx0
  have hx00 : x = 0 := by omega
  rw [hx00]
  simp

/-- For naturals: `|S(N) - log N| ≤ log 4 + 4`. -/
private theorem mertens_first_bound_nat (N : ℕ) (hN : 1 ≤ N) :
    |mertensS (N : ℝ) - Real.log N| ≤ Real.log 4 + 4 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hlog_fact : Real.log ((Nat.factorial N : ℕ) : ℝ) =
      ∑ d ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
    have hfactR : ((Nat.factorial N : ℕ) : ℝ) =
        ∏ n ∈ Finset.Ioc 0 N, (n : ℝ) := by
      rw [← Nat.cast_prod, ← prod_Ioc_eq_factorial]
    have hne : ∀ n ∈ Finset.Ioc 0 N, ((n : ℕ) : ℝ) ≠ 0 := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      exact_mod_cast ne_of_gt hn.1
    rw [hfactR, Real.log_prod hne]
    have hconv := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
      (ArithmeticFunction.vonMangoldt) N
    rw [← hconv]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply]
  have hdiv_le : ∀ d ∈ Finset.Ioc 0 N,
      ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hdd : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (ne_of_gt hd.1)
    rw [le_div_iff₀ hdd]
    have hle : N / d * d ≤ N := Nat.div_mul_le_self N d
    have hcast : ((N / d * d : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
    calc ((N / d : ℕ) : ℝ) * (d : ℝ) = ((N / d * d : ℕ) : ℝ) := by
          rw [Nat.cast_mul]
      _ ≤ (N : ℝ) := hcast
  have hdiv_lt : ∀ d ∈ Finset.Ioc 0 N,
      (N : ℝ) / (d : ℝ) - 1 < ((N / d : ℕ) : ℝ) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hdd : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (ne_of_gt hd.1)
    have hmod : N % d < d := Nat.mod_lt N (Nat.pos_of_ne_zero (ne_of_gt hd.1))
    have hdiv : d * (N / d) + N % d = N := Nat.div_add_mod N d
    have hN : (N : ℝ) < ((N / d : ℕ) : ℝ) * (d : ℝ) + (d : ℝ) := by
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hdiv
      push_cast at hcast
      have h2 : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
      linarith
    have hgoal : (N : ℝ) < (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) := by
      have heq : (d : ℝ) * (((N / d : ℕ) : ℝ) + 1) =
          ((N / d : ℕ) : ℝ) * (d : ℝ) + (d : ℝ) := by ring
      rw [heq]
      exact hN
    have hlt : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀' hdd]
      exact hgoal
    linarith [hlt]
  have hNS : ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n * ((N : ℝ) / (n : ℝ)) =
        (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N,
          ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hSand1 : (N : ℝ) *
        (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        (∑ d ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt d) ≤
        Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    rw [hlog_fact]
    have hpt : ∀ d ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) -
          ArithmeticFunction.vonMangoldt d ≤
          ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
      intro d hd
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt (hdiv_lt d hd)) hΛ
      have heq : ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) -
          ArithmeticFunction.vonMangoldt d =
          ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ) - 1) := by ring
      rwa [heq]
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib] at hsum
    rwa [hNS] at hsum
  have hSand2 : Real.log ((Nat.factorial N : ℕ) : ℝ) ≤ (N : ℝ) *
      (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    rw [hlog_fact]
    have hpt : ∀ d ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) ≤
          ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) := by
      intro d hd
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt_nonneg
      exact mul_le_mul_of_nonneg_left (hdiv_le d hd) hΛ
    have hsum := Finset.sum_le_sum hpt
    rwa [hNS] at hsum
  have hfact_pos : (0 : ℝ) < ((Nat.factorial N : ℕ) : ℝ) := by
    have hpos : 0 < Nat.factorial N := Nat.factorial_pos N
    exact_mod_cast hpos
  have hfact_le : Real.log ((Nat.factorial N : ℕ) : ℝ) ≤
      (N : ℝ) * Real.log (N : ℝ) := by
    have hle : Nat.factorial N ≤ N ^ N := Nat.factorial_le_pow N
    have hleR : ((Nat.factorial N : ℕ) : ℝ) ≤ ((N ^ N : ℕ) : ℝ) := by
      exact_mod_cast hle
    have hlog := Real.log_le_log hfact_pos hleR
    rwa [Nat.cast_pow, Real.log_pow] at hlog
  have hfact_ge : (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤
      Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    have hStirling : (N : ℝ) ^ N / ((Nat.factorial N : ℕ) : ℝ) ≤
        Real.exp (N : ℝ) :=
      Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
    have hNp : (0 : ℝ) < (N : ℝ) ^ N := pow_pos hN0 N
    have hfact_ne : ((Nat.factorial N : ℕ) : ℝ) ≠ 0 := ne_of_gt hfact_pos
    have hNp_ne : (N : ℝ) ^ N ≠ 0 := ne_of_gt hNp
    have hlog := Real.log_le_log (div_pos hNp hfact_pos) hStirling
    rw [Real.log_div hNp_ne hfact_ne, Real.log_pow, Real.log_exp] at hlog
    linarith [hlog]
  have hψ : ∑ d ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt d ≤
      (Real.log 4 + 4) * (N : ℝ) := by
    have h1 : ∑ d ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt d ≤
        Chebyshev.psi (N : ℝ) := by
      rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.Ioc_subset_Icc_self
      intro i _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
    have h2 : Chebyshev.psi (N : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) :=
      Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
    linarith [h1, h2]
  have hS_lo : Real.log (N : ℝ) - 1 ≤
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    have h1 : (N : ℝ) * (Real.log (N : ℝ) - 1) ≤ (N : ℝ) *
        (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
      have heq : (N : ℝ) * (Real.log (N : ℝ) - 1) =
          (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) := by ring
      rw [heq]
      linarith [hSand2, hfact_ge]
    exact le_of_mul_le_mul_left h1 hN0
  have hS_hi : ∑ n ∈ Finset.Ioc 0 N,
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      Real.log (N : ℝ) + (Real.log 4 + 4) := by
    have h2 : (N : ℝ) *
        (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤
        (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 4)) := by
      have heq : (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 4)) =
          (N : ℝ) * Real.log (N : ℝ) + (Real.log 4 + 4) * (N : ℝ) := by ring
      rw [heq]
      linarith [hSand1, hfact_le, hψ]
    exact le_of_mul_le_mul_left h2 hN0
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  rw [mertensS_natCast]
  rw [abs_le]
  constructor
  · linarith [hS_lo, hlog4]
  · linarith [hS_hi]

private theorem mertens_first_bound :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |mertensS x - Real.log x| ≤ C := by
  refine ⟨Real.log 4 + 5, fun x hx => ?_⟩
  have hN1 : 1 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    rwa [Nat.floor_one] at h
  have hSx : mertensS x = mertensS ((⌊x⌋₊ : ℕ) : ℝ) := by
    unfold mertensS
    rw [Nat.floor_natCast]
  have hnat := mertens_first_bound_nat ⌊x⌋₊ hN1
  have hlog2 : Real.log 2 ≤ 1 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2e
    rwa [Real.log_exp] at h
  have hNx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
  have hN0 : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by
    have hpos : 0 < ⌊x⌋₊ := by omega
    exact_mod_cast hpos
  have hx2N : x ≤ 2 * ((⌊x⌋₊ : ℕ) : ℝ) := by
    have hfl := Nat.lt_floor_add_one x
    have h1N : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN1
    linarith
  have hlogN_le : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x :=
    Real.log_le_log hN0 hNx
  have hlogx_le : Real.log x ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) + Real.log 2 := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < x) hx2N
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hN0)] at h
    linarith [h]
  have habs : |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| ≤ Real.log 2 := by
    rw [abs_of_nonpos (by linarith [hlogN_le] :
      Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x ≤ 0)]
    linarith [hlogx_le]
  have htri : |mertensS ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| ≤
      |mertensS ((⌊x⌋₊ : ℕ) : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| +
        |Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x| := by
    have h := abs_add_le (mertensS ((⌊x⌋₊ : ℕ) : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ))
      (Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x)
    have heq : (mertensS ((⌊x⌋₊ : ℕ) : ℝ) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)) +
        (Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x) =
        mertensS ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x := by ring
    rwa [heq] at h
  rw [hSx]
  linarith [htri, hnat, habs, hlog2]

/-- Coefficient `Λ(k)/k` vanishes at `k = 0`. -/
private theorem mertensS_coeff_zero :
    (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ)) 0 = 0 := by
  simp

/-- Coefficient `Λ(k)/k` vanishes at `k = 1`. -/
private theorem mertensS_coeff_one :
    (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ)) 1 = 0 := by
  simp

/-- Term identity `(log k)⁻¹ * (Λ(k)/k) = a(k)`; pure algebra, no side conditions. -/
private theorem mertensA_term_eq (k : ℕ) :
    (Real.log (k : ℝ))⁻¹ * (ArithmeticFunction.vonMangoldt k / (k : ℝ)) =
      mertensAcoeff k := by
  unfold mertensAcoeff
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- `A(x)` as a sum of `(log k)⁻¹ * (Λ(k)/k)`, the shape Abel summation needs. -/
private theorem mertensA_sum_eq (x : ℝ) :
    mertensA x = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
      (Real.log (k : ℝ))⁻¹ * (ArithmeticFunction.vonMangoldt k / (k : ℝ)) := by
  unfold mertensA
  exact Finset.sum_congr rfl fun k _ => (mertensA_term_eq k).symm

/-- `t ↦ (log t)⁻¹` is differentiable on `[2, x]`. -/
private theorem mertensA_diff_on (x : ℝ) :
    ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun n : ℝ => (Real.log n)⁻¹) t := by
  intro t ht
  have h2 : (2 : ℝ) ≤ t := ht.1
  exact Real.differentiableAt_inv_log (by linarith) (by linarith) (by linarith)

/-- The derivative of `t ↦ (log t)⁻¹` is integrable on `[2, x]`. -/
private theorem mertensA_deriv_integrable (x : ℝ) :
    MeasureTheory.IntegrableOn (deriv fun n : ℝ => (Real.log n)⁻¹)
      (Set.Icc 2 x) := by
  refine ContinuousOn.integrableOn_Icc fun z hz ↦
    ContinuousWithinAt.congr ?_ (fun _ _ ↦ Real.deriv_inv_log_apply)
      Real.deriv_inv_log_apply
  have hz0 : z ≠ 0 := by linarith [hz.1]
  have hlog2 : Real.log z ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
  exact ContinuousAt.continuousWithinAt <| by fun_prop

/-- Pointwise derivative identity inside the Abel integral. -/
private theorem mertensA_deriv_mul_eq (t : ℝ) :
    deriv (fun n : ℝ => (Real.log n)⁻¹) t * mertensS t =
      -(mertensS t / (t * (Real.log t) ^ 2)) := by
  rw [Real.deriv_inv_log_apply, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

-- Abel summation: A in terms of S.
-- Template: Chebyshev.primeCounting_eq_theta_div_log_add_integral.
private theorem mertensA_eq_abel (x : ℝ) (hx : 2 ≤ x) :
    mertensA x = mertensS x / Real.log x +
      ∫ t in (2 : ℝ)..x, mertensS t / (t * (Real.log t) ^ 2) := by
  have hS : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
      ArithmeticFunction.vonMangoldt k / (k : ℝ)) = mertensS t :=
    fun _ => rfl
  have hint : (∫ t in (2 : ℝ)..x,
        deriv (fun n : ℝ => (Real.log n)⁻¹) t * mertensS t) =
      -(∫ t in (2 : ℝ)..x, mertensS t / (t * (Real.log t) ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun t _ => mertensA_deriv_mul_eq t
  rw [mertensA_sum_eq x,
    sum_mul_eq_sub_integral_mul₁ _ mertensS_coeff_zero mertensS_coeff_one x
      (mertensA_diff_on x) (mertensA_deriv_integrable x),
    ← intervalIntegral.integral_of_le hx]
  simp only [hS]
  rw [hint, sub_neg_eq_add, div_eq_mul_inv]
  ring

/-- `S(x)` is monotone: terms are nonnegative and the index set grows. -/
private theorem mertensS_mono : Monotone mertensS := by
  intro x y hxy
  unfold mertensS
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc (le_refl 0) (Nat.floor_mono hxy)
  · intro i _ _
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg i)

/-- `S(x)` is measurable, for free from monotonicity. -/
private theorem mertensS_measurable : Measurable mertensS :=
  mertensS_mono.measurable

/-- `a(n) = (Λ(n)/n) * (log n)⁻¹`. -/
private theorem mertensAcoeff_mul_inv (n : ℕ) :
    mertensAcoeff n =
      (ArithmeticFunction.vonMangoldt n / (n : ℝ)) * (Real.log (n : ℝ))⁻¹ := by
  unfold mertensAcoeff
  rw [div_eq_mul_inv, mul_inv]
  ring

/-- For `n ≥ 2`, `a(n) ≤ (Λ(n)/n) / log 2`. -/
private theorem mertensAcoeff_le (n : ℕ) (hn : 2 ≤ n) :
    mertensAcoeff n ≤
      (ArithmeticFunction.vonMangoldt n / (n : ℝ)) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) h2n
  have hinv : (Real.log (n : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ hlogn hlog2).mpr hlog
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  rw [mertensAcoeff_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hinv hΛ

/-- `A(x) ≤ S(x) / log 2` for all `x` (termwise for `n ≥ 2`, trivial below). -/
private theorem mertensA_le_mertensS_div (x : ℝ) :
    mertensA x ≤ mertensS x / Real.log 2 := by
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  unfold mertensA mertensS
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  by_cases hn2 : 2 ≤ n
  · exact mertensAcoeff_le n hn2
  · have ha0 : mertensAcoeff n = 0 := by
      push Not at hn2
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl <;> simp [mertensAcoeff]
    rw [ha0]
    exact div_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)) hlog2

/-- Derivative of `log ∘ log` at `t ≥ 2` is `(t * log t)⁻¹`. -/
private theorem hasDerivAt_log_log (t : ℝ) (ht : 2 ≤ t) :
    HasDerivAt (fun t => Real.log (Real.log t)) ((t * Real.log t)⁻¹) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h := (Real.hasDerivAt_log (ne_of_gt ht0)).log (ne_of_gt hlog)
  rwa [show t⁻¹ / Real.log t = (t * Real.log t)⁻¹ by
    rw [div_eq_mul_inv, mul_inv]] at h

/-- `∫₂ˣ 1/(t log t) = log log x − log log 2`. -/
private theorem integral_inv_mul_log (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (t * Real.log t)⁻¹) =
      Real.log (Real.log x) - Real.log (Real.log 2) := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x,
      HasDerivAt (fun t => Real.log (Real.log t)) ((t * Real.log t)⁻¹) t := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    exact hasDerivAt_log_log t ht.1
  have hint : IntervalIntegrable (fun t => (t * Real.log t)⁻¹)
      MeasureTheory.volume (2 : ℝ) x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦
      ContinuousAt.continuousWithinAt ?_
    rw [Set.mem_uIcc] at ht
    have ht0 : (0 : ℝ) < t := by
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hx]
    have ht1 : t ≠ 0 := ne_of_gt ht0
    have hlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one ht0
      rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hx]
    have htm : t * Real.log t ≠ 0 := mul_ne_zero ht1 hlog
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Fold the explicit von Mangoldt sum into `mertensS`. -/
private theorem mertensS_fold (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
    ArithmeticFunction.vonMangoldt k / (k : ℝ)) = mertensS t :=
  rfl

/-- Integrability of `S(t) / (t (log t)²)` on `[2, x]`. -/
private theorem mertensS_div_integrable (x : ℝ) :
    MeasureTheory.IntegrableOn (fun t => mertensS t / (t * (Real.log t) ^ 2))
      (Set.Icc 2 x) := by
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹)
      (Set.Icc 2 x) := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦
      ContinuousAt.continuousWithinAt ?_
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht1 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one (by linarith)
      linarith
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    have htm : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht1 hlog2
    fun_prop
  have hmul := integrableOn_mul_sum_Icc
    (fun k : ℕ => ArithmeticFunction.vonMangoldt k / (k : ℝ)) (m := 0)
    (show (0 : ℝ) ≤ 2 by norm_num) hg
  have heq : (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹ *
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k / (k : ℝ))) =
      (fun t : ℝ => mertensS t / (t * (Real.log t) ^ 2)) := by
    funext t
    show (t * (Real.log t) ^ 2)⁻¹ *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k / (k : ℝ)) =
        mertensS t / (t * (Real.log t) ^ 2)
    rw [mertensS_fold t, div_eq_mul_inv, mul_comm]
  rw [heq] at hmul
  exact hmul

/-- Interval version of `mertensS_div_integrable`. -/
private theorem mertensS_div_intervalIntegrable (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => mertensS t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume (2 : ℝ) x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  exact mertensS_div_integrable x

/-- Interval integrability of the `log` part. -/
private theorem log_div_intervalIntegrable (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => Real.log t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume (2 : ℝ) x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦
    ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at ht
  have ht0 : (0 : ℝ) < t := by
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hx]
  have ht1 : t ≠ 0 := ne_of_gt ht0
  have hlog : Real.log t ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one ht0
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hx]
  have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
  have htm : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht1 hlog2
  fun_prop

/-- Interval integrability of `R(t) / (t (log t)²)` on `[2, x]`. -/
private theorem mertensR_div_intervalIntegrable (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable
      (fun t => (mertensS t - Real.log t) / (t * (Real.log t) ^ 2))
      MeasureTheory.volume (2 : ℝ) x := by
  have hfun : (fun t : ℝ => (mertensS t - Real.log t) / (t * (Real.log t) ^ 2)) =
      (fun t : ℝ => mertensS t / (t * (Real.log t) ^ 2) -
        Real.log t / (t * (Real.log t) ^ 2)) := by
    funext t
    exact sub_div _ _ _
  rw [hfun]
  exact (mertensS_div_intervalIntegrable x hx).sub (log_div_intervalIntegrable x hx)

/-- `S(x)/log x = 1 + R(x)/log x` for `x ≥ 2`. -/
private theorem mertensS_div_log_eq (x : ℝ) (hx : 2 ≤ x) :
    mertensS x / Real.log x =
      1 + (mertensS x - Real.log x) / Real.log x := by
  have hlogx : Real.log x ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  rw [sub_div, div_self hlogx]
  ring

/-- The `log` part of the split integral equals `(t * log t)⁻¹` pointwise. -/
private theorem log_div_eq_inv_mul_log (t : ℝ) (ht : 2 ≤ t) :
    Real.log t / (t * (Real.log t) ^ 2) = (t * Real.log t)⁻¹ := by
  have ht0 : (t : ℝ) ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have htm : t * Real.log t ≠ 0 := mul_ne_zero ht0 hlog
  have htm2 : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hlog)
  field_simp

/-- Split `∫ S/(t log²)` into `∫ R/(t log²)` plus the FTC term. -/
private theorem mertensS_integral_split (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, mertensS t / (t * (Real.log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, (mertensS t - Real.log t) / (t * (Real.log t) ^ 2)) +
        (Real.log (Real.log x) - Real.log (Real.log 2)) := by
  have hfun : (fun t : ℝ => (mertensS t - Real.log t) / (t * (Real.log t) ^ 2) +
      Real.log t / (t * (Real.log t) ^ 2)) =
      (fun t : ℝ => mertensS t / (t * (Real.log t) ^ 2)) := by
    funext t
    rw [← add_div, sub_add_cancel]
  have hlogint : (∫ t in (2 : ℝ)..x, Real.log t / (t * (Real.log t) ^ 2)) =
      (∫ t in (2 : ℝ)..x, (t * Real.log t)⁻¹) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.mem_uIcc] at ht
    have ht2 : (2 : ℝ) ≤ t := by
      rcases ht with ⟨h1, _⟩ | ⟨h1, h2⟩ <;> linarith [hx]
    exact log_div_eq_inv_mul_log t ht2
  rw [← hfun, intervalIntegral.integral_add
    (mertensR_div_intervalIntegrable x hx) (log_div_intervalIntegrable x hx),
    hlogint, integral_inv_mul_log x hx]

/-- Key identity: `A(x) − log log x` via the remainder `R = S − log`. -/
private theorem mertensA_sub_loglog_eq (x : ℝ) (hx : 2 ≤ x) :
    mertensA x - Real.log (Real.log x) =
      (1 - Real.log (Real.log 2)) + (mertensS x - Real.log x) / Real.log x +
        ∫ t in (2 : ℝ)..x, (mertensS t - Real.log t) / (t * (Real.log t) ^ 2) := by
  rw [mertensA_eq_abel x hx, mertensS_div_log_eq x hx, mertensS_integral_split x hx]
  ring

/-- HasDerivAt for `g(t) = −(log t)⁻¹` with derivative `(t (log t)²)⁻¹`. -/
private theorem hasDerivAt_neg_inv_log (t : ℝ) (ht : 2 ≤ t) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) ((t * (Real.log t) ^ 2)⁻¹) t := by
  have ht0 : (t : ℝ) ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have h := (Real.hasDerivAt_inv_log ht0 (by linarith) (by linarith)).neg
  have heq : -(-t⁻¹ / Real.log t ^ 2) = (t * (Real.log t) ^ 2)⁻¹ := by
    have htm : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hlog)
    field_simp
  rwa [heq] at h

/-- The dominating function `(t (log t)²)⁻¹` is integrable on `Ioi 2`. -/
private theorem integrableOn_inv_mul_log_sq :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹)
      (Set.Ioi 2) := by
  have hderiv : ∀ t ∈ Set.Ici (2 : ℝ),
      HasDerivAt (fun t => -(Real.log t)⁻¹) ((t * (Real.log t) ^ 2)⁻¹) t := by
    intro t ht
    rw [Set.mem_Ici] at ht
    exact hasDerivAt_neg_inv_log t ht
  have hpos : ∀ t ∈ Set.Ioi (2 : ℝ), 0 ≤ (t * (Real.log t) ^ 2)⁻¹ := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    apply inv_nonneg.mpr
    apply mul_nonneg (by linarith)
    exact sq_nonneg _
  have hlim : Filter.Tendsto (fun t : ℝ => -(Real.log t)⁻¹)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (Real.log t)⁻¹)
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop
    simpa using h1.neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim

/-- `R(x)/log x → 0` by squeeze against `±C/log x`. -/
private theorem mertensR_div_log_tendsto_zero (C : ℝ)
    (hC : ∀ t : ℝ, 1 ≤ t → |mertensS t - Real.log t| ≤ C) :
    Filter.Tendsto (fun x => (mertensS x - Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x)
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop
  have hpos : Filter.Tendsto (fun x : ℝ => C / Real.log x)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hlog C
  have hneg : Filter.Tendsto (fun x : ℝ => -C / Real.log x)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop hlog (-C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hpos ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hR := hC x (by linarith : (1 : ℝ) ≤ x)
    rw [abs_le] at hR
    obtain ⟨hlo, hhi⟩ := hR
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    rw [div_le_div_iff_of_pos_right hlogx]
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hR := hC x (by linarith : (1 : ℝ) ≤ x)
    rw [abs_le] at hR
    obtain ⟨hlo, hhi⟩ := hR
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    rw [div_le_div_iff_of_pos_right hlogx]
    linarith

/-- `R(t)/(t (log t)²)` is integrable on `Ioi 2` by domination. -/
private theorem mertensR_div_integrable_Ioi (C : ℝ)
    (hC : ∀ t : ℝ, 1 ≤ t → |mertensS t - Real.log t| ≤ C) :
    MeasureTheory.IntegrableOn
      (fun t => (mertensS t - Real.log t) / (t * (Real.log t) ^ 2))
      (Set.Ioi 2) := by
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    exact le_trans (abs_nonneg _) h1
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (mertensS t - Real.log t) / (t * (Real.log t) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 2)) := by
    apply Measurable.aestronglyMeasurable
    exact (mertensS_measurable.sub Real.measurable_log).div
      (measurable_id.mul (Real.measurable_log.pow_const 2))
  have hdom : MeasureTheory.Integrable
      (fun t : ℝ => C / (t * (Real.log t) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 2)) := by
    have hcm := integrableOn_inv_mul_log_sq.const_mul C
    have heq : (fun t : ℝ => C * (t * (Real.log t) ^ 2)⁻¹) =
        (fun t : ℝ => C / (t * (Real.log t) ^ 2)) := by
      funext t
      rw [div_eq_mul_inv]
    rwa [heq] at hcm
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  rw [Set.mem_Ioi] at ht
  have habs : |mertensS t - Real.log t| ≤ C :=
    abs_le.mpr ⟨(abs_le.mp (hC t (by linarith : (1 : ℝ) ≤ t))).1,
      (abs_le.mp (hC t (by linarith : (1 : ℝ) ≤ t))).2⟩
  have hlog : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) < t * (Real.log t) ^ 2 :=
    mul_pos (by linarith) (pow_pos hlog 2)
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos,
    div_le_div_iff_of_pos_right hpos]
  exact habs

-- Mertens second theorem, prime-power form (limit exists).
private theorem exists_tendsto_mertensA_sub_loglog :
    ∃ c : ℝ, Filter.Tendsto (fun x => mertensA x - Real.log (Real.log x))
      Filter.atTop (nhds c) := by
  obtain ⟨C, hC⟩ := mertens_first_bound
  refine ⟨(1 - Real.log (Real.log 2)) +
    (∫ t in Set.Ioi (2 : ℝ),
      (mertensS t - Real.log t) / (t * (Real.log t) ^ 2)), ?_⟩
  have hRzero := mertensR_div_log_tendsto_zero C (fun t ht => hC t ht)
  have hInt := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 : ℝ)
    (mertensR_div_integrable_Ioi C (fun t ht => hC t ht)) Filter.tendsto_id
  have heq : (fun x => mertensA x - Real.log (Real.log x)) =ᶠ[Filter.atTop]
      (fun x => (1 - Real.log (Real.log 2)) +
        (mertensS x - Real.log x) / Real.log x +
        ∫ t in (2 : ℝ)..x,
          (mertensS t - Real.log t) / (t * (Real.log t) ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    exact mertensA_sub_loglog_eq x hx
  have hconst : Filter.Tendsto (fun _ : ℝ => (1 - Real.log (Real.log 2)))
      Filter.atTop (nhds (1 - Real.log (Real.log 2))) := tendsto_const_nhds
  simp only [id_eq] at hInt
  have hlim := (hconst.add hRzero).add hInt
  rw [add_zero] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

/-- `A(t) ≤ (log t + C) / log 2` for `t ≥ 1`. -/
private theorem gronwall_mertensA_le_log (C : ℝ)
    (hC : ∀ x : ℝ, 1 ≤ x → |mertensS x - Real.log x| ≤ C) (t : ℝ) (ht : 1 ≤ t) :
    mertensA t ≤ (Real.log t + C) / Real.log 2 := by
  have h1 := mertensA_le_mertensS_div t
  have h2 := hC t ht
  rw [abs_le] at h2
  have hS : mertensS t ≤ Real.log t + C := by linarith [h2.2]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc mertensA t ≤ mertensS t / Real.log 2 := h1
    _ ≤ (Real.log t + C) / Real.log 2 := by
        rw [div_le_div_iff_of_pos_right hlog2]
        exact hS

/-- `A(t)` as a sum over `Icc 1 ⌊t⌋₊`. -/
private theorem gronwall_mertensA_eq_sum_Icc1 (t : ℝ) :
    mertensA t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, mertensAcoeff k := by
  unfold mertensA
  refine (Finset.sum_subset
    (Finset.Icc_subset_Icc (Nat.zero_le 1) le_rfl) (fun x hx1 hx2 => ?_)).symm
  rw [Finset.mem_Icc] at hx1 hx2
  have hx0 : x = 0 := by
    by_contra hne
    have h1x : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hne
    exact hx2 ⟨h1x, hx1.2⟩
  rw [hx0]
  simp [mertensAcoeff]

/-- `A` is nonnegative. -/
private theorem gronwall_mertensA_nonneg (x : ℝ) : 0 ≤ mertensA x := by
  unfold mertensA
  exact Finset.sum_nonneg (fun i _ => mertensAcoeff_nonneg i)

/-- Each log-ζ series term equals `a(n) / n^σ`. -/
private theorem gronwall_zeta_term_eq (σ : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ (1 + σ) * Real.log n) =
      mertensAcoeff n / (n : ℝ) ^ σ := by
  rcases eq_or_ne n 0 with rfl | hn0
  · have ha0 : mertensAcoeff 0 = 0 := by simp [mertensAcoeff]
    rw [ha0]
    simp
  rcases eq_or_ne n 1 with rfl | hn1
  · have ha1 : mertensAcoeff 1 = 0 := by simp [mertensAcoeff]
    rw [ha1]
    simp
  · have hn2 : 2 ≤ n := by omega
    have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hn0r : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hn1r : (n : ℝ) ≠ 1 := by exact_mod_cast hn1
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one hnpos hn1r
    have hrpow : (n : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hnpos σ).ne'
    have hsplit : (n : ℝ) ^ (1 + σ) = (n : ℝ) * (n : ℝ) ^ σ := by
      rw [Real.rpow_add hnpos, Real.rpow_one]
    rw [hsplit]
    unfold mertensAcoeff
    field_simp

/-- The ratio `log n / n^{σ/2} → 0` along naturals. -/
private theorem gronwall_log_rpow_ratio_nat (σ : ℝ) (hσ : 0 < σ) :
    Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (σ / 2))
      Filter.atTop (nhds 0) :=
  ((isLittleO_log_rpow_atTop (by linarith : (0 : ℝ) < σ / 2)).comp_tendsto
    tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero

/-- Partial sums of `a` are `O(n^{σ/2})`. -/
private theorem gronwall_partials_isBigO (C : ℝ)
    (hC : ∀ x : ℝ, 1 ≤ x → |mertensS x - Real.log x| ≤ C) (σ : ℝ) (hσ : 0 < σ) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, mertensAcoeff k) =O[Filter.atTop]
      fun n : ℕ => (n : ℝ) ^ (σ / 2) := by
  have hσ2 : (0 : ℝ) < σ / 2 := by linarith
  have hratio := gronwall_log_rpow_ratio_nat σ hσ
  have hlog_ev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (σ / 2) := by
    have h1 : ∀ᶠ n : ℕ in Filter.atTop,
        Real.log (n : ℝ) / (n : ℝ) ^ (σ / 2) ≤ 1 :=
      hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn2
    have hpos : (0 : ℝ) < (n : ℝ) ^ (σ / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
    rw [div_le_iff₀ hpos] at hn1
    rwa [one_mul] at hn1
  have htop : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (σ / 2))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hσ2).comp tendsto_natCast_atTop_atTop
  have hC_ev : ∀ᶠ n : ℕ in Filter.atTop, |C| ≤ (n : ℝ) ^ (σ / 2) :=
    htop.eventually_ge_atTop |C|
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / Real.log 2, ?_⟩
  filter_upwards [hlog_ev, hC_ev, Filter.eventually_ge_atTop 1] with n hn1 hn2 hn3
  have hA : mertensA (n : ℝ) ≤ (Real.log (n : ℝ) + C) / Real.log 2 :=
    gronwall_mertensA_le_log C hC (n : ℝ) (by exact_mod_cast hn3)
  have hAsum : (∑ k ∈ Finset.Icc 1 n, mertensAcoeff k) = mertensA (n : ℝ) := by
    rw [gronwall_mertensA_eq_sum_Icc1, Nat.floor_natCast]
  rw [hAsum]
  have hA0 : (0 : ℝ) ≤ mertensA (n : ℝ) := gronwall_mertensA_nonneg _
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (σ / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA0, abs_of_nonneg hnn]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfin : mertensA (n : ℝ) ≤ (2 / Real.log 2) * (n : ℝ) ^ (σ / 2) := by
    have h1 : Real.log (n : ℝ) + C ≤ 2 * (n : ℝ) ^ (σ / 2) := by
      have hC' : C ≤ |C| := le_abs_self C
      linarith
    calc mertensA (n : ℝ) ≤ (Real.log (n : ℝ) + C) / Real.log 2 := hA
      _ = (1 / Real.log 2) * (Real.log (n : ℝ) + C) := by ring
      _ ≤ (1 / Real.log 2) * (2 * (n : ℝ) ^ (σ / 2)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg zero_le_one hlog2.le)
      _ = (2 / Real.log 2) * (n : ℝ) ^ (σ / 2) := by ring
  exact hfin

/-- The real ratio `log t / t^{σ/2} → 0`. -/
private theorem gronwall_log_rpow_ratio (σ : ℝ) (hσ : 0 < σ) :
    Filter.Tendsto (fun t : ℝ => Real.log t / t ^ (σ / 2))
      Filter.atTop (nhds 0) :=
  (isLittleO_log_rpow_atTop (by linarith : (0 : ℝ) < σ / 2)).tendsto_div_nhds_zero

/-- Real integrability of `A(t) * t^{-σ-1}` on `Ioi 1`. -/
private theorem gronwall_integrand_integrable (C : ℝ)
    (hC : ∀ x : ℝ, 1 ≤ x → |mertensS x - Real.log x| ≤ C) (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun t => mertensA t * t ^ (-σ - 1))
      (Set.Ioi 1) := by
  have hσ2 : (0 : ℝ) < σ / 2 := by linarith
  have hratio := gronwall_log_rpow_ratio σ hσ
  have hlogR : ∀ᶠ t in Filter.atTop, Real.log t ≤ t ^ (σ / 2) := by
    have h1 : ∀ᶠ t in Filter.atTop, Real.log t / t ^ (σ / 2) ≤ 1 :=
      hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h1, Filter.eventually_ge_atTop 1] with t ht1 ht2
    have hpos : (0 : ℝ) < t ^ (σ / 2) :=
      Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < t) _
    rw [div_le_iff₀ hpos] at ht1
    rwa [one_mul] at ht1
  have hCR : ∀ᶠ t in Filter.atTop, |C| ≤ t ^ (σ / 2) :=
    (tendsto_rpow_atTop hσ2).eventually_ge_atTop |C|
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hlogR.and (hCR.and (Filter.eventually_ge_atTop 1)))
  have hT01 : (1 : ℝ) ≤ max T 1 := le_max_right _ _
  have hBlo : ∀ t : ℝ, max T 1 ≤ t →
      Real.log t ≤ t ^ (σ / 2) ∧ |C| ≤ t ^ (σ / 2) := by
    intro t ht
    have h := hT t (le_trans (le_max_left T 1) ht)
    exact ⟨h.1, h.2.1⟩
  have hIcc : MeasureTheory.IntegrableOn (fun t => mertensA t * t ^ (-σ - 1))
      (Set.Ioc 1 (max T 1)) := by
    have gcont : ContinuousOn (fun t : ℝ => t ^ (-σ - 1))
        (Set.Icc 1 (max T 1)) := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t)
      exact (Real.continuousAt_rpow_const t (-σ - 1)
        (Or.inl ht0)).continuousWithinAt
    have hg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-σ - 1))
        (Set.Icc 1 (max T 1)) :=
      gcont.integrableOn_Icc
    have hmul := integrableOn_mul_sum_Icc (fun k : ℕ => mertensAcoeff k)
      (m := 1) (show (0 : ℝ) ≤ 1 by norm_num) hg
    have hcongr : MeasureTheory.IntegrableOn
        (fun t => mertensA t * t ^ (-σ - 1)) (Set.Icc 1 (max T 1)) := by
      refine hmul.congr_fun ?_ measurableSet_Icc
      intro t ht
      change t ^ (-σ - 1) * (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, mertensAcoeff k)
        = mertensA t * t ^ (-σ - 1)
      have hA : mertensA t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, mertensAcoeff k :=
        gronwall_mertensA_eq_sum_Icc1 t
      rw [hA, mul_comm]
    exact hcongr.mono_set Set.Ioc_subset_Icc_self
  have hIoi : MeasureTheory.IntegrableOn (fun t => mertensA t * t ^ (-σ - 1))
      (Set.Ioi (max T 1)) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t => (2 / Real.log 2) * t ^ (-1 - σ / 2)) (Set.Ioi (max T 1)) :=
      MeasureTheory.Integrable.const_mul
        (integrableOn_Ioi_rpow_of_lt (show -1 - σ / 2 < -1 by linarith)
          (by linarith [hT01] : (0 : ℝ) < max T 1)) (2 / Real.log 2)
    have gcont' : ContinuousOn (fun t : ℝ => t ^ (-σ - 1))
        (Set.Ioi (max T 1)) := by
      intro t ht
      rw [Set.mem_Ioi] at ht
      have ht0 : t ≠ 0 := ne_of_gt (by linarith [hT01, ht] : (0 : ℝ) < t)
      exact (Real.continuousAt_rpow_const t (-σ - 1)
        (Or.inl ht0)).continuousWithinAt
    refine MeasureTheory.Integrable.mono' hdom
      (mertensA_measurable.aestronglyMeasurable.mul
        (gcont'.aestronglyMeasurable measurableSet_Ioi)) ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    rw [Set.mem_Ioi] at ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hT01 ht.le
    have ht0 : (0 : ℝ) < t := by linarith
    have hA := gronwall_mertensA_le_log C hC t ht1
    have hb := hBlo t ht.le
    have hA0 : (0 : ℝ) ≤ mertensA t := gronwall_mertensA_nonneg t
    have hpow_nn : (0 : ℝ) ≤ t ^ (-σ - 1) :=
      Real.rpow_nonneg ht0.le _
    have e0 : ‖mertensA t * t ^ (-σ - 1)‖ = mertensA t * t ^ (-σ - 1) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA0 hpow_nn)]
    rw [e0]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : mertensA t * t ^ (-σ - 1)
        ≤ ((2 * t ^ (σ / 2)) / Real.log 2) * t ^ (-σ - 1) := by
      apply mul_le_mul_of_nonneg_right _ hpow_nn
      calc mertensA t ≤ (Real.log t + C) / Real.log 2 :=
            gronwall_mertensA_le_log C hC t ht1
        _ ≤ (2 * t ^ (σ / 2)) / Real.log 2 := by
            rw [div_le_div_iff_of_pos_right hlog2]
            have hC' : C ≤ |C| := le_abs_self C
            linarith [hb.1, hb.2]
    have h2 : ((2 * t ^ (σ / 2)) / Real.log 2) * t ^ (-σ - 1)
        = (2 / Real.log 2) * t ^ (-1 - σ / 2) := by
      have hrw : t ^ (σ / 2) * t ^ (-σ - 1) = t ^ (-1 - σ / 2) := by
        rw [← Real.rpow_add ht0]
        congr 1
        ring
      calc ((2 * t ^ (σ / 2)) / Real.log 2) * t ^ (-σ - 1)
          = (2 / Real.log 2) * (t ^ (σ / 2) * t ^ (-σ - 1)) := by ring
        _ = (2 / Real.log 2) * t ^ (-1 - σ / 2) := by rw [hrw]
    calc mertensA t * t ^ (-σ - 1)
        ≤ ((2 * t ^ (σ / 2)) / Real.log 2) * t ^ (-σ - 1) := h1
      _ = (2 / Real.log 2) * t ^ (-1 - σ / 2) := h2
  have hunion : Set.Ioc (1 : ℝ) (max T 1) ∪ Set.Ioi (max T 1) = Set.Ioi 1 := by
    ext v
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h0, -⟩ | hT'')
      · exact h0
      · exact lt_of_le_of_lt hT01 hT''
    · intro h0
      by_cases hle : v ≤ max T 1
      · exact Or.inl ⟨h0, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
  rw [← hunion]
  exact hIcc.union hIoi

/-- The complex `L`-series of `a` equals `log ζ(1+σ)`. -/
private theorem gronwall_LSeries_eq_log_zeta (σ : ℝ) (hσ : 0 < σ) :
    LSeries (fun n => ((mertensAcoeff n : ℝ) : ℂ)) ((σ : ℝ) : ℂ) =
      ((Real.log (riemannZeta ((1 + σ : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  have hs : (1 : ℝ) < 1 + σ := by linarith
  have hzeta := log_riemannZeta_eq hs
  have ha0 : mertensAcoeff 0 = 0 := by simp [mertensAcoeff]
  have hf0 : (fun n => ((mertensAcoeff n : ℝ) : ℂ)) 0 = 0 := by simp [ha0]
  have htermC : ∀ n : ℕ, ((mertensAcoeff n : ℝ) : ℂ) / ((n : ℂ) ^ ((σ : ℝ) : ℂ))
      = ((mertensAcoeff n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n) σ,
      Complex.ofReal_natCast]
  have step1 : LSeries (fun n => ((mertensAcoeff n : ℝ) : ℂ)) ((σ : ℝ) : ℂ)
      = ∑' n, ((mertensAcoeff n : ℝ) : ℂ) / ((n : ℂ) ^ ((σ : ℝ) : ℂ)) :=
    LSeries_def₀ hf0 _
  rw [step1, tsum_congr htermC, ← Complex.ofReal_tsum]
  congr 1
  rw [hzeta]
  exact (tsum_congr (gronwall_zeta_term_eq σ)).symm

/-- The `L`-series of `a` as a Laplace-type integral. -/
private theorem gronwall_LSeries_integral (σ : ℝ) (hσ : 0 < σ) (C : ℝ)
    (hC : ∀ x : ℝ, 1 ≤ x → |mertensS x - Real.log x| ≤ C) :
    LSeries (fun n => ((mertensAcoeff n : ℝ) : ℂ)) ((σ : ℝ) : ℂ) =
      ((σ : ℝ) : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((mertensAcoeff k : ℝ) : ℂ))
          * (t : ℂ) ^ (-(((σ : ℝ) : ℂ) + 1))) := by
  have hO := gronwall_partials_isBigO C hC σ hσ
  exact LSeries_eq_mul_integral_of_nonneg mertensAcoeff
    (show (0 : ℝ) ≤ σ / 2 by linarith)
    (show σ / 2 < (((σ : ℝ) : ℂ)).re by simpa using half_lt_self hσ) hO
    mertensAcoeff_nonneg

/-- Pullback identity `e^v * (A(e^v) * (e^v)^{-σ-1}) = A(e^v) * e^{-σv}`. -/
private theorem gronwall_exp_pullback_eq (σ v : ℝ) :
    Real.exp v • (mertensA (Real.exp v) * (Real.exp v) ^ (-σ - 1))
      = mertensA (Real.exp v) * Real.exp (-σ * v) := by
  have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
  have hrw : (Real.exp v) ^ (-σ - 1) = Real.exp (v * (-σ - 1)) := by
    rw [Real.rpow_def_of_pos hev, Real.log_exp]
  have key : Real.exp v * (Real.exp v) ^ (-σ - 1) = Real.exp (-σ * v) := by
    rw [hrw, ← Real.exp_add]
    congr 1
    ring
  rw [smul_eq_mul,
    show Real.exp v * (mertensA (Real.exp v) * (Real.exp v) ^ (-σ - 1))
      = mertensA (Real.exp v) * (Real.exp v * (Real.exp v) ^ (-σ - 1)) by ring,
    key]

/-- Integrability transfers to the pullback on `Ioi 0`. -/
private theorem gronwall_pullback_integrable (σ : ℝ)
    (hInt1 : MeasureTheory.IntegrableOn
      (fun y => mertensA y * y ^ (-σ - 1)) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun v => mertensA (Real.exp v) * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)) := by
  have hbase := MeasureTheory.integrableOn_comp_exp_Ioi
    (fun y : ℝ => mertensA y * y ^ (-σ - 1)) (0 : ℝ)
  rw [Real.exp_zero] at hbase
  refine (hbase.mpr hInt1).congr_fun ?_ measurableSet_Ioi
  intro v hv
  exact gronwall_exp_pullback_eq σ v

private theorem log_zeta_eq_laplace_mertensA (σ : ℝ) (hσ : 0 < σ) :
    Real.log (riemannZeta ((1 + σ : ℝ) : ℂ)).re =
      σ * (∫ v in Set.Ioi (0 : ℝ), mertensA (Real.exp v) * Real.exp (-σ * v)) ∧
    MeasureTheory.IntegrableOn (fun v => mertensA (Real.exp v) * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := mertens_first_bound
  have hInt1 := gronwall_integrand_integrable C hC σ hσ
  have hLC := gronwall_LSeries_eq_log_zeta σ hσ
  have hLI := gronwall_LSeries_integral σ hσ C hC
  have hInt_eq : (∫ t in Set.Ioi (1 : ℝ),
        ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((mertensAcoeff k : ℝ) : ℂ))
          * (t : ℂ) ^ (-(((σ : ℝ) : ℂ) + 1))))
      = (((∫ t in Set.Ioi (1 : ℝ), mertensA t * t ^ (-σ - 1) : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((mertensAcoeff k : ℝ) : ℂ))
        * (t : ℂ) ^ (-(((σ : ℝ) : ℂ) + 1)))
      = (((mertensA t * t ^ (-σ - 1) : ℝ)) : ℂ)
    rw [Set.mem_Ioi] at ht
    have ht0 : (0 : ℝ) ≤ t := by linarith [ht]
    have hsum : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((mertensAcoeff k : ℝ) : ℂ))
        = ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, mertensAcoeff k : ℝ) : ℂ) :=
      (Complex.ofReal_sum _ _).symm
    have hexp : (-(((σ : ℝ) : ℂ) + 1)) = (((-σ - 1 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hsum, hexp, ← Complex.ofReal_cpow ht0, ← Complex.ofReal_mul,
      gronwall_mertensA_eq_sum_Icc1]
  have hReal : Real.log (riemannZeta ((1 + σ : ℝ) : ℂ)).re
      = σ * (∫ t in Set.Ioi (1 : ℝ), mertensA t * t ^ (-σ - 1)) := by
    have hCD := hLC.symm.trans hLI
    rw [hInt_eq, ← Complex.ofReal_mul] at hCD
    exact Complex.ofReal_injective hCD
  have hexp_change : (∫ t in Set.Ioi (1 : ℝ), mertensA t * t ^ (-σ - 1))
      = ∫ v in Set.Ioi (0 : ℝ), mertensA (Real.exp v) * Real.exp (-σ * v) := by
    have hbase := MeasureTheory.integral_comp_exp_Ioi
      (fun y : ℝ => mertensA y * y ^ (-σ - 1)) (0 : ℝ)
    rw [Real.exp_zero] at hbase
    rw [← hbase]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact gronwall_exp_pullback_eq σ v
  refine ⟨?_, gronwall_pullback_integrable σ hInt1⟩
  rw [hReal, hexp_change]

/-- The exponential `exp (-σ * ·)` is `≤ 1` on `[0, ∞)` for `σ > 0`. -/
private theorem gronwall_exp_le_one (σ v : ℝ) (hσ : 0 < σ) (hv : 0 ≤ v) :
    Real.exp (-σ * v) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) hv

/-- `‖exp x‖ = exp x`. -/
private theorem gronwall_norm_exp (x : ℝ) : ‖Real.exp x‖ = Real.exp x := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Measurability of the Laplace integrand. -/
private theorem gronwall_laplace_measurable (h : ℝ → ℝ) (σ : ℝ)
    (hmeas : Measurable h) :
    Measurable (fun v => h v * Real.exp (-σ * v)) :=
  Measurable.mul hmeas
    (Real.measurable_exp.comp (Measurable.mul measurable_const measurable_id'))

/-- The split `Ioc 0 T' ∪ Ioi T' = Ioi 0` for `0 ≤ T'`. -/
private theorem gronwall_Ioc_union_Ioi (T' : ℝ) (hT' : 0 ≤ T') :
    Set.Ioc (0 : ℝ) T' ∪ Set.Ioi T' = Set.Ioi 0 := by
  ext v
  simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro (⟨h0, -⟩ | hT'')
    · exact h0
    · exact lt_of_le_of_lt hT' hT''
  · intro h0
    by_cases hle : v ≤ T'
    · exact Or.inl ⟨h0, hle⟩
    · exact Or.inr (lt_of_not_ge hle)

/-- `‖h v - c‖ → 0`. -/
private theorem gronwall_tendsto_norm_sub (h : ℝ → ℝ) (c : ℝ)
    (hlim : Filter.Tendsto h Filter.atTop (nhds c)) :
    Filter.Tendsto (fun v => ‖h v - c‖) Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (fun _ : ℝ => c) Filter.atTop (nhds c) :=
    tendsto_const_nhds
  have hsub : Filter.Tendsto (fun v => h v - c) Filter.atTop (nhds (c - c)) :=
    hlim.sub hc
  rw [sub_self] at hsub
  simpa using hsub.norm

/-- The difference `h - c` is eventually bounded by `1`. -/
private theorem gronwall_laplace_eventually_bound (h : ℝ → ℝ) (c : ℝ)
    (hlim : Filter.Tendsto h Filter.atTop (nhds c)) :
    ∃ T : ℝ, ∀ v : ℝ, T ≤ v → ‖h v - c‖ ≤ 1 := by
  have hle : ∀ᶠ v in Filter.atTop, ‖h v - c‖ ≤ 1 :=
    (gronwall_tendsto_norm_sub h c hlim).eventually_le_const
      (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at hle
  obtain ⟨T, hT⟩ := hle
  exact ⟨T, fun v hv => hT v hv⟩

/-- Integrability of the Laplace integrand on the compact piece `Ioc 0 T'`. -/
private theorem gronwall_laplace_integrable_Ioc (h : ℝ → ℝ) (σ T' : ℝ)
    (hσ : 0 < σ) (hmeas : Measurable h)
    (hint : MeasureTheory.IntegrableOn h (Set.Ioc 0 T')) :
    MeasureTheory.IntegrableOn (fun v => h v * Real.exp (-σ * v))
      (Set.Ioc 0 T') := by
  refine MeasureTheory.Integrable.mono' hint.norm
    (gronwall_laplace_measurable h σ hmeas).aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with v hv
  rw [Set.mem_Ioc] at hv
  have hexp : Real.exp (-σ * v) ≤ 1 := gronwall_exp_le_one σ v hσ hv.1.le
  have e1 : ‖h v * Real.exp (-σ * v)‖ = ‖h v‖ * Real.exp (-σ * v) := by
    rw [norm_mul, gronwall_norm_exp]
  calc ‖h v * Real.exp (-σ * v)‖ = ‖h v‖ * Real.exp (-σ * v) := e1
    _ ≤ ‖h v‖ * 1 := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = ‖h v‖ := mul_one _

/-- Integrability of the Laplace integrand on `Ioi T'`, given a bound there. -/
private theorem gronwall_laplace_integrable_Ioi (h : ℝ → ℝ) (c σ T' : ℝ)
    (hσ : 0 < σ) (hmeas : Measurable h)
    (hB : ∀ v : ℝ, T' ≤ v → ‖h v‖ ≤ |c| + 1) :
    MeasureTheory.IntegrableOn (fun v => h v * Real.exp (-σ * v))
      (Set.Ioi T') := by
  have hexp : MeasureTheory.IntegrableOn (fun v => Real.exp (-σ * v))
      (Set.Ioi T') :=
    integrableOn_exp_mul_Ioi (show -σ < 0 by linarith) T'
  have hdom : MeasureTheory.Integrable
      (fun v => (|c| + 1) * Real.exp (-σ * v))
      (MeasureTheory.volume.restrict (Set.Ioi T')) :=
    MeasureTheory.Integrable.const_mul hexp (|c| + 1)
  refine MeasureTheory.Integrable.mono' hdom
    (gronwall_laplace_measurable h σ hmeas).aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with v hv
  rw [Set.mem_Ioi] at hv
  have e1 : ‖h v * Real.exp (-σ * v)‖ = ‖h v‖ * Real.exp (-σ * v) := by
    rw [norm_mul, gronwall_norm_exp]
  calc ‖h v * Real.exp (-σ * v)‖ = ‖h v‖ * Real.exp (-σ * v) := e1
    _ ≤ (|c| + 1) * Real.exp (-σ * v) :=
        mul_le_mul_of_nonneg_right (hB v hv.le) (Real.exp_pos _).le

/-- Part (i) of the Abelian lemma: integrability on `Ioi 0`. -/
private theorem gronwall_laplace_integrable (h : ℝ → ℝ) (c : ℝ)
    (hmeas : Measurable h)
    (hint : ∀ T : ℝ, MeasureTheory.IntegrableOn h (Set.Ioc 0 T))
    (hlim : Filter.Tendsto h Filter.atTop (nhds c)) :
    ∀ σ : ℝ, 0 < σ → MeasureTheory.IntegrableOn
      (fun v => h v * Real.exp (-σ * v)) (Set.Ioi (0 : ℝ)) := by
  intro σ hσ
  obtain ⟨T, hT⟩ := gronwall_laplace_eventually_bound h c hlim
  have hT' : (0 : ℝ) ≤ max T 0 := le_max_right _ _
  have hIoc := gronwall_laplace_integrable_Ioc h σ (max T 0) hσ hmeas
    (hint (max T 0))
  have hIoi := gronwall_laplace_integrable_Ioi h c σ (max T 0) hσ hmeas
    (fun v hv => by
      have h2 := hT v (le_trans (le_max_left T 0) hv)
      have h3 := norm_sub_norm_le (h v) c
      have h4 : ‖c‖ = |c| := Real.norm_eq_abs c
      linarith)
  rw [← gronwall_Ioc_union_Ioi (max T 0) hT']
  exact hIoc.union hIoi

/-- `σ * ∫₀^∞ e^{-σv} dv = 1` for `σ > 0`. -/
private theorem gronwall_exp_laplace_one (σ : ℝ) (hσ : 0 < σ) :
    σ * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) = 1 := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have h := integral_exp_mul_Ioi (show -σ < 0 by linarith) (0 : ℝ)
  rw [h, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  exact mul_inv_cancel₀ hσ0

/-- Subtracting the limit passes inside the Laplace integral. -/
private theorem gronwall_laplace_sub (h : ℝ → ℝ) (c σ : ℝ) (hσ : 0 < σ)
    (he : MeasureTheory.IntegrableOn (fun v => h v * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)))
    (hce : MeasureTheory.IntegrableOn (fun v => c * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ))) :
    σ * (∫ v in Set.Ioi (0 : ℝ), h v * Real.exp (-σ * v)) - c =
      σ * (∫ v in Set.Ioi (0 : ℝ), (h v - c) * Real.exp (-σ * v)) := by
  have econgr : (∫ v in Set.Ioi (0 : ℝ), (h v - c) * Real.exp (-σ * v)) =
      (∫ v in Set.Ioi (0 : ℝ),
        (h v * Real.exp (-σ * v) - c * Real.exp (-σ * v))) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => by ring)
  have hc : σ * (c * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v))) = c := by
    rw [mul_left_comm, gronwall_exp_laplace_one σ hσ, mul_one]
  rw [econgr, MeasureTheory.integral_sub he hce,
    MeasureTheory.integral_const_mul, mul_sub, hc]

private theorem tendsto_mul_laplace_of_tendsto (h : ℝ → ℝ) (c : ℝ)
    (hmeas : Measurable h)
    (hint : ∀ T : ℝ, MeasureTheory.IntegrableOn h (Set.Ioc 0 T))
    (hlim : Filter.Tendsto h Filter.atTop (nhds c)) :
    (∀ σ : ℝ, 0 < σ → MeasureTheory.IntegrableOn
      (fun v => h v * Real.exp (-σ * v)) (Set.Ioi (0 : ℝ))) ∧
    Filter.Tendsto (fun σ => σ * (∫ v in Set.Ioi (0 : ℝ), h v * Real.exp (-σ * v)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) := by
  refine ⟨gronwall_laplace_integrable h c hmeas hint hlim, ?_⟩
  refine Metric.tendsto_nhdsWithin_nhds.mpr (fun ε hε => ?_)
  have hle : ∀ᶠ v in Filter.atTop, ‖h v - c‖ ≤ ε / 2 :=
    (gronwall_tendsto_norm_sub h c hlim).eventually_le_const (half_pos hε)
  rw [Filter.eventually_atTop] at hle
  obtain ⟨Tε, hTε⟩ := hle
  have hT'0 : (0 : ℝ) ≤ max Tε 0 := le_max_right _ _
  have hK0' : (0 : ℝ) ≤ ∫ v in Set.Ioc (0 : ℝ) (max Tε 0), (‖h v‖ + |c|) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      (fun v _ => add_nonneg (norm_nonneg _) (abs_nonneg _))
  set K : ℝ := ∫ v in Set.Ioc (0 : ℝ) (max Tε 0), (‖h v‖ + |c|) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; exact hK0'
  have hKp1 : (0 : ℝ) < K + 1 := by linarith [hK0]
  have hconst : MeasureTheory.IntegrableOn (fun _ => |c|)
      (Set.Ioc (0 : ℝ) (max Tε 0)) :=
    ((continuous_const.continuousOn).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hdomK : MeasureTheory.IntegrableOn (fun v => ‖h v‖ + |c|)
      (Set.Ioc (0 : ℝ) (max Tε 0)) :=
    (hint (max Tε 0)).norm.add hconst
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) (max Tε 0)) (Set.Ioi (max Tε 0)) := by
    rw [Set.disjoint_left]
    intro v hv1 hv2
    rw [Set.mem_Ioc] at hv1
    rw [Set.mem_Ioi] at hv2
    linarith
  refine ⟨(ε / 2) / (K + 1), div_pos (half_pos hε) (by linarith [hK0]),
    fun σ hmem hdist => ?_⟩
  have hσ0 : (0 : ℝ) < σ := Set.mem_Ioi.mp hmem
  have hσδ : σ < (ε / 2) / (K + 1) := by
    have hd := hdist
    rw [Real.dist_eq, sub_zero, abs_of_pos hσ0] at hd
    exact hd
  have he := (gronwall_laplace_integrable h c hmeas hint hlim) σ hσ0
  have hce : MeasureTheory.IntegrableOn (fun v => c * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Integrable.const_mul
      (integrableOn_exp_mul_Ioi (show -σ < 0 by linarith) 0) c
  have hsub : MeasureTheory.IntegrableOn
      (fun v => h v * Real.exp (-σ * v) - c * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)) :=
    he.sub hce
  have h_hce : MeasureTheory.IntegrableOn
      (fun v => (h v - c) * Real.exp (-σ * v)) (Set.Ioi (0 : ℝ)) :=
    hsub.congr (Filter.Eventually.of_forall (fun v => by ring))
  have h_Ioc_hce : MeasureTheory.IntegrableOn
      (fun v => (h v - c) * Real.exp (-σ * v))
      (Set.Ioc (0 : ℝ) (max Tε 0)) :=
    h_hce.mono_set (fun v hv => (Set.mem_Ioc.mp hv).1)
  have h_Ioi_hce : MeasureTheory.IntegrableOn
      (fun v => (h v - c) * Real.exp (-σ * v)) (Set.Ioi (max Tε 0)) :=
    h_hce.mono_set (fun v hv => lt_of_le_of_lt hT'0 (Set.mem_Ioi.mp hv))
  have hexp : σ * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) = 1 :=
    gronwall_exp_laplace_one σ hσ0
  have hFeq : (fun σ => σ * (∫ v in Set.Ioi (0 : ℝ),
      h v * Real.exp (-σ * v))) σ - c =
      σ * (∫ v in Set.Ioi (0 : ℝ), (h v - c) * Real.exp (-σ * v)) :=
    gronwall_laplace_sub h c σ hσ0 he hce
  have hsplit : (∫ v in Set.Ioi (0 : ℝ), (h v - c) * Real.exp (-σ * v)) =
      (∫ v in Set.Ioc (0 : ℝ) (max Tε 0), (h v - c) * Real.exp (-σ * v)) +
      (∫ v in Set.Ioi (max Tε 0), (h v - c) * Real.exp (-σ * v)) := by
    have h := MeasureTheory.setIntegral_union
      (s := Set.Ioc (0 : ℝ) (max Tε 0)) (t := Set.Ioi (max Tε 0))
      hdisj measurableSet_Ioi h_Ioc_hce h_Ioi_hce
    rwa [gronwall_Ioc_union_Ioi (max Tε 0) hT'0] at h
  have hIoc_est : ‖∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
      (h v - c) * Real.exp (-σ * v)‖ ≤ K := by
    have h1 : ‖∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
        (h v - c) * Real.exp (-σ * v)‖ ≤
        ∫ v in Set.Ioc (0 : ℝ) (max Tε 0), ‖(h v - c) * Real.exp (-σ * v)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h2 : (∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
        ‖(h v - c) * Real.exp (-σ * v)‖) ≤
        ∫ v in Set.Ioc (0 : ℝ) (max Tε 0), (‖h v‖ + |c|) := by
      apply MeasureTheory.setIntegral_mono_on h_Ioc_hce.norm hdomK
        measurableSet_Ioc
      intro v hv
      have e1 : ‖(h v - c) * Real.exp (-σ * v)‖
          = ‖h v - c‖ * Real.exp (-σ * v) := by
        rw [norm_mul, gronwall_norm_exp]
      rw [Set.mem_Ioc] at hv
      rw [e1]
      calc ‖h v - c‖ * Real.exp (-σ * v)
          ≤ (‖h v‖ + |c|) * Real.exp (-σ * v) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            calc ‖h v - c‖ ≤ ‖h v‖ + ‖c‖ := norm_sub_le _ _
              _ = ‖h v‖ + |c| := by rw [Real.norm_eq_abs c]
        _ ≤ ‖h v‖ + |c| := by
            have hexp : Real.exp (-σ * v) ≤ 1 :=
              gronwall_exp_le_one σ v hσ0 hv.1.le
            have hnn : (0 : ℝ) ≤ ‖h v‖ + |c| :=
              add_nonneg (norm_nonneg _) (abs_nonneg _)
            calc (‖h v‖ + |c|) * Real.exp (-σ * v)
                ≤ (‖h v‖ + |c|) * 1 :=
                mul_le_mul_of_nonneg_left hexp hnn
              _ = ‖h v‖ + |c| := mul_one _
    have h2' : (∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
        ‖(h v - c) * Real.exp (-σ * v)‖) ≤ K := by
      rw [hKdef]
      exact h2
    exact h1.trans h2'
  have hIoi_est : ‖∫ v in Set.Ioi (max Tε 0),
      (h v - c) * Real.exp (-σ * v)‖ ≤
      (ε / 2) * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) := by
    have h1 : ‖∫ v in Set.Ioi (max Tε 0),
        (h v - c) * Real.exp (-σ * v)‖ ≤
        ∫ v in Set.Ioi (max Tε 0), ‖(h v - c) * Real.exp (-σ * v)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hce_Ioi : MeasureTheory.IntegrableOn
        (fun v => (ε / 2) * Real.exp (-σ * v)) (Set.Ioi (max Tε 0)) :=
      MeasureTheory.Integrable.const_mul
        (integrableOn_exp_mul_Ioi (show -σ < 0 by linarith) (max Tε 0)) (ε / 2)
    have h2 : (∫ v in Set.Ioi (max Tε 0),
        ‖(h v - c) * Real.exp (-σ * v)‖) ≤
        ∫ v in Set.Ioi (max Tε 0), (ε / 2) * Real.exp (-σ * v) := by
      apply MeasureTheory.setIntegral_mono_on h_Ioi_hce.norm hce_Ioi
        measurableSet_Ioi
      intro v hv
      have e1 : ‖(h v - c) * Real.exp (-σ * v)‖
          = ‖h v - c‖ * Real.exp (-σ * v) := by
        rw [norm_mul, gronwall_norm_exp]
      rw [Set.mem_Ioi] at hv
      rw [e1]
      exact mul_le_mul_of_nonneg_right
        (hTε v (le_trans (le_max_left Tε 0) hv.le)) (Real.exp_pos _).le
    have h3 : (∫ v in Set.Ioi (max Tε 0), (ε / 2) * Real.exp (-σ * v))
        = (ε / 2) * (∫ v in Set.Ioi (max Tε 0), Real.exp (-σ * v)) := by
      rw [MeasureTheory.integral_const_mul]
    have he_Ioc : MeasureTheory.IntegrableOn (fun v => Real.exp (-σ * v))
        (Set.Ioc (0 : ℝ) (max Tε 0)) :=
      (integrableOn_exp_mul_Ioi (show -σ < 0 by linarith) 0).mono_set
        (fun v hv => (Set.mem_Ioc.mp hv).1)
    have he_Ioi : MeasureTheory.IntegrableOn (fun v => Real.exp (-σ * v))
        (Set.Ioi (max Tε 0)) :=
      integrableOn_exp_mul_Ioi (show -σ < 0 by linarith) (max Tε 0)
    have hsplit_e : (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) =
        (∫ v in Set.Ioc (0 : ℝ) (max Tε 0), Real.exp (-σ * v)) +
        (∫ v in Set.Ioi (max Tε 0), Real.exp (-σ * v)) := by
      have h := MeasureTheory.setIntegral_union
        (s := Set.Ioc (0 : ℝ) (max Tε 0)) (t := Set.Ioi (max Tε 0))
        hdisj measurableSet_Ioi he_Ioc he_Ioi
      rwa [gronwall_Ioc_union_Ioi (max Tε 0) hT'0] at h
    have hnn_e : (0 : ℝ) ≤
        ∫ v in Set.Ioc (0 : ℝ) (max Tε 0), Real.exp (-σ * v) :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioc
        (fun v _ => (Real.exp_pos _).le)
    have hleE : (∫ v in Set.Ioi (max Tε 0), Real.exp (-σ * v)) ≤
        (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) := by
      linarith [hsplit_e, hnn_e]
    calc ‖∫ v in Set.Ioi (max Tε 0), (h v - c) * Real.exp (-σ * v)‖
        ≤ ∫ v in Set.Ioi (max Tε 0), ‖(h v - c) * Real.exp (-σ * v)‖ := h1
      _ ≤ ∫ v in Set.Ioi (max Tε 0), (ε / 2) * Real.exp (-σ * v) := h2
      _ = (ε / 2) * (∫ v in Set.Ioi (max Tε 0), Real.exp (-σ * v)) := h3
      _ ≤ (ε / 2) * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) :=
          mul_le_mul_of_nonneg_left hleE (le_of_lt (half_pos hε))
  have hKlt : σ * K < ε / 2 := by
    have h1 : σ * K ≤ σ * (K + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hK0]) hσ0.le
    have h2 : σ * (K + 1) < ((ε / 2) / (K + 1)) * (K + 1) :=
      mul_lt_mul_of_pos_right hσδ hKp1
    have h3 : ((ε / 2) / (K + 1)) * (K + 1) = ε / 2 :=
      div_mul_cancel₀ _ (ne_of_gt hKp1)
    linarith
  have hE2 : σ * ((ε / 2) * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)))
      = ε / 2 := by
    rw [← mul_assoc, mul_comm σ (ε / 2), mul_assoc, hexp, mul_one]
  have hIoc_σ : ‖σ * (∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
      (h v - c) * Real.exp (-σ * v))‖ < ε / 2 := by
    have eσ : ‖σ * (∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
        (h v - c) * Real.exp (-σ * v))‖
        = σ * ‖∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
          (h v - c) * Real.exp (-σ * v)‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hσ0]
    rw [eσ]
    calc σ * ‖∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
        (h v - c) * Real.exp (-σ * v)‖ ≤ σ * K :=
          mul_le_mul_of_nonneg_left hIoc_est hσ0.le
      _ < ε / 2 := hKlt
  have hIoi_σ : ‖σ * (∫ v in Set.Ioi (max Tε 0),
      (h v - c) * Real.exp (-σ * v))‖ ≤ ε / 2 := by
    have eσ : ‖σ * (∫ v in Set.Ioi (max Tε 0),
        (h v - c) * Real.exp (-σ * v))‖
        = σ * ‖∫ v in Set.Ioi (max Tε 0),
          (h v - c) * Real.exp (-σ * v)‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hσ0]
    rw [eσ]
    calc σ * ‖∫ v in Set.Ioi (max Tε 0),
        (h v - c) * Real.exp (-σ * v)‖
        ≤ σ * ((ε / 2) * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v))) :=
          mul_le_mul_of_nonneg_left hIoi_est hσ0.le
      _ = ε / 2 := hE2
  rw [dist_eq_norm, hFeq, hsplit, mul_add]
  calc ‖σ * (∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
      (h v - c) * Real.exp (-σ * v)) +
      σ * (∫ v in Set.Ioi (max Tε 0), (h v - c) * Real.exp (-σ * v))‖
      ≤ ‖σ * (∫ v in Set.Ioc (0 : ℝ) (max Tε 0),
        (h v - c) * Real.exp (-σ * v))‖ +
        ‖σ * (∫ v in Set.Ioi (max Tε 0),
          (h v - c) * Real.exp (-σ * v))‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hIoc_σ hIoi_σ
    _ = ε := add_halves ε

-- Laplace transform of log: ∫ log u e^{-u} = -γ.
-- Complex form, following RegularizedIntegral.lean.
private theorem laplace_log_complex_int :
    (∫ t : ℝ in Set.Ioi 0, (Real.exp (-t) * Real.log t : ℂ)) =
      -(Real.eulerMascheroniConstant : ℂ) := by
  have hGI := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  have hEq : Complex.Gamma =ᶠ[nhds (1 : ℂ)] Complex.GammaIntegral := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {s : ℂ | 0 < s.re})]
      with s hs
    exact Complex.Gamma_eq_integral hs
  have hd : deriv Complex.Gamma (1 : ℂ) =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
        (Real.log t * Real.exp (-t)) := by
    rw [hEq.deriv_eq, hGI.deriv]
  rw [Complex.hasDerivAt_Gamma_one.deriv] at hd
  simpa [mul_comm] using hd.symm

private theorem laplace_log_complex_integrable :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Real.exp (-t) * Real.log t : ℂ))
      (Set.Ioi 0) := by
  have hm :=
    (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (a := 2) (b := 0)
      (f := fun x : ℝ => (Real.exp (-x) : ℂ)) (s := (1 : ℂ))
      (by
        refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
        exact Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg))
      (by
        rw [← Asymptotics.isBigO_norm_left]
        simp_rw [Complex.norm_real, Asymptotics.isBigO_norm_left]
        simpa only [neg_one_mul] using
          (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO)
      (by norm_num)
      (by
        simp_rw [neg_zero, Real.rpow_zero]
        refine Asymptotics.isBigO_const_of_tendsto
          (?_ : Filter.Tendsto (fun x : ℝ => (Real.exp (-x) : ℂ))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) one_ne_zero
        rw [(by simp : (1 : ℂ) = Real.exp (-0))]
        exact (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg)).continuousWithinAt)
      (by norm_num)).1
  simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul,
    Complex.real_smul, one_mul, mul_comm] using hm

private theorem laplace_log_eq :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-u)) =
      -Real.eulerMascheroniConstant := by
  have hfun : (fun t : ℝ => (Real.exp (-t) * Real.log t : ℂ)) =
      (fun t : ℝ => ((Real.log t * Real.exp (-t) : ℝ) : ℂ)) := by
    ext t
    push_cast
    ring
  have hC := laplace_log_complex_integrable
  have hV := laplace_log_complex_int
  rw [hfun] at hC hV
  refine ⟨MeasureTheory.Integrable.iff_ofReal.mpr hC, ?_⟩
  rw [integral_complex_ofReal] at hV
  exact_mod_cast hV

/-- The exponential integral `∫₀^∞ e^{-σv} dv = 1/σ`. -/
private theorem integral_exp_neg_mul_Ioi_zero (σ : ℝ) (hσ : 0 < σ) :
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) = σ⁻¹ := by
  have h := integral_exp_mul_Ioi (a := -σ) (by linarith : -σ < 0) (0 : ℝ)
  rw [mul_zero, Real.exp_zero] at h
  rw [h, neg_div_neg_eq, one_div]

/-- Scaling of the Laplace transform of log. -/
private theorem laplace_log_scaling (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)) ∧
    σ * (∫ v in Set.Ioi (0 : ℝ), Real.log v * Real.exp (-σ * v)) =
      -Real.eulerMascheroniConstant - Real.log σ := by
  have hbase := laplace_log_eq
  have hexp : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-σ * v))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith : -σ < 0) 0
  have hcomp : MeasureTheory.IntegrableOn
      (fun v : ℝ => Real.log (σ * v) * Real.exp (-(σ * v))) (Set.Ioi (0 : ℝ)) := by
    have hiff := MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.log u * Real.exp (-u)) (0 : ℝ) (a := σ) hσ
    rw [mul_zero] at hiff
    exact hiff.mpr hbase.1
  have hsplit : ∀ v ∈ Set.Ioi (0 : ℝ),
      Real.log (σ * v) * Real.exp (-(σ * v)) =
        Real.log σ * Real.exp (-σ * v) + Real.log v * Real.exp (-σ * v) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := Set.mem_Ioi.mp hv
    have hexp_eq : Real.exp (-(σ * v)) = Real.exp (-σ * v) := by rw [neg_mul]
    rw [Real.log_mul (ne_of_gt hσ) (ne_of_gt hv0), hexp_eq]
    ring
  have htarget : MeasureTheory.IntegrableOn
      (fun v : ℝ => Real.log v * Real.exp (-σ * v)) (Set.Ioi (0 : ℝ)) := by
    have hcm := MeasureTheory.Integrable.const_mul hexp (Real.log σ)
    have hsub := hcomp.sub hcm
    refine hsub.congr_fun ?h measurableSet_Ioi
    intro v hv
    have e := hsplit v hv
    change Real.log (σ * v) * Real.exp (-(σ * v)) - Real.log σ * Real.exp (-σ * v) =
      Real.log v * Real.exp (-σ * v)
    rw [e]
    ring
  refine ⟨htarget, ?_⟩
  have hsub : (∫ v in Set.Ioi (0 : ℝ), Real.log (σ * v) * Real.exp (-(σ * v))) =
      σ⁻¹ * (∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-u)) := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi
      (fun u : ℝ => Real.log u * Real.exp (-u)) (0 : ℝ) (b := σ) hσ
    rw [mul_zero] at h
    simpa [smul_eq_mul] using h
  have hsplit_int :
      (∫ v in Set.Ioi (0 : ℝ), Real.log (σ * v) * Real.exp (-(σ * v))) =
        Real.log σ * (∫ v in Set.Ioi (0 : ℝ), Real.exp (-σ * v)) +
          (∫ v in Set.Ioi (0 : ℝ), Real.log v * Real.exp (-σ * v)) := by
    have hcongr :
        (∫ v in Set.Ioi (0 : ℝ), Real.log (σ * v) * Real.exp (-(σ * v))) =
          ∫ v in Set.Ioi (0 : ℝ), (Real.log σ * Real.exp (-σ * v) +
            Real.log v * Real.exp (-σ * v)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsplit
    rw [hcongr, MeasureTheory.integral_add
      (MeasureTheory.Integrable.const_mul hexp (Real.log σ)) htarget,
      MeasureTheory.integral_const_mul]
  have hexp_val := integral_exp_neg_mul_Ioi_zero σ hσ
  rw [hsub, hbase.2, hexp_val] at hsplit_int
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hT : (∫ v in Set.Ioi (0 : ℝ), Real.log v * Real.exp (-σ * v)) =
      σ⁻¹ * -Real.eulerMascheroniConstant - Real.log σ * σ⁻¹ := by
    linarith [hsplit_int]
  rw [hT]
  field_simp

private theorem tendsto_mertensA_sub_loglog_eulerMascheroni :
    Filter.Tendsto (fun x => mertensA x - Real.log (Real.log x))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  obtain ⟨c, hc⟩ := exists_tendsto_mertensA_sub_loglog
  have hlim : Filter.Tendsto (fun v => mertensA (Real.exp v) - Real.log v)
      Filter.atTop (nhds c) := by
    have hcomp := hc.comp Real.tendsto_exp_atTop
    refine Filter.Tendsto.congr' ?_ hcomp
    filter_upwards with v
    simp only [Function.comp_apply, Real.log_exp]
  have hmeas : Measurable (fun v => mertensA (Real.exp v) - Real.log v) :=
    (mertensA_measurable.comp Real.measurable_exp).sub Real.measurable_log
  have hint : ∀ T : ℝ, MeasureTheory.IntegrableOn
      (fun v => mertensA (Real.exp v) - Real.log v) (Set.Ioc 0 T) := by
    intro T
    have hA_int : MeasureTheory.IntegrableOn (fun v => mertensA (Real.exp v))
        (Set.Ioc 0 T) := by
      have hmem : Measurable (fun v => mertensA (Real.exp v)) :=
        mertensA_measurable.comp Real.measurable_exp
      have hdom : MeasureTheory.IntegrableOn (fun _ => mertensA (Real.exp T))
          (Set.Ioc 0 T) :=
        ((continuous_const.continuousOn).integrableOn_Icc).mono_set
          Set.Ioc_subset_Icc_self
      refine MeasureTheory.Integrable.mono' hdom hmem.aestronglyMeasurable ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with v hv
      rw [Set.mem_Ioc] at hv
      have hnn : (0 : ℝ) ≤ mertensA (Real.exp v) := gronwall_mertensA_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mertensA_mono (Real.exp_le_exp.mpr hv.2)
    have hlog_int : MeasureTheory.IntegrableOn (fun v => Real.log v)
        (Set.Ioc 0 T) := by
      by_cases hT : (0 : ℝ) ≤ T
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
          hT).mp intervalIntegral.intervalIntegrable_log'
      · have hempty : Set.Ioc (0 : ℝ) T = ∅ :=
          Set.Ioc_eq_empty (not_lt.mpr (le_of_lt (lt_of_not_ge hT)))
        rw [hempty]
        exact MeasureTheory.integrableOn_empty
    exact hA_int.sub hlog_int
  have hN5 := tendsto_mul_laplace_of_tendsto
    (fun v => mertensA (Real.exp v) - Real.log v) c hmeas hint hlim
  have hγc : Filter.Tendsto (fun _ : ℝ => Real.eulerMascheroniConstant)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Real.eulerMascheroniConstant) :=
    tendsto_const_nhds
  have hG : Filter.Tendsto
      (fun σ => σ * (∫ v in Set.Ioi (0 : ℝ),
        (mertensA (Real.exp v) - Real.log v) * Real.exp (-σ * v))
        - Real.eulerMascheroniConstant)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (c - Real.eulerMascheroniConstant)) :=
    hN5.2.sub hγc
  have key : ∀ σ : ℝ, 0 < σ →
      Real.log (riemannZeta ((1 + σ : ℝ) : ℂ)).re + Real.log σ
      = σ * (∫ v in Set.Ioi (0 : ℝ),
          (mertensA (Real.exp v) - Real.log v) * Real.exp (-σ * v))
        - Real.eulerMascheroniConstant := by
    intro σ hσ
    have hN4 := (log_zeta_eq_laplace_mertensA σ hσ).1
    have hN6 := laplace_log_scaling σ hσ
    have hN5i := hN5.1 σ hσ
    have e1 : (∫ v in Set.Ioi (0 : ℝ),
          mertensA (Real.exp v) * Real.exp (-σ * v))
        = (∫ v in Set.Ioi (0 : ℝ),
            (mertensA (Real.exp v) - Real.log v) * Real.exp (-σ * v))
          + (∫ v in Set.Ioi (0 : ℝ), Real.log v * Real.exp (-σ * v)) := by
      have ec : (∫ v in Set.Ioi (0 : ℝ),
            mertensA (Real.exp v) * Real.exp (-σ * v))
          = ∫ v in Set.Ioi (0 : ℝ),
            ((mertensA (Real.exp v) - Real.log v) * Real.exp (-σ * v)
              + Real.log v * Real.exp (-σ * v)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => by ring)
      rw [ec, MeasureTheory.integral_add hN5i hN6.1]
    rw [hN4, e1, mul_add, hN6.2]
    ring
  have hF : Filter.Tendsto
      (fun σ => Real.log (riemannZeta ((1 + σ : ℝ) : ℂ)).re + Real.log σ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (c - Real.eulerMascheroniConstant)) := by
    refine Filter.Tendsto.congr' ?_ hG
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (key σ (Set.mem_Ioi.mp hσ)).symm
  have hF0 : Filter.Tendsto
      (fun σ => Real.log (riemannZeta ((1 + σ : ℝ) : ℂ)).re + Real.log σ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hzeta := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
    have hmap : Filter.Tendsto (fun σ : ℝ => (1 + σ : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
      have h1 : Filter.Tendsto (fun σ : ℝ => (1 + σ : ℝ)) (nhds (0 : ℝ))
          (nhds (1 : ℝ)) := by
        have hc1 : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds (0 : ℝ))
            (nhds 1) := tendsto_const_nhds
        have hid : Filter.Tendsto (fun σ : ℝ => σ) (nhds (0 : ℝ)) (nhds 0) :=
          Filter.tendsto_id
        have h := hc1.add hid
        simpa using h
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h1.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact Set.mem_Ioi.mpr (by
        have h := Set.mem_Ioi.mp hσ
        linarith)
    have hcomp : Filter.Tendsto
        (fun σ : ℝ => riemannZeta ((1 + σ : ℝ) : ℂ)
          - 1 / (((1 + σ : ℝ) : ℂ) - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      hzeta.comp hmap
    have h0c : Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ)) (nhds (0 : ℝ))
        (nhds ((0 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.tendsto 0
    have hσ0 : Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h : Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ) : ℂ)) :=
        h0c.mono_left nhdsWithin_le_nhds
      rwa [Complex.ofReal_zero] at h
    have hmul : Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ)
          * (riemannZeta ((1 + σ : ℝ) : ℂ) - 1 / (((1 + σ : ℝ) : ℂ) - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hσ0.mul hcomp
      simpa using h
    have h_sz : Filter.Tendsto
        (fun σ : ℝ => ((σ : ℝ) : ℂ) * riemannZeta ((1 + σ : ℝ) : ℂ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have hsub : ∀ σ : ℝ, σ ∈ Set.Ioi (0 : ℝ) →
          ((σ : ℝ) : ℂ) * (riemannZeta ((1 + σ : ℝ) : ℂ)
            - 1 / (((1 + σ : ℝ) : ℂ) - 1))
          = ((σ : ℝ) : ℂ) * riemannZeta ((1 + σ : ℝ) : ℂ) - 1 := by
        intro σ hσ
        have hσ0 : ((σ : ℝ) : ℂ) ≠ 0 :=
          by exact_mod_cast ne_of_gt (Set.mem_Ioi.mp hσ)
        have hexp : ((((1 + σ : ℝ)) : ℂ) - 1) = ((σ : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hexp, mul_sub, mul_one_div_cancel hσ0]
      have hmul' : Filter.Tendsto (fun σ : ℝ => ((σ : ℝ) : ℂ)
            * riemannZeta ((1 + σ : ℝ) : ℂ) - 1)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        refine Filter.Tendsto.congr' ?_ hmul
        filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact hsub σ hσ
      have h1c : Filter.Tendsto (fun _ : ℝ => (1 : ℂ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
      have h2 := hmul'.add h1c
      rw [zero_add] at h2
      refine Filter.Tendsto.congr' ?_ h2
      filter_upwards with σ
      rw [sub_add_cancel]
    have h_re : Filter.Tendsto
        (fun σ : ℝ => σ * (riemannZeta ((1 + σ : ℝ) : ℂ)).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp h_sz
      have hre1 : ((1 : ℂ)).re = 1 := Complex.one_re
      rw [hre1] at h
      refine Filter.Tendsto.congr' ?_ h
      filter_upwards with σ
      simp only [Function.comp_apply]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
    have h_log : Filter.Tendsto
        (fun σ : ℝ => Real.log (σ * (riemannZeta ((1 + σ : ℝ) : ℂ)).re))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.log 1)) :=
      h_re.log (by norm_num : (1 : ℝ) ≠ 0)
    rw [Real.log_one] at h_log
    have hpos : ∀ᶠ σ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 < (riemannZeta ((1 + σ : ℝ) : ℂ)).re := by
      have h1 : ∀ᶠ σ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (1 : ℝ) / 2 < σ * (riemannZeta ((1 + σ : ℝ) : ℂ)).re :=
        h_re.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))
      filter_upwards [h1, self_mem_nhdsWithin] with σ hσ hσ0
      have hσpos : (0 : ℝ) < σ := Set.mem_Ioi.mp hσ0
      have hdiv : (0 : ℝ) < σ * (riemannZeta ((1 + σ : ℝ) : ℂ)).re / σ :=
        div_pos (by linarith [hσ]) hσpos
      rwa [mul_div_cancel_left₀ _ (ne_of_gt hσpos)] at hdiv
    refine Filter.Tendsto.congr' ?_ h_log
    filter_upwards [hpos, self_mem_nhdsWithin] with σ hσ hσ0
    have hσpos : (0 : ℝ) < σ := Set.mem_Ioi.mp hσ0
    rw [Real.log_mul (ne_of_gt hσpos) (ne_of_gt hσ)]
    ring
  have hceq : c - Real.eulerMascheroniConstant = 0 :=
    tendsto_nhds_unique hF hF0
  have hcγ : c = Real.eulerMascheroniConstant := by linarith
  rw [hcγ] at hc
  exact hc

-- Truncated log-series bound.
private theorem neg_log_one_sub_inv_sub_primeTail {p N : ℕ} (hp : p.Prime) (h : p ≤ N) :
    0 ≤ -Real.log (1 - (p : ℝ)⁻¹) - primeTail p N ∧
    -Real.log (1 - (p : ℝ)⁻¹) - primeTail p N ≤ 2 / ((N : ℝ) + 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hN2 : 2 ≤ N := le_trans hp.two_le h
  have h0p : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have h1p : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have habs : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_nonneg h0p]
    exact h1p
  have hHasSum : HasSum (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - (p : ℝ)⁻¹)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hS : Summable
      (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) / ((n : ℝ) + 1)) :=
    hHasSum.summable
  have hf0 : ∀ j : ℕ, 0 ≤ ((p : ℝ)⁻¹) ^ (j + 1) / ((j : ℝ) + 1) := by
    intro j
    apply div_nonneg (pow_nonneg h0p _)
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hT_eq : primeTail p N = ∑ j ∈ Finset.range (Nat.log p N),
      (((p : ℝ)⁻¹) ^ (j + 1) / ((j : ℝ) + 1)) := by
    unfold primeTail
    have hIcc : Finset.Icc 1 (Nat.log p N) =
        Finset.Ico 1 (Nat.log p N + 1) :=
      (Finset.Ico_add_one_right_eq_Icc_of_not_isMax
        (not_isMax_of_lt (Nat.lt_succ_self _)) 1).symm
    rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm (1 : ℕ) k, Nat.cast_add, Nat.cast_one, inv_pow, one_div, mul_inv,
      div_eq_mul_inv]
    ring
  have hle1 : primeTail p N ≤ -Real.log (1 - (p : ℝ)⁻¹) := by
    rw [hT_eq]
    exact sum_le_hasSum _ (fun j _ => hf0 j) hHasSum
  have hsplit := Summable.sum_add_tsum_nat_add (Nat.log p N) hS
  have htsum := hHasSum.tsum_eq
  have hsplit' : (∑ j ∈ Finset.range (Nat.log p N),
        (((p : ℝ)⁻¹) ^ (j + 1) / ((j : ℝ) + 1))) +
        (∑' j : ℕ, ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) /
          ((((j + Nat.log p N : ℕ)) : ℝ) + 1)) =
        ∑' j : ℕ, (((p : ℝ)⁻¹) ^ (j + 1) / ((j : ℝ) + 1)) := hsplit
  have hR_sum : Summable (fun j : ℕ => ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) /
      ((((j + Nat.log p N : ℕ)) : ℝ) + 1)) :=
    (summable_nat_add_iff (Nat.log p N)).mpr hS
  have hgeom_sum : (∑' j : ℕ, ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * ((p : ℝ)⁻¹) ^ j) =
      ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one h0p h1p]
  have hSg : Summable
      (fun j : ℕ => ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * ((p : ℝ)⁻¹) ^ j) :=
    Summable.mul_left _ (summable_geometric_of_lt_one h0p h1p)
  have hgeom_has : HasSum
      (fun j : ℕ => ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * ((p : ℝ)⁻¹) ^ j)
      (((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * (1 - (p : ℝ)⁻¹)⁻¹) := by
    have h := hSg.hasSum
    rwa [hgeom_sum] at h
  have hpartial : ∀ J : ℕ, (∑ j ∈ Finset.range J,
      ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) /
        ((((j + Nat.log p N : ℕ)) : ℝ) + 1)) ≤
      ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro J
    have hpt : ∀ j ∈ Finset.range J,
        ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) /
          ((((j + Nat.log p N : ℕ)) : ℝ) + 1) ≤
          ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * ((p : ℝ)⁻¹) ^ j := by
      intro j hj
      have h1 : ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) /
          ((((j + Nat.log p N : ℕ)) : ℝ) + 1) ≤
          ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) := by
        apply div_le_self (pow_nonneg h0p _)
        have h1N : (1 : ℝ) ≤ ((((j + Nat.log p N : ℕ)) : ℝ) + 1) := by
          have hnn : (0 : ℝ) ≤ ((((j + Nat.log p N : ℕ)) : ℝ)) :=
            Nat.cast_nonneg _
          linarith
        exact h1N
      have h2 : ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) =
          ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * ((p : ℝ)⁻¹) ^ j := by
        rw [show (j + Nat.log p N) + 1 = (Nat.log p N + 1) + j by omega, pow_add]
      linarith [h1, h2]
    have hsum := Finset.sum_le_sum hpt
    have hpg : (∑ j ∈ Finset.range J,
        ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * ((p : ℝ)⁻¹) ^ j) ≤
        ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * (1 - (p : ℝ)⁻¹)⁻¹ :=
      sum_le_hasSum _ (fun j _ =>
        mul_nonneg (pow_nonneg h0p _) (pow_nonneg h0p _)) hgeom_has
    linarith [hsum, hpg]
  have hR_le : (∑' j : ℕ, ((p : ℝ)⁻¹) ^ ((j + Nat.log p N) + 1) /
      ((((j + Nat.log p N : ℕ)) : ℝ) + 1)) ≤
      ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) * (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply le_of_tendsto hR_sum.hasSum.tendsto_sum_nat
    exact Filter.Eventually.of_forall hpartial
  have hpr : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp2
  have hfac2 : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ (by linarith [hpr] : (0 : ℝ) < 1 - (p : ℝ)⁻¹)
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith [hpr] : (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹)
    have h2inv : ((1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    rwa [h2inv] at h
  have hplt : N < p ^ (Nat.log p N).succ :=
    Nat.lt_pow_succ_log_self hp.one_lt N
  have hNp1 : (N : ℝ) + 1 ≤ (p : ℝ) ^ (Nat.log p N + 1) := by
    have h1 : N + 1 ≤ p ^ (Nat.log p N).succ := hplt
    have h2 : ((N + 1 : ℕ) : ℝ) ≤ ((p ^ (Nat.log p N).succ : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h2
    exact h2
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by
    have h0N : (0 : ℝ) < (N : ℝ) := by
      have hpos : 0 < N := by omega
      exact_mod_cast hpos
    linarith
  have hrK : ((p : ℝ)⁻¹) ^ (Nat.log p N + 1) ≤ 1 / ((N : ℝ) + 1) := by
    rw [inv_pow, inv_eq_one_div]
    exact one_div_le_one_div_of_le hNpos hNp1
  have hnonneg_c : (0 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    have h1 := one_le_inv_one_sub_inv_prime p hp
    linarith
  have hnonneg_b : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
    div_nonneg zero_le_one (le_of_lt hNpos)
  have h3 := mul_le_mul hrK hfac2 hnonneg_c hnonneg_b
  have heq : (1 / ((N : ℝ) + 1)) * 2 = 2 / ((N : ℝ) + 1) := by ring
  rw [heq] at h3
  constructor
  · linarith [hle1]
  · linarith [hsplit', htsum, hR_le, h3, hT_eq]

/-- `a(p^k) = 1/(k * p^k)` for prime `p` and `k ≥ 1`. -/
private theorem mertensAcoeff_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    mertensAcoeff (p ^ k) = 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
  have hk0 : k ≠ 0 := by omega
  have hΛ : ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log ((p ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hplog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hp.pos)
      (by exact_mod_cast hp.ne_one)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hpkR : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hp.pos)
  unfold mertensAcoeff
  rw [hΛ, hlog]
  push_cast
  field_simp

/-- `a(n) = 0` off prime powers. -/
private theorem mertensAcoeff_eq_zero_of_not_isPrimePow {n : ℕ}
    (hn : ¬IsPrimePow n) : mertensAcoeff n = 0 := by
  unfold mertensAcoeff
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

-- Prime-power regrouping: A(N) = ∑ T(p,N).
private theorem mertensA_natCast_eq_sum_primeTail (N : ℕ) :
    mertensA (N : ℝ) = ∑ p ∈ Nat.primesLE N, primeTail p N := by
  have hLHS : mertensA (N : ℝ)
      = ∑ n ∈ (Finset.Icc 0 N).filter IsPrimePow, mertensAcoeff n := by
    unfold mertensA
    rw [Nat.floor_natCast]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun n hnIcc hnfil => ?_).symm
    rw [Finset.mem_filter] at hnfil
    push Not at hnfil
    exact mertensAcoeff_eq_zero_of_not_isPrimePow (hnfil hnIcc)
  have hterm : ∀ p ∈ Nat.primesLE N, ∀ k ∈ Finset.Icc 1 (Nat.log p N),
      (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k) = mertensAcoeff (p ^ k) := by
    intro p hp k hk
    rw [Finset.mem_Icc] at hk
    exact (mertensAcoeff_prime_pow (Nat.prime_of_mem_primesLE hp) hk.1).symm
  have hRHS : (∑ p ∈ Nat.primesLE N, primeTail p N)
      = ∑ x ∈ (Nat.primesLE N).sigma (fun p => Finset.Icc 1 (Nat.log p N)),
        mertensAcoeff (x.1 ^ x.2) := by
    unfold primeTail
    rw [Finset.sum_sigma']
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_sigma] at hx
    exact hterm x.1 hx.1 x.2 hx.2
  rw [hLHS, hRHS]
  refine (Finset.sum_bij (fun a _ => a.1 ^ a.2) ?_ ?_ ?_ ?_).symm
  · intro a ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hap, hak⟩ := ha
    rw [Finset.mem_Icc] at hak
    have hpp := Nat.prime_of_mem_primesLE hap
    rw [Nat.mem_primesLE] at hap
    have hN0 : N ≠ 0 := by
      have h2N : 2 ≤ N := le_trans hpp.two_le hap.1
      omega
    have hpow_le : a.1 ^ a.2 ≤ N := Nat.pow_le_of_le_log hN0 hak.2
    have hppow : IsPrimePow (a.1 ^ a.2) := by
      rw [isPrimePow_pow_iff (by omega : a.2 ≠ 0)]
      exact hpp.isPrimePow
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le _, hpow_le⟩, hppow⟩
  · intro a₁ ha₁ a₂ ha₂ h
    rw [Finset.mem_sigma] at ha₁ ha₂
    obtain ⟨hap₁, hak₁⟩ := ha₁
    obtain ⟨hap₂, hak₂⟩ := ha₂
    rw [Finset.mem_Icc] at hak₁ hak₂
    have hpp₁ := Nat.prime_of_mem_primesLE hap₁
    have hpp₂ := Nat.prime_of_mem_primesLE hap₂
    have hk₁ : a₁.2 ≠ 0 := by omega
    have hk₂ : a₂.2 ≠ 0 := by omega
    obtain ⟨e1, e2⟩ := Nat.Prime.pow_inj' hpp₁ hpp₂ hk₁ hk₂ h
    exact Sigma.ext e1 (heq_of_eq e2)
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨-, hnN⟩, hppow⟩ := hn
    rw [isPrimePow_nat_iff] at hppow
    obtain ⟨p, k, hpprime, hkpos, rfl⟩ := hppow
    refine ⟨⟨p, k⟩, ?_, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_primesLE]
    refine ⟨⟨?_, hpprime⟩, hkpos, ?_⟩
    · exact le_trans (le_self_pow hpprime.one_lt.le (ne_of_gt hkpos)) hnN
    · exact Nat.le_log_of_pow_le hpprime.one_lt hnN
  · intro a _
    rfl

/-- `P(x) = P(⌊x⌋₊)` by unfolding. -/
private theorem mertensP_floor (x : ℝ) : mertensP x = mertensP (⌊x⌋₊ : ℝ) := by
  unfold mertensP
  rw [Nat.floor_natCast]

/-- `A(x) = A(⌊x⌋₊)` by unfolding. -/
private theorem mertensA_floor (x : ℝ) : mertensA x = mertensA (⌊x⌋₊ : ℝ) := by
  unfold mertensA
  rw [Nat.floor_natCast]

/-- `log P(N) = ∑ −log(1 − 1/p)` over `p ∈ primesLE N`. -/
private theorem log_mertensP_eq (N : ℕ) :
    Real.log (mertensP (N : ℝ)) =
      ∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹) := by
  have hP : mertensP (N : ℝ) = ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
    unfold mertensP
    rw [Nat.floor_natCast]
  rw [hP, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    exact Real.log_inv _
  · intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have h1p : (p : ℝ)⁻¹ < 1 := by
      apply inv_lt_one_of_one_lt₀
      linarith
    exact inv_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 1 - (p : ℝ)⁻¹))

/-- `0 ≤ log P(N) − A(N) ≤ 2 * #(primesLE N)/(N+1)`. -/
private theorem log_mertensP_sub_mertensA_bound (N : ℕ) :
    0 ≤ Real.log (mertensP (N : ℝ)) - mertensA (N : ℝ) ∧
      Real.log (mertensP (N : ℝ)) - mertensA (N : ℝ) ≤
        2 * ((Nat.primesLE N).card : ℝ) / ((N : ℝ) + 1) := by
  rw [log_mertensP_eq N, mertensA_natCast_eq_sum_primeTail N]
  have hterm : ∀ p ∈ Nat.primesLE N,
      0 ≤ -Real.log (1 - (p : ℝ)⁻¹) - primeTail p N ∧
        -Real.log (1 - (p : ℝ)⁻¹) - primeTail p N ≤ 2 / ((N : ℝ) + 1) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    exact neg_log_one_sub_inv_sub_primeTail hp.2 hp.1
  have hsub : (∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹)) -
      (∑ p ∈ Nat.primesLE N, primeTail p N) =
      ∑ p ∈ Nat.primesLE N, (-Real.log (1 - (p : ℝ)⁻¹) - primeTail p N) := by
    rw [Finset.sum_sub_distrib]
  rw [hsub]
  refine ⟨Finset.sum_nonneg (fun p hp => (hterm p hp).1), ?_⟩
  have h3 := Finset.sum_le_card_nsmul (Nat.primesLE N)
    (fun p => -Real.log (1 - (p : ℝ)⁻¹) - primeTail p N) (2 / ((N : ℝ) + 1))
    (fun p hp => (hterm p hp).2)
  rw [nsmul_eq_mul] at h3
  calc ∑ p ∈ Nat.primesLE N, (-Real.log (1 - (p : ℝ)⁻¹) - primeTail p N)
      ≤ ((Nat.primesLE N).card : ℝ) * (2 / ((N : ℝ) + 1)) := h3
    _ = 2 * ((Nat.primesLE N).card : ℝ) / ((N : ℝ) + 1) := by ring

/-- `2 * π(⌊x⌋₊)/x → 0`, from Chebyshev's explicit upper bound. -/
private theorem tendsto_primeCounting_div : Filter.Tendsto
    (fun x : ℝ => 2 * ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) / x)
    Filter.atTop (nhds 0) := by
  have hbound := Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num)
  have hlim : Filter.Tendsto (fun x : ℝ => 2 * (Real.log 4 + 1) / Real.log x)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Real.tendsto_log_atTop _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hx0.le
  · filter_upwards [hbound, Filter.eventually_ge_atTop 2] with x hpi hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hlog : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    have hne_x : (x : ℝ) ≠ 0 := ne_of_gt hx0
    have hne_log : Real.log x ≠ 0 := ne_of_gt hlog
    have h2 : 2 * ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) / x ≤
        2 * ((Real.log 4 + 1) * x / Real.log x) / x := by
      rw [div_le_div_iff_of_pos_right hx0]
      linarith [hpi]
    have h4 : 2 * ((Real.log 4 + 1) * x / Real.log x) / x =
        2 * (Real.log 4 + 1) / Real.log x := by
      field_simp
    rwa [h4] at h2

/-- The error `log P(x) − A(x) → 0` by squeeze against `2π/x`. -/
private theorem tendsto_log_mertensP_sub_mertensA :
    Filter.Tendsto (fun x => Real.log (mertensP x) - mertensA x)
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_primeCounting_div ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    rw [mertensP_floor x, mertensA_floor x]
    exact (log_mertensP_sub_mertensA_bound ⌊x⌋₊).1
  · filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    rw [mertensP_floor x, mertensA_floor x]
    have hx0 : (0 : ℝ) < x := by linarith
    have hN1 : (0 : ℝ) < (⌊x⌋₊ : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
      linarith
    have hxN1 : x ≤ (⌊x⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    have hle := (log_mertensP_sub_mertensA_bound ⌊x⌋₊).2
    rw [Nat.primesLE_card_eq_primeCounting] at hle
    have hπnn : (0 : ℝ) ≤
        2 * ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    refine hle.trans ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hN1 hx0).mpr hxN1) hπnn

/-- `log P(x) − log log x → γ`, from the Euler–Mascheroni limit plus the vanishing error. -/
private theorem tendsto_log_mertensP_sub_loglog :
    Filter.Tendsto
      (fun x => Real.log (mertensP x) - Real.log (Real.log x))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have hsum := tendsto_mertensA_sub_loglog_eulerMascheroni.add
    tendsto_log_mertensP_sub_mertensA
  rw [add_zero] at hsum
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards with x
  ring

-- Mertens' third theorem.
private theorem tendsto_mertensP_div_log :
    Filter.Tendsto (fun x => mertensP x / Real.log x)
      Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have heq : (fun x => mertensP x / Real.log x) =ᶠ[Filter.atTop]
      (fun x => Real.exp (Real.log (mertensP x) - Real.log (Real.log x))) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hP : (0 : ℝ) < mertensP x := mertensP_pos x
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    rw [Real.exp_sub, Real.exp_log hP, Real.exp_log hlogx]
  refine Filter.Tendsto.congr' heq.symm ?_
  exact (Real.continuous_exp.tendsto _).comp tendsto_log_mertensP_sub_loglog

-- σ(n)/n upper bound by Mertens product.
/-- The Mertens factor as `1 + 1/(p-1)`. -/
private theorem inv_one_sub_inv_eq (p : ℕ) (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ))
  have hp1 : ((p : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) - 1)
  field_simp
  ring

/-- Product inequality over `ℝ` by induction. -/
private theorem prod_le_prod_of_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · intro h0 h1
    simp
  · intro a t hat ih h0 h1
    rw [Finset.prod_insert hat, Finset.prod_insert hat]
    have h0t : ∀ i ∈ t, 0 ≤ f i :=
      fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1t : ∀ i ∈ t, f i ≤ g i :=
      fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hag : f a ≤ g a := h1 a (Finset.mem_insert_self a t)
    have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a t)
    exact mul_le_mul hag (ih h0t h1t) (Finset.prod_nonneg h0t) (le_trans ha0 hag)

/-- A product of terms `≥ 1` is `≥ 1`, over `ℝ`. -/
private theorem one_le_prod_of_one_le {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a t hat ih h
    rw [Finset.prod_insert hat]
    have ha : 1 ≤ f a := h a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, 1 ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1t : 1 ≤ ∏ i ∈ t, f i := ih ht
    calc (1 : ℝ) ≤ ∏ i ∈ t, f i := h1t
      _ ≤ f a * ∏ i ∈ t, f i :=
        le_mul_of_one_le_left (zero_le_one.trans h1t) ha

/-- Lower bound `r^#s ≤ ∏ f` over `ℝ` by induction. -/
private theorem pow_card_le_prod_of_le {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, r ≤ f i) : r ^ s.card ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a t hat ih h
    rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat, pow_succ,
      mul_comm (f a)]
    have ht : ∀ i ∈ t, r ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha : r ≤ f a := h a (Finset.mem_insert_self a t)
    have h0t : ∀ i ∈ t, 0 ≤ f i := fun i hi => le_trans hr (ht i hi)
    exact mul_le_mul (ih ht) ha hr (Finset.prod_nonneg h0t)

/-- `σ₁(p^a)/p^a` is bounded by the Mertens factor (partial geometric sum). -/
private theorem sigma_prime_pow_div_le (p a : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) ≤
      (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  have hre : ∀ k ∈ Finset.range (a + 1),
      (p : ℝ) ^ k * ((p : ℝ) ^ a)⁻¹ = ((p : ℝ)⁻¹) ^ (a - k) := by
    intro k hk
    have hka : k ≤ a := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hp0 : (p : ℝ) ≠ 0 := by
      have hne : p ≠ 0 := ne_of_gt hp.pos
      exact_mod_cast hne
    have hxk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ hp0
    have hpa : (p : ℝ) ^ a = (p : ℝ) ^ k * (p : ℝ) ^ (a - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hka]
    rw [hpa, mul_inv, ← mul_assoc, mul_inv_cancel₀ hxk, one_mul, inv_pow]
  rw [Finset.sum_congr rfl hre]
  have hreflect := Finset.sum_range_reflect (fun j => ((p : ℝ)⁻¹) ^ j) (a + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1p : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have h0p : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hgeom : HasSum (fun j : ℕ => ((p : ℝ)⁻¹) ^ j) (1 - (p : ℝ)⁻¹)⁻¹ :=
    hasSum_geometric_of_lt_one h0p h1p
  exact sum_le_hasSum (Finset.range (a + 1))
    (fun j _ => pow_nonneg h0p j) hgeom

/-- Upper bound `∏ f ≤ r^#s` over `ℝ` by induction. -/
private theorem prod_le_pow_card_of_le {ι : Type*} {s : Finset ι}
    {f : ι → ℝ} {r : ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i) (hr : 0 ≤ r)
    (h : ∀ i ∈ s, f i ≤ r) : ∏ i ∈ s, f i ≤ r ^ s.card := by
  classical
  revert h0 h
  refine Finset.induction_on s ?_ ?_
  · intro h0 h
    simp
  · intro a t hat ih h0 h
    rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat, pow_succ']
    have h0t : ∀ i ∈ t, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have ht : ∀ i ∈ t, f i ≤ r := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha : f a ≤ r := h a (Finset.mem_insert_self a t)
    exact mul_le_mul ha (ih h0t ht) (Finset.prod_nonneg h0t) hr

private theorem sigma_div_self_le_mertensP_mul_exp (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 2 ≤ y) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) ≤
      mertensP y * Real.exp (Real.log n / ((y - 1) * Real.log y)) := by
  have hn0 : n ≠ 0 := by omega
  have hsigma :=
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) (n := n) hn0
  have hn_eq : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h
  have hfac : ∀ p ∈ n.primeFactors,
      ((∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1) : ℕ) : ℝ) /
        ((p ^ n.factorization p : ℕ) : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hpmem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hS : (∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1)) =
        ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hpp]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_one]
    rw [hS]
    exact sigma_prime_pow_div_le p _ hpp
  have hσ_cast : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors,
        ((∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1) : ℕ) : ℝ) := by
    conv_lhs => rw [hsigma]
    rw [Nat.cast_prod]
  have hn_cast : (n : ℝ) =
      ∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ) := by
    conv_lhs => rw [← hn_eq]
    rw [Nat.cast_prod]
  conv_lhs => rw [hσ_cast, hn_cast, ← Finset.prod_div_distrib]
  have hstep1 : ∏ p ∈ n.primeFactors,
        (((∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1) : ℕ) : ℝ) /
          ((p ^ n.factorization p : ℕ) : ℝ)) ≤
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
    prod_le_prod_of_nonneg
      (fun p _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hfac
  refine le_trans hstep1 ?_
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors
    (fun p => p ≤ ⌊y⌋₊) (fun p => (1 - (p : ℝ)⁻¹)⁻¹)
  rw [← hsplit]
  have hsmall : ∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤ mertensP y := by
    have hsub : n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊) ⊆
        Nat.primesLE ⌊y⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE]
      exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
    have h1 : ∀ p ∈ Nat.primesLE ⌊y⌋₊,
        p ∉ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊) →
        1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro p hp _
      exact one_le_inv_one_sub_inv_prime p (Nat.prime_of_mem_primesLE hp)
    have hdecomp : (∏ p ∈ Nat.primesLE ⌊y⌋₊ \
        n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊), (1 - (p : ℝ)⁻¹)⁻¹) *
        (∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
          (1 - (p : ℝ)⁻¹)⁻¹) =
        ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ :=
      Finset.prod_sdiff hsub
    have hdiff1 : 1 ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊ \
        n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊), (1 - (p : ℝ)⁻¹)⁻¹ := by
      apply one_le_prod_of_one_le
      intro p hp
      rw [Finset.mem_sdiff] at hp
      exact h1 p hp.1 hp.2
    have hfilter1 : ∀ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
        (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact one_le_inv_one_sub_inv_prime p
        (Nat.prime_of_mem_primeFactors hp.1)
    have hnonneg : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ :=
      Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hfilter1 p hp))
    have hle : ∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [← hdecomp]
      exact le_mul_of_one_le_left hnonneg hdiff1
    have hP : mertensP y = ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := rfl
    rwa [hP]
  have hlarge : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤
      Real.exp (Real.log n / ((y - 1) * Real.log y)) := by
    have hplt : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        y < (p : ℝ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have h1 : ⌊y⌋₊ < p := Nat.lt_of_not_ge hp.2
      have h3 : y - 1 < (⌊y⌋₊ : ℝ) := by
        have hfl := Nat.lt_floor_add_one y
        linarith
      have h4 : (⌊y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
        have h5 : ⌊y⌋₊ + 1 ≤ p := by omega
        exact_mod_cast h5
      linarith
    have hfac_le : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (1 / (y - 1)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hp2 : 2 ≤ p := hpp.two_le
      have hpy : y < (p : ℝ) := hplt p (Finset.mem_filter.mpr hp)
      rw [inv_one_sub_inv_eq p hp2]
      have h1 : (1 : ℝ) + 1 / ((p : ℝ) - 1) ≤
          Real.exp (1 / ((p : ℝ) - 1)) := by
        rw [add_comm (1 : ℝ)]
        exact Real.add_one_le_exp _
      have h2 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / (y - 1) := by
        apply one_div_le_one_div_of_le
        · linarith
        · linarith
      calc (1 : ℝ) + 1 / ((p : ℝ) - 1) ≤ Real.exp (1 / ((p : ℝ) - 1)) := h1
        _ ≤ Real.exp (1 / (y - 1)) := Real.exp_le_exp.mpr h2
    have h0fac : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        0 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have h1 := one_le_inv_one_sub_inv_prime p
        (Nat.prime_of_mem_primeFactors hp.1)
      linarith
    have hexp0 : (0 : ℝ) ≤ Real.exp (1 / (y - 1)) := (Real.exp_pos _).le
    have hprod_pow : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ ≤
        Real.exp (1 / (y - 1)) ^
          (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card :=
      prod_le_pow_card_of_le h0fac hexp0 hfac_le
    have hy0 : (0 : ℝ) < y := by linarith
    have hpow_le : y ^ (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card ≤
        ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) :=
      pow_card_le_prod_of_le hy0.le (fun p hp => le_of_lt (hplt p hp))
    have hle1 : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) ≤
        ∏ p ∈ n.primeFactors, (p : ℝ) := by
      have hsubf : n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊) ⊆
          n.primeFactors :=
        Finset.filter_subset _ _
      have h1 : ∀ p ∈ n.primeFactors,
          p ∉ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊) →
          (1 : ℝ) ≤ (p : ℝ) := by
        intro p hpmem _
        have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpmem).two_le
        have h2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
        linarith
      have hdecompf : (∏ p ∈ n.primeFactors \
          n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ)) *
          (∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ)) =
          ∏ p ∈ n.primeFactors, (p : ℝ) :=
        Finset.prod_sdiff hsubf
      have hdiff1 : 1 ≤ ∏ p ∈ n.primeFactors \
          n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) := by
        apply one_le_prod_of_one_le
        intro p hp
        rw [Finset.mem_sdiff] at hp
        exact h1 p hp.1 hp.2
      have hnonneg : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
          (p : ℝ) :=
        Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)
      rw [← hdecompf]
      exact le_mul_of_one_le_left hnonneg hdiff1
    have hle2 : ∏ p ∈ n.primeFactors, (p : ℝ) ≤ (n : ℝ) := by
      have hdvd := Nat.prod_primeFactors_dvd n
      have hle_nat : ∏ p ∈ n.primeFactors, p ≤ n :=
        Nat.le_of_dvd (by omega : 0 < n) hdvd
      have hcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hle_nat
      rwa [Nat.cast_prod] at hcast
    have hlog : ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
        Real.log y ≤ Real.log n := by
      have hpos1 : (0 : ℝ) <
          y ^ (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card :=
        pow_pos hy0 _
      have hpos2 : (0 : ℝ) <
          ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) := by
        apply Finset.prod_pos
        intro p hp
        rw [Finset.mem_filter] at hp
        have hpos : 0 < p := (Nat.prime_of_mem_primeFactors hp.1).pos
        exact_mod_cast hpos
      have hpos3 : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p : ℝ) := by
        apply Finset.prod_pos
        intro p hpmem
        have hpos : 0 < p := (Nat.prime_of_mem_primeFactors hpmem).pos
        exact_mod_cast hpos
      calc ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
            Real.log y
          = Real.log (y ^ (n.primeFactors.filter
            (fun p => ¬ p ≤ ⌊y⌋₊)).card) := by rw [Real.log_pow]
        _ ≤ Real.log (∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
            (p : ℝ)) := Real.log_le_log hpos1 hpow_le
        _ ≤ Real.log (∏ p ∈ n.primeFactors, (p : ℝ)) :=
            Real.log_le_log hpos2 hle1
        _ ≤ Real.log n := Real.log_le_log hpos3 hle2
    have hy1 : (0 : ℝ) < y - 1 := by linarith
    have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith : (1 : ℝ) < y)
    have hexp_eq : Real.exp (1 / (y - 1)) ^
        (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card =
        Real.exp (((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) /
          (y - 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hfrac : ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) /
        (y - 1) ≤ Real.log n / ((y - 1) * Real.log y) := by
      have hpos : (0 : ℝ) < (y - 1) * Real.log y := mul_pos hy1 hlogy
      rw [div_le_div_iff₀ hy1 hpos]
      have hmul := mul_le_mul_of_nonneg_right hlog hy1.le
      have heq : ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
          ((y - 1) * Real.log y) =
          (((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
            Real.log y) * (y - 1) := by ring
      rwa [heq]
    calc ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
          (1 - (p : ℝ)⁻¹)⁻¹
        ≤ Real.exp (1 / (y - 1)) ^
          (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card := hprod_pow
      _ = Real.exp (((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) /
          (y - 1)) := hexp_eq
      _ ≤ Real.exp (Real.log n / ((y - 1) * Real.log y)) :=
          Real.exp_le_exp.mpr hfrac
  have hlarge0 : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
      (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    rw [Finset.mem_filter] at hp
    have h1 := one_le_inv_one_sub_inv_prime p
      (Nat.prime_of_mem_primeFactors hp.1)
    linarith
  have hP0 : 0 ≤ mertensP y := le_trans zero_le_one (mertensP_ge_one y)
  exact mul_le_mul hsmall hlarge hlarge0 hP0

-- Witness family lower bound.
/-- The witness `n(m,a)` is `≥ 1` and `log n(m,a) = a * θ(m)`. -/
private theorem prod_primesLE_pow_ge_one_log (m a : ℕ) :
    1 ≤ ∏ p ∈ Nat.primesLE m, p ^ a ∧
      Real.log ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) =
        (a : ℝ) * Chebyshev.theta (m : ℝ) := by
  refine ⟨?_, ?_⟩
  · apply Finset.one_le_prod
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    exact one_le_pow₀ hpp.one_lt.le
  · have hne : ∀ p ∈ Nat.primesLE m, (((p ^ a : ℕ)) : ℝ) ≠ 0 := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesLE hp
      have hpa : p ^ a ≠ 0 := by
        apply pow_ne_zero
        exact ne_of_gt hpp.pos
      exact Nat.cast_ne_zero.mpr hpa
    rw [Nat.cast_prod, Real.log_prod hne]
    have hterm : ∀ p ∈ Nat.primesLE m,
        Real.log (((p ^ a : ℕ)) : ℝ) = (a : ℝ) * Real.log (p : ℝ) := by
      intro p hp
      rw [Nat.cast_pow, Real.log_pow]
    rw [Finset.sum_congr rfl hterm, Chebyshev.theta_eq_sum_primesLE_log,
      ← Finset.mul_sum]

/-- Bridge between `(2⁻¹)^(a+1)` and the rpow `2^(-(a+1))`. -/
private theorem inv_pow_eq_rpow_neg (a : ℕ) :
    ((2 : ℝ)⁻¹) ^ (a + 1) = (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
  have hrw : (2 : ℝ) ^ (-((a : ℝ) + 1)) = (((2 : ℝ) ^ (a + 1))⁻¹) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_natCast, pow_succ']
    ring
  rw [hrw, inv_pow]

/-- `σ₁(p^a)/p^a` equals `(1 - p^{-(a+1)})(1-1/p)⁻¹` (geometric sum). -/
private theorem sigma_prime_pow_div_eq (p a : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) =
      (1 - ((p : ℝ)⁻¹) ^ (a + 1)) * (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  have hre : ∀ k ∈ Finset.range (a + 1),
      (p : ℝ) ^ k * ((p : ℝ) ^ a)⁻¹ = ((p : ℝ)⁻¹) ^ (a - k) := by
    intro k hk
    have hka : k ≤ a := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hp0 : (p : ℝ) ≠ 0 := by
      have hne : p ≠ 0 := ne_of_gt hp.pos
      exact_mod_cast hne
    have hxk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ hp0
    have hpa : (p : ℝ) ^ a = (p : ℝ) ^ k * (p : ℝ) ^ (a - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hka]
    rw [hpa, mul_inv, ← mul_assoc, mul_inv_cancel₀ hxk, one_mul, inv_pow]
  rw [Finset.sum_congr rfl hre]
  have hreflect := Finset.sum_range_reflect (fun j => ((p : ℝ)⁻¹) ^ j) (a + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr1 : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have hne1 : (p : ℝ)⁻¹ - 1 ≠ 0 := ne_of_lt (by linarith : (p : ℝ)⁻¹ - 1 < 0)
  have hne2 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - (p : ℝ)⁻¹)
  have hgeom := geom_sum_mul ((p : ℝ)⁻¹) (a + 1)
  have hdiv : ∑ j ∈ Finset.range (a + 1), ((p : ℝ)⁻¹) ^ j =
      (((p : ℝ)⁻¹) ^ (a + 1) - 1) / ((p : ℝ)⁻¹ - 1) := by
    rw [eq_div_iff hne1]
    exact hgeom
  rw [hdiv]
  have h3 : (1 - (p : ℝ)⁻¹)⁻¹ = -(((p : ℝ)⁻¹ - 1)⁻¹) := by
    rw [show (1 : ℝ) - (p : ℝ)⁻¹ = -((p : ℝ)⁻¹ - 1) by ring, inv_neg]
  rw [h3, div_eq_mul_inv]
  ring

/-- Abundancy lower bound for the witness family. -/
private theorem sigma_div_prod_primesLE_pow_ge (m a : ℕ) :
    mertensP (m : ℝ) * (1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1))) ≤
      ((ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) : ℕ) : ℝ) /
        ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) := by
  have hpair : ((Nat.primesLE m : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun p => p ^ a) := by
    intro x hx y hy hxy
    have hxp : x.Prime := Nat.prime_of_mem_primesLE (Finset.mem_coe.mp hx)
    have hyp : y.Prime := Nat.prime_of_mem_primesLE (Finset.mem_coe.mp hy)
    have hcop : Nat.Coprime x y := (Nat.coprime_primes hxp hyp).mpr hxy
    change Nat.Coprime (x ^ a) (y ^ a)
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [pow_zero]
      exact Nat.coprime_one_left 1
    · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
      rw [Nat.coprime_pow_left_iff ha0, Nat.coprime_pow_right_iff ha0]
      exact hcop
  have hσ_prod : ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) =
      ∏ p ∈ Nat.primesLE m, ArithmeticFunction.sigma 1 (p ^ a) :=
    ArithmeticFunction.isMultiplicative_sigma.map_prod _ _ hpair
  have hdiv2 : ((ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) : ℕ) : ℝ) /
        ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) =
        ∏ p ∈ Nat.primesLE m,
          (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) /
            ((p ^ a : ℕ) : ℝ)) := by
    rw [hσ_prod]
    simp only [Nat.cast_prod]
    rw [← Finset.prod_div_distrib]
  have hδ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
    rw [← inv_pow_eq_rpow_neg]
    positivity
  have hδ10 : (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤ 1 := by
    rw [← inv_pow_eq_rpow_neg]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ ≤ 1)
  have hfac_ge : ∀ p ∈ Nat.primesLE m,
      (1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹ ≤
        ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    rw [sigma_prime_pow_div_eq p a hpp]
    have hδ : ((p : ℝ)⁻¹) ^ (a + 1) ≤ (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hle_r : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by linarith : (0 : ℝ) < (p : ℝ))
          (by norm_num : (0 : ℝ) < 2)).mpr hp2
      have h0p : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
      have h1 : ((p : ℝ)⁻¹) ^ (a + 1) ≤ ((2 : ℝ)⁻¹) ^ (a + 1) :=
        pow_le_pow_left₀ h0p hle_r (a + 1)
      rwa [inv_pow_eq_rpow_neg] at h1
    have hnonneg : (0 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      have h1 := one_le_inv_one_sub_inv_prime p hpp
      linarith
    have hle : 1 - (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤ 1 - ((p : ℝ)⁻¹) ^ (a + 1) := by
      linarith [hδ]
    exact mul_le_mul_of_nonneg_right hle hnonneg
  have hge1 : ∏ p ∈ Nat.primesLE m,
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹) ≤
      ∏ p ∈ Nat.primesLE m,
        (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) /
          ((p ^ a : ℕ) : ℝ)) :=
    prod_le_prod_of_nonneg (fun p hp => by
      have hpp := Nat.prime_of_mem_primesLE hp
      have h1 := one_le_inv_one_sub_inv_prime p hpp
      have h10 : (0 : ℝ) ≤ 1 - (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
        linarith [hδ10]
      exact mul_nonneg h10 (by linarith)) hfac_ge
  have hPm : mertensP (m : ℝ) = ∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹)⁻¹ := by
    unfold mertensP
    rw [Nat.floor_natCast]
  have hprod_split : ∏ p ∈ Nat.primesLE m,
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹) =
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) *
          mertensP (m : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hPm]
  have hbern : ∀ n : ℕ, 1 - (n : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤
      (1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ n := by
    intro n
    have h := one_add_mul_le_pow (a := -((2 : ℝ) ^ (-((a : ℝ) + 1))))
      (show (-2 : ℝ) ≤ -((2 : ℝ) ^ (-((a : ℝ) + 1))) from by
        linarith [hδ0, hδ10]) n
    have e1 : (1 : ℝ) - (n : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) =
        1 + (n : ℝ) * -((2 : ℝ) ^ (-((a : ℝ) + 1))) := by ring
    have e2 : ((1 : ℝ) - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ n =
        (1 + -((2 : ℝ) ^ (-((a : ℝ) + 1)))) ^ n := by rw [sub_eq_add_neg]
    rwa [e1, e2]
  have hcard : (Nat.primesLE m).card ≤ m := by
    have hsub : Nat.primesLE m ⊆ Finset.Icc 1 m := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesLE hp
      rw [Nat.mem_primesLE] at hp
      rw [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, hp.1⟩
    calc (Nat.primesLE m).card ≤ (Finset.Icc 1 m).card :=
          Finset.card_le_card hsub
      _ = m := by rw [Nat.card_Icc]; omega
  have hbern_m : 1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤
      (1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card := by
    have h1 := hbern (Nat.primesLE m).card
    have hcardR : (((Nat.primesLE m).card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hcard
    have hmul : ((Nat.primesLE m).card : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤
        (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hcardR hδ0
    linarith [h1, hmul]
  have hP0 : 0 ≤ mertensP (m : ℝ) := (mertensP_pos _).le
  have hmul_le : mertensP (m : ℝ) * (1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1))) ≤
      mertensP (m : ℝ) *
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) :=
    mul_le_mul_of_nonneg_left hbern_m hP0
  calc mertensP (m : ℝ) * (1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)))
      ≤ mertensP (m : ℝ) *
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) := hmul_le
    _ = ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) *
        mertensP (m : ℝ) := mul_comm _ _
    _ = ∏ p ∈ Nat.primesLE m,
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹) :=
        hprod_split.symm
    _ ≤ ∏ p ∈ Nat.primesLE m,
        (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) /
          ((p ^ a : ℕ) : ℝ)) := hge1
    _ = ((ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) : ℕ) : ℝ) /
        ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) := hdiv2.symm

/-- `log n → ∞` along naturals. -/
private theorem tendsto_log_natCast_atTop : Filter.Tendsto
    (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `2 ≤ log 16`, since `log 16 = 4 log 2`. -/
private theorem two_le_log_sixteen : (2 : ℝ) ≤ Real.log 16 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h16e : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h16e, Real.log_pow]
    norm_num
  linarith

/-- The error exponent `log n / ((log n - 1) * log log n) -> 0`. -/
private theorem tendsto_gronwall_err : Filter.Tendsto
    (fun n : ℕ => Real.log (n : ℝ) /
      ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))))
    Filter.atTop (nhds 0) := by
  have htop : Filter.Tendsto (fun n : ℕ => 2 / Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (Real.tendsto_log_atTop.comp tendsto_log_natCast_atTop) 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hy2 : (2 : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans two_le_log_sixteen (Real.log_le_log (by norm_num) hn16)
    have hlogy : (0 : ℝ) < Real.log (Real.log (n : ℝ)) :=
      Real.log_pos (by linarith)
    have hden : (0 : ℝ) ≤
        (Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ)) :=
      mul_nonneg (by linarith) hlogy.le
    exact div_nonneg (Real.log_nonneg (by linarith)) hden
  · filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hy2 : (2 : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans two_le_log_sixteen (Real.log_le_log (by norm_num) hn16)
    have hlogy : (0 : ℝ) < Real.log (Real.log (n : ℝ)) :=
      Real.log_pos (by linarith)
    have h1 : Real.log (n : ℝ) / (Real.log (n : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (show (0 : ℝ) < Real.log (n : ℝ) - 1 by linarith)]
      linarith
    have h2 : Real.log (n : ℝ) /
        ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))) =
        (Real.log (n : ℝ) / (Real.log (n : ℝ) - 1)) /
          Real.log (Real.log (n : ℝ)) := by
      rw [div_div]
    rw [h2, div_le_div_iff_of_pos_right hlogy]
    exact h1

-- Eventual upper bound for Gronwall's f.
private theorem gronwall_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (Real.log n)) ≤
        Real.exp Real.eulerMascheroniConstant + ε := by
  have hP : Filter.Tendsto
      (fun n : ℕ => mertensP (Real.log n) / Real.log (Real.log n))
      Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) :=
    tendsto_mertensP_div_log.comp tendsto_log_natCast_atTop
  have hexp : Filter.Tendsto
      (fun n : ℕ => Real.exp (Real.log (n : ℝ) /
        ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ)))))
      Filter.atTop (nhds 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp tendsto_gronwall_err
    rwa [Real.exp_zero] at h
  have hprod := hP.mul hexp
  rw [mul_one] at hprod
  have hev := hprod.eventually_le_const
    (show Real.exp Real.eulerMascheroniConstant <
      Real.exp Real.eulerMascheroniConstant + ε by linarith)
  filter_upwards [hev, Filter.eventually_ge_atTop 16] with n hle hn16
  have hn16r : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn16
  have hn1 : 1 ≤ n := by omega
  have hy2 : (2 : ℝ) ≤ Real.log (n : ℝ) :=
    le_trans two_le_log_sixteen (Real.log_le_log (by norm_num) hn16r)
  have hlogy : (0 : ℝ) < Real.log (Real.log (n : ℝ)) :=
    Real.log_pos (by linarith)
  have hN11 := sigma_div_self_le_mertensP_mul_exp n hn1 (Real.log n) hy2
  have hdiv : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
      ((n : ℝ) * Real.log (Real.log n)) =
      (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) /
        Real.log (Real.log n) := by
    rw [div_div]
  rw [hdiv]
  have hle2 : ((((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) /
      Real.log (Real.log n)) ≤
      ((mertensP (Real.log n) *
        Real.exp (Real.log (n : ℝ) /
          ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))))) /
        Real.log (Real.log n)) := by
    rw [div_le_div_iff_of_pos_right hlogy]
    exact hN11
  have hmul : (mertensP (Real.log n) *
      Real.exp (Real.log (n : ℝ) /
        ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))))) /
      Real.log (Real.log n) =
      (mertensP (Real.log n) / Real.log (Real.log n)) *
        Real.exp (Real.log (n : ℝ) /
          ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ)))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hmul] at hle2
  exact hle2.trans hle

/-- Witness `n_k = prod_{p <= 2^k} p^{2k}`. -/
private noncomputable def gronwallWit (k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)

/-- `2` is in `primesLE (2^k)` for `k >= 1`. -/
private theorem gronwallWit_mem_two (k : ℕ) (hk : 1 ≤ k) :
    2 ∈ Nat.primesLE (2 ^ k) := by
  rw [Nat.mem_primesLE]
  refine ⟨?_, Nat.prime_two⟩
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk

/-- `2^{2k} <= n_k` for `k >= 1`, by `single_le_prod`. -/
private theorem gronwallWit_pow_le (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (2 * k) ≤ gronwallWit k := by
  unfold gronwallWit
  exact Finset.single_le_prod
    (fun i hi => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesLE hi).pos)
    (gronwallWit_mem_two k hk)

/-- Every witness is at least `1`. -/
private theorem gronwallWit_ge_one (k : ℕ) : 1 ≤ gronwallWit k := by
  unfold gronwallWit
  exact Finset.one_le_prod
    (fun i hi => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesLE hi).pos)

/-- `(2^k : R) -> infinity`. -/
private theorem tendsto_two_pow_natCast_atTop : Filter.Tendsto
    (fun k : ℕ => (((2 ^ k : ℕ)) : ℝ)) Filter.atTop Filter.atTop := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)

/-- The witness correction factor equals `2^(-(k+1))`. -/
private theorem gronwallWit_corr_eq (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ) * (2 : ℝ) ^ (-(((2 * k : ℕ) : ℝ) + 1)) =
      (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1)) := by
  have h1 : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (((k : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_ofNat]
  rw [h1, ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

/-- `2^(-(k+1)) -> 0`. -/
private theorem tendsto_rpow_neg_add_one : Filter.Tendsto
    (fun k : ℕ => (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) Filter.atTop (nhds 0) := by
  have heq : ∀ k : ℕ, (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1)) =
      1 / (2 * (2 : ℝ) ^ (k : ℕ)) := by
    intro k
    rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_natCast, one_div]
    congr 1
    ring
  have hlim : Filter.Tendsto (fun k : ℕ => 1 / (2 * (2 : ℝ) ^ (k : ℕ)))
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.const_div_atTop _ 1
    exact Filter.Tendsto.const_mul_atTop (by norm_num)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have heqEv : (fun k : ℕ => 1 / (2 * (2 : ℝ) ^ (k : ℕ))) =ᶠ[Filter.atTop]
      (fun k : ℕ => (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) :=
    Filter.Eventually.of_forall (fun k => (heq k).symm)
  exact Filter.Tendsto.congr' heqEv hlim

/-- The witness tends to infinity. -/
private theorem tendsto_gronwallWit_atTop : Filter.Tendsto
    (fun k : ℕ => ((gronwallWit k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun k => ?_)
    tendsto_two_pow_natCast_atTop
  rcases eq_or_ne k 0 with rfl | hk0
  · simp only [pow_zero, Nat.cast_one]
    exact_mod_cast gronwallWit_ge_one 0
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have h1 : (2 ^ k : ℕ) ≤ 2 ^ (2 * k) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 ^ (2 * k) : ℕ) ≤ gronwallWit k := gronwallWit_pow_le k hk
    exact_mod_cast le_trans h1 h2

/-- `log (2^k) = k * log 2` for naturals. -/
private theorem gronwall_log_two_pow (k : ℕ) :
    Real.log (((2 ^ k : ℕ)) : ℝ) = (k : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- `1 < log (wit k)` for `k ≥ 1`, from `wit k ≥ 2 ^ (2k)`. -/
private theorem gronwallWit_log_gt_one (k : ℕ) (hk : 1 ≤ k) :
    1 < Real.log (gronwallWit k : ℝ) := by
  have hle : (2 : ℝ) ^ (2 * k) ≤ (gronwallWit k : ℝ) := by
    have h := gronwallWit_pow_le k hk
    calc (2 : ℝ) ^ (2 * k) = (((2 ^ (2 * k) : ℕ)) : ℝ) := by
            rw [Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ ((gronwallWit k : ℕ) : ℝ) := by exact_mod_cast h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hle
  rw [Real.log_pow] at hlog
  have hcast : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hcast] at hlog
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hbase : (1 : ℝ) < 2 * Real.log 2 := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmono : 2 * Real.log 2 ≤ 2 * (k : ℝ) * Real.log 2 := by
    calc 2 * Real.log 2 = (2 * Real.log 2) * 1 := by ring
      _ ≤ (2 * Real.log 2) * (k : ℝ) :=
          mul_le_mul_of_nonneg_left hk1 (by linarith)
      _ = 2 * (k : ℝ) * Real.log 2 := by ring
  linarith

/-- `log log (wit k) ≤ log (2k log 4) + k log 2` for `k ≥ 1`, via `θ`. -/
private theorem gronwallWit_loglog_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (Real.log (gronwallWit k : ℝ)) ≤
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
  have hgt := gronwallWit_log_gt_one k hk
  have hlog_eq := (prod_primesLE_pow_ge_one_log (2 ^ k) (2 * k)).2
  have hwit : (∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)) = gronwallWit k := rfl
  rw [hwit] at hlog_eq
  have hθ := Chebyshev.theta_le_log4_mul_x
    (show (0 : ℝ) ≤ (((2 ^ k : ℕ)) : ℝ) from Nat.cast_nonneg _)
  have hcast : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hcast] at hlog_eq
  have hm0 : (0 : ℝ) < (((2 ^ k : ℕ)) : ℝ) := by
    exact_mod_cast pow_pos (show (0 : ℕ) < 2 by norm_num) k
  have hle1 : Real.log (gronwallWit k : ℝ) ≤
      (2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ)) := by
    rw [hlog_eq]
    exact mul_le_mul_of_nonneg_left hθ (by
      have hkk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith)
  have hpos1 : (0 : ℝ) < 2 * (k : ℝ) * Real.log 4 := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    exact mul_pos (mul_pos (by norm_num) hk0) h4
  have hle2 : Real.log (Real.log (gronwallWit k : ℝ)) ≤
      Real.log ((2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ))) :=
    Real.log_le_log (by linarith) hle1
  have hsplit : Real.log ((2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ))) =
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
    have heq : (2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ)) =
        (2 * (k : ℝ) * Real.log 4) * (((2 ^ k : ℕ)) : ℝ) := by ring
    rw [heq, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hm0),
      gronwall_log_two_pow]
  rwa [hsplit] at hle2

/-- `σ(wit k) / wit k ≥ P(2^k) * (1 - 2 ^ (-(k+1)))`. -/
private theorem gronwallWit_sigma_div_ge (k : ℕ) :
    mertensP (((2 ^ k : ℕ)) : ℝ) * (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) ≤
      ((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
        ((gronwallWit k : ℕ) : ℝ) := by
  have hN12 := sigma_div_prod_primesLE_pow_ge (2 ^ k) (2 * k)
  have hwit : (∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)) = gronwallWit k := rfl
  rw [hwit, gronwallWit_corr_eq] at hN12
  exact hN12

/-- `f(wit k)` is at least the three-factor product. -/
private theorem gronwallWit_f_ge (k : ℕ) (hk : 1 ≤ k) :
    (mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ)) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
        (Real.log (((2 ^ k : ℕ)) : ℝ) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) ≤
      ((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
        (((gronwallWit k : ℕ) : ℝ) * Real.log (Real.log (gronwallWit k : ℝ))) := by
  have hσ := gronwallWit_sigma_div_ge k
  have hgt := gronwallWit_log_gt_one k hk
  have hU := gronwallWit_loglog_le k hk
  have hlogm : Real.log (((2 ^ k : ℕ)) : ℝ) = (k : ℝ) * Real.log 2 :=
    gronwall_log_two_pow k
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogm_pos : (0 : ℝ) < Real.log (((2 ^ k : ℕ)) : ℝ) := by
    rw [hlogm]
    exact mul_pos hk0 hlog2
  have hll_pos : (0 : ℝ) < Real.log (Real.log (gronwallWit k : ℝ)) :=
    Real.log_pos hgt
  have hU_pos : (0 : ℝ) <
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
    linarith
  have hσ0 : (0 : ℝ) ≤ ((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
      ((gronwallWit k : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hstep : mertensP (((2 ^ k : ℕ)) : ℝ) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) ≤
      (((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
        ((gronwallWit k : ℕ) : ℝ)) /
        Real.log (Real.log (gronwallWit k : ℝ)) := by
    have h1 : mertensP (((2 ^ k : ℕ)) : ℝ) *
          (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) ≤
        (((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
          ((gronwallWit k : ℕ) : ℝ)) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) :=
      (div_le_div_iff_of_pos_right hU_pos).mpr hσ
    have h2 : ((((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
          ((gronwallWit k : ℕ) : ℝ)) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) ≤
        (((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
          ((gronwallWit k : ℕ) : ℝ)) /
          Real.log (Real.log (gronwallWit k : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ hU_pos hll_pos).mpr hU) hσ0
    exact h1.trans h2
  have hid : (mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ)) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
        (Real.log (((2 ^ k : ℕ)) : ℝ) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) =
      mertensP (((2 ^ k : ℕ)) : ℝ) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) := by
    have h1 : Real.log (((2 ^ k : ℕ)) : ℝ) ≠ 0 := ne_of_gt hlogm_pos
    have h2 : Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 ≠ 0 :=
      ne_of_gt hU_pos
    field_simp
  rw [hid, ← div_div]
  exact hstep

/-- `log k / k → 0` along naturals. -/
private theorem gronwall_log_div_nat_tendsto : Filter.Tendsto
    (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) Filter.atTop (nhds 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop

/-- The constant part `log (2 log 4) / k → 0`. -/
private theorem gronwall_const_div_nat_tendsto :
    Filter.Tendsto (fun k : ℕ => Real.log (2 * Real.log 4) / (k : ℝ))
      Filter.atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

/-- `log (2k log 4) / k → 0`. -/
private theorem gronwall_Ck_div_tendsto : Filter.Tendsto
    (fun k : ℕ => Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ))
    Filter.atTop (nhds 0) := by
  have hsplit : (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ) +
      Real.log (2 * Real.log 4) / (k : ℝ)) =ᶠ[Filter.atTop]
      (fun k : ℕ => Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h4 : (2 : ℝ) * Real.log 4 ≠ 0 :=
      mul_ne_zero (by norm_num) (Real.log_ne_zero_of_pos_of_ne_one
        (by norm_num) (by norm_num))
    have heq : Real.log (2 * (k : ℝ) * Real.log 4) =
        Real.log (k : ℝ) + Real.log (2 * Real.log 4) := by
      rw [show 2 * (k : ℝ) * Real.log 4 = (k : ℝ) * (2 * Real.log 4) by ring,
        Real.log_mul hk0 h4]
    rw [heq, add_div]
  have h := gronwall_log_div_nat_tendsto.add gronwall_const_div_nat_tendsto
  rw [add_zero] at h
  exact Filter.Tendsto.congr' hsplit h

/-- `k log 2 / (log (2k log 4) + k log 2) → 1`. -/
private theorem gronwall_logwit_ratio_tendsto : Filter.Tendsto
    (fun k : ℕ => (k : ℝ) * Real.log 2 /
      (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2))
    Filter.atTop (nhds 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hconst : Filter.Tendsto (fun _ : ℕ => Real.log 2)
      Filter.atTop (nhds (Real.log 2)) := tendsto_const_nhds
  have hden : Filter.Tendsto
      (fun k : ℕ => Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
    have h := hconst.add gronwall_Ck_div_tendsto
    rwa [add_zero] at h
  have hdiv := hconst.div hden hlog2.ne'
  rw [div_self hlog2.ne'] at hdiv
  have hdiv' : Filter.Tendsto
      (fun k : ℕ => Real.log 2 /
        (Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)))
      Filter.atTop (nhds 1) := hdiv
  refine Filter.Tendsto.congr' ?_ hdiv'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hCk0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) * Real.log 4) := by
    apply Real.log_nonneg
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog4 : (1 : ℝ) ≤ 2 * Real.log 4 := by
      have h16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
        have h16e : (16 : ℝ) = 4 ^ 2 := by norm_num
        rw [h16e, Real.log_pow]
        norm_num
      have h2 := two_le_log_sixteen
      linarith
    have h1k : (1 : ℝ) ≤ (k : ℝ) * (2 * Real.log 4) := by
      calc (1 : ℝ) ≤ 2 * Real.log 4 := hlog4
        _ = (2 * Real.log 4) * 1 := by ring
        _ ≤ (2 * Real.log 4) * (k : ℝ) :=
            mul_le_mul_of_nonneg_left hk1 (by linarith)
        _ = (k : ℝ) * (2 * Real.log 4) := by ring
    have heq : 2 * (k : ℝ) * Real.log 4 = (k : ℝ) * (2 * Real.log 4) := by ring
    rwa [heq]
  have hUpos : (0 : ℝ) <
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
    have hpos : (0 : ℝ) < (k : ℝ) * Real.log 2 :=
      mul_pos (by exact_mod_cast (by omega : 0 < k)) hlog2
    linarith
  have hU0 : Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 ≠ 0 :=
    ne_of_gt hUpos
  have hden0 : Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ) ≠ 0 := by
    have hdiv0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ) :=
      div_nonneg hCk0 (Nat.cast_nonneg _)
    have hpos : (0 : ℝ) < Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ) := by
      linarith
    exact ne_of_gt hpos
  rw [div_eq_div_iff hden0 hU0]
  have hcancel : (k : ℝ) * (Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)) =
      Real.log (2 * (k : ℝ) * Real.log 4) :=
    mul_div_cancel₀ _ hk0
  rw [mul_add, mul_add,
    show (k : ℝ) * Real.log 2 * (Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)) =
      Real.log 2 * ((k : ℝ) * (Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ))) by
      ring,
    hcancel]
  ring

/-- Mertens' third theorem along `2 ^ k`. -/
private theorem gronwall_mertens_two_pow_tendsto : Filter.Tendsto
    (fun k : ℕ => mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ))
    Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) :=
  tendsto_mertensP_div_log.comp tendsto_two_pow_natCast_atTop

/-- The correction `1 - 2 ^ (-(k+1)) → 1`. -/
private theorem gronwall_corr_tendsto : Filter.Tendsto
    (fun k : ℕ => 1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1)))
    Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have h := h1.sub tendsto_rpow_neg_add_one
  rwa [sub_zero] at h

/-- The lower-bound product tends to `exp γ`. -/
private theorem gronwall_g_tendsto : Filter.Tendsto
    (fun k : ℕ => (mertensP (((2 ^ k : ℕ)) : ℝ) /
        Real.log (((2 ^ k : ℕ)) : ℝ)) *
      (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
      (Real.log (((2 ^ k : ℕ)) : ℝ) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)))
    Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h3 : Filter.Tendsto
      (fun k : ℕ => Real.log (((2 ^ k : ℕ)) : ℝ) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2))
      Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ gronwall_logwit_ratio_tendsto
    filter_upwards with k
    rw [gronwall_log_two_pow]
  have h := (gronwall_mertens_two_pow_tendsto.mul gronwall_corr_tendsto).mul h3
  rw [mul_one, mul_one] at h
  exact h

private theorem gronwall_frequently_ge (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in Filter.atTop,
      Real.exp Real.eulerMascheroniConstant - ε ≤
        ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n)) := by
  rw [Filter.frequently_atTop]
  intro N
  have hwit_top : Filter.Tendsto gronwallWit Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp tendsto_gronwallWit_atTop
  have hevW : ∀ᶠ k : ℕ in Filter.atTop, N ≤ gronwallWit k :=
    hwit_top.eventually_ge_atTop N
  have hev1 : ∀ᶠ k : ℕ in Filter.atTop, 1 ≤ k := Filter.eventually_ge_atTop 1
  have hev2 : ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp Real.eulerMascheroniConstant - ε ≤
        (mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ)) *
          (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
          (Real.log (((2 ^ k : ℕ)) : ℝ) /
            (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) := by
    have hlt : Real.exp Real.eulerMascheroniConstant - ε <
        Real.exp Real.eulerMascheroniConstant := by linarith
    have h := gronwall_g_tendsto.eventually (Ioi_mem_nhds hlt)
    filter_upwards [h] with k hk
    exact (Set.mem_Ioi.mp hk).le
  obtain ⟨k, hk1, hkN, hkg⟩ := (hev1.and (hevW.and hev2)).exists
  refine ⟨gronwallWit k, hkN, ?_⟩
  exact le_trans hkg (gronwallWit_f_ge k hk1)

/--
**Gronwall's theorem.** Let $\sigma(n)$ be the sum of the positive divisors of $n$ and let
$\gamma$ be the Euler–Mascheroni constant. Then, as $n$ runs over the natural numbers,
$\limsup_{n \to \infty} \sigma(n) / (n \log \log n) = e^{\gamma}$.

The quotient is read with the conventions $\log 0 = 0$ and $x/0 = 0$, so it is defined for every
natural number $n$; the finitely many $n \le 2$ with $n \log \log n \le 0$ do not affect the
limit superior.

Proves `Wanted` entry `gronwall_sigma_limsup`.

Source: S. Nazardonyavi and S. Yakubovich,
"Extremely Abundant Numbers and the Riemann Hypothesis," Journal of Integer Sequences 17
(2014), Article 14.2.8, lines 98–111,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex (live source SHA-256
`6854eacdc72e1e5a005b005552942d6d7cfa7a41d7892c0f61bb2b1886e1d7c5`); original
attribution: T. H. Gronwall, "Some asymptotic expressions in the theory of numbers,"
Transactions of the AMS 14 (1913), 113–122.
-/
theorem gronwall_sigma_limsup :
    Filter.limsup
      (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (Real.log n))) Filter.atTop =
      Real.exp Real.eulerMascheroniConstant := by
  apply le_antisymm
  · -- Upper: limsup ≤ exp γ + ε for every ε > 0 (eventual upper bound + frequent lower bound).
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcob : Filter.IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) Filter.atTop
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) :=
      Filter.IsCoboundedUnder.of_frequently_ge
        (gronwall_frequently_ge 1 one_pos)
    have hev := gronwall_eventually_le ε hε
    have hle : Filter.limsup
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) Filter.atTop ≤
        Real.exp Real.eulerMascheroniConstant + ε :=
      Filter.limsup_le_of_le hcob hev
    exact hle
  · -- Lower: exp γ - ε ≤ limsup for every ε > 0 (frequent lower bound + eventual boundedness).
    apply le_of_forall_pos_le_add
    intro ε hε
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) Filter.atTop
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) :=
      Filter.isBoundedUnder_of_eventually_le
        (gronwall_eventually_le 1 one_pos)
    have hfreq := gronwall_frequently_ge ε hε
    have hle : Real.exp Real.eulerMascheroniConstant - ε ≤ Filter.limsup
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) Filter.atTop :=
      Filter.le_limsup_of_frequently_le hfreq hbdd
    linarith

end MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted
end

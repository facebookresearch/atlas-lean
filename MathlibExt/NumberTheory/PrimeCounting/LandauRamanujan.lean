/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Floor.Semifield

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumTwoSquares
import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

namespace MetaMathlibExt

open Asymptotics Filter Finset Nat Chebyshev ArithmeticFunction
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Indicator of positive integers with no prime factor `≡ 3 mod 4`. -/
private noncomputable def lrH (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 then 1 else 0

/-- Indicator of positive integers all of whose prime factors are `≡ 3 mod 4`. -/
private noncomputable def lrG (k : ℕ) : ℝ :=
  if k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 then 1 else 0

private lemma lrH_zero : lrH 0 = 0 := by simp [lrH]

private lemma lrG_zero : lrG 0 = 0 := by simp [lrG]

private lemma lrH_one : lrH 1 = 1 := by simp [lrH]

private lemma lrG_one : lrG 1 = 1 := by simp [lrG]

private lemma lrH_nonneg (n : ℕ) : 0 ≤ lrH n := by
  unfold lrH
  split_ifs <;> norm_num

private lemma lrH_le_one (n : ℕ) : lrH n ≤ 1 := by
  unfold lrH
  split_ifs <;> norm_num

private lemma lrG_nonneg (k : ℕ) : 0 ≤ lrG k := by
  unfold lrG
  split_ifs <;> norm_num

private lemma lrG_le_one (k : ℕ) : lrG k ≤ 1 := by
  unfold lrG
  split_ifs <;> norm_num

private lemma lrH_mul (m n : ℕ) : lrH (m * n) = lrH m * lrH n := by
  by_cases hm : m = 0
  · subst hm
    simp [lrH_zero]
  · by_cases hn : n = 0
    · subst hn
      simp [lrH_zero]
    · have hU : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
        Nat.primeFactors_mul hm hn
      have hIff : (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, p % 4 ≠ 3) ↔
          (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p % 4 ≠ 3) ∧
          (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3) := by
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
      simp only [lrH, hIff]
      split_ifs with h1 h2 h3 <;> simp_all

private lemma lrH_log_eq {n : ℕ} (hn : 1 ≤ n) :
    lrH n * Real.log n
      = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d) := by
  have hn0 : n ≠ 0 := by omega
  have hterm : ∀ d ∈ n.divisors,
      ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d)
        = ArithmeticFunction.vonMangoldt d * lrH n := by
    intro d hd
    have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
    have hmul : lrH d * lrH (n / d) = lrH n := by
      rw [← lrH_mul, hdeq]
    calc ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d)
        = ArithmeticFunction.vonMangoldt d * (lrH d * lrH (n / d)) := by ring
      _ = ArithmeticFunction.vonMangoldt d * lrH n := by rw [hmul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ArithmeticFunction.vonMangoldt_sum, mul_comm]

private lemma lrH_log_div_eq {n : ℕ} (hn : 1 ≤ n) :
    lrH n * Real.log n / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
        (lrH (n / d) / ((n / d : ℕ) : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  rw [lrH_log_eq hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
  have hcast : (d : ℝ) * (((n / d : ℕ)) : ℝ) = (n : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdeq
    rwa [Nat.cast_mul] at h
  have e : (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
      (lrH (n / d) / (((n / d : ℕ)) : ℝ))
      = (ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d)) /
        ((d : ℝ) * (((n / d : ℕ)) : ℝ)) := by
    ring
  rw [e, hcast]

private lemma lr_sum_swap (F G : ℕ → ℝ) (hF : F 0 = 0) (hG : G 0 = 0)
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

/-- `H(x)`: count of `n ≤ x` with `lrH n = 1`. -/
private noncomputable def lrCount (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n

/-- `A(x)`: reciprocal sum of `lrH` over `n ≤ x`. -/
private noncomputable def lrA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ)

/-- `ψ_h(y)`: von Mangoldt sum restricted by `lrH`. -/
private noncomputable def lrPsi (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * lrH d

/-- `M(y)`: reciprocal Mertens sum restricted by `lrH`. -/
private noncomputable def lrMert (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)

/-- `J(x)`: log-weighted reciprocal sum. -/
private noncomputable def lrJ (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ))

private lemma lr_L_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * lrPsi (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * lrH d) 0 = 0 := by
    simp [lrH_zero]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d) * lrH (n / d) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [lrH_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact lrH_log_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d) * lrH (n / d) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, ArithmeticFunction.vonMangoldt d * lrH d :=
        lr_sum_swap _ _ hF lrH_zero x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * lrPsi (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [lrPsi]

private lemma lr_logA_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) 0 = 0 := by
    simp [lrH_zero]
  have hG : (fun m : ℕ => lrH m / (m : ℝ)) 0 = 0 := by
    simp [lrH_zero]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
        (lrH (n / d) / (((n / d : ℕ)) : ℝ)) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [lrH_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact lrH_log_div_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
        (lrH (n / d) / (((n / d : ℕ)) : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ) :=
        lr_sum_swap (fun d : ℕ => ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ))
          (fun m : ℕ => lrH m / (m : ℝ)) hF hG x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [lrMert]

private lemma lrCount_nonneg (x : ℝ) : 0 ≤ lrCount x :=
  Finset.sum_nonneg fun n _ => lrH_nonneg n

private lemma lrA_nonneg (x : ℝ) : 0 ≤ lrA x := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)

private lemma lrPsi_nonneg (y : ℝ) : 0 ≤ lrPsi y := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (lrH_nonneg d)

private lemma lrA_mono : Monotone lrA := by
  intro x y hxy
  simp only [lrA]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · intro n _ _
    exact div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)

private lemma lrA_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ lrA x := by
  have h1 : 1 ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    rw [Finset.mem_Ioc]
    exact ⟨by omega, (Nat.one_le_floor_iff x).mpr hx⟩
  have h := Finset.single_le_sum
    (fun n _ => div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)) h1
  simpa [lrH_one, lrA] using h

private lemma lrCount_le {y : ℝ} (hy : 0 ≤ y) : lrCount y ≤ y := by
  calc lrCount y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n := rfl
    _ ≤ ∑ _n ∈ Finset.Ioc 0 ⌊y⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => lrH_le_one n
    _ = (⌊y⌋₊ : ℝ) := by simp [Finset.sum_const, Nat.card_Ioc]
    _ ≤ y := Nat.floor_le hy

private lemma lrPsi_le_psi (y : ℝ) : lrPsi y ≤ Chebyshev.psi y := by
  simp only [lrPsi, Chebyshev.psi]
  apply Finset.sum_le_sum
  intro d _
  calc ArithmeticFunction.vonMangoldt d * lrH d
      ≤ ArithmeticFunction.vonMangoldt d * 1 :=
        mul_le_mul_of_nonneg_left (lrH_le_one d)
          ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt d := mul_one _

private lemma lrPsi_le_mul_self {y : ℝ} (hy : 0 ≤ y) :
    lrPsi y ≤ (Real.log 4 + 4) * y :=
  le_trans (lrPsi_le_psi y) (Chebyshev.psi_le_const_mul_self hy)

/-- `lrH` on a prime is determined by the residue of the prime mod 4. -/
private lemma lrH_prime_eq {p : ℕ} (hp : p.Prime) :
    lrH p = if p % 4 = 3 then 0 else 1 := by
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
  unfold lrH
  by_cases h : p % 4 = 3
  · rw [ite_eq_left h, ite_eq_right]
    intro hc
    exact hc.2 p ((hmem p).mpr rfl) h
  · rw [ite_eq_right h, ite_eq_left]
    exact ⟨hp.ne_zero, fun q hq => by rw [(hmem q).mp hq]; exact h⟩

/-- The residue-class von Mangoldt function as an `if`. -/
private lemma lr_residueClass_eq (d : ℕ) :
    ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d
      = if (d : ZMod 4) = 1 then ArithmeticFunction.vonMangoldt d else 0 := by
  change Set.indicator {n : ℕ | (n : ZMod 4) = (1 : ZMod 4)} _ _ = _
  split_ifs with h
  · have hm : d ∈ {n : ℕ | (n : ZMod 4) = (1 : ZMod 4)} := h
    exact Set.indicator_of_mem hm _
  · have hm : d ∉ {n : ℕ | (n : ZMod 4) = (1 : ZMod 4)} := h
    exact Set.indicator_of_notMem hm _

/-- Pointwise comparison of `Λ · lrH ·` with the residue class of `1 mod 4`. -/
private lemma lr_resid_diff_le (d : ℕ) :
    |ArithmeticFunction.vonMangoldt d * lrH d -
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d|
      ≤ (if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d) := by
  by_cases h2 : d = 2
  · subst h2
    have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hH : lrH 2 = 1 := by
      rw [lrH_prime_eq Nat.prime_two, ite_eq_right (by decide)]
    have hr : ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) 2 = 0 := by
      rw [lr_residueClass_eq, ite_eq_right (by decide)]
    rw [hΛ, hH, hr, ite_eq_left rfl, ite_eq_left Nat.prime_two, mul_one, sub_zero,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
    exact le_add_of_nonneg_right le_rfl
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
        have hΛr : ArithmeticFunction.vonMangoldt d * lrH d
            = ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d := by
          rw [lr_residueClass_eq, lrH_prime_eq hp]
          rcases hmod with h1 | h3
          · have hc : (d : ZMod 4) = 1 := by
              rw [hcast, h1]
              simp
            rw [ite_eq_right (by omega : d % 4 ≠ 3), ite_eq_left hc, mul_one]
          · have hc : (d : ZMod 4) ≠ 1 := by
              rw [hcast, h3]
              decide
            rw [ite_eq_left h3, ite_eq_right hc, mul_zero]
        rw [hΛr, sub_self, abs_zero, ite_eq_right h2, ite_eq_left hp]
        norm_num
    · -- `d` is not prime: both terms lie in `[0, Λ d]`.
      rw [ite_eq_right h2, ite_eq_right hp]
      have ha0 : 0 ≤ ArithmeticFunction.vonMangoldt d * lrH d :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (lrH_nonneg d)
      have ha1 : ArithmeticFunction.vonMangoldt d * lrH d
          ≤ ArithmeticFunction.vonMangoldt d := by
        calc ArithmeticFunction.vonMangoldt d * lrH d
            ≤ ArithmeticFunction.vonMangoldt d * 1 :=
              mul_le_mul_of_nonneg_left (lrH_le_one d)
                ArithmeticFunction.vonMangoldt_nonneg
          _ = ArithmeticFunction.vonMangoldt d := mul_one _
      have hb0 : 0 ≤ ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d :=
        ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _
      have hb1 : ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d
          ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt.residueClass_le _ _
      rw [abs_le]
      constructor <;> linarith

/-- For `t ≥ 1`, `log t` is at most four times `t ^ (1/4 : ℝ)`. -/
private lemma lr_log_le_four_rpow (t : ℝ) (ht : 1 ≤ t) :
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
private lemma lr_two_sqrt_mul_log_le (t : ℝ) (ht : 1 ≤ t) :
    2 * Real.sqrt t * Real.log t ≤ 8 * t ^ (3/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog := lr_log_le_four_rpow t ht
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
private lemma lr_psi_sub_theta_div_le (t : ℝ) (ht : 1 ≤ t) :
    (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 ≤ 8 * t ^ (-5/4 : ℝ) := by
  have hnn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hle := Chebyshev.psi_sub_theta_le ht
  have hnum := lr_two_sqrt_mul_log_le t ht
  calc (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
      ≤ (8 * t ^ (3/4 : ℝ)) / t ^ 2 :=
        div_le_div_of_nonneg_right (le_trans hle hnum) (sq_nonneg t)
    _ = 8 * t ^ (-5/4 : ℝ) := by
      rw [← Real.rpow_natCast t 2, mul_div_assoc,
        ← Real.rpow_sub (lt_of_lt_of_le zero_lt_one ht)]
      congr 1
      norm_num

/-- Monotonicity of `ψ - θ` (a sum of nonnegative terms over a growing set). -/
private lemma lr_psi_sub_theta_mono :
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
private lemma lr_sum_not_prime_le :
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
    have hnum := lr_two_sqrt_mul_log_le y hy
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
    · exact ((lr_psi_sub_theta_mono.measurable.div
        (measurable_id.pow_const 2)).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.mem_Ioc] at ht
      have ht1 : 1 ≤ t := le_of_lt ht.1
      have hnn : 0 ≤ (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
        apply div_nonneg _ (sq_nonneg t)
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
        exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
      have hle := lr_psi_sub_theta_div_le t ht1
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
      (fun t ht => lr_psi_sub_theta_div_le t (le_of_lt (Set.mem_Ioc.mp ht).1))
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

/-- Mertens bound for the `lrH`-restricted reciprocal sum. -/
private lemma lr_mertens :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → |lrMert y - 1 / 2 * Real.log y| ≤ C := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  obtain ⟨C₁, hC₁⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le
    (q := 4) (1 : ZMod 4) isUnit_one
  obtain ⟨C₂, hC₂⟩ := lr_sum_not_prime_le
  have hφ : Nat.totient 4 = 2 := by decide
  refine ⟨C₁ + (Real.log 2 / 2 + C₂), fun y hy => ?_⟩
  have hmain : ∀ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ)|
      ≤ (if d = 2 then Real.log 2 / 2 else 0) +
        (if d.Prime then (0 : ℝ)
          else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Ioc.mp hd).1
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have h := lr_resid_diff_le d
    have hdiv : |(ArithmeticFunction.vonMangoldt d * lrH d -
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ)|
        = |ArithmeticFunction.vonMangoldt d * lrH d -
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d| / (d : ℝ) := by
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
      |(ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ)|
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
  have hrfl : lrMert y =
      ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ) := rfl
  have hdiff_sum : (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) -
      (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        (ArithmeticFunction.vonMangoldt d * lrH d -
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [sub_div]
  have hM : |lrMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))|
      ≤ Real.log 2 / 2 + C₂ := by
    rw [hrfl, hdiff_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) hsum
  have hN5a : |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
      1 / 2 * Real.log y| ≤ C₁ := by
    have h := hC₁ y hy
    rw [hφ, Nat.cast_two] at h
    rwa [show Real.log y / 2 = 1 / 2 * Real.log y from by ring] at h
  calc |lrMert y - 1 / 2 * Real.log y|
      = |(lrMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))) +
        ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
          1 / 2 * Real.log y)| := by
        congr 1
        ring
    _ ≤ |lrMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))| +
        |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
          1 / 2 * Real.log y| := abs_add_le _ _
    _ ≤ (Real.log 2 / 2 + C₂) + C₁ := add_le_add hM hN5a
    _ = C₁ + (Real.log 2 / 2 + C₂) := by ring

/-- The difference between `lrPsi` and the residue-class psi is at most
`log 2 + (ψ - θ)`. -/
private lemma lr_psi_diff_le (y : ℝ) :
    |lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y|
      ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) := by
  have e : lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) := by
    unfold lrPsi Chebyshev.psiResidueClass
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
  calc |∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d)|
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, |ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ((if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_le_sum fun d _ => lr_resid_diff_le d
    _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)) +
        (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_add_distrib
    _ ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) :=
        add_le_add h2part (le_of_eq (hnp y))

/-- The normalized error between `lrPsi` and the residue-class psi tends to zero. -/
private lemma lr_psi_err_tendsto :
    Filter.Tendsto (fun y => (lrPsi y -
      Chebyshev.psiResidueClass (1 : ZMod 4) y) / y)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ y in Filter.atTop,
      ‖(lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y) / y‖
        ≤ Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have h1 := lr_psi_diff_le y
    have h2 := Chebyshev.psi_sub_theta_le hy
    have h3 := lr_two_sqrt_mul_log_le y hy
    have e1 : y ^ (3/4 : ℝ) / y = y ^ (-1/4 : ℝ) := by
      have h3 : (3/4 : ℝ) - 1 = -1/4 := by norm_num
      rw [← h3, Real.rpow_sub hypos, Real.rpow_one]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hypos.le]
    calc |lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y| / y
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

/-- `lrPsi y / y` tends to `1 / 2`. -/
private lemma lr_psi_tendsto :
    Filter.Tendsto (fun y => lrPsi y / y) Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  have hPNT := Chebyshev.tendsto_psiResidueClass_div_self (1 : ZMod 4) isUnit_one
  have hφ : Nat.totient 4 = 2 := by decide
  have eφ : ((Nat.totient 4 : ℝ))⁻¹ = 1 / 2 := by
    rw [hφ]
    norm_num
  rw [eφ] at hPNT
  have heq : (fun y => lrPsi y / y) =ᶠ[Filter.atTop]
      (fun y => (lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y) / y +
        Chebyshev.psiResidueClass (1 : ZMod 4) y / y) := by
    filter_upwards with y
    rw [sub_div]
    ring
  have hlim := lr_psi_err_tendsto.add hPNT
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 from by ring] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

/-- `J` is close to `(2/3) A log`: the Mertens error propagates. -/
private lemma lr_J_near :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |lrJ x - 2 / 3 * lrA x * Real.log x| ≤ 2 / 3 * C * lrA x := by
  obtain ⟨C, hC⟩ := lr_mertens
  refine ⟨C, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hm : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      |lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| ≤ C := by
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
  have hR : |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
      (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| ≤ C * lrA x := by
    calc _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          |(lrH m / (m : ℝ)) *
            (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          (lrH m / (m : ℝ)) * C := by
          apply Finset.sum_le_sum
          intro m hmem
          calc |(lrH m / (m : ℝ)) *
              (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))|
              = (lrH m / (m : ℝ)) *
                |lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| := by
                rw [abs_mul, abs_of_nonneg
                  (div_nonneg (lrH_nonneg m) (Nat.cast_nonneg m))]
            _ ≤ (lrH m / (m : ℝ)) * C :=
                mul_le_mul_of_nonneg_left (hm m hmem)
                  (div_nonneg (lrH_nonneg m) (Nat.cast_nonneg m))
      _ = C * lrA x := by
          have hrfl : lrA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m / (m : ℝ) := rfl
          rw [← Finset.sum_mul, ← hrfl]
          ring
  have hsplit : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)))
      = 1 / 2 * lrJ x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
        (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have hJ2 : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
        (lrH m / (m : ℝ)) * (1 / 2 * Real.log (x / (m : ℝ)))) = 1 / 2 * lrJ x := by
      have hJ : lrJ x =
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * Real.log (x / (m : ℝ)) := rfl
      rw [hJ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    calc (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)))
        = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ((lrH m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ))) + (lrH m / (m : ℝ)) *
          (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))) :=
          Finset.sum_congr rfl fun m _ => by ring
      _ = (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ)))) +
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
          (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) :=
          Finset.sum_add_distrib
      _ = 1 / 2 * lrJ x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
          (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
          rw [hJ2]
  have hAJ : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ))
      = lrA x * Real.log x - lrJ x := by
    have hJ : lrJ x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
    have hA : lrA x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ) := rfl
    rw [hJ, hA, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hmem
    by_cases hn : n = 0
    · subst hn
      simp [lrH_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
      ring
  have hRe : (lrA x * Real.log x - lrJ x) - 1 / 2 * lrJ x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
        (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have h1 := lr_logA_eq x
    rw [hAJ] at h1
    rw [h1, hsplit]
    ring
  rw [← hRe] at hR
  have hRw : lrJ x - 2 / 3 * lrA x * Real.log x
      = -((2 / 3) * ((lrA x * Real.log x - lrJ x) - 1 / 2 * lrJ x)) := by
    ring
  rw [hRw, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  calc 2 / 3 * |(lrA x * Real.log x - lrJ x) - 1 / 2 * lrJ x|
      ≤ 2 / 3 * (C * lrA x) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = 2 / 3 * C * lrA x := by ring

/-- Increment bounds for `J`: splitting the sum at `⌊x⌋₊`. -/
private lemma lr_J_increment {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    lrA x * Real.log (y / x) ≤ lrJ y - lrJ x ∧
      lrJ y - lrJ x ≤ lrA y * Real.log (y / x) := by
  have hy : 1 ≤ y := le_trans hx hxy
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hle : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hJx : lrJ x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
  have hJy : lrJ y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) := rfl
  have hAx : lrA x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ) := rfl
  have hAy : lrA y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n / (n : ℝ) := rfl
  have hsplitJ : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ))) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hsplitA : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n / (n : ℝ))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ)) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hlogyx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hypos) (ne_of_gt hxpos)
  have hmain : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
        (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ))
      = (lrH n / (n : ℝ)) * Real.log (y / x) := by
    intro n hmem
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hmem).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Real.log_div (ne_of_gt hypos) (ne_of_gt hnpos),
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos), hlogyx]
    ring
  have hRnn : 0 ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
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
    exact mul_nonneg (div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)) hlog
  have hRle : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ)) * Real.log (y / x) := by
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
      (div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n))
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ))) -
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ)))
      = lrA x * Real.log (y / x) := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
          (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ))))
        = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (y / x) :=
      Finset.sum_congr rfl fun n hmem => hmain n hmem
    rw [hcongr, ← Finset.sum_mul, hAx]
  have hR_eq : lrA y - lrA x
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ) := by
    rw [hAy, hAx, hsplitA, add_sub_cancel_left]
  have hJyJx : lrJ y - lrJ x = lrA x * Real.log (y / x) +
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    rw [hJy, hJx, hsplitJ]
    linear_combination hdiff
  rw [hJyJx]
  constructor
  · exact le_add_of_nonneg_right hRnn
  · have hRR : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ (lrA y - lrA x) * Real.log (y / x) := by
      rw [hR_eq]
      calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
          ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ)) * Real.log (y / x) :=
            hRle
        _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ)) * Real.log (y / x) :=
            rfl
    calc lrA x * Real.log (y / x) +
        (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ lrA x * Real.log (y / x) + (lrA y - lrA x) * Real.log (y / x) :=
          add_le_add (le_refl _) hRR
      _ = lrA y * Real.log (y / x) := by ring

/-- For `|t| ≤ 1/2`, `|log (1 + t) - t| ≤ 2 t²`. -/
private lemma lr_log_one_add_le (t : ℝ) (ht : |t| ≤ 1 / 2) :
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
private lemma lr_growth_limit (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
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
private lemma lr_growth (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
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
      lr_log_one_add_le _ (htbound k hk)
    have hB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 :=
      hudev k hk
    have hC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
        ≤ 2 * (1 / (k : ℝ)) ^ 2 :=
      lr_log_one_add_le _ (hinvbound k hk)
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
  exact lr_growth_limit u hpos K hK k₂ hincr

/-- `B(x)`: the `k`-sum in the two-squares decomposition. -/
private noncomputable def lrB (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2)

/-- `lrH n = 1` unfolds to the defining condition. -/
private lemma lrH_eq_one {n : ℕ} :
    lrH n = 1 ↔ n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 := by
  unfold lrH
  by_cases h : n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 <;> simp [h]

/-- `lrG k = 1` unfolds to the defining condition. -/
private lemma lrG_eq_one {k : ℕ} :
    lrG k = 1 ↔ k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 := by
  unfold lrG
  by_cases h : k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 <;> simp [h]

/-- `lrH` takes only the values `0` and `1`. -/
private lemma lrH_01 (n : ℕ) : lrH n = 0 ∨ lrH n = 1 := by
  unfold lrH
  split_ifs <;> simp

/-- `lrG` takes only the values `0` and `1`. -/
private lemma lrG_01 (k : ℕ) : lrG k = 0 ∨ lrG k = 1 := by
  unfold lrG
  split_ifs <;> simp

/-- A product `k ^ 2 * m` with `lrH m = 1` is a sum of two squares
(the `k ^ 2` part always contributes even valuations). -/
private lemma lr_sq_mul_mem {k m : ℕ} (hk0 : k ≠ 0) (hm0 : m ≠ 0)
    (hm : lrH m = 1) :
    ∃ a b : ℕ, k ^ 2 * m = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq3
  have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqP⟩
  have hqm : ¬ q ∣ m := by
    intro hdvd
    have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hdvd, hm0⟩
    exact (lrH_eq_one.mp hm).2 q hmem hq3
  have h1 : padicValNat q m = 0 := padicValNat.eq_zero_of_not_dvd hqm
  have h2 : padicValNat q (k ^ 2 * m) = 2 * padicValNat q k := by
    rw [padicValNat.mul (pow_ne_zero 2 hk0) hm0, padicValNat.pow, h1, add_zero]
  rw [h2]
  exact ⟨padicValNat q k, by ring⟩

/-- Uniqueness of the `k ^ 2 * m` decomposition. -/
private lemma lr_sq_mul_inj {k m k' m' : ℕ} (hk0 : k ≠ 0) (hm0 : m ≠ 0)
    (hk0' : k' ≠ 0) (hm0' : m' ≠ 0)
    (hk : lrG k = 1) (hm : lrH m = 1) (hk' : lrG k' = 1) (hm' : lrH m' = 1)
    (h : k ^ 2 * m = k' ^ 2 * m') : k = k' ∧ m = m' := by
  have hkk : k = k' := by
    apply Nat.eq_of_factorization_eq hk0 hk0'
    intro p
    by_cases hpP : p.Prime
    · have : Fact p.Prime := ⟨hpP⟩
      have hval : padicValNat p (k ^ 2 * m) = padicValNat p (k' ^ 2 * m') := by
        rw [h]
      rw [padicValNat.mul (pow_ne_zero 2 hk0) hm0, padicValNat.pow,
        padicValNat.mul (pow_ne_zero 2 hk0') hm0', padicValNat.pow] at hval
      by_cases hp3 : p % 4 = 3
      · have hvm : padicValNat p m = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ m.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hm0⟩
          exact (lrH_eq_one.mp hm).2 p hmem hp3
        have hvm' : padicValNat p m' = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ m'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hm0'⟩
          exact (lrH_eq_one.mp hm').2 p hmem hp3
        have hkk2 : padicValNat p k = padicValNat p k' := by omega
        rw [Nat.factorization_def _ hpP, Nat.factorization_def _ hpP, hkk2]
      · have hvk : padicValNat p k = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ k.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hk0⟩
          exact hp3 ((lrG_eq_one.mp hk).2 p hmem)
        have hvk' : padicValNat p k' = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ k'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hk0'⟩
          exact hp3 ((lrG_eq_one.mp hk').2 p hmem)
        rw [Nat.factorization_def _ hpP, Nat.factorization_def _ hpP, hvk, hvk']
    · rw [Nat.factorization_eq_zero_of_not_prime _ hpP,
        Nat.factorization_eq_zero_of_not_prime _ hpP]
  refine ⟨hkk, ?_⟩
  rw [hkk] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hk0') h

/-- Every positive sum of two squares splits as `k ^ 2 * m` with `lrG k = lrH m = 1`. -/
private lemma lr_exists_sq_mul {n : ℕ} (hn1 : 1 ≤ n)
    (hsq : ∃ a b : ℕ, n = a ^ 2 + b ^ 2) :
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m = n := by
  have hn0 : n ≠ 0 := by omega
  have hchar := Nat.eq_sq_add_sq_iff.mp hsq
  set S : Finset ℕ := n.primeFactors.filter (fun p => p % 4 = 3) with hSdef
  set k : ℕ := ∏ p ∈ S, p ^ (n.factorization p / 2) with hkdef
  have hmemS : ∀ p ∈ S, p.Prime ∧ p % 4 = 3 := by
    intro p hp
    have hpf : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
    exact ⟨Nat.prime_of_mem_primeFactors hpf, (Finset.mem_filter.mp hp).2⟩
  have heven : ∀ p ∈ S, Even (n.factorization p) := by
    intro p hp
    have hpf : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
    have hpp := (hmemS p hp).1
    rw [Nat.factorization_def n hpp]
    exact hchar p hpf (hmemS p hp).2
  have hksq : k ^ 2 = ∏ p ∈ S, p ^ (n.factorization p) := by
    rw [hkdef, pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨t, ht⟩ := heven p hp
    have hv2 : n.factorization p / 2 = t := by omega
    rw [hv2, ← pow_add, ← ht]
  have hprod_eq : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h
  have hdvd : k ^ 2 ∣ n := by
    have hsub : S ⊆ n.primeFactors := Finset.filter_subset _ _
    have h := Finset.prod_sdiff hsub (f := fun p => p ^ (n.factorization p))
    rw [mul_comm] at h
    have h2 : k ^ 2 ∣ ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      rw [hksq]
      exact ⟨∏ x ∈ n.primeFactors \ S, x ^ (n.factorization x), h.symm⟩
    rwa [hprod_eq] at h2
  obtain ⟨m, hm⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rw [hkdef]
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpp := (hmemS p hp).1
    exact pow_ne_zero _ (ne_of_gt hpp.pos)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hkm_eq : k ^ 2 * m = n := hm.symm
  have hm0 : m ≠ 0 := by
    intro hcon
    apply hn0
    calc n = k ^ 2 * m := hm
      _ = 0 := by rw [hcon, mul_zero]
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have hGk : lrG k = 1 := by
    rw [lrG_eq_one]
    refine ⟨hk0, fun q hq => ?_⟩
    have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ k := Nat.dvd_of_mem_primeFactors hq
    rw [hkdef] at hqdvd
    obtain ⟨p, hpS, hqp⟩ :=
      (Nat.prime_iff.mp hqP).dvd_finsetProd_iff _ |>.mp hqdvd
    have hqp2 : q ∣ p := hqP.dvd_of_dvd_pow hqp
    have hpP : p.Prime := (hmemS p hpS).1
    have hqp3 : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpP).mp hqp2
    rw [hqp3]
    exact (hmemS p hpS).2
  have hHm : lrH m = 1 := by
    rw [lrH_eq_one]
    refine ⟨hm0, fun q hq => ?_⟩
    have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    intro hq3
    have hmn : m ∣ n := by
      have h := dvd_mul_left m (k ^ 2)
      rwa [hkm_eq] at h
    have hqn : q ∣ n := dvd_trans hqdvd hmn
    have hmem_n : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hqn, hn0⟩
    have hqS : q ∈ S := Finset.mem_filter.mpr ⟨hmem_n, hq3⟩
    have hpow_dvd_k2 : q ^ (n.factorization q) ∣ k ^ 2 := by
      rw [hksq]
      exact Finset.dvd_prod_of_mem _ hqS
    have hpow_dvd_m : q ^ (m.factorization q) ∣ m := Nat.ordProj_dvd m q
    have hmul_dvd : q ^ (n.factorization q) * q ^ (m.factorization q) ∣ k ^ 2 * m :=
      mul_dvd_mul hpow_dvd_k2 hpow_dvd_m
    rw [hkm_eq] at hmul_dvd
    rw [← pow_add] at hmul_dvd
    have hle : n.factorization q + m.factorization q ≤ n.factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hqP hn0).mp hmul_dvd
    have hposv : 1 ≤ m.factorization q := by
      have hqdvd1 : q ^ 1 ∣ m := by rwa [pow_one]
      exact (Nat.Prime.pow_dvd_iff_le_factorization hqP hm0).mp hqdvd1
    omega
  exact ⟨k, m, hk1, hm1, hGk, hHm, hkm_eq⟩

/-- Decomposition of the two-squares count: the number of `n ≤ x`, `n ≥ 1`,
that are a sum of two squares equals `B(x)`. -/
private lemma lr_twoSq_count_eq {x : ℝ} (hx : 0 ≤ x) :
    ((Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
      (Finset.Ioc 0 ⌊x⌋₊)).card : ℝ) = lrB x := by
  classical
  set T : Finset (Σ _ : ℕ, ℕ) := (Finset.Ioc 0 ⌊x⌋₊).sigma
    (fun k => (Finset.Ioc 0 ⌊x⌋₊).filter
      (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)) with hTdef
  have himg : Finset.image (fun p : Σ _ : ℕ, ℕ => p.1 ^ 2 * p.2) T
      = Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨k, m⟩, hkm, rfl⟩
      obtain ⟨hkI, hmF⟩ := Finset.mem_sigma.mp hkm
      obtain ⟨hmI, hGk, hHm, hle⟩ := Finset.mem_filter.mp hmF
      obtain ⟨hk0, hkN⟩ := Finset.mem_Ioc.mp hkI
      obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hmI
      have hk0k : 0 < k := hk0
      have hm0m : 0 < m := hm0
      have hpos : 0 < k ^ 2 * m :=
        Nat.mul_pos (pow_pos hk0k 2) hm0m
      refine ⟨Finset.mem_Ioc.mpr ⟨hpos, hle⟩,
        lr_sq_mul_mem (ne_of_gt hk0k) (ne_of_gt hm0m) hHm⟩
    · rintro ⟨hnI, hsq⟩
      obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hnI
      obtain ⟨k, m, hk1, hm1, hGk, hHm, hkm⟩ := lr_exists_sq_mul hn0 hsq
      have hpos : 0 < k ^ 2 * m := by
        rw [hkm]
        omega
      have hk_le : k ≤ k ^ 2 * m :=
        Nat.le_of_dvd hpos ⟨k * m, by ring⟩
      have hm_le : m ≤ k ^ 2 * m :=
        Nat.le_of_dvd hpos ⟨k ^ 2, by ring⟩
      refine ⟨⟨k, m⟩, ?_, hkm⟩
      rw [hTdef]
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hk1, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hm1, ?_⟩, hGk, hHm, ?_⟩⟩
      · exact le_trans hk_le (hkm ▸ hnN)
      · exact le_trans hm_le (hkm ▸ hnN)
      · rw [hkm]
        exact hnN
  have hinj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => p.1 ^ 2 * p.2) (↑T) := by
    intro a ha b hb hab
    obtain ⟨k, m⟩ := a
    obtain ⟨k', m'⟩ := b
    have ha' := Finset.mem_coe.mp ha
    have hb' := Finset.mem_coe.mp hb
    obtain ⟨hkI, hmF⟩ := Finset.mem_sigma.mp ha'
    obtain ⟨hmI, hGk, hHm, -⟩ := Finset.mem_filter.mp hmF
    obtain ⟨hkI', hmF'⟩ := Finset.mem_sigma.mp hb'
    obtain ⟨hmI', hGk', hHm', -⟩ := Finset.mem_filter.mp hmF'
    have hk0k : 0 < k := (Finset.mem_Ioc.mp hkI).1
    have hm0m : 0 < m := (Finset.mem_Ioc.mp hmI).1
    have hk0k' : 0 < k' := (Finset.mem_Ioc.mp hkI').1
    have hm0m' : 0 < m' := (Finset.mem_Ioc.mp hmI').1
    have hab' : k ^ 2 * m = k' ^ 2 * m' := hab
    have hk0n : k ≠ 0 := ne_of_gt hk0k
    have hm0n : m ≠ 0 := ne_of_gt hm0m
    have hk0n' : k' ≠ 0 := ne_of_gt hk0k'
    have hm0n' : m' ≠ 0 := ne_of_gt hm0m'
    obtain ⟨hkk, hmm⟩ :=
      lr_sq_mul_inj hk0n hm0n hk0n' hm0n' hGk hHm hGk' hHm' hab'
    subst hkk
    subst hmm
    rfl
  have hcardT : (T.card : ℝ) = lrB x := by
    have hsigma : T.card = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)).card := by
      rw [hTdef]
      exact Finset.card_sigma _ _
    have hlrB : lrB x
        = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2) := rfl
    rw [hsigma, Nat.cast_sum, hlrB]
    apply Finset.sum_congr rfl
    intro k hkI
    have hk1 : 1 ≤ k := (Finset.mem_Ioc.mp hkI).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hcast : ∀ m : ℕ, ((k ^ 2 * m : ℕ) : ℝ) = (k : ℝ) ^ 2 * (m : ℝ) := by
      intro m
      push_cast
      ring
    by_cases hGk : lrG k = 1
    · have hfib : (Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)
          = (Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊).filter (fun m => lrH m = 1) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hm0, hmN⟩, -, hHm, hle⟩
          have hleR : (k : ℝ) ^ 2 * (m : ℝ) ≤ x := by
            have h1 : ((k ^ 2 * m : ℕ) : ℝ) ≤ x :=
              le_trans (by exact_mod_cast hle) (Nat.floor_le hx)
            rwa [hcast] at h1
          have hmk : (m : ℝ) ≤ x / (k : ℝ) ^ 2 := by
            rw [le_div_iff₀ (pow_pos hkpos 2)]
            linear_combination hleR
          exact ⟨⟨hm0, Nat.le_floor hmk⟩, hHm⟩
        · rintro ⟨⟨hm0, hmN'⟩, hHm⟩
          have hmk : (m : ℝ) ≤ x / (k : ℝ) ^ 2 :=
            le_trans (by exact_mod_cast hmN')
              (Nat.floor_le (by positivity))
          have hleR : (k : ℝ) ^ 2 * (m : ℝ) ≤ x := by
            have h2 := (le_div_iff₀ (pow_pos hkpos 2)).mp hmk
            linear_combination h2
          have hle : k ^ 2 * m ≤ ⌊x⌋₊ := by
            apply Nat.le_floor
            rw [hcast]
            exact hleR
          have hkk2 : x / (k : ℝ) ^ 2 ≤ x := by
            apply div_le_self hx
            calc (1 : ℝ) = 1 ^ 2 := by norm_num
              _ ≤ (k : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hk1) 2
          have hmN : m ≤ ⌊x⌋₊ := Nat.le_floor (le_trans hmk hkk2)
          exact ⟨⟨hm0, hmN⟩, hGk, hHm, hle⟩
      rw [hfib]
      have hcard : (((Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊).filter
          (fun m => lrH m = 1)).card : ℝ) = lrCount (x / (k : ℝ) ^ 2) := by
        have hlrC : lrCount (x / (k : ℝ) ^ 2)
            = ∑ m ∈ Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊, lrH m := rfl
        rw [hlrC, ← Finset.sum_boole]
        apply Finset.sum_congr rfl
        intro m _
        rcases lrH_01 m with h0 | h1
        · simp [h0]
        · simp [h1]
      rw [hcard, hGk, one_mul]
    · have hGk0 : lrG k = 0 := by
        rcases lrG_01 k with h | h
        · exact h
        · exact absurd h hGk
      have hfib_empty : (Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m _
        simp [hGk0]
      rw [hfib_empty, Finset.card_empty, Nat.cast_zero, hGk0, zero_mul]
  have h1 : (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
      (Finset.Ioc 0 ⌊x⌋₊)).card = T.card := by
    rw [← himg]
    exact Finset.card_image_of_injOn hinj
  rw [h1]
  exact hcardT

/-- The `Set.ncard` of the Wanted set is one plus the positive count. -/
private lemma lr_ncard_eq {x : ℝ} (hx : 0 ≤ x) :
    Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}
      = (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.Ioc 0 ⌊x⌋₊)).card + 1 := by
  have hset : {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}
      = ↑(Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.range (⌊x⌋₊ + 1))) := by
    ext m
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmx, hsq⟩
      have hle : m ≤ ⌊x⌋₊ := Nat.le_floor hmx
      exact ⟨by omega, hsq⟩
    · rintro ⟨hm, hsq⟩
      have hle : m ≤ ⌊x⌋₊ := by omega
      have hcast : (m : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
      exact ⟨le_trans hcast (Nat.floor_le hx), hsq⟩
  have hsplit : Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.range (⌊x⌋₊ + 1))
      = Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.Ioc 0 ⌊x⌋₊) ∪ {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hsq⟩
      by_cases hm0 : m = 0
      · exact Or.inr hm0
      · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
        exact Or.inl ⟨⟨hpos, by omega⟩, hsq⟩
    · rintro (⟨⟨hm0, hmN⟩, hsq⟩ | rfl)
      · exact ⟨by omega, hsq⟩
      · exact ⟨Nat.zero_lt_succ _, 0, 0, by simp⟩
  have hdisj : Disjoint
      (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.Ioc 0 ⌊x⌋₊)) {0} := by
    rw [Finset.disjoint_left]
    intro m hmI hm0
    rw [Finset.mem_filter, Finset.mem_Ioc] at hmI
    rw [Finset.mem_singleton] at hm0
    omega
  rw [hset, Set.ncard_coe_finset, hsplit,
    Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- Ratio bounds for `J` at exponential points: the input for `lr_growth`. -/
private lemma lr_J_ratio :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      |lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := lr_J_near
  obtain ⟨D, hD, hCD⟩ : ∃ D : ℝ, 0 ≤ D ∧ C ≤ D :=
    ⟨|C|, abs_nonneg _, le_abs_self _⟩
  have hC' : ∀ x : ℝ, 1 ≤ x →
      |lrJ x - 2 / 3 * lrA x * Real.log x| ≤ 2 / 3 * D * lrA x := by
    intro x hx
    have h := hC x hx
    have hA := lrA_nonneg x
    have h3 : C * lrA x ≤ D * lrA x :=
      mul_le_mul_of_nonneg_right hCD hA
    calc |lrJ x - 2 / 3 * lrA x * Real.log x| ≤ 2 / 3 * C * lrA x := h
      _ ≤ 2 / 3 * D * lrA x := by linarith [h3]
  have hE : ∀ k : ℕ, (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    intro k
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA1 : lrA 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrA
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have hJ1zero : lrJ 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrJ
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
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
  have hJ1 : 1 ≤ lrJ (Real.exp 1) := by
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := lr_J_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  have hJk : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ lrJ (Real.exp (k : ℝ)) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
      Real.exp_le_exp_of_le hkR
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := lr_J_increment h1e h1k
    have hnn : 0 ≤ lrA (Real.exp 1)
        * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
      apply mul_nonneg (lrA_nonneg _)
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
  have hJpos : 0 < lrJ (Real.exp (k : ℝ)) := by
    have h := hJk k (le_trans hk₀pos hk)
    linarith
  have hN6k := hC' (Real.exp (k : ℝ)) (hE k)
  rw [Real.log_exp] at hN6k
  have hN6k1 := hC' (Real.exp (((k + 1 : ℕ)) : ℝ)) (hE (k + 1))
  have hlogk1 : Real.log (Real.exp (((k + 1 : ℕ)) : ℝ)) = ((k + 1 : ℕ) : ℝ) :=
    Real.log_exp _
  rw [hlogk1] at hN6k1
  obtain ⟨hN7lo, hN7hi⟩ := lr_J_increment (hE k) (hEmono k)
  rw [hlogR k, mul_one] at hN7lo hN7hi
  have hposSD : (0 : ℝ) < (k : ℝ) + D := add_pos_of_pos_of_nonneg hsk hD
  have hposT : (0 : ℝ) < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
  have hSDne : (k : ℝ) + D ≠ 0 := ne_of_gt hposSD
  have hTne : ((k : ℝ) + 1) - D ≠ 0 := ne_of_gt hposT
  have hsne : (k : ℝ) ≠ 0 := ne_of_gt hsk
  have hs2ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hsne
  have hAlo : (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ lrA (Real.exp (k : ℝ)) := by
    have hhi := (abs_le.mp hN6k).2
    have hle : lrJ (Real.exp (k : ℝ))
        ≤ (2 / 3) * ((k : ℝ) + D) * lrA (Real.exp (k : ℝ)) := by
      linarith [hhi]
    have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + D) :=
      div_nonneg (by norm_num) hposSD.le
    have h := mul_le_mul_of_nonneg_right hle hpos
    have e1 : ((2 / 3) * ((k : ℝ) + D) * lrA (Real.exp (k : ℝ)))
          * ((3 / 2) / ((k : ℝ) + D))
        = lrA (Real.exp (k : ℝ)) := by
      field_simp
    have e0 : lrJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + D))
        = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e0, e1] at h
    exact h
  have hA'hi : lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) := by
    have hlo := (abs_le.mp hN6k1).1
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hle' : (2 / 3) * (((k : ℝ) + 1) - D)
          * lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
        ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      have e : (2 / 3) * (((k : ℝ) + 1) - D)
            * lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
          = (2 / 3) * lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) * (((k + 1 : ℕ)) : ℝ)
            - (2 / 3) * D * lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
        rw [hcast]
        ring
      rw [e]
      linarith [hlo]
    have hpos : (0 : ℝ) ≤ 3 / (2 * (((k : ℝ) + 1) - D)) :=
      div_nonneg (by norm_num) (mul_nonneg (by norm_num) hposT.le)
    have h := mul_le_mul_of_nonneg_right hle' hpos
    have e1 : ((2 / 3) * (((k : ℝ) + 1) - D)
          * lrA (Real.exp (((k + 1 : ℕ)) : ℝ)))
          * (3 / (2 * (((k : ℝ) + 1) - D)))
        = lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      field_simp
    rw [e1] at h
    exact h
  have h1 : (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ)) :=
    le_trans hAlo hN7lo
  have h2 : (3 / 2) / ((k : ℝ) + D)
      ≤ (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ)))
        / lrJ (Real.exp (k : ℝ)) := by
    rw [le_div_iff₀ hJpos]
    have e : ((3 / 2) / ((k : ℝ) + D)) * lrJ (Real.exp (k : ℝ))
        = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e]
    exact h1
  have eJJ : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)) - 1
      = (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ)))
        / lrJ (Real.exp (k : ℝ)) := by
    rw [← div_self (ne_of_gt hJpos), ← sub_div]
  have h3 : 1 + (3 / 2) / ((k : ℝ) + D)
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)) := by
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
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ))) := by
    linarith [h3, h4]
  have h5 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ))
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) :=
    le_trans hN7hi hA'hi
  have h6 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      ≤ lrJ (Real.exp (k : ℝ)) := by
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
  have h7 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
      ≤ 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    rw [le_div_iff₀ h1δ]
    have e : (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)))
          * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
        = (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
            * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))) / lrJ (Real.exp (k : ℝ)) := by
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
  have h8 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)) - 1
      ≤ (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    linarith [h7, hfrac]
  have hup : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))
      ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    have efin : (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2
        = 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by ring
    linarith [h8, hfrac2, h10, h11, efin]
  have hfin : |lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
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
private lemma lr_J_exp_pos : ∀ k : ℕ, 1 ≤ k → 0 < lrJ (Real.exp (k : ℝ)) := by
  have hA1 : lrA 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrA
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have hJ1zero : lrJ 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrJ
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hJ1 : 1 ≤ lrJ (Real.exp 1) := by
    obtain ⟨lo, _⟩ := lr_J_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
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
  obtain ⟨lo, _⟩ := lr_J_increment h1e h1k
  have hnn : 0 ≤ lrA (Real.exp 1)
      * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
    apply mul_nonneg (lrA_nonneg _)
    apply Real.log_nonneg
    rw [le_div_iff₀ (Real.exp_pos _)]
    simpa using h1k
  linarith [lo, hnn, hJ1]

/-- `k / (k + c) → 1` along naturals. -/
private lemma lr_nat_div_add_tendsto (c : ℝ) :
    Filter.Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + c))
      Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto (fun k : ℕ => c / (k : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have h1 : Filter.Tendsto (fun k : ℕ => 1 + c / (k : ℝ))
      Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h1
  have h2 : Filter.Tendsto (fun k : ℕ => 1 / (1 + c / (k : ℝ)))
      Filter.atTop (nhds (1 / 1)) :=
    tendsto_const_nhds.div h1 one_ne_zero
  rw [div_one] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hsk : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have e : (1 : ℝ) + c / (k : ℝ) = ((k : ℝ) + c) / (k : ℝ) := by
    rw [add_div, div_self hsk]
  rw [e, one_div_div]

/-- Sequential version: `A(e^k) / √k → α` for some `α > 0`. -/
private lemma lr_A_seq_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
        Filter.atTop (nhds α) := by
  obtain ⟨K, hK, k₀, hk₀, hstep⟩ := lr_J_ratio
  obtain ⟨C, hC⟩ := lr_J_near
  have hpos : ∀ k : ℕ, 1 ≤ k → 0 < (fun k => lrJ (Real.exp (k : ℝ))) k :=
    fun k hk => lr_J_exp_pos k hk
  obtain ⟨L, hLpos, hL⟩ := lr_growth _ hpos K hK k₀ hk₀ hstep
  have hrpow : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ (3 / 2 : ℝ)
      = (k : ℝ) * Real.sqrt (k : ℝ) := by
    intro k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [e, Real.rpow_add hsk, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hconv : ∀ k : ℕ, 1 ≤ k → |C| < (k : ℝ) →
      (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + C)
        ≤ lrA (Real.exp (k : ℝ)) ∧
      lrA (Real.exp (k : ℝ))
        ≤ (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by
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
    · have hle : lrJ (Real.exp (k : ℝ))
          ≤ (2 / 3) * ((k : ℝ) + C) * lrA (Real.exp (k : ℝ)) := by
        linarith [hhi]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + C) :=
        div_nonneg (by norm_num) hposPC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) + C) * lrA (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) + C))
          = lrA (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : lrJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + C))
          = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + C) := by ring
      rw [e0, e1] at h
      exact h
    · have hle : (2 / 3) * ((k : ℝ) - C) * lrA (Real.exp (k : ℝ))
          ≤ lrJ (Real.exp (k : ℝ)) := by
        linarith [hlo]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) - C) :=
        div_nonneg (by norm_num) hposMC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) - C) * lrA (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) - C))
          = lrA (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : lrJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) - C))
          = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by ring
      rw [e0, e1] at h
      exact h
  have hLo : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) + C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (lr_nat_div_add_tendsto C)
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    simpa [mul_one] using hmul2
  have hHi : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) - C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (lr_nat_div_add_tendsto (-C))
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    have heq : (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        = (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
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
    have e : ((3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
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
    have e : lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)
        ≤ ((3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right hconvk.2 (Real.sqrt_nonneg _)
    have e2 : ((3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [e2] at e
    exact e

/-- Shifted end: `A(e^k) / √(k+1) → α`. -/
private lemma lr_A_seq_low (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (((k + 1 : ℕ)) : ℝ))
        Filter.atTop (nhds 1) := by
      have h := lr_nat_div_add_tendsto (1 : ℝ)
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
  have heq : (fun k : ℕ => (lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
          * (Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ)) := by
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
private lemma lr_A_seq_high (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α) := by
  have hshift : Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
        / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds α)
      (f := fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)) 1
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
  have heq : (fun k : ℕ => (lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
          / Real.sqrt (((k + 1 : ℕ)) : ℝ))
          * (Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ)) := by
    filter_upwards with k
    have hS : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- `A(x) / √(log x)` converges to a positive limit. -/
private lemma lr_A_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun x => lrA x / Real.sqrt (Real.log x))
        Filter.atTop (nhds α) := by
  obtain ⟨α, hαpos, hAseq⟩ := lr_A_seq_tendsto
  have hlow := lr_A_seq_low α hAseq
  have hhigh := lr_A_seq_high α hAseq
  have hk_tend : Filter.Tendsto (fun x : ℝ => ⌊Real.log x⌋₊)
      Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop
  have hlowx : Filter.Tendsto
      (fun x : ℝ => lrA (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
        Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := hlow.comp hk_tend
  have hhighx : Filter.Tendsto
      (fun x : ℝ => lrA (Real.exp (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)) /
        Real.sqrt ((⌊Real.log x⌋₊ : ℕ) : ℝ))
      Filter.atTop (nhds α) := hhigh.comp hk_tend
  refine ⟨α, hαpos, ?_⟩
  have key_lo : ∀ᶠ x : ℝ in Filter.atTop,
      lrA (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)
        ≤ lrA x / Real.sqrt (Real.log x) := by
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
    have hAle1 : lrA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) ≤ lrA x :=
      lrA_mono hexpk
    have hsq2 : Real.sqrt (Real.log x)
        ≤ Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      rw [hcast1]
      exact Real.sqrt_le_sqrt hku.le
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc lrA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) /
            Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        ≤ lrA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_left (lrA_nonneg _) hsqrt_log hsq2
      _ ≤ lrA x / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle1 hsqrt_log.le
  have key_hi : ∀ᶠ x : ℝ in Filter.atTop,
      lrA x / Real.sqrt (Real.log x)
        ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
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
    have hAle2 : lrA x ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) :=
      lrA_mono hxexp.le
    have hsq1 : Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ)
        ≤ Real.sqrt (Real.log x) :=
      Real.sqrt_le_sqrt hkd
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc lrA x / Real.sqrt (Real.log x)
        ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle2 hsqrt_log.le
      _ ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_left (lrA_nonneg _)
            (Real.sqrt_pos.mpr hsk) hsq1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowx hhighx key_lo key_hi

/-- `A(x)` tends to infinity. -/
private lemma lr_A_atTop (α : ℝ) (hα : 0 < α)
    (hA : Filter.Tendsto (fun x => lrA x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto lrA Filter.atTop Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x))
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun y : ℝ => y ^ (1/2 : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    have h2 := h1.comp Real.tendsto_log_atTop
    refine h2.congr' ?_
    filter_upwards with x
    exact (Real.sqrt_eq_rpow _).symm
  have hAev : ∀ᶠ x : ℝ in Filter.atTop, α / 2 ≤ lrA x / Real.sqrt (Real.log x) := by
    have hmem : Set.Ioi (α / 2) ∈ nhds α := Ioi_mem_nhds (by linarith)
    filter_upwards [hA.eventually hmem] with x hx
    exact le_of_lt (Set.mem_Ioi.mp hx)
  have hlogev : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.sqrt (Real.log x) * (α / 2) ≤ lrA x := by
    filter_upwards [hAev, hlogev] with x hx1 hx2
    have hpos : (0:ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    have h := (le_div_iff₀ hpos).mp hx1
    linarith [h]
  exact Filter.tendsto_atTop_mono' _ hev
    (hsqrt.atTop_mul_const (by linarith))

/-- The log-weighted sum over the natural density:
`(Σ_{n ≤ x} lrH n · log n) / (x · A(x)) → 1 / 2`. -/
private lemma lr_L_tendsto :
    Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ))
        / (x * lrA x))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨α, hαpos, hA⟩ := lr_A_tendsto
  have hAinf := lr_A_atTop α hαpos hA
  have hKpos : (0:ℝ) < Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK1 : (1/2 : ℝ) ≤ Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK : ∀ y : ℝ, 0 ≤ y → |lrPsi y - y / 2| ≤ (Real.log 4 + 4) * y := by
    intro y hy
    have h1 : 0 ≤ lrPsi y := lrPsi_nonneg y
    have h2 : lrPsi y ≤ (Real.log 4 + 4) * y := lrPsi_le_mul_self hy
    have h3 : (0:ℝ) ≤ y / 2 := by linarith
    have h4 : y / 2 ≤ (Real.log 4 + 4) * y := by
      have hnn := mul_nonneg (sub_nonneg.mpr hK1) hy
      linarith
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevY : ∀ᶠ y : ℝ in Filter.atTop, dist (lrPsi y / y) (1/2) ≤ ε/4 :=
    lr_psi_tendsto.eventually
      (Metric.closedBall_mem_nhds (1/2 : ℝ) (show (0:ℝ) < ε/4 by linarith))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevY
  set Y : ℝ := max Y₀ 1 with hYdef
  have hY1 : (1:ℝ) ≤ Y := le_max_right _ _
  have hYpos : (0:ℝ) < Y := by linarith
  have hYrel : ∀ y : ℝ, Y ≤ y → |lrPsi y - y/2| ≤ (ε/4) * y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hYpos hy
    have h := hY₀ y (le_trans (le_max_left _ _) hy)
    rw [Real.dist_eq] at h
    have hyne : y ≠ 0 := ne_of_gt hy0
    have e : lrPsi y - y/2 = y * (lrPsi y / y - 1/2) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg hy0.le]
    calc y * |lrPsi y / y - 1 / 2| ≤ y * (ε/4) :=
        mul_le_mul_of_nonneg_left h hy0.le
      _ = (ε/4) * y := by ring
  have hBpos : (0:ℝ) < 4 * ((Real.log 4 + 4) * Y) / ε :=
    div_pos (mul_pos (by norm_num) (mul_pos hKpos hYpos)) hε
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 4 * ((Real.log 4 + 4) * Y) / ε ≤ lrA x :=
    hAinf.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [Filter.eventually_ge_atTop 1, hB] with x hx1 hBA
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hApos : (0:ℝ) < lrA x := lt_of_lt_of_le hBpos hBA
  have hxA : (0:ℝ) < x * lrA x := mul_pos hxpos hApos
  have hhalf : x / 2 * lrA x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * (x / (2 * (m:ℝ))) := by
    have hlrA : lrA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m / (m:ℝ) := rfl
    rw [hlrA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) - x/2 * lrA x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ))) := by
    rw [lr_L_eq, hhalf, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hbig : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, Y ≤ x/(m:ℝ) →
      |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (ε/4) * (x * (lrH m/(m:ℝ))) := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have h1 := hYrel _ hYm
    have hnn : (0:ℝ) ≤ lrH m := lrH_nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [abs_mul, abs_of_nonneg hnn]
    calc lrH m * |lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ))|
        = lrH m * |lrPsi (x/(m:ℝ)) - (x/(m:ℝ))/2| := by rw [e]
      _ ≤ lrH m * ((ε/4) * (x/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = (ε/4) * (x * (lrH m/(m:ℝ))) := by ring
  have hsmall : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, ¬ Y ≤ x/(m:ℝ) →
      |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (Real.log 4 + 4) * Y := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have hlt : x/(m:ℝ) < Y := lt_of_not_ge hYm
    have hxm0 : (0:ℝ) ≤ x/(m:ℝ) := div_nonneg hx0 hmpos.le
    have h1 := hK _ hxm0
    have hle1 : lrH m ≤ 1 := lrH_le_one m
    have hnn : (0:ℝ) ≤ lrH m := lrH_nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [← e] at h1
    calc |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        = lrH m * |lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ))| := by
          rw [abs_mul, abs_of_nonneg hnn]
      _ ≤ 1 * ((Real.log 4 + 4) * (x/(m:ℝ))) :=
          mul_le_mul hle1 h1 (abs_nonneg _) (by norm_num)
      _ = (Real.log 4 + 4) * (x/(m:ℝ)) := one_mul _
      _ ≤ (Real.log 4 + 4) * Y :=
          mul_le_mul_of_nonneg_left hlt.le hKpos.le
  have hbig_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
        |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (lrH m/(m:ℝ))) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hbig m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun m _ _ => mul_nonneg (show (0:ℝ) ≤ ε/4 by linarith)
          (mul_nonneg hx0
            (div_nonneg (lrH_nonneg m) (Nat.cast_nonneg m)))))
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
        |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ x * ((Real.log 4 + 4) * Y) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hsmall m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (le_trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
        (mul_le_mul_of_nonneg_right hcardx
          (mul_nonneg hKpos.le hYpos.le)))
  have hsum_le : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) - x/2 * lrA x|
      ≤ (ε/4) * (x * lrA x) + x * ((Real.log 4 + 4) * Y) := by
    rw [hdiff]
    calc |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
            |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
              |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|)
          + (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
              |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|) :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (lrH m/(m:ℝ))))
          + x * ((Real.log 4 + 4) * Y) :=
          _root_.add_le_add hbig_sum hsmall_sum
      _ = (ε/4) * (x * lrA x) + x * ((Real.log 4 + 4) * Y) := by
          congr 1
          calc ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (lrH m/(m:ℝ)))
              = (ε/4) * x * ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m/(m:ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m _
                ring
            _ = (ε/4) * (x * lrA x) := by
                have hlrA : lrA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m/(m:ℝ) := rfl
                rw [hlrA]
                ring
  have e : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x) - 1/2
      = ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) - x/2 * lrA x)
        / (x * lrA x) := by
    have hxAne : x * lrA x ≠ 0 := ne_of_gt hxA
    field_simp
  have hBY : (Real.log 4 + 4) * Y / lrA x ≤ ε/4 := by
    rw [div_le_iff₀ hApos]
    have h2 : 4 * ((Real.log 4 + 4) * Y) ≤ lrA x * ε := by
      rwa [div_le_iff₀ hε] at hBA
    linarith [h2]
  have hfin : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x)
      - 1/2| ≤ ε/2 := by
    rw [e, abs_div, abs_of_nonneg hxA.le, div_le_iff₀ hxA]
    have h1 : x * ((Real.log 4 + 4) * Y) ≤ (ε/4) * (x * lrA x) := by
      have e2 : x * ((Real.log 4 + 4) * Y)
          = (x * lrA x) * ((Real.log 4 + 4) * Y / lrA x) := by
        have hAne : lrA x ≠ 0 := ne_of_gt hApos
        field_simp
      rw [e2]
      calc (x * lrA x) * ((Real.log 4 + 4) * Y / lrA x)
          ≤ (x * lrA x) * (ε/4) :=
            mul_le_mul_of_nonneg_left hBY hxA.le
        _ = (ε/4) * (x * lrA x) := by ring
    linarith [hsum_le, h1]
  change dist ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x))
    (1/2 : ℝ) < ε
  rw [Real.dist_eq]
  linarith [hfin, hε]

/-- For `x ≥ 1`: `∑_{n ≤ x} log (x / n) ≤ x`, via `N!`. -/
private lemma lr_log_sum_le {x : ℝ} (hx : 1 ≤ x) :
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

/-- Natural density: `H(x) · √(log x) / x → α / 2`. -/
private lemma lr_count_tendsto (α : ℝ)
    (hA : Filter.Tendsto (fun x => lrA x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2)) := by
  obtain ⟨α', hα'pos, hA'⟩ := lr_A_tendsto
  have hAinf := lr_A_atTop α' hα'pos hA'
  -- The `J₂` sum and its bounds.
  have hJ2eq : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
      = lrCount x * Real.log x
        - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) := by
    intro x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hlrC : lrCount x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n := rfl
    rw [hlrC, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
    ring
  have hJ2nn : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
        / (x * lrA x) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < lrA x :=
      lt_of_lt_of_le (by norm_num) (lrA_ge_one hx)
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
    exact mul_nonneg (lrH_nonneg n) hlog
  have hJ2le : ∀ᶠ x : ℝ in Filter.atTop,
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
        / (x * lrA x) ≤ 1 / lrA x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < lrA x :=
      lt_of_lt_of_le (by norm_num) (lrA_ge_one hx)
    have hxA : (0:ℝ) < x * lrA x := mul_pos hxpos hApos
    have hJle : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ))) ≤ x := by
      calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ))
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
            calc lrH n * Real.log (x/(n:ℝ))
                ≤ 1 * Real.log (x/(n:ℝ)) :=
                  mul_le_mul_of_nonneg_right (lrH_le_one n) hlog
              _ = Real.log (x/(n:ℝ)) := one_mul _
        _ ≤ x := lr_log_sum_le hx
    calc (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ))) / (x * lrA x)
        ≤ x / (x * lrA x) :=
          div_le_div_of_nonneg_right hJle hxA.le
      _ = 1 / lrA x := by
          have hxne : x ≠ 0 := ne_of_gt hxpos
          have hAne : lrA x ≠ 0 := ne_of_gt hApos
          field_simp
  have h1A : Filter.Tendsto (fun x => 1 / lrA x) Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hAinf
    refine h.congr' ?_
    filter_upwards with x
    exact (one_div _).symm
  have hJ2 : Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
        / (x * lrA x))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1A
      hJ2nn hJ2le
  have hHlog : Filter.Tendsto
      (fun x => lrCount x * Real.log x / (x * lrA x))
      Filter.atTop (nhds (1 / 2)) := by
    have heq : (fun x => lrCount x * Real.log x / (x * lrA x)) =ᶠ[Filter.atTop]
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
          / (x * lrA x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      rw [hJ2eq x hx]
      ring
    have hsum := hJ2.add lr_L_tendsto
    rw [show (0:ℝ) + 1/2 = 1/2 by ring] at hsum
    have hsum' : Filter.Tendsto
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
          / (x * lrA x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x))
        Filter.atTop (nhds (1/2)) := hsum
    exact hsum'.congr' heq.symm
  have heq2 : (fun x => (lrCount x * Real.log x / (x * lrA x))
        * (lrA x / Real.sqrt (Real.log x)))
      =ᶠ[Filter.atTop]
      (fun x => lrCount x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsq : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlog)
    have hApos : (0:ℝ) < lrA x :=
      lt_of_lt_of_le (by norm_num) (lrA_ge_one (le_of_lt hx))
    have hxne : x ≠ 0 := ne_of_gt (by linarith)
    have hAne : lrA x ≠ 0 := ne_of_gt hApos
    have hdiv : Real.log x / Real.sqrt (Real.log x)
        = Real.sqrt (Real.log x) := by
      rw [div_eq_iff hsq, Real.mul_self_sqrt hlog.le]
    calc (lrCount x * Real.log x / (x * lrA x))
            * (lrA x / Real.sqrt (Real.log x))
        = (lrCount x / x) * (Real.log x / Real.sqrt (Real.log x)) := by
          field_simp
      _ = (lrCount x / x) * Real.sqrt (Real.log x) := by rw [hdiv]
      _ = lrCount x * Real.sqrt (Real.log x) / x := by ring
  have hprod := hHlog.mul hA
  have eα : (1/2 : ℝ) * α = α / 2 := by ring
  rw [eα] at hprod
  have hprod' : Filter.Tendsto
      (fun x => (lrCount x * Real.log x / (x * lrA x))
        * (lrA x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds (α/2)) := hprod
  exact hprod'.congr' heq2

/-- `lrCount` vanishes below `1`. -/
private lemma lrCount_eq_zero_of_lt_one {y : ℝ} (hy : y < 1) : lrCount y = 0 := by
  have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy
  simp [lrCount, hfl]

/-- The square-root log ratio `√(log x) / √(log (x / c))` tends to `1`. -/
private lemma lr_sqrt_ratio_tendsto (c : ℝ) (hc : 1 ≤ c) :
    Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c)))
      Filter.atTop (nhds 1) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hx : Filter.Tendsto (fun x : ℝ => x / c) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hc0 tendsto_id
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log c / Real.log x)
      Filter.atTop (nhds 0) := by
    have hloginv : Filter.Tendsto (fun x : ℝ => (Real.log x)⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have h := Filter.Tendsto.const_mul (Real.log c) hloginv
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with x
    rw [div_eq_mul_inv]
  have hratio : Filter.Tendsto (fun x : ℝ => Real.log (x / c) / Real.log x)
      Filter.atTop (nhds 1) := by
    have heq : (fun x : ℝ => Real.log (x / c) / Real.log x) =ᶠ[Filter.atTop]
        (fun x : ℝ => 1 - Real.log c / Real.log x) := by
      filter_upwards [Filter.eventually_gt_atTop 1] with x hx1
      have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx1
      have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hc0),
        sub_div, div_self hlogx]
    have h1 : Filter.Tendsto (fun x : ℝ => 1 - Real.log c / Real.log x)
        Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h1
    exact h1.congr' heq.symm
  have hsqrt : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log (x / c) / Real.log x))
      Filter.atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hratio
    rw [Real.sqrt_one] at h
    exact h
  have hinv : Filter.Tendsto
      (fun x : ℝ => (Real.sqrt (Real.log (x / c) / Real.log x))⁻¹)
      Filter.atTop (nhds 1) := by
    have h := Filter.Tendsto.inv₀ hsqrt one_ne_zero
    rwa [inv_one] at h
  refine hinv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 1 c)] with x hxc
  have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hxc
  have hxc' : c < x := lt_of_le_of_lt (le_max_right _ _) hxc
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hy1 : (1 : ℝ) < x / c := by
    rw [lt_div_iff₀ hc0]
    linarith
  have hlogy : (0 : ℝ) < Real.log (x / c) := Real.log_pos hy1
  rw [Real.sqrt_div hlogy.le, inv_div]

/-- Pointwise limit of the `k`-th summand in the `B`-sum. -/
private lemma lr_f_tendsto (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hH : Filter.Tendsto
      (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    Filter.Tendsto
      (fun x => lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (lrG k * (α / 2) / (k : ℝ) ^ 2)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  set c : ℝ := (k : ℝ) ^ 2 with hc
  have hcc : (0 : ℝ) < c := pow_pos hkpos 2
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hkR 2
  have h1 : Filter.Tendsto
      (fun x : ℝ => lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c))
      Filter.atTop (nhds (α / 2)) :=
    hH.comp (Filter.Tendsto.atTop_div_const hcc tendsto_id)
  have h2 := lr_sqrt_ratio_tendsto c hc1
  have hmul : Filter.Tendsto
      (fun x : ℝ => (lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c)) *
        (Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c))))
      Filter.atTop (nhds ((α / 2) * 1)) :=
    h1.mul h2
  rw [mul_one] at hmul
  have hscale : Filter.Tendsto
      (fun x : ℝ => (lrG k / c) *
        ((lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c)) *
        (Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c)))))
      Filter.atTop (nhds ((lrG k / c) * (α / 2))) :=
    Filter.Tendsto.const_mul _ hmul
  have e : (lrG k / c) * (α / 2) = lrG k * (α / 2) / c := by ring
  rw [e] at hscale
  refine hscale.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 1 c)] with x hxc
  have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hxc
  have hxc' : c < x := lt_of_le_of_lt (le_max_right _ _) hxc
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : (0 : ℝ) < x / c := div_pos hxpos hcc
  have hy1 : (1 : ℝ) < x / c := by
    rw [lt_div_iff₀ hcc]
    linarith
  have hlogy : (0 : ℝ) < Real.log (x / c) := Real.log_pos hy1
  have hs2 : Real.sqrt (Real.log (x / c)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hlogy)
  have hyc : (x / c) ≠ 0 := ne_of_gt hypos
  have hxc0 : x ≠ 0 := ne_of_gt hxpos
  have hc0n : c ≠ 0 := ne_of_gt hcc
  field_simp

/-- Uniform bound for `lrCount y · √(log y) / y` over `y ≥ 2`. -/
private lemma lr_count_uniform_bound (α : ℝ) (hα : 0 < α)
    (hH : Filter.Tendsto
      (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    ∃ D : ℝ, 0 < D ∧
      ∀ y : ℝ, 2 ≤ y → lrCount y * Real.sqrt (Real.log y) / y ≤ D := by
  have h1 : ∀ᶠ y : ℝ in Filter.atTop,
      lrCount y * Real.sqrt (Real.log y) / y < α / 2 + 1 :=
    hH.eventually (Iio_mem_nhds (by linarith))
  rw [Filter.eventually_atTop] at h1
  obtain ⟨Y₁, hY₁⟩ := h1
  set Y₀ : ℝ := max Y₁ 2 with hY₀
  have hY₀ge : (2 : ℝ) ≤ Y₀ := le_max_right _ _
  refine ⟨max (α / 2 + 1) (Real.sqrt (Real.log Y₀)),
    lt_max_of_lt_left (show (0 : ℝ) < α / 2 + 1 by linarith),
    fun y hy => ?_⟩
  rcases le_total y Y₀ with hle | hle
  · have hypos : (0 : ℝ) < y := by linarith
    have hYpos : (0 : ℝ) < Y₀ := by linarith
    have hlog_le : Real.log y ≤ Real.log Y₀ :=
      Real.log_le_log hypos hle
    have hsq_le : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log Y₀) :=
      Real.sqrt_le_sqrt hlog_le
    have h1 : lrCount y * Real.sqrt (Real.log y)
        ≤ Real.sqrt (Real.log Y₀) * y := by
      calc lrCount y * Real.sqrt (Real.log y)
          ≤ y * Real.sqrt (Real.log y) :=
            mul_le_mul_of_nonneg_right (lrCount_le hypos.le)
              (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (Real.log Y₀) * y := by
            calc y * Real.sqrt (Real.log y)
                ≤ y * Real.sqrt (Real.log Y₀) :=
                  mul_le_mul_of_nonneg_left hsq_le hypos.le
              _ = Real.sqrt (Real.log Y₀) * y := mul_comm _ _
    have h2 : lrCount y * Real.sqrt (Real.log y) / y
        ≤ Real.sqrt (Real.log Y₀) := by
      rw [div_le_iff₀ hypos]
      linarith [h1]
    exact le_trans h2 (le_max_right _ _)
  · have hY₁le : Y₁ ≤ y := le_trans (le_max_left _ _) hle
    have hlt := hY₁ y hY₁le
    have hle2 : lrCount y * Real.sqrt (Real.log y) / y ≤ α / 2 + 1 := le_of_lt hlt
    exact le_trans hle2 (le_max_left _ _)

/-- Dominating bound for the `k`-th summand in the `B`-sum. -/
private noncomputable def lrBnd (D : ℝ) (k : ℕ) : ℝ :=
  (Real.sqrt 2 * D + 2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2

/-- The dominating bound is summable. -/
private lemma lr_bnd_summable (D : ℝ) : Summable (lrBnd D) := by
  have h1 : Summable (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2) := by
    have hs : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have he : (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2)
        = (fun k : ℕ => (Real.sqrt 2 * D) * ((1 : ℝ) / (k : ℝ) ^ 2)) := by
      funext k
      ring
    rw [he]
    exact hs.mul_left _
  have h2 : Summable
      (fun k : ℕ => (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) := by
    have hs : Summable
        (fun k : ℕ => (2 : ℝ) * (((k : ℝ) ^ ((3 / 2 : ℝ)))⁻¹)) :=
      ((Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr
        (by norm_num)).mul_left 2
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs
    · apply div_nonneg _ (sq_nonneg _)
      apply mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hkpos : (0 : ℝ) < (k : ℝ) :=
          by exact_mod_cast Nat.pos_of_ne_zero hk0
        have hK : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
        have hR : (0 : ℝ) < (k : ℝ) ^ ((3 / 2 : ℝ)) :=
          Real.rpow_pos_of_pos hkpos _
        have hsqrt_le : Real.sqrt (Real.log k) ≤ Real.sqrt (k : ℝ) :=
          Real.sqrt_le_sqrt (Real.log_le_self hkpos.le)
        have hkey : Real.sqrt (Real.log k) * (k : ℝ) ^ ((3 / 2 : ℝ))
            ≤ (k : ℝ) ^ 2 := by
          have hle := mul_le_mul_of_nonneg_right hsqrt_le hR.le
          have eR : Real.sqrt (k : ℝ) * (k : ℝ) ^ ((3 / 2 : ℝ))
              = (k : ℝ) ^ 2 := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hkpos]
            norm_num [Real.rpow_two]
          rwa [eR] at hle
        have eR2 : (2 : ℝ) * (((k : ℝ) ^ ((3 / 2 : ℝ)))⁻¹)
            = 2 / (k : ℝ) ^ ((3 / 2 : ℝ)) :=
          (div_eq_mul_inv _ _).symm
        rw [eR2, div_le_div_iff₀ hK hR]
        have h2x := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 2 by norm_num)
        linarith [h2x]
  have hsum : Summable (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2 +
      (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) := h1.add h2
  have heq : (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2 +
      (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) = lrBnd D := by
    funext k
    unfold lrBnd
    rw [add_div]
  rw [← heq]
  exact hsum

/-- Domination of the `B`-summands by the summable bound. -/
private lemma lr_B_dominated (D : ℝ)
    (hDb : ∀ y : ℝ, 2 ≤ y → lrCount y * Real.sqrt (Real.log y) / y ≤ D) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k : ℕ,
      ‖lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x‖
        ≤ lrBnd D k := by
  have hDnn : (0 : ℝ) ≤ D := by
    have h2 := hDb 2 le_rfl
    have hnn : (0 : ℝ) ≤ lrCount 2 * Real.sqrt (Real.log 2) / 2 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (lrCount_nonneg _) (Real.sqrt_nonneg _)
    linarith
  filter_upwards [Filter.eventually_ge_atTop 16] with x hx
  intro k
  rcases eq_or_ne k 0 with rfl | hk0
  · have hb0 : lrBnd D 0 = 0 := by
      unfold lrBnd
      norm_num
    rw [lrG_zero, hb0]
    simp
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hc0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
    have hxpos : (0 : ℝ) < x := by linarith
    have hnn : (0 : ℝ)
        ≤ lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x := by
      apply div_nonneg _ hxpos.le
      apply mul_nonneg _ (Real.sqrt_nonneg _)
      exact mul_nonneg (lrG_nonneg k) (lrCount_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hlogk_nn : (0 : ℝ) ≤ Real.log k := Real.log_nonneg hkR
    have hb_extra : (0 : ℝ) ≤ 2 * Real.sqrt (Real.log k) :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hb_main : (0 : ℝ) ≤ Real.sqrt 2 * D :=
      mul_nonneg (Real.sqrt_nonneg _) hDnn
    by_cases hcase : (k : ℝ) ^ 2 ≤ Real.sqrt x
    · have hsqrt4 : (4 : ℝ) ≤ Real.sqrt x := by
        have h16 : Real.sqrt 16 ≤ Real.sqrt x :=
          Real.sqrt_le_sqrt (by linarith)
        have e16 : Real.sqrt (16 : ℝ) = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rwa [e16] at h16
      have hsqrtx_nn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
      have hy_ge : Real.sqrt x ≤ x / (k : ℝ) ^ 2 := by
        rw [le_div_iff₀ hc0]
        calc Real.sqrt x * (k : ℝ) ^ 2
            ≤ Real.sqrt x * Real.sqrt x :=
              mul_le_mul_of_nonneg_left hcase hsqrtx_nn
          _ = x := Real.mul_self_sqrt (by linarith)
      have hy2 : (2 : ℝ) ≤ x / (k : ℝ) ^ 2 := by linarith
      have hypos : (0 : ℝ) < x / (k : ℝ) ^ 2 := by linarith
      have hD := hDb _ hy2
      have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have hlogc : Real.log ((k : ℝ) ^ 2) ≤ (1 / 2) * Real.log x := by
        have h1 : Real.log ((k : ℝ) ^ 2) ≤ Real.log (Real.sqrt x) :=
          Real.log_le_log (pow_pos hkpos 2) hcase
        have h2 : Real.log (Real.sqrt x) = (1 / 2) * Real.log x := by
          rw [Real.log_sqrt (by linarith)]
          ring
        linarith
      have hlogy : Real.log (x / (k : ℝ) ^ 2)
          = Real.log x - Real.log ((k : ℝ) ^ 2) :=
        Real.log_div (ne_of_gt hxpos) (ne_of_gt hc0)
      have hlogy_ge : (1 / 2) * Real.log x ≤ Real.log (x / (k : ℝ) ^ 2) := by
        linarith
      have hlogy_pos : (0 : ℝ) < Real.log (x / (k : ℝ) ^ 2) := by linarith
      have hratio : Real.sqrt (Real.log x)
          / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) ≤ Real.sqrt 2 := by
        have h1 : Real.log x / Real.log (x / (k : ℝ) ^ 2) ≤ 2 := by
          rw [div_le_iff₀ hlogy_pos]
          linarith
        calc Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / (k : ℝ) ^ 2))
            = Real.sqrt (Real.log x / Real.log (x / (k : ℝ) ^ 2)) := by
              rw [Real.sqrt_div hlogx_pos.le]
          _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
      have hHle : lrCount (x / (k : ℝ) ^ 2)
          ≤ D * (x / (k : ℝ) ^ 2)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) := by
        have hspos : (0 : ℝ) < Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) :=
          Real.sqrt_pos.mpr hlogy_pos
        have hD' : lrCount (x / (k : ℝ) ^ 2)
              * Real.sqrt (Real.log (x / (k : ℝ) ^ 2))
            ≤ D * (x / (k : ℝ) ^ 2) :=
          (div_le_iff₀ hypos).mp hD
        rw [le_div_iff₀ hspos]
        exact hD'
      have g1 : lrG k * lrCount (x / (k : ℝ) ^ 2)
          ≤ D * (x / (k : ℝ) ^ 2)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) := by
        calc lrG k * lrCount (x / (k : ℝ) ^ 2)
            ≤ 1 * lrCount (x / (k : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (lrG_le_one k) (lrCount_nonneg _)
          _ = lrCount (x / (k : ℝ) ^ 2) := one_mul _
          _ ≤ _ := hHle
      have hspos : (0 : ℝ) < Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) :=
        Real.sqrt_pos.mpr hlogy_pos
      have hxc0 : x ≠ 0 := ne_of_gt hxpos
      have hc0n : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hc0
      have hs2n : Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) ≠ 0 := ne_of_gt hspos
      calc lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x
          ≤ (D * (x / (k : ℝ) ^ 2)
              / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)))
              * Real.sqrt (Real.log x) / x := by
              apply div_le_div_of_nonneg_right _ hxpos.le
              exact mul_le_mul_of_nonneg_right g1 (Real.sqrt_nonneg _)
        _ = D * (Real.sqrt (Real.log x)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2))) / (k : ℝ) ^ 2 := by
              field_simp
        _ ≤ D * Real.sqrt 2 / (k : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_right _ hc0.le
              exact mul_le_mul_of_nonneg_left hratio hDnn
        _ ≤ lrBnd D k := by
              unfold lrBnd
              apply div_le_div_of_nonneg_right _ hc0.le
              linarith [mul_comm D (Real.sqrt 2)]
    · have hlt : Real.sqrt x < (k : ℝ) ^ 2 := lt_of_not_ge hcase
      have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have hlog_lt : Real.log x < 4 * Real.log k := by
        have h1 : Real.log (Real.sqrt x) < Real.log ((k : ℝ) ^ 2) :=
          Real.log_lt_log (Real.sqrt_pos.mpr (by linarith)) hlt
        have h2 : Real.log (Real.sqrt x) = Real.log x / 2 :=
          Real.log_sqrt (by linarith)
        have h3 : Real.log ((k : ℝ) ^ 2) = 2 * Real.log (k : ℝ) := by
          rw [Real.log_pow]
          norm_num
        linarith
      have hy_nn : (0 : ℝ) ≤ x / (k : ℝ) ^ 2 := div_nonneg hxpos.le hc0.le
      have hHle : lrCount (x / (k : ℝ) ^ 2) ≤ x / (k : ℝ) ^ 2 :=
        lrCount_le hy_nn
      have hsq_le : Real.sqrt (Real.log x)
          ≤ 2 * Real.sqrt (Real.log k) := by
        have h1 : Real.log x ≤ 4 * Real.log k := le_of_lt hlog_lt
        calc Real.sqrt (Real.log x)
            ≤ Real.sqrt (4 * Real.log k) := Real.sqrt_le_sqrt h1
          _ = 2 * Real.sqrt (Real.log k) := by
              have e4 : Real.sqrt (4 : ℝ) = 2 := by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                  Real.sqrt_sq (by norm_num)]
              rw [Real.sqrt_mul (by norm_num), e4]
      have hxc0 : x ≠ 0 := ne_of_gt hxpos
      have hc0n : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hc0
      calc lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x
          ≤ 1 * (x / (k : ℝ) ^ 2) * (2 * Real.sqrt (Real.log k)) / x := by
            apply div_le_div_of_nonneg_right _ hxpos.le
            have g1 : lrG k * lrCount (x / (k : ℝ) ^ 2)
                ≤ 1 * (x / (k : ℝ) ^ 2) := by
              calc lrG k * lrCount (x / (k : ℝ) ^ 2)
                  ≤ 1 * lrCount (x / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_right (lrG_le_one k) (lrCount_nonneg _)
                _ ≤ 1 * (x / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_left hHle (by norm_num)
            exact mul_le_mul g1 hsq_le (Real.sqrt_nonneg _)
              (by simpa using hy_nn)
        _ = (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2 := by
              field_simp
        _ ≤ lrBnd D k := by
              unfold lrBnd
              apply div_le_div_of_nonneg_right _ hc0.le
              linarith [hb_main]

/-- `B(x) · √(log x) / x` as a topological sum over `k`. -/
private lemma lr_B_tsum (x : ℝ) :
    lrB x * Real.sqrt (Real.log x) / x
      = ∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x := by
  have hvan : ∀ k : ℕ, k ∉ Finset.Ioc 0 ⌊x⌋₊ →
      lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x = 0 := by
    intro k hk
    rw [Finset.mem_Ioc, not_and] at hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [lrG_zero]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk1pos : 0 < k := hk1
      have hkN : ⌊x⌋₊ < k := lt_of_not_ge (hk hk1pos)
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1pos
      have hc0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
      have hkk : (⌊x⌋₊ : ℝ) + 1 ≤ (k : ℝ) := by
        have h : ⌊x⌋₊ + 1 ≤ k := by omega
        calc (⌊x⌋₊ : ℝ) + 1 = ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_add, Nat.cast_one]
          _ ≤ (k : ℝ) := by exact_mod_cast h
      have hkx : x < (k : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) hkk
      have hkk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr h1k)]
      have hlt : x / (k : ℝ) ^ 2 < 1 := by
        rw [div_lt_one hc0]
        exact lt_of_lt_of_le hkx hkk2
      have h0 : lrCount (x / (k : ℝ) ^ 2) = 0 := lrCount_eq_zero_of_lt_one hlt
      simp [h0]
  have e : (∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
      * Real.sqrt (Real.log x) / x)
      = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x :=
    tsum_eq_sum hvan
  rw [e]
  unfold lrB
  rw [Finset.sum_mul, Finset.sum_div]

/-- Summability of `lrG k / k ^ 2`. -/
private lemma lr_G_div_sq_summable :
    Summable (fun k : ℕ => lrG k / (k : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  · apply div_nonneg (lrG_nonneg k)
    positivity
  · apply div_le_div_of_nonneg_right (lrG_le_one k) (by positivity)

/-- The `G`-series has positive sum. -/
private lemma lr_G_div_sq_tsum_pos :
    0 < ∑' k : ℕ, lrG k / (k : ℝ) ^ 2 := by
  refine Summable.tsum_pos lr_G_div_sq_summable (fun k => ?_) 1 ?_
  · apply div_nonneg (lrG_nonneg k)
    positivity
  · rw [lrG_one]
    norm_num

/-- Dominated convergence for the `k`-sum: `B(x) · √(log x) / x → c₀ > 0`. -/
private lemma lr_B_tendsto (α : ℝ) (hα : 0 < α)
    (hH : Filter.Tendsto (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Filter.Tendsto (fun x => lrB x * Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds c₀) := by
  obtain ⟨D, hDpos, hDb⟩ := lr_count_uniform_bound α hα hH
  have hBsum := lr_bnd_summable D
  have hpt : ∀ k : ℕ, Filter.Tendsto
      (fun x => lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (lrG k * (α / 2) / (k : ℝ) ^ 2)) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [lrG_zero, zero_mul, zero_div]
      exact tendsto_const_nhds
    · exact lr_f_tendsto k (Nat.one_le_iff_ne_zero.mpr hk0) α hH
  have hdom : ∀ᶠ x : ℝ in Filter.atTop, ∀ k : ℕ,
      ‖lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x‖
        ≤ lrBnd D k :=
    lr_B_dominated D hDb
  have hlim := tendsto_tsum_of_dominated_convergence hBsum hpt hdom
  have heq : (fun x : ℝ => ∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x)
      =ᶠ[Filter.atTop] (fun x => lrB x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_ge_atTop 0] with x _
    exact (lr_B_tsum x).symm
  have hlimB : Filter.Tendsto (fun x => lrB x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (∑' k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2)) :=
    hlim.congr' heq
  have hS := lr_G_div_sq_tsum_pos
  have htsum_eq : (∑' k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2)
      = (α / 2) * (∑' k : ℕ, lrG k / (k : ℝ) ^ 2) := by
    have e : ∀ k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2
        = (α / 2) * (lrG k / (k : ℝ) ^ 2) := fun k => by ring
    simp_rw [e]
    exact tsum_mul_left
  refine ⟨(α / 2) * (∑' k : ℕ, lrG k / (k : ℝ) ^ 2),
    mul_pos (by linarith) hS, ?_⟩
  rw [← htsum_eq]
  exact hlimB

/-- `√(log x) / x` tends to `0`. -/
private lemma lr_sqrt_log_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.sqrt (Real.log x) / x‖ ≤ x ^ ((-1 / 2 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hle : Real.sqrt (Real.log x) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (Real.log_le_self hxpos.le)
    have e : Real.sqrt x / x = x ^ ((-1 / 2 : ℝ)) := by
      have esub : ((1 / 2 : ℝ) - 1) = -1 / 2 := by norm_num
      rw [Real.sqrt_eq_rpow, ← esub, Real.rpow_sub hxpos, Real.rpow_one]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hxpos.le)]
    calc Real.sqrt (Real.log x) / x ≤ Real.sqrt x / x :=
          div_le_div_of_nonneg_right hle hxpos.le
      _ = x ^ ((-1 / 2 : ℝ)) := e
  have hg : Filter.Tendsto (fun x : ℝ => x ^ ((-1 / 2 : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have e : ((-1 / 2 : ℝ)) = -((1 / 2 : ℝ)) := by norm_num
    rw [e]
    simpa using h
  exact squeeze_zero_norm' hbound hg

@[expose] public section

/-- Landau–Ramanujan theorem: the count of distinct naturals `m ≤ x` of the form
    `m = a ^ 2 + b ^ 2` is asymptotically equivalent to
    `c₀ * x / Real.sqrt (Real.log x)` for some constant `c₀ > 0`.

    Scope note: this statement asserts only the existence of an unspecified
    positive constant `c₀`; it does not identify `c₀` with the
    Landau–Ramanujan constant (the Euler product over the primes
    `p ≡ 3 (mod 4)` in the cited result). That identification is an
    intentional omission relative to the source.

    Controlling source: Labib Haddad and Charles Helou,
    "Representation of Integers by Near Quadratic Sequences,"
    Journal of Integer Sequences 15 (2012),
    `https://cs.uwaterloo.ca/journals/JIS/VOL15/Helou/helou3.tex`,
    lines 483–486. Complete-source SHA-256
    `5441e9d5677d97ca6a836146d5725a10a21bb1e60efa374e366cd803626cd1b1`;
    exact cited span (CRLF-preserving) SHA-256
    `ce727da79eee9763f20dcbafc1b04c02d719c74c58648eddb71f0e34524e91bf`.
    Proof-method source (distinct from the statement source above): the proof
    adapts Wirsing's mean-value method as presented in Gérald Tenenbaum,
    *Introduction to Analytic and Probabilistic Number Theory*, Chapter III.4.
    Concept ID: jis_dep_8a097e6d8b6de10033dfb175;
    grounded candidate: jis_grounded_b8d7333e5ca6cb47b348367c;
    corrected mentions/papers/proof-uses: 2/1/1.

Proves `Wanted` entry `landau_ramanujan_asymptotic`. -/
public theorem landau_ramanujan_asymptotic :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Asymptotics.IsEquivalent (Filter.atTop : Filter ℝ)
        (fun x : ℝ =>
          ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ))
        (fun x : ℝ => c₀ * x / Real.sqrt (Real.log x)) := by
  obtain ⟨α, hαpos, hA⟩ := lr_A_tendsto
  have hH := lr_count_tendsto α hA
  obtain ⟨c₀, hc₀pos, hB⟩ := lr_B_tendsto α hαpos hH
  have hcount : ∀ᶠ x : ℝ in Filter.atTop,
      ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
        = lrB x + 1 := by
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have h1 := lr_ncard_eq hx
    have h2 := lr_twoSq_count_eq hx
    rw [h1, Nat.cast_add, Nat.cast_one, h2]
  have hratio : Filter.Tendsto
      (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧
        ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
        / (c₀ * x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds 1) := by
    have heq : (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧
          ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
          / (c₀ * x / Real.sqrt (Real.log x)))
        =ᶠ[Filter.atTop]
        (fun x : ℝ => (lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x) / c₀) := by
      filter_upwards [Filter.eventually_gt_atTop 1, hcount] with x hx1 hcx
      have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hsq : Real.sqrt (Real.log x) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hlog)
      have hxx : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
      have hc : c₀ ≠ 0 := ne_of_gt hc₀pos
      rw [hcx]
      field_simp
    have hB' : Filter.Tendsto
        (fun x : ℝ => lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds (c₀ + 0)) :=
      hB.add lr_sqrt_log_div_tendsto
    rw [add_zero] at hB'
    have hdiv : Filter.Tendsto
        (fun x : ℝ => (lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x) / c₀)
        Filter.atTop (nhds (c₀ / c₀)) :=
      hB'.div_const c₀
    have hc0 : c₀ ≠ 0 := ne_of_gt hc₀pos
    rw [div_self hc0] at hdiv
    exact hdiv.congr' heq.symm
  refine ⟨c₀, hc₀pos, ?_⟩
  exact Asymptotics.isEquivalent_of_tendsto_one hratio

end

end MetaMathlibExt

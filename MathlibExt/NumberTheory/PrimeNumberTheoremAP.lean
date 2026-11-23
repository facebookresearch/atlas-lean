/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClass
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import MathlibExt.NumberTheory.PrimeCounting.Chebyshev
import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Prime number theorem for arithmetic progressions

This file proves the prime number theorem for arithmetic progressions: for `q ≥ 2`
and `Nat.Coprime a q`, the count of primes `p ≤ n` with `p ≡ a [MOD q]` satisfies
`count * log n / n → 1 / φ(q)`.

The proof deduces the result from the weak prime number theorem in arithmetic
progressions (the `ψ`-asymptotic) by comparison with the classical Chebyshev
estimate, avoiding a residue-class Abel summation.
-/

namespace Chebyshev

/-- The sum of the residue-class von Mangoldt function over primes `p ≤ x`. -/
private noncomputable def pnapThetaResidueClass {q : ℕ} (b : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime,
    ArithmeticFunction.vonMangoldt.residueClass b n

/-- The difference `ψ_b - θ_b` is the non-prime von Mangoldt residue sum. -/
private lemma pnap_psiResidueClass_sub_thetaResidueClass_eq {q : ℕ}
    (b : ZMod q) (x : ℝ) :
    psiResidueClass b x - pnapThetaResidueClass b x
      = ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt.residueClass b n := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc 0 ⌊x⌋₊) (fun n => n.Prime)
    (fun n => ArithmeticFunction.vonMangoldt.residueClass b n)
  simp only [psiResidueClass, pnapThetaResidueClass] at hsplit ⊢
  rw [← hsplit]
  exact add_sub_cancel_left _ _

/-- The difference `ψ_b - θ_b` is nonnegative. -/
private lemma pnap_psiResidueClass_sub_thetaResidueClass_nonneg {q : ℕ}
    (b : ZMod q) (x : ℝ) :
    0 ≤ psiResidueClass b x - pnapThetaResidueClass b x := by
  rw [pnap_psiResidueClass_sub_thetaResidueClass_eq]
  exact Finset.sum_nonneg fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_nonneg b n

/-- The difference `ψ_b - θ_b` is at most the classical difference `ψ - θ`. -/
private lemma pnap_psiResidueClass_sub_thetaResidueClass_le {q : ℕ}
    (b : ZMod q) (x : ℝ) :
    psiResidueClass b x - pnapThetaResidueClass b x ≤ psi x - theta x := by
  rw [pnap_psiResidueClass_sub_thetaResidueClass_eq,
    psi_sub_theta_eq_sum_not_prime]
  exact Finset.sum_le_sum fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_le b n

/-- The real-variable prime number theorem in a residue class for `θ_b`. -/
private lemma pnap_tendsto_thetaResidueClass_div_self {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    Filter.Tendsto (fun x : ℝ => pnapThetaResidueClass b x / x) Filter.atTop
      (nhds ((q.totient : ℝ)⁻¹)) := by
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, (0 : ℝ) < x := Filter.eventually_gt_atTop 0
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt x) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop
  have hbound : Filter.Tendsto (fun x : ℝ => C * (Real.sqrt x / x)) Filter.atTop
      (nhds 0) := by
    have h2 := hsqrt.inv_tendsto_atTop.const_mul C
    rw [mul_zero] at h2
    refine Filter.Tendsto.congr (fun x => ?_) h2
    change C * (Real.sqrt x)⁻¹ = C * (Real.sqrt x / x)
    rw [Real.sqrt_div_self]
  have hsqueeze : Filter.Tendsto
      (fun x : ℝ => (psiResidueClass b x - pnapThetaResidueClass b x) / x)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hbound ?_ ?_
    · filter_upwards [hpos] with x hx
      exact div_nonneg (pnap_psiResidueClass_sub_thetaResidueClass_nonneg b x)
        (le_of_lt hx)
    · filter_upwards [hpos] with x hx
      have hle : (psiResidueClass b x - pnapThetaResidueClass b x) / x
          ≤ (psi x - theta x) / x := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (pnap_psiResidueClass_sub_thetaResidueClass_le b x)
          (inv_nonneg.mpr hx.le)
      have hle2 : (psi x - theta x) / x ≤ C * (Real.sqrt x / x) := by
        have hmul : C * (Real.sqrt x / x) = (C * Real.sqrt x) / x :=
          (mul_div_assoc _ _ _).symm
        rw [hmul]
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hC x) (inv_nonneg.mpr hx.le)
      exact le_trans hle hle2
  have hpsi := tendsto_psiResidueClass_div_self (q := q) b hb
  have hsub := hpsi.sub hsqueeze
  rw [sub_zero] at hsub
  have heq : (fun x : ℝ => pnapThetaResidueClass b x / x)
      =ᶠ[Filter.atTop]
        (fun x : ℝ => psiResidueClass b x / x
          - (psiResidueClass b x - pnapThetaResidueClass b x) / x) := by
    filter_upwards [Filter.eventually_ne_atTop 0] with x hx
    field_simp
    ring
  exact Filter.Tendsto.congr' heq.symm hsub

end Chebyshev

namespace MathlibExt.NumberTheory.PrimeNumberTheoremAPWanted

/-- `θ_b` at a natural number is the sum of `log p` over the wanted finset. -/
private lemma pnap_thetaResidueClass_natCast_eq_sum_log {q : ℕ} [NeZero q]
    (a n : ℕ) :
    Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ)
      = ∑ p ∈ (Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a,
        Real.log (p : ℝ) := by
  have hIoc : (Finset.Ioc 0 n).filter (fun k => k.Prime) = Nat.primesLE n :=
    (Nat.primesLE_eq_filter_Ioc_zero n).symm
  have hfilter : (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ Nat.ModEq q p a)
      = (Nat.primesLE n).filter (fun p : ℕ => (p : ZMod q) = (a : ZMod q)) := by
    rw [Nat.primesLE_eq_filter_range, Finset.filter_filter]
    exact Finset.filter_congr fun p _ =>
      and_congr_right fun _ => (ZMod.natCast_eq_natCast_iff p a q).symm
  have hrc : ∀ p : ℕ, p.Prime →
      ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) p
        = if (p : ZMod q) = (a : ZMod q) then Real.log (p : ℝ) else 0 := by
    intro p hp
    unfold ArithmeticFunction.vonMangoldt.residueClass
    split_ifs with hcast
    · have hmem : p ∈ {n : ℕ | (n : ZMod q) = (a : ZMod q)} := hcast
      rw [Set.indicator_of_mem hmem]
      exact ArithmeticFunction.vonMangoldt_apply_prime hp
    · have hmem : p ∉ {n : ℕ | (n : ZMod q) = (a : ZMod q)} := hcast
      exact Set.indicator_of_notMem hmem _
  unfold Chebyshev.pnapThetaResidueClass
  rw [Nat.floor_natCast, hIoc, hfilter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun p hp => hrc p (Nat.mem_primesLE.mp hp).2

/-- The residue-class counting error is between `0` and the classical error. -/
private lemma pnap_card_sub_thetaResidueClass_div_log_le {q : ℕ} [NeZero q]
    (a n : ℕ) (hn : 2 ≤ n) :
    0 ≤ (((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ)
        - Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ) / Real.log (n : ℝ)
      ∧ (((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ)
        - Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ) / Real.log (n : ℝ)
        ≤ (Nat.primeCounting n : ℝ) - Chebyshev.theta (n : ℝ) / Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn1
  have hM3 := pnap_thetaResidueClass_natCast_eq_sum_log (q := q) (a := a) (n := n)
  have hterm : ∀ p ∈ Nat.primesLE n,
      (0 : ℝ) ≤ 1 - Real.log (p : ℝ) / Real.log (n : ℝ) := by
    intro p hp
    have hprime : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have hplog : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast Nat.le_of_mem_primesLE hp)
    have hdiv : Real.log (p : ℝ) / Real.log (n : ℝ) ≤ 1 := (div_le_one hL).mpr hplog
    linarith
  have hsub : (Finset.range (n + 1)).filter
        (fun p => Nat.Prime p ∧ Nat.ModEq q p a) ⊆ Nat.primesLE n := by
    rw [Nat.primesLE_eq_filter_range]
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hEb : ((((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ)
        - Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ) / Real.log (n : ℝ))
      = ∑ p ∈ (Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a,
        (1 - Real.log (p : ℝ) / Real.log (n : ℝ)) := by
    rw [hM3, Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  have hE : ((Nat.primeCounting n : ℝ) - Chebyshev.theta (n : ℝ) / Real.log (n : ℝ))
      = ∑ p ∈ Nat.primesLE n, (1 - Real.log (p : ℝ) / Real.log (n : ℝ)) := by
    have hcard : (Nat.primeCounting n : ℝ) = ((Nat.primesLE n).card : ℝ) := by
      rw [Nat.primesLE_card_eq_primeCounting]
    rw [hcard, Chebyshev.theta_eq_sum_primesLE_log, Finset.card_eq_sum_ones,
      Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [hEb, hE]
  exact ⟨Finset.sum_nonneg fun p hp => hterm p (hsub hp),
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hterm p hp⟩

/-- The residue-class error times `log n / n` tends to zero. -/
private lemma pnap_tendsto_card_sub_thetaResidueClass_mul_log_div {q : ℕ} [NeZero q]
    (a : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        ((((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ)
          - Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ) / Real.log (n : ℝ)) *
          Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hnat : Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => (Nat.primeCounting n : ℝ) - Chebyshev.theta (n : ℝ) / Real.log (n : ℝ))
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
    have hcomp := Chebyshev.primeCounting_sub_theta_div_log_isLittleO.comp_tendsto
      tendsto_natCast_atTop_atTop
    refine hcomp.congr (fun n => ?_) (fun n => ?_)
    · simp only [Function.comp_apply, Nat.floor_natCast]
    · simp only [Function.comp_apply]
  have hnorm : ∀ᶠ n : ℕ in Filter.atTop,
      ‖((((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ)
        - Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ) / Real.log (n : ℝ))‖
        ≤ 1 * ‖(Nat.primeCounting n : ℝ) - Chebyshev.theta (n : ℝ) / Real.log (n : ℝ)‖ := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    obtain ⟨h0, hle⟩ := pnap_card_sub_thetaResidueClass_div_log_le (q := q) a n hn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
    exact le_trans hle (le_abs_self _)
  have hbig := Asymptotics.IsBigO.of_bound 1 hnorm
  have hEbLittle := hbig.trans_isLittleO hnat
  have hzero := hEbLittle.tendsto_div_nhds_zero
  refine Filter.Tendsto.congr (fun n => ?_) hzero
  rw [div_div_eq_mul_div]

end MathlibExt.NumberTheory.PrimeNumberTheoremAPWanted

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeNumberTheoremAPWanted

/--
**Prime number theorem in arithmetic progressions.** Let $q \ge 2$ and $a$ be natural numbers
with $\gcd(a, q) = 1$, and for each natural number $n$ let $N(n)$ be the number of primes
$p \le n$ with $p \equiv a \pmod q$. Then $N(n) \log n / n \to 1 / \varphi(q)$ as $n \to \infty$,
where $\varphi$ is Euler's totient function and $\log$ is the natural logarithm.

Proves `Wanted` entry `prime_number_theorem_arithmetic_progression`.

Source: G. L. Dirichlet 1837
existence, PNT for AP by de la Vallée Poussin and Hadamard 1896-1899 extensions; textbook in
Montgomery-Vaughan, Multiplicative Number Theory I, Multiplicative Number Theory
-/
public theorem prime_number_theorem_arithmetic_progression :
    ∀ (q a : ℕ), 2 ≤ q → Nat.Coprime a q →
      Filter.Tendsto
        (fun n : ℕ =>
          (((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ) *
            Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (nhds (1 / (Nat.totient q : ℝ))) := by
  intro q a hq hcop
  have : NeZero q := ⟨by omega⟩
  have hb : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
  have htheta : Filter.Tendsto
      (fun n : ℕ => Chebyshev.pnapThetaResidueClass (a : ZMod q) (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds ((q.totient : ℝ)⁻¹)) :=
    (Chebyshev.pnap_tendsto_thetaResidueClass_div_self (a : ZMod q) hb).comp
      tendsto_natCast_atTop_atTop
  have herr := pnap_tendsto_card_sub_thetaResidueClass_mul_log_div (q := q) a
  have hadd := htheta.add herr
  have hlim : Filter.Tendsto
      (fun n : ℕ =>
        (((Finset.range (n + 1)).filter fun p => Nat.Prime p ∧ Nat.ModEq q p a).card : ℝ) *
          Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds ((q.totient : ℝ)⁻¹ + 0)) := by
    refine Filter.Tendsto.congr' ?_ hadd
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
    ring
  simpa using hlim

/-- **Prime number theorem for the residue-class prime count.** Let $q \ge 2$ and $a$ be natural
numbers with $\gcd(a, q) = 1$, and let $\pi(n; q, a)$ be the number of primes $p \le n$ with
$p \equiv a \pmod q$. Then $\pi(n; q, a) \log n / n \to 1 / \varphi(q)$ as $n \to \infty$,
where $\varphi$ is Euler's totient function and $\log$ is the natural logarithm. -/
public theorem tendsto_primeCountingMod_mul_log_div (q a : ℕ)
    (hq : 2 ≤ q) (hcop : Nat.Coprime a q) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.primeCountingMod n q a : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds (1 / (Nat.totient q : ℝ))) := by
  simpa only [Nat.primeCountingMod_eq_card_filter_range] using
    prime_number_theorem_arithmetic_progression q a hq hcop

end MathlibExt.NumberTheory.PrimeNumberTheoremAPWanted

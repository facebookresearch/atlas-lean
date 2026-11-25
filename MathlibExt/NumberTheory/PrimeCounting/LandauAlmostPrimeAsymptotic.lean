/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.AlmostPrime
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.PrimeCounting.Chebyshev
import MathlibExt.NumberTheory.PrimeNumberTheorem

namespace MetaMathlibExt

open Asymptotics Filter Nat Chebyshev ArithmeticFunction

attribute [local instance] Classical.propDecidable

@[expose] public section


open Classical in
/-- **Counting almost primes.** For natural numbers $k$ and $x$, $\pi_k(x)$ is the number of
integers $n$ with $1 \le n \le x$ that have exactly $k$ prime factors, counted with multiplicity.
This is the counting function in Landau's theorem on almost primes.

Source: Rafael Jakimczuk, "Functions of Slow Increase and Integer Sequences,"
Journal of Integer Sequences 13 (2010),
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Jakimczuk/jakimczuk8.tex`,
lines 451-453, file SHA256
`b4a7154095398fc4a1729bef9ec80c4005190c1d9ad1dd585fbd2fcdd1eae8d7`, text SHA256
`4af87d665e5485d49e794b3927864d50a1162127411c1427d0f1a379b50b2065`,
module `WantedExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptoticWanted`. -/
noncomputable def almostPrimeCounting (k x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => Nat.IsAlmostPrime k n)).card

open Classical in
/-- Sum of `1 / p` over primes `p ∈ [1, N]`. -/
private noncomputable def lapPrimeRecipSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p), (1 : ℝ) / (p : ℝ)

open Classical in
/-- Sum of `1 / m` over `k`-almost-primes `m ∈ [1, N]`. -/
private noncomputable def lapAlmostPrimeRecipSum (k N : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime k m), (1 : ℝ) / (m : ℝ)

open Classical in
/-- Restriction of an arithmetic function to `j`-almost-primes. -/
private noncomputable def lapRestrictAlmostPrime (j : ℕ) (f : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.IsAlmostPrime j n then f n else 0, by simp [Nat.IsAlmostPrime]⟩

/-- Generic sandwich for `~`. -/
private theorem lapIsEquivalent_of_le_of_le {α : Type*} {l : Filter α}
    {lo u hi v : α → ℝ}
    (hle : ∀ᶠ x in l, lo x ≤ u x ∧ u x ≤ hi x)
    (hlo : lo ~[l] v) (hhi : hi ~[l] v) : u ~[l] v := by
  have hlo' : (lo - v) =o[l] v := hlo
  have hhi' : (hi - v) =o[l] v := hhi
  change (u - v) =o[l] v
  rw [Asymptotics.isLittleO_iff] at hlo' hhi' ⊢
  intro c hc
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  filter_upwards [hlo' hc2, hhi' hc2, hle] with x hlo_x hhi_x hle_x
  simp only [Pi.sub_apply] at hlo_x hhi_x ⊢
  have h1 : lo x - v x ≤ u x - v x := by linarith [hle_x.1]
  have h2 : u x - v x ≤ hi x - v x := by linarith [hle_x.2]
  have h3 : ‖u x - v x‖ ≤ ‖lo x - v x‖ + ‖hi x - v x‖ := by
    rcases le_total 0 (u x - v x) with hpos | hneg
    · rw [Real.norm_eq_abs, abs_of_nonneg hpos, Real.norm_eq_abs]
      exact le_trans h2
        (le_trans (le_abs_self _) (le_add_of_nonneg_left (abs_nonneg _)))
    · rw [Real.norm_eq_abs, abs_of_nonpos hneg, Real.norm_eq_abs]
      exact le_trans (neg_le_neg h1)
        (le_trans (neg_le_abs _) (le_add_of_nonneg_right (abs_nonneg _)))
  linarith [hlo_x, hhi_x, h3]

/-- The prime-power reciprocal sum at one prime is `O(p ^ (-3/2))`. -/
private theorem lapGeomPrime (p N : ℕ) (hp : Nat.Prime p) :
    ∑ a ∈ Finset.Icc 2 N,
      ArithmeticFunction.vonMangoldt (p ^ a) / ((p ^ a : ℕ) : ℝ)
      ≤ 4 * (((p : ℝ) ^ (3/2 : ℝ))⁻¹) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hp2
  have hq1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hlogp : Real.log (p:ℝ) ≤ 2 * (p:ℝ)^((1/2):ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hq0) (show (0:ℝ) < 1/2 by norm_num)
    have e : ((p:ℝ)^((1/2):ℝ))/(1/2:ℝ) = 2 * (p:ℝ)^((1/2):ℝ) := by ring
    rwa [e] at h
  have hterm : ∀ a ∈ Finset.Icc 2 N,
      ArithmeticFunction.vonMangoldt (p ^ a) / ((p ^ a : ℕ) : ℝ)
      = Real.log (p:ℝ) * (((p:ℝ)^a)⁻¹) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha0 : a ≠ 0 := by omega
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha0,
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, div_eq_mul_inv]
  have hSnn : 0 ≤ ∑ a ∈ Finset.Icc 2 N, (((p:ℝ)^a)⁻¹) := by
    apply Finset.sum_nonneg
    intro a _
    positivity
  have hS : ∑ a ∈ Finset.Icc 2 N, (((p:ℝ)^a)⁻¹) ≤ 2 / (p:ℝ)^2 := by
    have eI : Finset.Icc 2 N = Finset.Ico 2 (N+1) :=
      (Finset.Ico_add_one_right_eq_Icc 2 N).symm
    have hterm2 : ∀ a ∈ Finset.Ico 2 (N+1), (((p:ℝ)^a)⁻¹) = (((p:ℝ)⁻¹)^a) :=
      fun a _ => (inv_pow _ _).symm
    rw [eI, Finset.sum_congr rfl hterm2]
    have hy1 : ((p:ℝ)⁻¹) < 1 := by
      rw [← one_div, div_lt_one hq0]
      exact hq1
    have hle : ∑ a ∈ Finset.Ico 2 (N+1), (((p:ℝ)⁻¹)^a)
        ≤ (((p:ℝ)⁻¹)^2)/(1-((p:ℝ)⁻¹)) :=
      geom_sum_Ico_le_of_lt_one (inv_nonneg.mpr (le_of_lt hq0)) hy1
    have h1m : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by
      rw [sub_pos]
      exact hy1
    have e2 : (((p:ℝ)⁻¹)^2)/(1-((p:ℝ)⁻¹)) ≤ 2/(p:ℝ)^2 := by
      rw [div_le_div_iff₀ h1m (by positivity)]
      have e3 : (((p:ℝ)⁻¹)^2) * (p:ℝ)^2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hq0), one_pow]
      rw [e3]
      have hy2 : ((p:ℝ))⁻¹ ≤ 1/2 := by
        rw [← one_div, div_le_div_iff₀ hq0 (by norm_num)]
        have hq2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
        linarith
      linarith [hy2]
    exact le_trans hle e2
  have hfin : (p:ℝ)^((1/2):ℝ) / (p:ℝ)^2 = (((p:ℝ)^((3/2):ℝ))⁻¹) := by
    have key : (p:ℝ)^((3/2):ℝ) * (p:ℝ)^((1/2):ℝ) = (p:ℝ)^2 := by
      have e : (3/2 : ℝ) + 1/2 = ((2:ℕ):ℝ) := by norm_num
      rw [← Real.rpow_add hq0, e, Real.rpow_natCast]
    have h1 : (p:ℝ)^((3/2):ℝ) ≠ 0 := by positivity
    have h2 : (p:ℝ)^2 ≠ 0 := by positivity
    field_simp
    linear_combination key
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  calc Real.log (p:ℝ) * ∑ a ∈ Finset.Icc 2 N, (((p:ℝ)^a)⁻¹)
      ≤ (2 * (p:ℝ)^((1/2):ℝ)) * (2/(p:ℝ)^2) :=
        mul_le_mul hlogp hS hSnn (by positivity)
    _ = 4 * ((p:ℝ)^((1/2):ℝ)/(p:ℝ)^2) := by ring
    _ = 4 * (((p:ℝ)^((3/2):ℝ))⁻¹) := by rw [hfin]

/-- Each nonprime term is covered by the prime-power double sum. -/
private theorem lapCoverNonprime (N d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
    (if ¬ Nat.Prime d then
      ArithmeticFunction.vonMangoldt d / (d : ℝ) else 0)
    ≤ ∑ x ∈ (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N,
      (if x.1 ^ x.2 = d then
        ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ)
      else 0) := by
  have hnn : ∀ x ∈ (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N,
      0 ≤ (if x.1 ^ x.2 = d then
        ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ)
      else 0) := by
    intro x _
    split_ifs with h
    · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      exact Nat.cast_nonneg _
    · exact le_refl 0
  by_cases hprime : Nat.Prime d
  · rw [ite_eq_right (not_not.mpr hprime)]
    exact Finset.sum_nonneg hnn
  · by_cases hpp : IsPrimePow d
    · obtain ⟨p, k, hpk_prime, hkpos, hpk_eq⟩ := isPrimePow_nat_iff d |>.mp hpp
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · have hk1 : k = 1 := by omega
          exfalso
          rw [hk1, pow_one] at hpk_eq
          exact hprime (hpk_eq ▸ hpk_prime)
        · exact hge
      have hpd : p ≤ d := hpk_eq ▸ Nat.le_self_pow (by omega) p
      rw [Finset.mem_Icc] at hd
      have hp_mem : p ∈ (Finset.Icc 1 N).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hpk_prime.one_le, by omega⟩, hpk_prime⟩
      have hk_mem : k ∈ Finset.Icc 2 N := by
        rw [Finset.mem_Icc]
        have h2k : 2 ^ k ≤ d := hpk_eq ▸ Nat.pow_le_pow_left hpk_prime.two_le k
        have hkle : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
        omega
      have hmem : (p, k) ∈
          (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N :=
        Finset.mk_mem_product hp_mem hk_mem
      rw [ite_eq_left hprime]
      have h1 := Finset.single_le_sum hnn hmem
      simpa [hpk_eq] using h1
    · have h0 : ArithmeticFunction.vonMangoldt d / (d:ℝ) = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
        exact zero_div _
      rw [ite_eq_left hprime, h0]
      exact Finset.sum_nonneg hnn

/-- The nonprime von Mangoldt reciprocal sum is bounded. -/
private theorem lapSumNonprimeVonMangoldtDivLe :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ Nat.Prime d),
        ArithmeticFunction.vonMangoldt d / (d : ℝ) ≤ C := by
  have hsumm : Summable (fun n : ℕ => (4:ℝ) * (((n : ℝ) ^ (3/2 : ℝ))⁻¹)) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine ⟨∑' n : ℕ, (4:ℝ) * (((n : ℝ) ^ (3/2 : ℝ))⁻¹),
    tsum_nonneg (fun n => by positivity), fun N => ?_⟩
  have hinner : ∀ x ∈ (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N,
      ∑ d ∈ Finset.Icc 1 N, (if x.1 ^ x.2 = d then
        ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ)
      else 0)
      ≤ ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ) := by
    intro x _
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · exact le_refl _
    · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      exact Nat.cast_nonneg _
  calc ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ Nat.Prime d),
          ArithmeticFunction.vonMangoldt d / (d : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, (if ¬ Nat.Prime d then
          ArithmeticFunction.vonMangoldt d / (d:ℝ) else 0) :=
        (Finset.sum_filter _ _)
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ x ∈
          (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N,
          (if x.1 ^ x.2 = d then
            ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ)
          else 0) :=
        Finset.sum_le_sum (fun d hd => lapCoverNonprime N d hd)
    _ = ∑ x ∈ (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N,
          ∑ d ∈ Finset.Icc 1 N, (if x.1 ^ x.2 = d then
            ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ)
          else 0) := Finset.sum_comm
    _ ≤ ∑ x ∈ (Finset.Icc 1 N).filter Nat.Prime ×ˢ Finset.Icc 2 N,
          ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / (((x.1 ^ x.2 : ℕ)) : ℝ) :=
        Finset.sum_le_sum hinner
    _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ a ∈ Finset.Icc 2 N,
          ArithmeticFunction.vonMangoldt (p ^ a) / (((p ^ a : ℕ)) : ℝ) :=
        Finset.sum_product _ _ _
    _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          4 * (((p : ℝ) ^ (3/2 : ℝ))⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        exact lapGeomPrime p N hp.2
    _ ≤ ∑' n : ℕ, (4:ℝ) * (((n : ℝ) ^ (3/2 : ℝ))⁻¹) :=
        hsumm.sum_le_tsum _ (fun p _ => by positivity)

/-- The constant bounding the nonprime von Mangoldt sum. -/
private noncomputable def lapC : ℝ := Classical.choose lapSumNonprimeVonMangoldtDivLe

private theorem lapC_nonneg : 0 ≤ lapC :=
  (Classical.choose_spec lapSumNonprimeVonMangoldtDivLe).1

private theorem lapC_bound (N : ℕ) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ Nat.Prime d),
      ArithmeticFunction.vonMangoldt d / (d : ℝ) ≤ lapC :=
  (Classical.choose_spec lapSumNonprimeVonMangoldtDivLe).2 N

/-- Elementary Stirling-type bound. -/
private theorem lapSumLogDivLe (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / (m : ℝ)) ≤ (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hfactR : ((N.factorial : ℕ) : ℝ) ≠ 0 :=
      by exact_mod_cast Nat.factorial_ne_zero N
    have hprod : (∏ m ∈ Finset.Icc 1 N, (m : ℝ)) = ((N.factorial : ℕ) : ℝ) := by
      rw [← Nat.cast_prod, ← Finset.Ico_add_one_right_eq_Icc,
        Finset.prod_Ico_id_eq_factorial]
    have hterm : ∀ m ∈ Finset.Icc 1 N,
        Real.log ((N : ℝ) / (m : ℝ)) = Real.log N - Real.log (m : ℝ) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      exact Real.log_div (ne_of_gt hNr) (by exact_mod_cast ne_of_gt hm.1)
    have hconst : ∑ _m ∈ Finset.Icc 1 N, Real.log (N : ℝ)
        = (N : ℝ) * Real.log N := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
    have hsum : ∑ m ∈ Finset.Icc 1 N, Real.log ((N : ℝ) / (m : ℝ))
        = (N : ℝ) * Real.log N - Real.log ((N.factorial : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hconst,
        ← Real.log_prod (fun m hm => by
          rw [Finset.mem_Icc] at hm
          exact_mod_cast ne_of_gt hm.1), hprod]
    rw [hsum]
    have hle := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (le_of_lt hNr) N
    have hpos : (0 : ℝ) < (N : ℝ) ^ N / ((N.factorial : ℕ) : ℝ) := by
      positivity
    have hlog := Real.log_le_log hpos hle
    rw [Real.log_div (by positivity) hfactR, Real.log_pow, Real.log_exp] at hlog
    exact hlog

/-- `θ(n) ~ n` over `ℕ` from the public PNT. -/
private theorem lapThetaIsEquivalent :
    (fun n : ℕ => Chebyshev.theta (n : ℝ)) ~[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  have hfloor : (fun x : ℝ => ((⌊x⌋₊ : ℕ) : ℝ)) ~[Filter.atTop] (fun x : ℝ => x) :=
    Asymptotics.isEquivalent_nat_floor
  have hlog : (fun x : ℝ => Real.log ((⌊x⌋₊ : ℕ) : ℝ)) ~[Filter.atTop]
      (fun x : ℝ => Real.log x) :=
    Asymptotics.IsEquivalent.log hfloor tendsto_id
  have hPNT := MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem
  have hfl : Filter.Tendsto (Nat.floor : ℝ → ℕ) Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop
  have hcomp := hPNT.comp_tendsto hfl
  have hmid : (fun x : ℝ => ((⌊x⌋₊ : ℕ) : ℝ) / Real.log ((⌊x⌋₊ : ℕ) : ℝ))
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x) := hfloor.div hlog
  have hR : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x) := hcomp.trans hmid
  have htheta : Chebyshev.theta ~[Filter.atTop] (fun x : ℝ => x) :=
    Chebyshev.theta_isEquivalent_of_primeCounting_isEquivalent hR
  exact htheta.comp_tendsto tendsto_natCast_atTop_atTop

/-- Auxiliary definitions for the PNT error summand. -/
private noncomputable def lapH (n : ℕ) : ℝ :=
  Real.log (Real.log ((max n 2 : ℕ) : ℝ))

private noncomputable def lapG (n : ℕ) : ℝ := lapH (n + 1) - lapH n

private noncomputable def lapB (n : ℕ) : ℝ :=
  (Nat.primeCounting n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))

/-- Two-sided bound on the log-log difference. -/
private theorem lapG_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / (((n:ℝ)+1) * Real.log ((n:ℝ)+1)) ≤ lapG n ∧
    lapG n ≤ 1 / ((n:ℝ) * Real.log (n:ℝ)) := by
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have ha0 : (0:ℝ) < (n:ℝ) := by linarith
  have ha1 : (0:ℝ) < (n:ℝ)+1 := by linarith
  have ha0n : (n:ℝ) ≠ 0 := ne_of_gt ha0
  have ha1n : (n:ℝ)+1 ≠ 0 := ne_of_gt ha1
  have hlogn : (0:ℝ) < Real.log (n:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogn1 : (0:ℝ) < Real.log ((n:ℝ)+1) := Real.log_pos (by linarith)
  have hloglt : Real.log (n:ℝ) < Real.log ((n:ℝ)+1) :=
    Real.log_lt_log ha0 (by linarith)
  have hlogn_n : Real.log (n:ℝ) ≠ 0 := ne_of_gt hlogn
  have hlogn1_n : Real.log ((n:ℝ)+1) ≠ 0 := ne_of_gt hlogn1
  have hmax1 : max n 2 = n := Nat.max_eq_left hn
  have hmax2 : max (n+1) 2 = n+1 := Nat.max_eq_left (by omega)
  have hg : lapG n
      = Real.log (Real.log ((n:ℝ)+1)) - Real.log (Real.log (n:ℝ)) := by
    change Real.log (Real.log ((max (n+1) 2 : ℕ):ℝ))
      - Real.log (Real.log ((max n 2 : ℕ):ℝ)) = _
    rw [hmax1, hmax2, Nat.cast_add, Nat.cast_one]
  have hdy : Real.log ((n:ℝ)+1) - Real.log (n:ℝ)
      = Real.log (((n:ℝ)+1)/(n:ℝ)) := by
    rw [Real.log_div ha1n ha0n]
  have hposdiv : (0:ℝ) < ((n:ℝ)+1)/(n:ℝ) := by positivity
  have hd_lo : 1/((n:ℝ)+1)
      ≤ Real.log ((n:ℝ)+1) - Real.log (n:ℝ) := by
    rw [hdy]
    have h := Real.one_sub_inv_le_log_of_pos hposdiv
    have e : (1:ℝ) - ((((n:ℝ)+1)/(n:ℝ))⁻¹) = 1/((n:ℝ)+1) := by
      rw [inv_div, eq_div_iff ha1n, sub_mul, div_mul_cancel₀ _ ha1n, one_mul]
      ring
    rwa [e] at h
  have hd_hi : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) ≤ 1/(n:ℝ) := by
    rw [hdy]
    have h := Real.log_le_sub_one_of_pos hposdiv
    have e : ((n:ℝ)+1)/(n:ℝ) - 1 = 1/(n:ℝ) := by
      rw [add_div, div_self ha0n]
      ring
    rwa [e] at h
  have hy1 : (1:ℝ) < Real.log ((n:ℝ)+1) / Real.log (n:ℝ) := by
    rw [lt_div_iff₀ hlogn]
    linarith [hloglt]
  have hgy : lapG n = Real.log (Real.log ((n:ℝ)+1) / Real.log (n:ℝ)) := by
    rw [hg, Real.log_div hlogn1_n hlogn_n]
  have hlow : 1/(((n:ℝ)+1)*Real.log ((n:ℝ)+1)) ≤ lapG n := by
    rw [hgy]
    have h1 := Real.one_sub_inv_le_log_of_pos (lt_trans zero_lt_one hy1)
    have e : (1:ℝ) - (Real.log ((n:ℝ)+1) / Real.log (n:ℝ))⁻¹
        = (Real.log ((n:ℝ)+1) - Real.log (n:ℝ)) / Real.log ((n:ℝ)+1) := by
      field_simp
    rw [e] at h1
    refine le_trans ?_ h1
    rw [div_mul_eq_div_div, div_le_div_iff_of_pos_right hlogn1]
    exact hd_lo
  have hup : lapG n ≤ 1/((n:ℝ)*Real.log (n:ℝ)) := by
    rw [hgy]
    have h1 := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hy1)
    have e : Real.log ((n:ℝ)+1) / Real.log (n:ℝ) - 1
        = (Real.log ((n:ℝ)+1) - Real.log (n:ℝ)) / Real.log (n:ℝ) := by
      field_simp
    rw [e] at h1
    refine le_trans h1 ?_
    rw [div_mul_eq_div_div, div_le_div_iff_of_pos_right hlogn]
    exact hd_hi
  exact ⟨hlow, hup⟩

/-- The PNT error summand is equivalent to the log-log difference. -/
private theorem lapBIsEquivalentG : lapB ~[Filter.atTop] lapG := by
  have hPNT := MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem
  have hlim : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)/(n:ℝ)) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1:ℝ) + 1/(n:ℝ)) Filter.atTop
        (nhds (1+0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    refine Filter.Tendsto.congr' ?_ h1
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    field_simp
  have h2 : (fun n : ℕ => (n:ℝ)+1) ~[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    Asymptotics.isEquivalent_of_tendsto_one hlim
  have h3 : (fun n : ℕ => (n:ℝ)*((n:ℝ)+1)) ~[Filter.atTop]
      (fun n : ℕ => (n:ℝ)*(n:ℝ)) :=
    Asymptotics.IsEquivalent.refl.mul h2
  have hlog2 : (fun n : ℕ => Real.log ((n:ℝ)+1)) ~[Filter.atTop]
      (fun n : ℕ => Real.log (n:ℝ)) :=
    Asymptotics.IsEquivalent.log h2 tendsto_natCast_atTop_atTop
  have hb : lapB ~[Filter.atTop] (fun n : ℕ => 1/((n:ℝ)*Real.log (n:ℝ))) := by
    have hdiv := hPNT.div h3
    have hmid : (fun n : ℕ => ((n:ℝ)/Real.log (n:ℝ))/((n:ℝ)*(n:ℝ)))
        =ᶠ[Filter.atTop] (fun n : ℕ => 1/((n:ℝ)*Real.log (n:ℝ))) := by
      filter_upwards [Filter.eventually_gt_atTop 1] with n hn
      have hn0 : (n:ℝ) ≠ 0 :=
        by exact_mod_cast ne_of_gt (lt_trans zero_lt_one hn)
      have hlog : Real.log (n:ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast hn))
      field_simp
    exact hdiv.congr_right hmid
  have hlo : (fun n : ℕ => 1/(((n:ℝ)+1)*Real.log ((n:ℝ)+1)))
      ~[Filter.atTop] (fun n : ℕ => 1/((n:ℝ)*Real.log (n:ℝ))) := by
    have hmul := h2.mul hlog2
    have hinv := hmul.inv
    have e1 : (fun n : ℕ => 1/(((n:ℝ)+1)*Real.log ((n:ℝ)+1)))
        = (fun n : ℕ => (((n:ℝ)+1)*Real.log ((n:ℝ)+1))⁻¹) := by
      funext n
      rw [one_div]
    have e2 : (fun n : ℕ => 1/((n:ℝ)*Real.log (n:ℝ)))
        = (fun n : ℕ => (((n:ℝ))*Real.log (n:ℝ))⁻¹) := by
      funext n
      rw [one_div]
    rw [e1, e2]
    exact hinv
  have hle : ∀ᶠ (n : ℕ) in Filter.atTop,
      1/(((n:ℝ)+1)*Real.log ((n:ℝ)+1)) ≤ lapG n ∧
      lapG n ≤ 1/((n:ℝ)*Real.log (n:ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact lapG_bounds n hn
  have hg : lapG ~[Filter.atTop] (fun n : ℕ => 1/((n:ℝ)*Real.log (n:ℝ))) :=
    lapIsEquivalent_of_le_of_le hle hlo Asymptotics.IsEquivalent.refl
  exact hb.trans hg.symm

/-- Abel identity for the prime reciprocal sum. -/
private theorem lapAbel (N : ℕ) :
    lapPrimeRecipSum N
      = (Nat.primeCounting N : ℝ)/(N:ℝ) + ∑ n ∈ Finset.range N, lapB n := by
  have h0 : Nat.primeCounting 0 = 0 := by decide
  have hTfilter : ∀ M, lapPrimeRecipSum M
      = ∑ p ∈ Finset.Icc 1 M, (if Nat.Prime p then (1:ℝ)/(p:ℝ) else 0) := by
    intro M
    unfold lapPrimeRecipSum
    rw [Finset.sum_filter]
  have hpi : ∀ M, (Nat.primeCounting (M+1) : ℝ)
      = (Nat.primeCounting M : ℝ) + (if Nat.Prime (M+1) then 1 else 0) := by
    intro M
    have h := Nat.count_succ (p := Nat.Prime) (M+1)
    have e1 : Nat.primeCounting (M+1) = Nat.count Nat.Prime (M+1+1) := rfl
    have e2 : Nat.primeCounting M = Nat.count Nat.Prime (M+1) := rfl
    rw [e1, e2]
    exact_mod_cast h
  induction N with
  | zero => simp [lapPrimeRecipSum, lapB, h0]
  | succ N ih =>
    rw [hTfilter (N+1), Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      ← hTfilter N, ih, Finset.sum_range_succ, hpi N]
    have hBlap : lapB N
        = (Nat.primeCounting N : ℝ)/((N:ℝ)*((N:ℝ)+1)) := rfl
    have key : (Nat.primeCounting N : ℝ)/(N:ℝ)
          + (if Nat.Prime (N+1) then (1:ℝ)/(((N+1:ℕ)):ℝ) else 0)
        = ((Nat.primeCounting N : ℝ) + (if Nat.Prime (N+1) then 1 else 0))
            /(((N+1:ℕ)):ℝ) + lapB N := by
      rw [hBlap]
      by_cases hN : N = 0
      · subst hN
        rw [h0]
        split_ifs with hp
        · exact absurd hp (by decide)
        · simp
      · have hN0 : (N:ℝ) ≠ 0 := by
          have hpos : 0 < N := Nat.pos_of_ne_zero hN
          exact_mod_cast hpos.ne'
        have hN1 : (((N+1 : ℕ)):ℝ) ≠ 0 := by
          have hpos : 0 < N + 1 := Nat.succ_pos N
          exact_mod_cast hpos.ne'
        have hcast : (((N+1 : ℕ)):ℝ) = (N:ℝ)+1 := by push_cast; ring
        rw [hcast]
        split_ifs with hp
        · field_simp
          ring
        · field_simp
          ring
    linarith [key]

/-- `log log` tends to infinity over `ℕ`. -/
private theorem lapLogLogTendsto : Filter.Tendsto
    (fun N : ℕ => Real.log (Real.log (N:ℝ))) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `lapG` is always nonnegative. -/
private theorem lapG_nonneg : ∀ n, 0 ≤ lapG n := by
  intro n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have e1 : max (0+1) 2 = 2 := by decide
      have e0 : max 0 2 = 2 := by decide
      have hz : lapG 0 = 0 := by
        unfold lapG lapH
        rw [e1, e0, sub_self]
      rw [hz]
    · have e2 : max (1+1) 2 = 2 := by decide
      have e1 : max 1 2 = 2 := by decide
      have ho : lapG 1 = 0 := by
        unfold lapG lapH
        rw [e2, e1, sub_self]
      rw [ho]
  · have h1 : (0:ℝ) ≤ 1/(((n:ℝ)+1)*Real.log ((n:ℝ)+1)) := by
      have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have h1 : (0:ℝ) < (n:ℝ)+1 := by linarith
      have h2 : (0:ℝ) < Real.log ((n:ℝ)+1) := Real.log_pos (by linarith)
      exact le_of_lt (div_pos one_pos (mul_pos h1 h2))
    exact le_trans h1 (lapG_bounds n hn).1

/-- Range sums of `lapG` tend to infinity. -/
private theorem lapSumGTendsto : Filter.Tendsto
    (fun N => ∑ i ∈ Finset.range N, lapG i) Filter.atTop Filter.atTop := by
  have hsum_eq : ∀ N, ∑ i ∈ Finset.range N, lapG i = lapH N - lapH 0 :=
    fun N => Finset.sum_range_sub lapH N
  have hmax : Filter.Tendsto (fun N : ℕ => max N 2) Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.congr' ?_ tendsto_id
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    exact (Nat.max_eq_left hN).symm
  have hlapH : Filter.Tendsto lapH Filter.atTop Filter.atTop :=
    lapLogLogTendsto.comp hmax
  have h2 : Filter.Tendsto (fun N => lapH N + (-(lapH 0))) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ hlapH
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards with N
  rw [hsum_eq N, sub_eq_add_neg]

/-- The norm of `log log` tends to infinity. -/
private theorem lapLogLogNormTendsto : Filter.Tendsto
    (fun N : ℕ => ‖Real.log (Real.log (N:ℝ))‖) Filter.atTop Filter.atTop := by
  have hev : (fun N : ℕ => ‖Real.log (Real.log (N:ℝ))‖)
      =ᶠ[Filter.atTop] (fun N : ℕ => Real.log (Real.log (N:ℝ))) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    have hN3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have he : Real.exp 1 ≤ (N:ℝ) := by
      have h := Real.exp_one_lt_d9
      linarith
    have h1 : (1:ℝ) ≤ Real.log (N:ℝ) := by
      have hle := Real.log_le_log (Real.exp_pos 1) he
      rwa [Real.log_exp] at hle
    have hnn : (0:ℝ) ≤ Real.log (Real.log (N:ℝ)) := by
      rw [← Real.log_one]
      exact Real.log_le_log (by norm_num) h1
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact Filter.Tendsto.congr' hev.symm lapLogLogTendsto

/-- Weak Mertens II. -/
private theorem lapPrimeRecipSumIsEquivalent :
    (fun N : ℕ => lapPrimeRecipSum N) ~[Filter.atTop]
      (fun N : ℕ => Real.log (Real.log (N : ℝ))) := by
  have hbase : (fun n => lapB n - lapG n) =o[Filter.atTop] lapG :=
    lapBIsEquivalentG.isLittleO
  have hE := hbase.sum_range lapG_nonneg lapSumGTendsto
  have hsum_eq : ∀ N, ∑ i ∈ Finset.range N, lapG i = lapH N - lapH 0 :=
    fun N => Finset.sum_range_sub lapH N
  have hSeq : (fun N => ∑ i ∈ Finset.range N, lapG i)
      =ᶠ[Filter.atTop] (fun N => Real.log (Real.log (N:ℝ)) - lapH 0) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    rw [hsum_eq N]
    congr 1
    unfold lapH
    rw [Nat.max_eq_left hN]
  have hconst : (fun _ : ℕ => lapH 0) =o[Filter.atTop]
      (fun N : ℕ => Real.log (Real.log (N:ℝ))) := by
    rw [isLittleO_const_left]
    exact Or.inr lapLogLogNormTendsto
  have hLc : (fun N : ℕ => Real.log (Real.log (N:ℝ)) - lapH 0)
      ~[Filter.atTop] (fun N : ℕ => Real.log (Real.log (N:ℝ))) :=
    Asymptotics.IsEquivalent.refl.sub_isLittleO hconst
  have hSgL : (fun N => ∑ i ∈ Finset.range N, lapG i)
      ~[Filter.atTop] (fun N : ℕ => Real.log (Real.log (N:ℝ))) :=
    hLc.congr_left hSeq.symm
  have hSb : (fun N => ∑ i ∈ Finset.range N, lapB i)
      ~[Filter.atTop] (fun N : ℕ => Real.log (Real.log (N:ℝ))) := by
    have hSbEq : (fun N => ∑ i ∈ Finset.range N, lapB i)
        = (fun N => ∑ i ∈ Finset.range N, lapG i)
          + (fun N => ∑ i ∈ Finset.range N, (lapB i - lapG i)) := by
      funext N
      simp only [Pi.add_apply]
      have hss : ∑ i ∈ Finset.range N, (lapB i - lapG i)
          = ∑ i ∈ Finset.range N, lapB i - ∑ i ∈ Finset.range N, lapG i :=
        Finset.sum_sub_distrib _ _
      linarith [hss]
    rw [hSbEq]
    exact hSgL.add_isLittleO (hE.trans_isEquivalent hSgL)
  have hpiO : (fun N : ℕ => (Nat.primeCounting N : ℝ)/(N:ℝ)) =o[Filter.atTop]
      (fun N : ℕ => Real.log (Real.log (N:ℝ))) := by
    have hO : (fun N : ℕ => (Nat.primeCounting N : ℝ)/(N:ℝ)) =O[Filter.atTop]
        (fun _ : ℕ => (1:ℝ)) := by
      apply Asymptotics.IsBigO.of_bound 2
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      have hcount : Nat.count Nat.Prime (N+1) ≤ N + 1 := Nat.count_le Nat.Prime
      have hcount2 : Nat.primeCounting N ≤ N + 1 := hcount
      have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      have hle : (Nat.primeCounting N : ℝ)/(N:ℝ) ≤ 2 := by
        rw [div_le_iff₀ hN0]
        have h2 : (Nat.primeCounting N : ℝ) ≤ ((N+1 : ℕ):ℝ) := by
          exact_mod_cast hcount2
        push_cast at h2
        linarith
      have hnn : (0:ℝ) ≤ (Nat.primeCounting N : ℝ)/(N:ℝ) := by positivity
      simp only [Real.norm_eq_abs, abs_of_nonneg hnn, norm_one, mul_one]
      exact hle
    have h1o : (fun _ : ℕ => (1:ℝ)) =o[Filter.atTop]
        (fun N : ℕ => Real.log (Real.log (N:ℝ))) := by
      rw [Asymptotics.isLittleO_one_left_iff]
      exact lapLogLogNormTendsto
    exact hO.trans_isLittleO h1o
  have hfinal : (fun N : ℕ => (Nat.primeCounting N : ℝ)/(N:ℝ)
      + ∑ i ∈ Finset.range N, lapB i)
      ~[Filter.atTop] (fun N : ℕ => Real.log (Real.log (N:ℝ))) :=
    hpiO.add_isEquivalent hSb
  have hEq : (fun N : ℕ => lapPrimeRecipSum N)
      = (fun N : ℕ => (Nat.primeCounting N : ℝ)/(N:ℝ)
        + ∑ i ∈ Finset.range N, lapB i) := by
    funext N
    exact lapAbel N
  rw [hEq]
  exact hfinal

/-- Applying a restricted arithmetic function. -/
private theorem lapRestrictApply (j : ℕ) (h : ArithmeticFunction ℝ) (n : ℕ) :
    (lapRestrictAlmostPrime j h) n = if Nat.IsAlmostPrime j n then h n else 0 :=
  rfl

/-- Dirichlet product of restricted arithmetic functions. -/
private theorem lapRestrictMulApply (i j m : ℕ) (f g : ArithmeticFunction ℝ) :
    ((lapRestrictAlmostPrime i f) * (lapRestrictAlmostPrime j g)) m =
      if Nat.IsAlmostPrime (i + j) m then
        ∑ x ∈ m.divisorsAntidiagonal.filter (fun x => Nat.IsAlmostPrime i x.1),
          f x.1 * g x.2
      else 0 := by
  rw [ArithmeticFunction.mul_apply]
  by_cases hm : Nat.IsAlmostPrime (i + j) m
  · rw [ite_eq_left hm]
    simp only [Finset.sum_filter]
    obtain ⟨-, hΩm⟩ := hm
    apply Finset.sum_congr rfl
    intro x hx
    have hx1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    have hx2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
    obtain ⟨hxx, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hΩ : ArithmeticFunction.cardFactors (x.1 * x.2)
        = ArithmeticFunction.cardFactors x.1 + ArithmeticFunction.cardFactors x.2 :=
      ArithmeticFunction.cardFactors_mul hx1 hx2
    rw [lapRestrictApply, lapRestrictApply]
    by_cases h1 : Nat.IsAlmostPrime i x.1
    · have hΩ2 : ArithmeticFunction.cardFactors x.2 = j := by
        have hΩ1 : ArithmeticFunction.cardFactors x.1 = i := by
          obtain ⟨-, hΩ1⟩ := h1
          exact hΩ1
        have hmem : ArithmeticFunction.cardFactors (x.1 * x.2) = i + j := by
          rw [hxx]
          exact hΩm
        omega
      have h2 : Nat.IsAlmostPrime j x.2 := ⟨hx2, hΩ2⟩
      simp only [ite_eq_left h1, ite_eq_left h2]
    · simp only [ite_eq_right h1, zero_mul]
  · rw [ite_eq_right hm]
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨hxx, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [lapRestrictApply, lapRestrictApply]
    by_cases h1 : Nat.IsAlmostPrime i x.1
    · by_cases h2 : Nat.IsAlmostPrime j x.2
      · exfalso
        apply hm
        rw [← hxx]
        exact h1.mul h2
      · rw [ite_eq_left h1, ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- Summed form of restricted Dirichlet products. -/
private theorem lapRestrictSumIoc (i j N : ℕ) (f g : ArithmeticFunction ℝ) :
    ∑ n ∈ Finset.Ioc 0 N,
        ((lapRestrictAlmostPrime i f) * (lapRestrictAlmostPrime j g)) n =
      ∑ d ∈ Finset.Ioc 0 N, (lapRestrictAlmostPrime i f) d *
        ∑ e ∈ Finset.Ioc 0 (N / d), (lapRestrictAlmostPrime j g) e :=
  ArithmeticFunction.sum_Ioc_mul_eq_sum_sum _ _ _

/-- Nonnegativity and monotonicity. -/
private theorem lapRecipNonneg (k N : ℕ) : 0 ≤ lapAlmostPrimeRecipSum k N := by
  unfold lapAlmostPrimeRecipSum
  apply Finset.sum_nonneg
  intro m _
  positivity

private theorem lapRecipMono (k : ℕ) : Monotone (lapAlmostPrimeRecipSum k) := by
  intro N M hNM
  unfold lapAlmostPrimeRecipSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hNM)
  · intro m _ _
    positivity

/-- Level 0. -/
private theorem lapRecipZero (N : ℕ) (hN : 1 ≤ N) : lapAlmostPrimeRecipSum 0 N = 1 := by
  unfold lapAlmostPrimeRecipSum
  have h : (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime 0 m) = {1} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro hm
      exact Nat.isAlmostPrime_zero_iff.mp hm.2
    · intro hm
      rw [hm]
      exact ⟨⟨le_refl 1, hN⟩, Nat.isAlmostPrime_zero_iff.mpr rfl⟩
  rw [h]
  simp

/-- Level 1 is the prime reciprocal sum. -/
private theorem lapRecipOne (N : ℕ) : lapAlmostPrimeRecipSum 1 N = lapPrimeRecipSum N := by
  unfold lapAlmostPrimeRecipSum lapPrimeRecipSum
  congr 1
  apply Finset.filter_congr
  intro m _
  exact Nat.isAlmostPrime_one_iff

/-- The reciprocal arithmetic function. -/
private noncomputable def lapInvFun : ArithmeticFunction ℝ :=
  ⟨fun n => ((n : ℝ))⁻¹, by simp⟩

private theorem lapInvFunApply (n : ℕ) : lapInvFun n = ((n : ℝ))⁻¹ :=
  rfl

/-- `Icc 1 N` is `Ioc 0 N`. -/
private theorem lapIccEqIoc (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- Primes in the antidiagonal count the distinct prime factors. -/
private theorem lapPrimeAntidiagCard (m : ℕ) (hm0 : m ≠ 0) :
    m.primeFactors.card
      = (m.divisorsAntidiagonal.filter (fun x => Nat.Prime x.1)).card := by
  refine Finset.card_bij (fun p _ => (p, m / p)) ?_ ?_ ?_
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hdvd, -⟩ := hp
    rw [Finset.mem_filter]
    refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hm0⟩, hpp⟩
    exact Nat.mul_div_cancel' hdvd
  · intro p _ q _ hpq
    exact congrArg Prod.fst hpq
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, hxp⟩ := hx
    obtain ⟨hxx, -⟩ := Nat.mem_divisorsAntidiagonal.mp hxmem
    have hx1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hxmem
    have hdiv : m / x.1 = x.2 :=
      Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hx1)
        (by rw [mul_comm x.2 x.1]; exact hxx.symm)
    refine ⟨x.1, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hxp, ⟨x.2, hxx.symm⟩, hm0⟩
    · show (x.1, m / x.1) = x
      rw [hdiv]

/-- The `ω`-term as a Dirichlet product. -/
private theorem lapOmegaTerm (k m : ℕ) (hm : Nat.IsAlmostPrime (k + 1) m) :
    (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ) =
      ((lapRestrictAlmostPrime 1 lapInvFun)
        * (lapRestrictAlmostPrime k lapInvFun)) m := by
  have hm0 : m ≠ 0 := by
    obtain ⟨hm0, -⟩ := hm
    exact hm0
  have hm1 : Nat.IsAlmostPrime (1 + k) m := by
    have e : 1 + k = k + 1 := by omega
    rw [e]
    exact hm
  rw [lapRestrictMulApply, ite_eq_left hm1]
  have hfilter : m.divisorsAntidiagonal.filter (fun x => Nat.IsAlmostPrime 1 x.1)
      = m.divisorsAntidiagonal.filter (fun x => Nat.Prime x.1) :=
    Finset.filter_congr (fun x _ => Nat.isAlmostPrime_one_iff)
  rw [hfilter]
  have hterm : ∀ x ∈ m.divisorsAntidiagonal.filter (fun x => Nat.Prime x.1),
      lapInvFun x.1 * lapInvFun x.2 = ((m : ℝ))⁻¹ := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, -⟩ := hx
    obtain ⟨hxx, -⟩ := Nat.mem_divisorsAntidiagonal.mp hxmem
    rw [lapInvFunApply, lapInvFunApply]
    have hcast : ((x.1 * x.2 : ℕ) : ℝ) = (m : ℝ) := by rw [hxx]
    rw [← hcast, Nat.cast_mul, mul_inv_rev, mul_comm]
  have hω : m.primeFactors.card = ArithmeticFunction.cardDistinctFactors m := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors]
    exact List.card_toFinset _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
    ← hω, lapPrimeAntidiagCard m hm0]

/-- The restricted reciprocal sum over an interval is `T_k`. -/
private theorem lapInnerSum (k M : ℕ) :
    ∑ e ∈ Finset.Ioc 0 M, (lapRestrictAlmostPrime k lapInvFun) e
      = lapAlmostPrimeRecipSum k M := by
  rw [← lapIccEqIoc M]
  unfold lapAlmostPrimeRecipSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rw [lapRestrictApply, lapInvFunApply]
  by_cases he : Nat.IsAlmostPrime k e
  · simp only [ite_eq_left he, one_div]
  · simp only [ite_eq_right he]

/-- The outer summand in if-form. -/
private theorem lapOuterTerm (k N d : ℕ) :
    (lapRestrictAlmostPrime 1 lapInvFun) d *
        (∑ e ∈ Finset.Ioc 0 (N / d), (lapRestrictAlmostPrime k lapInvFun) e) =
      (if Nat.Prime d then ((1 : ℝ) / (d : ℝ)) * lapAlmostPrimeRecipSum k (N / d)
        else 0) := by
  rw [lapRestrictApply, lapInnerSum]
  by_cases hd1 : Nat.IsAlmostPrime 1 d
  · have hdp : Nat.Prime d := Nat.isAlmostPrime_one_iff.mp hd1
    simp only [ite_eq_left hd1, ite_eq_left hdp, lapInvFunApply, one_div]
  · have hdp : ¬ Nat.Prime d := fun hp => hd1 (Nat.isAlmostPrime_one_iff.mpr hp)
    rw [ite_eq_right hd1, ite_eq_right hdp, zero_mul]

/-- The `ω`-identity. -/
private theorem lapOmegaIdentity (k N : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ) =
      ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p),
        ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (N / p) := by
  have hC : ∀ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
      (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ) =
        ((lapRestrictAlmostPrime 1 lapInvFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m :=
    fun m hm => lapOmegaTerm k m (Finset.mem_filter.mp hm).2
  have hLHS : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ))
      = ∑ m ∈ Finset.Icc 1 N,
        ((lapRestrictAlmostPrime 1 lapInvFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m := by
    rw [Finset.sum_congr rfl hC, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Nat.IsAlmostPrime (k + 1) m
    · rw [ite_eq_left hm]
    · have hm' : ¬ Nat.IsAlmostPrime (1 + k) m := by
        have e : 1 + k = k + 1 := by omega
        rw [e]
        exact hm
      rw [ite_eq_right hm, lapRestrictMulApply, ite_eq_right hm']
  rw [hLHS, lapIccEqIoc, lapRestrictSumIoc, ← lapIccEqIoc N,
    Finset.sum_congr rfl (fun d _ => lapOuterTerm k N d), ← Finset.sum_filter]

/-- Lower bound. -/
private theorem lapRecipLower (k N : ℕ) :
    lapPrimeRecipSum (Nat.sqrt N) * lapAlmostPrimeRecipSum k (Nat.sqrt N) ≤
      ((k : ℝ) + 1) * lapAlmostPrimeRecipSum (k + 1) N := by
  have hcast2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hle : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ)
      ≤ ((k : ℝ) + 1) * lapAlmostPrimeRecipSum (k + 1) N := by
    unfold lapAlmostPrimeRecipSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨-, hAP⟩ := hm
    have hΩ : ArithmeticFunction.cardFactors m = k + 1 := hAP.2
    have hω : ArithmeticFunction.cardDistinctFactors m ≤ k + 1 :=
      calc ArithmeticFunction.cardDistinctFactors m
          = m.primeFactorsList.dedup.length :=
            ArithmeticFunction.cardDistinctFactors_apply
        _ ≤ m.primeFactorsList.length :=
            List.Sublist.length_le (List.dedup_sublist _)
        _ = ArithmeticFunction.cardFactors m :=
            ArithmeticFunction.cardFactors_apply.symm
        _ = k + 1 := hΩ
    have hcast : ((ArithmeticFunction.cardDistinctFactors m : ℕ) : ℝ)
        ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hω
    rw [div_eq_mul_inv, one_div, ← hcast2]
    exact mul_le_mul_of_nonneg_right hcast (by positivity)
  have hss : Nat.sqrt N * Nat.sqrt N ≤ N := by
    have h := Nat.sqrt_le' N
    rwa [pow_two] at h
  have hsub : (Finset.Icc 1 (Nat.sqrt N)).filter (fun p => Nat.Prime p)
      ⊆ (Finset.Icc 1 N).filter (fun p => Nat.Prime p) :=
    Finset.filter_subset_filter _
      (Finset.Icc_subset_Icc_right (Nat.sqrt_le_self N))
  have hmono : ∀ p ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun p => Nat.Prime p),
      ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (Nat.sqrt N)
        ≤ ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (N / p) := by
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply lapRecipMono
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hps⟩, -⟩ := hp
    have hp0 : 0 < p := by omega
    have hle2 : p * Nat.sqrt N ≤ N :=
      le_trans (Nat.mul_le_mul hps (le_refl _)) hss
    rw [Nat.le_div_iff_mul_le hp0, mul_comm _ p]
    exact hle2
  have hprod : lapPrimeRecipSum (Nat.sqrt N) * lapAlmostPrimeRecipSum k (Nat.sqrt N)
      ≤ ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p),
        ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (N / p) := by
    unfold lapPrimeRecipSum
    rw [Finset.sum_mul]
    calc ∑ p ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun p => Nat.Prime p),
          ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (Nat.sqrt N)
        ≤ ∑ p ∈ (Finset.Icc 1 (Nat.sqrt N)).filter (fun p => Nat.Prime p),
          ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (N / p) :=
          Finset.sum_le_sum (fun p hp => hmono p hp)
      _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p),
          ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (N / p) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
            mul_nonneg (by positivity) (lapRecipNonneg _ _))
  calc lapPrimeRecipSum (Nat.sqrt N) * lapAlmostPrimeRecipSum k (Nat.sqrt N)
      ≤ ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p),
        ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum k (N / p) := hprod
    _ = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ) :=
        (lapOmegaIdentity k N).symm
    _ ≤ ((k : ℝ) + 1) * lapAlmostPrimeRecipSum (k + 1) N := hle

/-- Reciprocal on squares, zero elsewhere. -/
private noncomputable def lapSquareFun : ArithmeticFunction ℝ :=
  ⟨fun n => if IsSquare n then ((n : ℝ))⁻¹ else 0, by simp⟩

private theorem lapSquareFunApply (n : ℕ) :
    lapSquareFun n = if IsSquare n then ((n : ℝ))⁻¹ else 0 :=
  rfl

/-- A non-squarefree almost-prime has a prime-square antidiagonal pair. -/
private theorem lapNonsqWitness (k m : ℕ) (hm : Nat.IsAlmostPrime (k + 2) m)
    (hsq : ¬ Squarefree m) :
    ∃ x₀ ∈ m.divisorsAntidiagonal.filter
      (fun x => Nat.IsAlmostPrime 2 x.1 ∧ IsSquare x.1),
      lapSquareFun x₀.1 * lapInvFun x₀.2 = 1 / (m : ℝ) := by
  obtain ⟨hm0, -⟩ := hm
  have hex : ∃ q, Nat.Prime q ∧ q * q ∣ m := by
    by_contra hcon
    push Not at hcon
    exact hsq (Nat.squarefree_iff_prime_squarefree.mpr hcon)
  obtain ⟨q, hqp, hdvd⟩ := hex
  obtain ⟨e, he⟩ := hdvd
  have hq0 : q * q ≠ 0 := mul_ne_zero hqp.ne_zero hqp.ne_zero
  have hΩqq : ArithmeticFunction.cardFactors (q * q) = 2 := by
    have hsq2 : q * q = q ^ 2 := by ring
    rw [hsq2]
    exact ArithmeticFunction.cardFactors_apply_prime_pow hqp
  have hAPqq : Nat.IsAlmostPrime 2 (q * q) := ⟨hq0, hΩqq⟩
  have hsqx : IsSquare (q * q) := ⟨q, rfl⟩
  have hcast : (e : ℝ) * (((q * q : ℕ)) : ℝ) = (m : ℝ) := by
    rw [mul_comm]
    exact_mod_cast he.symm
  refine ⟨(q * q, e), ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hm0⟩, hAPqq, hsqx⟩
    exact he.symm
  · change lapSquareFun (q * q) * lapInvFun e = 1 / (m : ℝ)
    rw [lapSquareFunApply, lapInvFunApply, ite_eq_left hsqx, one_div, ← mul_inv_rev,
      hcast]

/-- The non-squarefree term is bounded by the Dirichlet product. -/
private theorem lapNonsqTerm (k m : ℕ) (hm : Nat.IsAlmostPrime (k + 2) m) :
    (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0)
      ≤ ((lapRestrictAlmostPrime 2 lapSquareFun)
        * (lapRestrictAlmostPrime k lapInvFun)) m := by
  have hm2 : Nat.IsAlmostPrime (2 + k) m := by
    have e : 2 + k = k + 2 := by omega
    rw [e]
    exact hm
  rw [lapRestrictMulApply, ite_eq_left hm2]
  have hnn : ∀ x ∈ m.divisorsAntidiagonal.filter (fun x => Nat.IsAlmostPrime 2 x.1),
      0 ≤ lapSquareFun x.1 * lapInvFun x.2 := by
    intro x _
    rw [lapSquareFunApply, lapInvFunApply]
    by_cases hsqx : IsSquare x.1
    · rw [ite_eq_left hsqx]
      exact mul_nonneg (by positivity) (by positivity)
    · rw [ite_eq_right hsqx, zero_mul]
  by_cases hsq : Squarefree m
  · rw [ite_eq_right (not_not_intro hsq)]
    exact Finset.sum_nonneg hnn
  · obtain ⟨x₀, hx₀, hval⟩ := lapNonsqWitness k m hm hsq
    rw [Finset.mem_filter] at hx₀
    have hx₀' : x₀ ∈ m.divisorsAntidiagonal.filter (fun x => Nat.IsAlmostPrime 2 x.1) :=
      Finset.mem_filter.mpr ⟨hx₀.1, hx₀.2.1⟩
    rw [ite_eq_left hsq, ← hval]
    exact Finset.single_le_sum hnn hx₀'

/-- The square-restricted sum over an interval, as a filter sum. -/
private theorem lapSquareFilterSum (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (lapRestrictAlmostPrime 2 lapSquareFun) d)
      = ∑ d ∈ (Finset.Icc 1 N).filter
        (fun d => Nat.IsAlmostPrime 2 d ∧ IsSquare d), ((d : ℝ))⁻¹ := by
  simp only [lapRestrictApply, lapSquareFunApply]
  have eper : ∀ d ∈ Finset.Icc 1 N,
      (if Nat.IsAlmostPrime 2 d then
        (if IsSquare d then ((d : ℝ))⁻¹ else 0) else 0)
      = (if Nat.IsAlmostPrime 2 d ∧ IsSquare d then ((d : ℝ))⁻¹ else 0) := by
    intro d _
    by_cases hd : Nat.IsAlmostPrime 2 d <;> by_cases hsqd : IsSquare d
    · have hconj : Nat.IsAlmostPrime 2 d ∧ IsSquare d := ⟨hd, hsqd⟩
      simp only [ite_eq_left hd, ite_eq_left hsqd, ite_eq_left hconj]
    · simp only [ite_eq_left hd, ite_eq_right hsqd,
        ite_eq_right (show ¬(Nat.IsAlmostPrime 2 d ∧ IsSquare d) from
          fun h => hsqd h.2)]
    · simp only [ite_eq_right hd,
        ite_eq_right (show ¬(Nat.IsAlmostPrime 2 d ∧ IsSquare d) from
          fun h => hd h.1)]
    · simp only [ite_eq_right hd,
        ite_eq_right (show ¬(Nat.IsAlmostPrime 2 d ∧ IsSquare d) from
          fun h => hd h.1)]
  rw [Finset.sum_congr rfl eper, Finset.sum_filter]

/-- 2-almost-prime squares lie in the image of `r ↦ r * r`. -/
private theorem lapSquareSubsetImage (N : ℕ) :
    (Finset.Icc 1 N).filter (fun d => Nat.IsAlmostPrime 2 d ∧ IsSquare d)
      ⊆ Finset.image (fun r => r * r) (Finset.Ioc 1 N) := by
  intro d hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, hdN⟩, hAPd, hsqd⟩ := hd
  obtain ⟨r, hr⟩ := hsqd
  rw [Finset.mem_image]
  refine ⟨r, ?_, hr.symm⟩
  rw [Finset.mem_Ioc]
  have hrr : r * r ≤ N := by rw [← hr]; exact hdN
  have hr1 : 1 < r := by
    by_contra hcon
    push Not at hcon
    interval_cases r
    · simp at hr
      omega
    · have hd1' : d = 1 := by rw [hr, mul_one]
      rw [hd1'] at hAPd
      have h2 := hAPd.2
      rw [ArithmeticFunction.cardFactors_one] at h2
      omega
  exact ⟨hr1, le_trans (Nat.le_mul_self r) hrr⟩

/-- The 2-almost-prime square reciprocal sum is at most 1. -/
private theorem lapSquareImageLe (N : ℕ) :
    (∑ d ∈ (Finset.Icc 1 N).filter
      (fun d => Nat.IsAlmostPrime 2 d ∧ IsSquare d), ((d : ℝ))⁻¹) ≤ 1 := by
  calc (∑ d ∈ (Finset.Icc 1 N).filter
        (fun d => Nat.IsAlmostPrime 2 d ∧ IsSquare d), ((d : ℝ))⁻¹)
      ≤ ∑ d ∈ Finset.image (fun r : ℕ => r * r) (Finset.Ioc 1 N), ((d : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (lapSquareSubsetImage N)
          (fun d _ _ => by positivity)
    _ = ∑ r ∈ Finset.Ioc 1 N, ((((r * r : ℕ)) : ℝ))⁻¹ := by
        apply Finset.sum_image
        intro a _ b _ hab
        have hab' : a * a = b * b := hab
        exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hab'
    _ ≤ 1 := by
        have h1 : (∑ r ∈ Finset.Ioc 1 N, ((((r * r : ℕ)) : ℝ))⁻¹)
            = ∑ r ∈ Finset.Ioc 1 N, (((r : ℝ)) ^ 2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Nat.cast_mul, pow_two]
        rw [h1]
        by_cases hN : 1 ≤ N
        · have hle := sum_Ioc_inv_sq_le_sub (α := ℝ) one_ne_zero hN
          calc (∑ r ∈ Finset.Ioc 1 N, (((r : ℝ)) ^ 2)⁻¹)
              ≤ (((1 : ℕ)) : ℝ)⁻¹ - ((N : ℝ))⁻¹ := hle
            _ ≤ 1 := by
                have hnn : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
                rw [Nat.cast_one, inv_one]
                linarith
        · have hN0 : N = 0 := by omega
          rw [hN0, Finset.Ioc_eq_empty_of_le (by norm_num), Finset.sum_empty]
          exact zero_le_one

/-- The square-restricted reciprocal sum over an interval is at most 1. -/
private theorem lapSquareSumLe (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N, (lapRestrictAlmostPrime 2 lapSquareFun) d) ≤ 1 := by
  rw [← lapIccEqIoc N, lapSquareFilterSum]
  exact lapSquareImageLe N

/-- The non-squarefree reciprocal sum is bounded by `T_k`. -/
private theorem lapNonsqLe (k N : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
      (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0))
      ≤ lapAlmostPrimeRecipSum k N := by
  have h2 : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
        (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0))
      ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
        ((lapRestrictAlmostPrime 2 lapSquareFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m :=
    Finset.sum_le_sum (fun m hm => lapNonsqTerm k m (Finset.mem_filter.mp hm).2)
  have hext : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
        ((lapRestrictAlmostPrime 2 lapSquareFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m)
      = ∑ m ∈ Finset.Icc 1 N,
        ((lapRestrictAlmostPrime 2 lapSquareFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Nat.IsAlmostPrime (k + 2) m
    · rw [ite_eq_left hm]
    · have hm' : ¬ Nat.IsAlmostPrime (2 + k) m := by
        have e : 2 + k = k + 2 := by omega
        rw [e]
        exact hm
      rw [ite_eq_right hm, lapRestrictMulApply, ite_eq_right hm']
  have h4 : (∑ d ∈ Finset.Ioc 0 N,
        (lapRestrictAlmostPrime 2 lapSquareFun) d *
          (∑ e ∈ Finset.Ioc 0 (N / d), (lapRestrictAlmostPrime k lapInvFun) e))
      ≤ (∑ d ∈ Finset.Ioc 0 N, (lapRestrictAlmostPrime 2 lapSquareFun) d) *
        lapAlmostPrimeRecipSum k N := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · rw [lapInnerSum]
      exact lapRecipMono k (Nat.div_le_self N d)
    · rw [lapRestrictApply]
      by_cases hd : Nat.IsAlmostPrime 2 d
      · rw [ite_eq_left hd, lapSquareFunApply]
        by_cases hsqd : IsSquare d
        · rw [ite_eq_left hsqd]
          positivity
        · rw [ite_eq_right hsqd]
      · rw [ite_eq_right hd]
  calc (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
        (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0))
      ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
        ((lapRestrictAlmostPrime 2 lapSquareFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m := h2
    _ = ∑ m ∈ Finset.Icc 1 N,
        ((lapRestrictAlmostPrime 2 lapSquareFun)
          * (lapRestrictAlmostPrime k lapInvFun)) m := hext
    _ = ∑ d ∈ Finset.Ioc 0 N,
        (lapRestrictAlmostPrime 2 lapSquareFun) d *
          (∑ e ∈ Finset.Ioc 0 (N / d),
            (lapRestrictAlmostPrime k lapInvFun) e) := by
        rw [lapIccEqIoc, lapRestrictSumIoc]
    _ ≤ (∑ d ∈ Finset.Ioc 0 N, (lapRestrictAlmostPrime 2 lapSquareFun) d) *
        lapAlmostPrimeRecipSum k N := h4
    _ ≤ 1 * lapAlmostPrimeRecipSum k N := by
        apply mul_le_mul_of_nonneg_right _ (lapRecipNonneg _ _)
        exact lapSquareSumLe N
    _ = lapAlmostPrimeRecipSum k N := one_mul _

/-- Upper bound. -/
private theorem lapRecipUpper (k N : ℕ) :
    ((k : ℝ) + 2) * lapAlmostPrimeRecipSum (k + 2) N ≤
      lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k + 1) N +
        ((k : ℝ) + 2) * lapAlmostPrimeRecipSum k N := by
  have hpoint : ∀ m ∈ (Finset.Icc 1 N).filter
      (fun m => Nat.IsAlmostPrime (k + 2) m),
      ((k : ℝ) + 2) * (1 / (m : ℝ))
        ≤ (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ)
          + ((k : ℝ) + 2) * (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨-, hAP⟩ := hm
    have hm0 : m ≠ 0 := hAP.1
    by_cases hsq : Squarefree m
    · have hω : ArithmeticFunction.cardDistinctFactors m = k + 2 := by
        rw [(ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
          hm0).mpr hsq]
        exact hAP.2
      have hωr : ((ArithmeticFunction.cardDistinctFactors m : ℕ) : ℝ)
          = (k : ℝ) + 2 := by
        rw [hω]
        push_cast
        ring
      rw [ite_eq_right (not_not_intro hsq), mul_zero, add_zero, hωr, one_div,
        div_eq_mul_inv]
    · rw [ite_eq_left hsq]
      have hnn : (0 : ℝ) ≤ (ArithmeticFunction.cardDistinctFactors m : ℕ) / (m : ℝ) := by
        positivity
      exact le_add_of_nonneg_left hnn
  have hsum : ((k : ℝ) + 2) * lapAlmostPrimeRecipSum (k + 2) N
      ≤ (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 2) m),
        (ArithmeticFunction.cardDistinctFactors m : ℝ) / (m : ℝ))
        + ((k : ℝ) + 2) * (∑ m ∈ (Finset.Icc 1 N).filter
          (fun m => Nat.IsAlmostPrime (k + 2) m),
          (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0)) := by
    unfold lapAlmostPrimeRecipSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun m hm => hpoint m hm)
  have e : (k + 1) + 1 = k + 2 := by omega
  have hEq := lapOmegaIdentity (k + 1) N
  rw [e] at hEq
  rw [hEq] at hsum
  have hPR : (∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p),
        ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum (k + 1) (N / p))
      ≤ lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k + 1) N := by
    unfold lapPrimeRecipSum
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply lapRecipMono
    exact Nat.div_le_self N p
  calc ((k : ℝ) + 2) * lapAlmostPrimeRecipSum (k + 2) N
      ≤ (∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p),
        ((1 : ℝ) / (p : ℝ)) * lapAlmostPrimeRecipSum (k + 1) (N / p))
        + ((k : ℝ) + 2) * (∑ m ∈ (Finset.Icc 1 N).filter
          (fun m => Nat.IsAlmostPrime (k + 2) m),
          (if ¬ Squarefree m then (1 : ℝ) / (m : ℝ) else 0)) := hsum
    _ ≤ lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k + 1) N +
        ((k : ℝ) + 2) * lapAlmostPrimeRecipSum k N :=
        add_le_add hPR
          (mul_le_mul_of_nonneg_left (lapNonsqLe k N) (by positivity))

/-- `Nat.sqrt` tends to infinity. -/
private theorem lapSqrtTendsto : Filter.Tendsto Nat.sqrt Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b * b, fun n hn => Nat.le_sqrt.mpr hn⟩

/-- Two-sided `log log` bound under `Nat.sqrt`. -/
private theorem lapLogSqrtBound (N : ℕ) (hN : 16 ≤ N) :
    Real.log (Real.log (N : ℝ)) - Real.log 4
      ≤ Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ))
    ∧ Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ))
      ≤ Real.log (Real.log (N : ℝ)) := by
  have hs4 : 4 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hsN : Nat.sqrt N ≤ N := Nat.sqrt_le_self N
  have hspos : (0 : ℝ) < ((Nat.sqrt N : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < Nat.sqrt N)
  have hlog1 : Real.log ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hspos (by exact_mod_cast hsN)
  have hlogpos : (0 : ℝ) < Real.log ((Nat.sqrt N : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Nat.sqrt N))
  have hupper : Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ))
      ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log hlogpos hlog1
  have h4s : (Nat.sqrt N : ℝ) + 1 ≤ (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ) := by
    have hs1 : Nat.sqrt N + 1 ≤ Nat.sqrt N * Nat.sqrt N := by
      have h2 : 2 ≤ Nat.sqrt N := by omega
      calc Nat.sqrt N + 1 ≤ Nat.sqrt N + Nat.sqrt N := by omega
        _ = 2 * Nat.sqrt N := by ring
        _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul h2 (le_refl _)
    exact_mod_cast hs1
  have hlogN : Real.log (N : ℝ) ≤ 4 * Real.log ((Nat.sqrt N : ℕ) : ℝ) := by
    have hNlt : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt' N
      rw [Nat.succ_eq_add_one] at h
      exact_mod_cast h
    have hsp1 : (0 : ℝ) < (Nat.sqrt N : ℝ) + 1 := by linarith [hspos]
    have h1 : Real.log (N : ℝ) < 2 * Real.log ((Nat.sqrt N : ℝ) + 1) := by
      have hlt := Real.log_lt_log (by exact_mod_cast (by omega : 0 < N)) hNlt
      simpa [Real.log_pow] using hlt
    have h2 : Real.log ((Nat.sqrt N : ℝ) + 1)
        ≤ 2 * Real.log ((Nat.sqrt N : ℕ) : ℝ) := by
      have hle : Real.log ((Nat.sqrt N : ℝ) + 1)
          ≤ Real.log ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) :=
        Real.log_le_log hsp1 h4s
      rw [Real.log_mul (ne_of_gt hspos) (ne_of_gt hspos)] at hle
      linarith
    linarith
  have hlower : Real.log (Real.log (N : ℝ)) - Real.log 4
      ≤ Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ)) := by
    have hlogNpos : (0 : ℝ) < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlog4 : Real.log (Real.log (N : ℝ))
        ≤ Real.log (4 * Real.log ((Nat.sqrt N : ℕ) : ℝ)) :=
      Real.log_le_log hlogNpos hlogN
    rw [Real.log_mul (by norm_num) (ne_of_gt hlogpos)] at hlog4
    linarith
  exact ⟨hlower, hupper⟩

/-- `log log` is slowly varying under `Nat.sqrt`. -/
private theorem lapLogLogSqrtIsEquivalent :
    (fun N : ℕ => Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ))) ~[Filter.atTop]
      (fun N : ℕ => Real.log (Real.log (N : ℝ))) := by
  have hb : ∀ᶠ (N : ℕ) in Filter.atTop,
      Real.log (Real.log (N : ℝ)) - Real.log 4
        ≤ Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ))
      ∧ Real.log (Real.log ((Nat.sqrt N : ℕ) : ℝ))
        ≤ Real.log (Real.log (N : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 16] with N hN
    exact lapLogSqrtBound N hN
  have hconst : (fun _ : ℕ => Real.log 4) =o[Filter.atTop]
      (fun N : ℕ => Real.log (Real.log (N : ℝ))) := by
    rw [Asymptotics.isLittleO_const_left]
    exact Or.inr lapLogLogNormTendsto
  have hLo : (fun N : ℕ => Real.log (Real.log (N : ℝ)) - Real.log 4)
      ~[Filter.atTop] (fun N : ℕ => Real.log (Real.log (N : ℝ))) :=
    Asymptotics.IsEquivalent.refl.sub_isLittleO hconst
  exact lapIsEquivalent_of_le_of_le hb hLo Asymptotics.IsEquivalent.refl

/-- The product `P * T_{k+1}` is equivalent to the main term. -/
private theorem lapProdEquiv (k : ℕ)
    (ih1 : (fun N : ℕ => lapAlmostPrimeRecipSum (k+1) N) ~[Filter.atTop]
      (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+1) / (((k+1).factorial:ℕ):ℝ))) :
    (fun N : ℕ => lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k+1) N)
      ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) := by
  have hmul := lapPrimeRecipSumIsEquivalent.mul ih1
  have heq : (fun N : ℕ => Real.log (Real.log (N:ℝ))
      * ((Real.log (Real.log (N:ℝ)))^(k+1) / (((k+1).factorial:ℕ):ℝ)))
      = (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) := by
    funext N
    conv_rhs => rw [show k + 2 = 1 + (k + 1) from by omega, pow_add, pow_one]
    rw [mul_div_assoc]
  exact hmul.congr_right (Filter.EventuallyEq.of_eq heq)

/-- The lower-order correction is negligible. -/
private theorem lapCorrLittleO (k : ℕ)
    (ih : (fun N : ℕ => lapAlmostPrimeRecipSum k N) ~[Filter.atTop]
      (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k / ((k.factorial:ℕ):ℝ))) :
    (fun N : ℕ => ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N)
      =o[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) := by
  have hpow : (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k)
      =o[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)) :=
    (Asymptotics.isLittleO_pow_pow_atTop_of_lt (p := k) (q := k+2)
      (by omega)).comp_tendsto lapLogLogTendsto
  have h3 : (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k / ((k.factorial:ℕ):ℝ))
      =o[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)) := by
    have h := hpow.const_mul_left ((((k.factorial : ℕ)):ℝ))⁻¹
    have heq : (fun N : ℕ => ((((k.factorial:ℕ)):ℝ))⁻¹
        * (Real.log (Real.log (N:ℝ)))^k)
        = (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k / ((k.factorial:ℕ):ℝ)) := by
      funext N
      rw [div_eq_mul_inv, mul_comm]
    rwa [heq] at h
  have hk1f : ((((k+1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k+1)
  have hmid : (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k / ((k.factorial:ℕ):ℝ))
      =o[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) := by
    have h := h3.const_mul_right (inv_ne_zero hk1f)
    have heq : (fun N : ℕ => ((((k+1).factorial:ℕ)):ℝ)⁻¹
        * (Real.log (Real.log (N:ℝ)))^(k+2))
        = (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
          / (((k+1).factorial:ℕ):ℝ)) := by
      funext N
      rw [div_eq_mul_inv, mul_comm]
    rwa [heq] at h
  have hTk := ih.isLittleO
  have hTk2 := hTk.const_mul_left ((k:ℝ)+2)
  have hadd : (fun N : ℕ => ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N)
      = (fun N : ℕ => ((k:ℝ)+2)
        * (lapAlmostPrimeRecipSum k N - (Real.log (Real.log (N:ℝ)))^k
          / ((k.factorial:ℕ):ℝ))
        + ((k:ℝ)+2) * ((Real.log (Real.log (N:ℝ)))^k / ((k.factorial:ℕ):ℝ))) := by
    funext N
    ring
  have hright : (fun N : ℕ => ((k:ℝ)+2)
      * ((Real.log (Real.log (N:ℝ)))^k / ((k.factorial:ℕ):ℝ)))
      =o[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) :=
    hmid.const_mul_left ((k:ℝ)+2)
  rw [hadd]
  exact (hTk2.trans hmid).add hright

/-- The product along `Nat.sqrt` is equivalent to the main term. -/
private theorem lapSqrtProdEquiv (k : ℕ)
    (ih1 : (fun N : ℕ => lapAlmostPrimeRecipSum (k+1) N) ~[Filter.atTop]
      (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+1) / (((k+1).factorial:ℕ):ℝ))) :
    (fun N : ℕ => lapPrimeRecipSum (Nat.sqrt N)
      * lapAlmostPrimeRecipSum (k+1) (Nat.sqrt N))
      ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) := by
  have hW := lapProdEquiv k ih1
  have hc1 : (fun N : ℕ => lapPrimeRecipSum (Nat.sqrt N)
      * lapAlmostPrimeRecipSum (k+1) (Nat.sqrt N))
      ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log ((Nat.sqrt N:ℕ):ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) :=
    hW.comp_tendsto lapSqrtTendsto
  have eL : (fun N : ℕ => (Real.log (Real.log ((Nat.sqrt N:ℕ):ℝ)))^(k+2)
      / (((k+1).factorial:ℕ):ℝ))
      ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ)) := by
    have hp := lapLogLogSqrtIsEquivalent.pow (k+2)
    have hdiv : (fun N : ℕ => (Real.log (Real.log ((Nat.sqrt N:ℕ):ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ))
        ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
          / (((k+1).factorial:ℕ):ℝ)) :=
      hp.div IsEquivalent.refl
    exact hdiv
  exact hc1.trans eL

/-- The `k`-almost-prime reciprocal sum asymptotic. -/
private theorem lapRecipIsEquivalent (k : ℕ) :
    (fun N : ℕ => lapAlmostPrimeRecipSum k N) ~[Filter.atTop]
      (fun N : ℕ => (Real.log (Real.log (N : ℝ))) ^ k / ((k.factorial : ℕ) : ℝ)) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    have hev : (fun N : ℕ => lapAlmostPrimeRecipSum 0 N)
        =ᶠ[Filter.atTop] (fun _ => 1) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      exact lapRecipZero N hN
    have htarg : (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^0
        / ((((0).factorial : ℕ)):ℝ)) = (fun _ => 1) := by
      funext N
      simp
    rw [htarg]
    exact Filter.EventuallyEq.isEquivalent hev
  | one =>
    rw [show (fun N : ℕ => lapAlmostPrimeRecipSum 1 N)
        = (fun N : ℕ => lapPrimeRecipSum N) from funext lapRecipOne]
    have htarg : (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^1
        / ((((1).factorial : ℕ)):ℝ))
        = (fun N : ℕ => Real.log (Real.log (N:ℝ))) := by
      funext N
      simp
    rw [htarg]
    exact lapPrimeRecipSumIsEquivalent
  | more k ihk ihk1 =>
    have hW := lapProdEquiv k ihk1
    have hcorr := lapCorrLittleO k ihk
    have hAdd : (fun N : ℕ => lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k+1) N
        + ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N)
        ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
          / (((k+1).factorial:ℕ):ℝ)) :=
      hW.add_isLittleO hcorr
    have hfact : ((((k+2).factorial : ℕ)) : ℝ)
        = (((k+1).factorial : ℕ) : ℝ) * ((k:ℝ)+2) := by
      have e1 : k + 2 = (k + 1) + 1 := by omega
      rw [e1, Nat.factorial_succ]
      push_cast
      ring
    have etarg : (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
        / (((k+1).factorial:ℕ):ℝ) / ((k:ℝ)+2))
        = (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
          / ((((k+2).factorial:ℕ)):ℝ)) := by
      funext N
      rw [div_div, hfact]
    have hU : (fun N : ℕ => (lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k+1) N
        + ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N) / ((k:ℝ)+2))
        ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
          / ((((k+2).factorial:ℕ)):ℝ)) := by
      have hdiv : (fun N : ℕ => (lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k+1) N
          + ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N) / ((k:ℝ)+2))
          ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
            / (((k+1).factorial:ℕ):ℝ) / ((k:ℝ)+2)) :=
        hAdd.div IsEquivalent.refl
      exact hdiv.congr_right (Filter.EventuallyEq.of_eq etarg)
    have hVside := lapSqrtProdEquiv k ihk1
    have hV : (fun N : ℕ => (lapPrimeRecipSum (Nat.sqrt N)
        * lapAlmostPrimeRecipSum (k+1) (Nat.sqrt N)) / ((k:ℝ)+2))
        ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
          / ((((k+2).factorial:ℕ)):ℝ)) := by
      have hdiv : (fun N : ℕ => (lapPrimeRecipSum (Nat.sqrt N)
          * lapAlmostPrimeRecipSum (k+1) (Nat.sqrt N)) / ((k:ℝ)+2))
          ~[Filter.atTop] (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^(k+2)
            / (((k+1).factorial:ℕ):ℝ) / ((k:ℝ)+2)) :=
        hVside.div IsEquivalent.refl
      exact hdiv.congr_right (Filter.EventuallyEq.of_eq etarg)
    have hk2pos : (0:ℝ) < (k:ℝ)+2 := by positivity
    have hUp : ∀ N, lapAlmostPrimeRecipSum (k+2) N
        ≤ (lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k+1) N
          + ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N) / ((k:ℝ)+2) := by
      intro N
      have h := lapRecipUpper k N
      rw [le_div_iff₀ hk2pos, mul_comm _ ((k:ℝ)+2)]
      exact h
    have hLow : ∀ N, (lapPrimeRecipSum (Nat.sqrt N)
        * lapAlmostPrimeRecipSum (k+1) (Nat.sqrt N)) / ((k:ℝ)+2)
        ≤ lapAlmostPrimeRecipSum (k+2) N := by
      intro N
      have h := lapRecipLower (k+1) N
      have e : (k + 1) + 1 = k + 2 := by omega
      have h2 : ((((k+1 : ℕ)):ℝ)+1) = (k:ℝ)+2 := by push_cast; ring
      rw [e, h2] at h
      rw [div_le_iff₀ hk2pos, mul_comm _ ((k:ℝ)+2)]
      exact h
    have hle : ∀ᶠ (N:ℕ) in Filter.atTop,
        (lapPrimeRecipSum (Nat.sqrt N) * lapAlmostPrimeRecipSum (k+1) (Nat.sqrt N))
          / ((k:ℝ)+2)
          ≤ lapAlmostPrimeRecipSum (k+2) N
        ∧ lapAlmostPrimeRecipSum (k+2) N
          ≤ (lapPrimeRecipSum N * lapAlmostPrimeRecipSum (k+1) N
            + ((k:ℝ)+2) * lapAlmostPrimeRecipSum k N) / ((k:ℝ)+2) :=
      Filter.Eventually.of_forall fun N => ⟨hLow N, hUp N⟩
    exact lapIsEquivalent_of_le_of_le hle hV hU

/-- The zeta restriction is one on nonzero naturals. -/
private theorem lapZetaRestrict (e : ℕ) (he0 : e ≠ 0) :
    (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) e = 1 := by
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne he0, Nat.cast_one]

/-- Pointwise log-sum over distinct prime factors as a Dirichlet product. -/
private theorem lapLogTerm (k m : ℕ) (hm : Nat.IsAlmostPrime (k + 1) m) :
    (∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ)) =
      ((lapRestrictAlmostPrime 1 ArithmeticFunction.log)
        * (lapRestrictAlmostPrime k
          (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ))) m := by
  have hm0 : m ≠ 0 := hm.1
  have hm1 : Nat.IsAlmostPrime (1 + k) m := by
    have e : 1 + k = k + 1 := by omega
    rwa [e]
  rw [lapRestrictMulApply, ite_eq_left hm1]
  have hfilter : m.divisorsAntidiagonal.filter (fun x => Nat.IsAlmostPrime 1 x.1)
      = m.divisorsAntidiagonal.filter (fun x => Nat.Prime x.1) :=
    Finset.filter_congr (fun x _ => Nat.isAlmostPrime_one_iff)
  rw [hfilter]
  have hterm : ∀ x ∈ m.divisorsAntidiagonal.filter (fun x => Nat.Prime x.1),
      ArithmeticFunction.log x.1 * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) x.2
        = Real.log ((x.1 : ℕ) : ℝ) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, -⟩ := hx
    have hx2 : x.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hxmem
    rw [ArithmeticFunction.log_apply, lapZetaRestrict x.2 hx2, mul_one]
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_bij (fun p _ => (p, m / p)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hdvd, -⟩ := hp
    rw [Finset.mem_filter]
    refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hm0⟩, hpp⟩
    exact Nat.mul_div_cancel' hdvd
  · intro p _ q _ hpq
    exact congrArg Prod.fst hpq
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, hxp⟩ := hx
    obtain ⟨hxx, -⟩ := Nat.mem_divisorsAntidiagonal.mp hxmem
    have hx1 : x.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hxmem
    have hdiv : m / x.1 = x.2 :=
      Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hx1)
        (by rw [mul_comm x.2 x.1]; exact hxx.symm)
    refine ⟨x.1, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hxp, ⟨x.2, hxx.symm⟩, hm0⟩
    · show (x.1, m / x.1) = x
      rw [hdiv]
  · intro p hp
    rfl

/-- The restricted log-sum over an interval is `θ`. -/
private theorem lapInnerTheta (M : ℕ) :
    (∑ d ∈ Finset.Ioc 0 M, (lapRestrictAlmostPrime 1 ArithmeticFunction.log) d)
      = Chebyshev.theta (((M : ℕ)) : ℝ) := by
  have h0M : (Finset.Icc 0 M).filter (fun p => Nat.Prime p)
      = (Finset.Icc 1 M).filter (fun p => Nat.Prime p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hM⟩, hp⟩
      exact ⟨⟨hp.one_le, hM⟩, hp⟩
    · rintro ⟨⟨-, hM⟩, hp⟩
      exact ⟨⟨Nat.zero_le _, hM⟩, hp⟩
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, h0M, ← lapIccEqIoc M,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  rw [lapRestrictApply]
  by_cases hd : Nat.IsAlmostPrime 1 d
  · have hdp : Nat.Prime d := Nat.isAlmostPrime_one_iff.mp hd
    rw [ite_eq_left hd, ite_eq_left hdp, ArithmeticFunction.log_apply]
  · have hdp : ¬ Nat.Prime d := fun hp => hd (Nat.isAlmostPrime_one_iff.mpr hp)
    rw [ite_eq_right hd, ite_eq_right hdp]

/-- The outer summand of the swapped sum in if-form. -/
private theorem lapOuterTheta (k N e : ℕ) :
    (lapRestrictAlmostPrime k (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) e *
      (∑ d ∈ Finset.Ioc 0 (N / e),
        (lapRestrictAlmostPrime 1 ArithmeticFunction.log) d) =
      (if Nat.IsAlmostPrime k e then Chebyshev.theta ((((N / e : ℕ))) : ℝ) else 0) := by
  rw [lapInnerTheta, lapRestrictApply]
  by_cases he : Nat.IsAlmostPrime k e
  · have he0 : e ≠ 0 := he.1
    rw [ite_eq_left he, lapZetaRestrict e he0, one_mul, ite_eq_left he]
  · rw [ite_eq_right he, zero_mul, ite_eq_right he]

/-- The divisor-sum swap. -/
private theorem lapThetaSumEq (k N : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
      ∑ p ∈ m.primeFactors, Real.log (p : ℝ)) =
    ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
      Chebyshev.theta (((N / e : ℕ)) : ℝ) := by
  have hC : ∀ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
      (∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ)) =
        ((lapRestrictAlmostPrime 1 ArithmeticFunction.log)
          * (lapRestrictAlmostPrime k
            (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ))) m :=
    fun m hm => lapLogTerm k m (Finset.mem_filter.mp hm).2
  have hLHS : (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        ∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ))
      = ∑ m ∈ Finset.Icc 1 N,
        ((lapRestrictAlmostPrime 1 ArithmeticFunction.log)
          * (lapRestrictAlmostPrime k
            (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ))) m := by
    rw [Finset.sum_congr rfl hC, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Nat.IsAlmostPrime (k + 1) m
    · rw [ite_eq_left hm]
    · have hm' : ¬ Nat.IsAlmostPrime (1 + k) m := by
        have e : 1 + k = k + 1 := by omega
        rwa [e]
      rw [ite_eq_right hm, lapRestrictMulApply, ite_eq_right hm']
  have hcomm : (lapRestrictAlmostPrime 1 ArithmeticFunction.log)
        * (lapRestrictAlmostPrime k (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ))
        = (lapRestrictAlmostPrime k (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ))
        * (lapRestrictAlmostPrime 1 ArithmeticFunction.log) :=
    mul_comm _ _
  rw [hLHS, lapIccEqIoc, hcomm, lapRestrictSumIoc, ← lapIccEqIoc N,
    Finset.sum_congr rfl (fun e _ => lapOuterTheta k N e), ← Finset.sum_filter]

/-- The distinct-prime log-sum equals the log of the radical. -/
private theorem lapLogRadical (m : ℕ) :
    (∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ))
      = Real.log (((∏ p ∈ m.primeFactors, p : ℕ)) : ℝ) := by
  have hne : ∀ p ∈ m.primeFactors, ((p : ℕ) : ℝ) ≠ 0 := by
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    exact_mod_cast hpp.ne_zero
  rw [Nat.cast_prod, Real.log_prod hne]

/-- Per-term lower bound: the distinct-prime log-sum is at most `log N`. -/
private theorem lapLogSumLe (m N : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ)) ≤ Real.log ((N : ℕ) : ℝ) := by
  have hm0 : 0 < m := hm1
  have hprod_pos : 0 < ∏ p ∈ m.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
  have hle : ∏ p ∈ m.primeFactors, p ≤ m :=
    Nat.le_of_dvd hm0 (Nat.prod_primeFactors_dvd m)
  have h1 : Real.log (((∏ p ∈ m.primeFactors, p : ℕ)) : ℝ)
      ≤ Real.log ((m : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hle)
  have h2 : Real.log ((m : ℕ) : ℝ) ≤ Real.log ((N : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast hmN)
  rw [lapLogRadical]
  exact le_trans h1 h2

/-- The distinct-prime log-sum as a von Mangoldt sum over prime divisors. -/
private theorem lapLogSumVonMangoldt (m : ℕ) :
    (∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ))
      = ∑ d ∈ m.divisors.filter (fun d => Nat.Prime d),
        ArithmeticFunction.vonMangoldt d := by
  rw [Nat.primeFactors_eq_to_filter_divisors_prime]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [ArithmeticFunction.vonMangoldt_apply_prime hd.2]

/-- Per-term upper identity: the gap is `log (N / m)` plus nonprime `Λ`. -/
private theorem lapUpperTerm (m N : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    Real.log ((N : ℕ) : ℝ) - (∑ p ∈ m.primeFactors, Real.log ((p : ℕ) : ℝ))
      = Real.log (((N : ℕ)) / ((m : ℕ)))
        + ∑ d ∈ m.divisors.filter (fun d => ¬ Nat.Prime d),
          ArithmeticFunction.vonMangoldt d := by
  have hN1 : 1 ≤ N := le_trans hm1 hmN
  have hNne : N ≠ 0 := by omega
  have hmne : m ≠ 0 := by omega
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hlogm : Real.log ((m:ℕ):ℝ)
      = ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d :=
    ArithmeticFunction.vonMangoldt_sum.symm
  have hsplit := Finset.sum_filter_add_sum_filter_not m.divisors (fun d => Nat.Prime d)
    ArithmeticFunction.vonMangoldt
  have hlogdiv : Real.log (((N:ℕ):ℝ) / ((m:ℕ):ℝ))
      = Real.log ((N:ℕ):ℝ) - Real.log ((m:ℕ):ℝ) :=
    Real.log_div (by exact_mod_cast hNne) (ne_of_gt hmR)
  rw [hlogdiv, hlogm, ← hsplit, lapLogSumVonMangoldt]
  ring

/-- The nonprime von Mangoldt sum as a Dirichlet convolution. -/
private theorem lapNonprimeVonMangoldt (m : ℕ) :
    (∑ d ∈ m.divisors.filter (fun d => ¬ Nat.Prime d), ArithmeticFunction.vonMangoldt d)
      = ((ArithmeticFunction.vonMangoldt
        - lapRestrictAlmostPrime 1 ArithmeticFunction.vonMangoldt)
        * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m := by
  rw [ArithmeticFunction.coe_mul_zeta_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    lapRestrictApply]
  by_cases hd : Nat.Prime d
  · have hd1 : Nat.IsAlmostPrime 1 d := Nat.isAlmostPrime_one_iff.mpr hd
    rw [ite_eq_right (not_not_intro hd), ite_eq_left hd1, add_neg_cancel]
  · have hd1 : ¬ Nat.IsAlmostPrime 1 d := fun h => hd (Nat.isAlmostPrime_one_iff.mp h)
    rw [ite_eq_left hd, ite_eq_right hd1, neg_zero, add_zero]

/-- The nonprime von Mangoldt difference vanishes on primes. -/
private theorem lapNonprimeDiffZero (n : ℕ) (hnp : Nat.Prime n) :
    ((ArithmeticFunction.vonMangoldt
      - lapRestrictAlmostPrime 1 ArithmeticFunction.vonMangoldt) n) = 0 := by
  have hn1 : Nat.IsAlmostPrime 1 n := Nat.isAlmostPrime_one_iff.mpr hnp
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    lapRestrictApply, ite_eq_left hn1, add_neg_cancel]

/-- The nonprime von Mangoldt difference is `Λ` off primes. -/
private theorem lapNonprimeDiffEq (n : ℕ) (hnp : ¬ Nat.Prime n) :
    ((ArithmeticFunction.vonMangoldt
      - lapRestrictAlmostPrime 1 ArithmeticFunction.vonMangoldt) n)
      = ArithmeticFunction.vonMangoldt n := by
  have hn1 : ¬ Nat.IsAlmostPrime 1 n := fun h => hnp (Nat.isAlmostPrime_one_iff.mp h)
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    lapRestrictApply, ite_eq_right hn1, neg_zero, add_zero]

/-- The nonprime von Mangoldt double sum is `O(N)`. -/
private theorem lapNonprimeDoubleLe (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors.filter (fun d => ¬ Nat.Prime d),
      ArithmeticFunction.vonMangoldt d) ≤ lapC * (N : ℝ) := by
  have hstep : (∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors.filter (fun d => ¬ Nat.Prime d),
        ArithmeticFunction.vonMangoldt d)
      = ∑ n ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.vonMangoldt
          - lapRestrictAlmostPrime 1 ArithmeticFunction.vonMangoldt) n)
          * (((N / n : ℕ)) : ℝ) := by
    rw [lapIccEqIoc N,
      Finset.sum_congr rfl (fun m _ => lapNonprimeVonMangoldt m),
      ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
  have hterm : ∀ n ∈ Finset.Ioc 0 N,
      ((ArithmeticFunction.vonMangoldt
        - lapRestrictAlmostPrime 1 ArithmeticFunction.vonMangoldt) n)
        * (((N / n : ℕ)) : ℝ)
      ≤ (if ¬ Nat.Prime n then
        (N:ℝ) * (ArithmeticFunction.vonMangoldt n / ((n:ℕ):ℝ)) else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := hn.1
    have hnR : (0:ℝ) < ((n:ℕ):ℝ) := by exact_mod_cast hn1
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hnp : Nat.Prime n
    · rw [lapNonprimeDiffZero n hnp, zero_mul, ite_eq_right (not_not_intro hnp)]
    · rw [lapNonprimeDiffEq n hnp, ite_eq_left hnp]
      have hcast : (((N / n : ℕ)) : ℝ) ≤ (N:ℝ) / ((n:ℕ):ℝ) := Nat.cast_div_le
      calc ArithmeticFunction.vonMangoldt n * (((N / n : ℕ)) : ℝ)
          ≤ ArithmeticFunction.vonMangoldt n * ((N:ℝ) / ((n:ℕ):ℝ)) :=
            mul_le_mul_of_nonneg_left hcast hΛ
        _ = (N:ℝ) * (ArithmeticFunction.vonMangoldt n / ((n:ℕ):ℝ)) := by ring
  have hle : (∑ n ∈ Finset.Ioc 0 N,
        ((ArithmeticFunction.vonMangoldt
          - lapRestrictAlmostPrime 1 ArithmeticFunction.vonMangoldt) n)
          * (((N / n : ℕ)) : ℝ))
      ≤ ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ Nat.Prime n),
        (N:ℝ) * (ArithmeticFunction.vonMangoldt n / ((n:ℕ):ℝ)) := by
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum hterm
  refine le_trans (hstep ▸ hle) ?_
  have hC : (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ Nat.Prime n),
      (ArithmeticFunction.vonMangoldt n / ((n:ℕ):ℝ))) ≤ lapC := by
    have heq : ((Finset.Ioc 0 N).filter (fun n => ¬ Nat.Prime n))
        = ((Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n)) := by
      rw [← lapIccEqIoc N]
    rw [heq]
    exact lapC_bound N
  calc (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ Nat.Prime n),
        (N:ℝ) * (ArithmeticFunction.vonMangoldt n / ((n:ℕ):ℝ)))
      = (N:ℝ) * ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ Nat.Prime n),
        (ArithmeticFunction.vonMangoldt n / ((n:ℕ):ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (N:ℝ) * lapC := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
    _ = lapC * (N:ℝ) := by ring

/-- Counting times log against the theta sum. -/
private theorem lapCountingMulLogSubLe (k N : ℕ) :
    0 ≤ (almostPrimeCounting (k + 1) N : ℝ) * Real.log (N : ℝ) -
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
          ∑ p ∈ m.primeFactors, Real.log (p : ℝ)) ∧
    (almostPrimeCounting (k + 1) N : ℝ) * Real.log (N : ℝ) -
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
          ∑ p ∈ m.primeFactors, Real.log (p : ℝ)) ≤ (1 + lapC) * (N : ℝ) := by
  have htau : ((almostPrimeCounting (k + 1) N : ℕ):ℝ) * Real.log ((N:ℕ):ℝ)
      = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        Real.log ((N:ℕ):ℝ) := by
    unfold almostPrimeCounting
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdiff : ((almostPrimeCounting (k + 1) N : ℕ):ℝ) * Real.log ((N:ℕ):ℝ)
      - (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ))
      = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
        (Real.log ((N:ℕ):ℝ) - ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ)) := by
    rw [htau, ← Finset.sum_sub_distrib]
  have hnn : ∀ m ∈ Finset.Icc 1 N,
      0 ≤ Real.log ((N:ℕ):ℝ) - ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact sub_nonneg.mpr (lapLogSumLe m N hm.1 hm.2)
  have hid : ∀ m ∈ Finset.Icc 1 N,
      (Real.log ((N:ℕ):ℝ) - ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ))
      = Real.log (((N:ℕ):ℝ) / ((m:ℕ):ℝ))
        + ∑ d ∈ m.divisors.filter (fun d => ¬ Nat.Prime d),
          ArithmeticFunction.vonMangoldt d := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact lapUpperTerm m N hm.1 hm.2
  have hsub : (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m)
      ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  rw [hdiff]
  constructor
  · exact Finset.sum_nonneg (fun m hm => hnn m (hsub hm))
  · calc (∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (k + 1) m),
          (Real.log ((N:ℕ):ℝ) - ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ)))
        ≤ ∑ m ∈ Finset.Icc 1 N,
          (Real.log ((N:ℕ):ℝ) - ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => hnn m hm)
      _ = (∑ m ∈ Finset.Icc 1 N, Real.log (((N:ℕ):ℝ) / ((m:ℕ):ℝ)))
          + (∑ m ∈ Finset.Icc 1 N, ∑ d ∈ m.divisors.filter (fun d => ¬ Nat.Prime d),
            ArithmeticFunction.vonMangoldt d) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl hid
      _ ≤ (N:ℝ) + lapC * (N:ℝ) :=
          add_le_add (lapSumLogDivLe N) (lapNonprimeDoubleLe N)
      _ = (1 + lapC) * (N:ℝ) := by ring

/-- `T_k` tends to infinity for `k ≥ 1`. -/
private theorem lapRecipTendstoAtTop (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun N : ℕ => lapAlmostPrimeRecipSum k N) Filter.atTop Filter.atTop := by
  have hk0 : k ≠ 0 := by omega
  have hpow : Filter.Tendsto (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop hk0).comp lapLogLogTendsto
  have hfact : (0:ℝ) < (((k.factorial : ℕ)):ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have htarget : Filter.Tendsto
      (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^k / (((k.factorial:ℕ)):ℝ))
      Filter.atTop Filter.atTop :=
    hpow.atTop_div_const hfact
  exact (lapRecipIsEquivalent k).symm.tendsto_atTop htarget

/-- Floor-division error is at most one. -/
private theorem lapFloorErrLe (N e : ℕ) (he1 : 1 ≤ e) :
    ‖(((N / e : ℕ)):ℝ) - (N:ℝ) / ((e:ℕ):ℝ)‖ ≤ 1 := by
  have heR : (0:ℝ) < ((e:ℕ):ℝ) := by exact_mod_cast he1
  have hfloor1 : (((N / e : ℕ)):ℝ) ≤ (N:ℝ) / ((e:ℕ):ℝ) := Nat.cast_div_le
  have hmod : N % e < e := Nat.mod_lt _ (by omega)
  have hdecomp : ((e:ℕ):ℝ) * (((N / e : ℕ)):ℝ) + (((N % e : ℕ)):ℝ) = (N:ℝ) := by
    exact_mod_cast (Nat.div_add_mod N e)
  have hlt : (((N % e : ℕ)):ℝ) < ((e:ℕ):ℝ) := by exact_mod_cast hmod
  have hfloor2 : (N:ℝ) / ((e:ℕ):ℝ) - (((N / e : ℕ)):ℝ) ≤ 1 := by
    rw [sub_le_iff_le_add, div_le_iff₀ heR]
    nlinarith [hdecomp, hlt]
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hfloor1, hfloor2]

/-- Small `θ` error: crude Chebyshev bound below the threshold. -/
private theorem lapThetaSmallLe (Y : ℕ) (N e : ℕ) (hYe : N / e < Y) :
    ‖Chebyshev.theta (((N / e : ℕ)):ℝ) - (((N / e : ℕ)):ℝ)‖
      ≤ (1 + Real.log 4) * ((Y:ℕ):ℝ) := by
  have hx : (((N / e : ℕ)):ℝ) ≤ ((Y:ℕ):ℝ) := by exact_mod_cast le_of_lt hYe
  have hxnn : (0:ℝ) ≤ (((N / e : ℕ)):ℝ) := Nat.cast_nonneg _
  have hθnn : (0:ℝ) ≤ Chebyshev.theta (((N / e : ℕ)):ℝ) := Chebyshev.theta_nonneg _
  have hle : Chebyshev.theta (((N / e : ℕ)):ℝ) ≤ Real.log 4 * (((N / e : ℕ)):ℝ) :=
    Chebyshev.theta_le_log4_mul_x hxnn
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsplit : Chebyshev.theta (((N / e : ℕ)):ℝ) - (((N / e : ℕ)):ℝ)
      = Chebyshev.theta (((N / e : ℕ)):ℝ) + (-(((N / e : ℕ)):ℝ)) := by ring
  calc ‖Chebyshev.theta (((N / e : ℕ)):ℝ) - (((N / e : ℕ)):ℝ)‖
      = ‖Chebyshev.theta (((N / e : ℕ)):ℝ) + (-(((N / e : ℕ)):ℝ))‖ := by rw [hsplit]
    _ ≤ ‖Chebyshev.theta (((N / e : ℕ)):ℝ)‖ + ‖-(((N / e : ℕ)):ℝ)‖ :=
        norm_add_le _ _
    _ = Chebyshev.theta (((N / e : ℕ)):ℝ) + (((N / e : ℕ)):ℝ) := by
        rw [Real.norm_of_nonneg hθnn, norm_neg, Real.norm_of_nonneg hxnn]
    _ ≤ Real.log 4 * ((Y:ℕ):ℝ) + ((Y:ℕ):ℝ) := by
        have h1 : Real.log 4 * (((N / e : ℕ)):ℝ) ≤ Real.log 4 * ((Y:ℕ):ℝ) :=
          mul_le_mul_of_nonneg_left hx hlog4
        exact add_le_add (le_trans hle h1) hx
    _ = (1 + Real.log 4) * ((Y:ℕ):ℝ) := by ring

/-- The theta sum is equivalent to `N * T_k(N)`. -/
private theorem lapThetaSumIsEquivalent (k : ℕ) (hk : 1 ≤ k) :
    (fun N : ℕ => ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
      Chebyshev.theta (((N / e : ℕ)) : ℝ)) ~[Filter.atTop]
    (fun N : ℕ => (N : ℝ) * lapAlmostPrimeRecipSum k N) := by
  have hTtop := lapRecipTendstoAtTop k hk
  have htheta := lapThetaIsEquivalent.isLittleO
  change ((fun N : ℕ => ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
      Chebyshev.theta (((N / e : ℕ)) : ℝ))
      - (fun N : ℕ => (N : ℝ) * lapAlmostPrimeRecipSum k N))
      =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * lapAlmostPrimeRecipSum k N)
  rw [Asymptotics.isLittleO_iff] at htheta ⊢
  intro c hc
  have hc2 : (0:ℝ) < c / 2 := by linarith
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp (htheta hc2)
  have hYclean : ∀ n ≥ Y,
      ‖Chebyshev.theta (((n:ℕ)):ℝ) - (((n:ℕ)):ℝ)‖ ≤ (c / 2) * (((n:ℕ):ℝ)) := by
    intro n hn
    have h := hY n hn
    simp only [Pi.sub_apply] at h
    have hxnn : (0:ℝ) ≤ (((n:ℕ)):ℝ) := Nat.cast_nonneg _
    rwa [Real.norm_of_nonneg hxnn] at h
  have hTev : ∀ᶠ N in Filter.atTop,
      (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1) / (c / 2))
        ≤ lapAlmostPrimeRecipSum k N :=
    hTtop.eventually (Filter.eventually_ge_atTop _)
  have hNT : ∀ N : ℕ, (∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
        (N:ℝ) / ((e:ℕ):ℝ)) = (N:ℝ) * lapAlmostPrimeRecipSum k N := by
    intro N
    unfold lapAlmostPrimeRecipSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [div_eq_mul_inv, one_div]
  filter_upwards [hTev] with N hN
  have hTnn : (0:ℝ) ≤ lapAlmostPrimeRecipSum k N := lapRecipNonneg _ _
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
  have hc2nn : (0:ℝ) ≤ c / 2 := le_of_lt hc2
  have hgN : ‖(N:ℝ) * lapAlmostPrimeRecipSum k N‖
      = (N:ℝ) * lapAlmostPrimeRecipSum k N :=
    Real.norm_of_nonneg (mul_nonneg hNnn hTnn)
  have hdiff : (∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
        Chebyshev.theta (((N / e : ℕ)) : ℝ)) - (N:ℝ) * lapAlmostPrimeRecipSum k N
      = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
        (Chebyshev.theta (((N / e : ℕ)) : ℝ) - (N:ℝ) / ((e:ℕ):ℝ)) := by
    rw [Finset.sum_sub_distrib, hNT]
  have hper : ∀ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
      ‖Chebyshev.theta (((N / e : ℕ)) : ℝ) - (N:ℝ) / ((e:ℕ):ℝ)‖
        ≤ (c / 2) * ((N:ℝ) / ((e:ℕ):ℝ))
          + (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1)) := by
    intro e he
    have heI : 1 ≤ e ∧ e ≤ N := Finset.mem_Icc.mp (Finset.mem_filter.mp he).1
    have htri : ‖Chebyshev.theta (((N / e : ℕ)):ℝ) - (N:ℝ) / ((e:ℕ):ℝ)‖
        ≤ ‖Chebyshev.theta (((N / e : ℕ)):ℝ) - (((N / e : ℕ)):ℝ)‖
          + ‖(((N / e : ℕ)):ℝ) - (N:ℝ) / ((e:ℕ):ℝ)‖ := by
      have h : Chebyshev.theta (((N / e : ℕ)):ℝ) - (N:ℝ) / ((e:ℕ):ℝ)
          = (Chebyshev.theta (((N / e : ℕ)):ℝ) - (((N / e : ℕ)):ℝ))
            + ((((N / e : ℕ)):ℝ) - (N:ℝ) / ((e:ℕ):ℝ)) := by ring
      rw [h]
      exact norm_add_le _ _
    have hδ := lapFloorErrLe N e heI.1
    have hK1 : (1:ℝ) ≤ ((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1) := by
      have h1 : (0:ℝ) ≤ (1 + Real.log 4) * ((Y:ℕ):ℝ) :=
        mul_nonneg (by linarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)])
          (Nat.cast_nonneg _)
      linarith
    by_cases hYe : Y ≤ N / e
    · have hθ := hYclean (N / e) hYe
      have hxr : (((N / e : ℕ)):ℝ) ≤ (N:ℝ) / ((e:ℕ):ℝ) := Nat.cast_div_le
      have hθr : ‖Chebyshev.theta (((N / e : ℕ)):ℝ) - (((N / e : ℕ)):ℝ)‖
          ≤ (c / 2) * ((N:ℝ) / ((e:ℕ):ℝ)) :=
        le_trans hθ (mul_le_mul_of_nonneg_left hxr hc2nn)
      linarith [htri, hθr, hδ, hK1]
    · have hθ := lapThetaSmallLe Y N e (lt_of_not_ge hYe)
      have hrnn : (0:ℝ) ≤ (c / 2) * ((N:ℝ) / ((e:ℕ):ℝ)) :=
        mul_nonneg hc2nn (div_nonneg hNnn (Nat.cast_nonneg _))
      linarith [htri, hθ, hδ, hrnn]
  have hcard : ((Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e)).card ≤ N := by
    calc ((Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e)).card
        ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
      _ = N := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hmid : (∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
        ((c / 2) * ((N:ℝ) / ((e:ℕ):ℝ)) + (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1))))
      = (c / 2) * ((N:ℝ) * lapAlmostPrimeRecipSum k N)
        + ((((Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e)).card : ℕ):ℝ)
          * (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hNT]
  have hcardR : (((((Finset.Icc 1 N).filter
      (fun e => Nat.IsAlmostPrime k e)).card : ℕ)):ℝ) ≤ (N:ℝ) := by
    exact_mod_cast hcard
  have hK1nn : (0:ℝ) ≤ ((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1) := by
    have h1 : (0:ℝ) ≤ (1 + Real.log 4) * ((Y:ℕ):ℝ) :=
      mul_nonneg (by linarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)])
        (Nat.cast_nonneg _)
    linarith
  have h2 : (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1))
      ≤ (c / 2) * lapAlmostPrimeRecipSum k N := by
    have h3 := hN
    rwa [div_le_iff₀ hc2, mul_comm (lapAlmostPrimeRecipSum k N)] at h3
  have hTK : (N:ℝ) * (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1))
      ≤ (c / 2) * ((N:ℝ) * lapAlmostPrimeRecipSum k N) := by
    calc (N:ℝ) * (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1))
        ≤ (N:ℝ) * ((c / 2) * lapAlmostPrimeRecipSum k N) :=
          mul_le_mul_of_nonneg_left h2 hNnn
      _ = (c / 2) * ((N:ℝ) * lapAlmostPrimeRecipSum k N) := by ring
  simp only [Pi.sub_apply]
  rw [hdiff, hgN]
  refine le_trans (norm_sum_le _ _) ?_
  have e1 : (∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
        ‖Chebyshev.theta (((N / e : ℕ)) : ℝ) - (N:ℝ) / ((e:ℕ):ℝ)‖)
      ≤ (∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime k e),
        ((c / 2) * ((N:ℝ) / ((e:ℕ):ℝ)) + (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1)))) :=
    Finset.sum_le_sum (fun e he => hper e he)
  rw [hmid] at e1
  have hcardK : (((((Finset.Icc 1 N).filter
      (fun e => Nat.IsAlmostPrime k e)).card : ℕ)):ℝ)
        * (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1))
      ≤ (N:ℝ) * (((1 + Real.log 4) * ((Y:ℕ):ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right hcardR hK1nn
  linarith [e1, hcardK, hTK]

/-- **Landau's theorem on almost primes.** Let $k \ge 1$ be a natural number and, for a natural
number $x$, let $\pi_k(x)$ be the number of integers $n$ with $1 \le n \le x$ that have exactly
$k$ prime factors, counted with multiplicity. Then, as the natural number $x$ tends to infinity,
$$\pi_k(x) \sim \frac{x \, (\log \log x)^{k-1}}{(k-1)! \, \log x}.$$

Source: Rafael Jakimczuk, "Functions of Slow Increase and Integer Sequences,"
Journal of Integer Sequences 13 (2010),
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Jakimczuk/jakimczuk8.tex`,
lines 451-453, file SHA256
`b4a7154095398fc4a1729bef9ec80c4005190c1d9ad1dd585fbd2fcdd1eae8d7`, text SHA256
`4af87d665e5485d49e794b3927864d50a1162127411c1427d0f1a379b50b2065`,
module `WantedExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptoticWanted`.

Proves `Wanted` entry `landau_almostPrimeCounting_isEquivalent`. -/
public theorem landau_almostPrimeCounting_isEquivalent (k : ℕ) (hk : 1 ≤ k) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun x : ℕ => (almostPrimeCounting k x : ℝ))
      (fun x : ℕ => (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (k - 1) /
        (((k - 1).factorial : ℝ) * Real.log (x : ℝ))) := by
  rcases eq_or_ne k 1 with rfl | hne
  · have hcount : ∀ N : ℕ, almostPrimeCounting 1 N = Nat.primeCounting N := by
      intro N
      have e1 : Nat.primeCounting N = Nat.count Nat.Prime (N + 1) := rfl
      have hset : (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime 1 m)
          = (Finset.range (N + 1)).filter (fun m => Nat.Prime m) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        constructor
        · rintro ⟨⟨hm1, hmN⟩, hmAP⟩
          have hmp : Nat.Prime m := Nat.isAlmostPrime_one_iff.mp hmAP
          exact ⟨by omega, hmp⟩
        · rintro ⟨hmN, hmP⟩
          exact ⟨⟨hmP.one_le, by omega⟩, Nat.isAlmostPrime_one_iff.mpr hmP⟩
      unfold almostPrimeCounting
      rw [e1, Nat.count_eq_card_filter_range, hset]
    have eA : (fun x : ℕ => ((almostPrimeCounting 1 x : ℕ):ℝ))
        = (fun x : ℕ => ((Nat.primeCounting x : ℕ):ℝ)) := by
      funext N
      rw [hcount N]
    have eT : (fun x : ℕ => (x:ℝ) * (Real.log (Real.log (x:ℝ)))^((1:ℕ) - 1) /
        ((((1:ℕ) - 1).factorial : ℝ) * Real.log (x:ℝ)))
        = (fun x : ℕ => (x:ℝ) / Real.log (x:ℝ)) := by
      funext x
      rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, Nat.factorial_zero, Nat.cast_one,
        one_mul, mul_one]
    rw [eA, eT]
    exact MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    have hj0 : j ≠ 0 := by omega
    have hfact : (0:ℝ) < (((j.factorial : ℕ)):ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    have hpow : Filter.Tendsto (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^j)
        Filter.atTop Filter.atTop :=
      (Filter.tendsto_pow_atTop hj0).comp lapLogLogTendsto
    have htarget_top : Filter.Tendsto
        (fun N : ℕ => (Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))
        Filter.atTop Filter.atTop :=
      hpow.atTop_div_const hfact
    have hA : (fun N : ℕ => ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime j e),
        Chebyshev.theta (((N / e : ℕ)) : ℝ))
        ~[Filter.atTop]
        (fun N : ℕ => (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) := by
      have hNT : (fun N : ℕ => (N:ℝ) * lapAlmostPrimeRecipSum j N)
          ~[Filter.atTop]
          (fun N : ℕ => (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) :=
        Asymptotics.IsEquivalent.refl.mul (lapRecipIsEquivalent j)
      exact (lapThetaSumIsEquivalent j hj).trans hNT
    have hNo : (fun N : ℕ => (1 + lapC) * (N:ℝ)) =o[Filter.atTop]
        (fun N : ℕ => (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      have hCnn : (0:ℝ) ≤ 1 + lapC := by linarith [lapC_nonneg]
      have hev : ∀ᶠ (N : ℕ) in Filter.atTop,
          (1 + lapC) / c ≤ (Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ) :=
        htarget_top.eventually (Filter.eventually_ge_atTop ((1 + lapC) / c))
      have hev0 : ∀ᶠ (N : ℕ) in Filter.atTop, (0:ℝ) ≤ Real.log (Real.log (N:ℝ)) :=
        lapLogLogTendsto.eventually (Filter.eventually_ge_atTop (0 : ℝ))
      filter_upwards [hev, hev0, Filter.eventually_gt_atTop 0] with N hN hL hNpos
      have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
      have hpow_nn : (0:ℝ) ≤ (Real.log (Real.log (N:ℝ)))^j := pow_nonneg hL _
      have htarg_nn : (0:ℝ) ≤ (Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ) :=
        div_nonneg hpow_nn (le_of_lt hfact)
      have h2 : (1 + lapC)
          ≤ c * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ)) := by
        have h3 : (1 + lapC)
            ≤ ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ)) * c := by
          rwa [div_le_iff₀ hc] at hN
        rwa [mul_comm] at h3
      have h1 : (1 + lapC) * (N:ℝ)
          ≤ c * ((N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) := by
        calc (1 + lapC) * (N:ℝ)
            ≤ (c * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) * (N:ℝ) :=
              mul_le_mul_of_nonneg_right h2 (le_of_lt hNpos)
          _ = c * ((N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) := by
              ring
      have e1 : ‖(1 + lapC) * (N:ℝ)‖ = (1 + lapC) * (N:ℝ) :=
        Real.norm_of_nonneg (mul_nonneg hCnn (le_of_lt hNpos))
      have e2 : ‖(N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))‖
          = (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ)) :=
        Real.norm_of_nonneg (mul_nonneg (le_of_lt hNpos) htarg_nn)
      rw [e1, e2]
      exact h1
    have hEo : (fun N : ℕ => (almostPrimeCounting (j+1) N : ℝ) * Real.log (N:ℝ)
        - ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (j + 1) m),
          ∑ p ∈ m.primeFactors, Real.log (p : ℝ))
        =o[Filter.atTop]
        (fun N : ℕ => (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j / (((j.factorial:ℕ)):ℝ))) := by
      have hle : (fun N : ℕ => (almostPrimeCounting (j+1) N : ℝ) * Real.log (N:ℝ)
          - ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (j + 1) m),
            ∑ p ∈ m.primeFactors, Real.log (p : ℝ))
          =O[Filter.atTop] (fun N : ℕ => (1 + lapC) * (N:ℝ)) := by
        apply Asymptotics.IsBigO.of_bound 1
        apply Filter.Eventually.of_forall
        intro N
        have h13 := lapCountingMulLogSubLe j N
        have hCN : (0:ℝ) ≤ (1 + lapC) * (N:ℝ) :=
          mul_nonneg (by linarith [lapC_nonneg]) (Nat.cast_nonneg _)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h13.1, abs_of_nonneg hCN]
        linarith [h13.2]
      exact hle.trans_isLittleO hNo
    have hAdd := hA.add_isLittleO hEo
    have hev : (fun N : ℕ => (almostPrimeCounting (j+1) N : ℝ) * Real.log (N:ℝ))
        =ᶠ[Filter.atTop] (fun N : ℕ => (∑ e ∈ (Finset.Icc 1 N).filter
          (fun e => Nat.IsAlmostPrime j e),
          Chebyshev.theta (((N / e : ℕ)) : ℝ))
          + ((almostPrimeCounting (j+1) N : ℝ) * Real.log (N:ℝ)
          - ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (j + 1) m),
            ∑ p ∈ m.primeFactors, Real.log (p : ℝ))) := by
      apply Filter.Eventually.of_forall
      intro N
      change ((almostPrimeCounting (j+1) N : ℕ):ℝ) * Real.log ((N:ℕ):ℝ)
        = (∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.IsAlmostPrime j e),
          Chebyshev.theta (((N / e : ℕ)) : ℝ))
          + (((almostPrimeCounting (j+1) N : ℕ):ℝ) * Real.log ((N:ℕ):ℝ)
          - ∑ m ∈ (Finset.Icc 1 N).filter (fun m => Nat.IsAlmostPrime (j + 1) m),
            ∑ p ∈ m.primeFactors, Real.log ((p:ℕ):ℝ))
      rw [← lapThetaSumEq j N]
      ring
    have hτlog := hev.isEquivalent.trans hAdd
    have hdiv : (fun N : ℕ => (almostPrimeCounting (j+1) N : ℝ) * Real.log (N:ℝ)
        / Real.log (N:ℝ))
        ~[Filter.atTop] (fun N : ℕ => (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j
          / (((j.factorial:ℕ)):ℝ)) / Real.log (N:ℝ)) :=
      hτlog.div Asymptotics.IsEquivalent.refl
    have hτeq : (fun N : ℕ => (almostPrimeCounting (j+1) N : ℝ))
        =ᶠ[Filter.atTop] (fun N : ℕ => (almostPrimeCounting (j+1) N : ℝ) * Real.log (N:ℝ)
          / Real.log (N:ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      show ((almostPrimeCounting (j+1) N : ℕ):ℝ)
        = ((almostPrimeCounting (j+1) N : ℕ):ℝ) * Real.log ((N:ℕ):ℝ)
          / Real.log ((N:ℕ):ℝ)
      have hlog : Real.log ((N:ℕ):ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
      rw [mul_div_assoc, div_self hlog, mul_one]
    have hwant : (fun N : ℕ => (N:ℝ) * ((Real.log (Real.log (N:ℝ)))^j
        / (((j.factorial:ℕ)):ℝ)) / Real.log (N:ℝ))
        = (fun N : ℕ => (N:ℝ) * (Real.log (Real.log (N:ℝ)))^((j+1) - 1) /
          ((((j+1) - 1).factorial : ℝ) * Real.log (N:ℝ))) := by
      funext N
      rw [Nat.add_sub_cancel, mul_div_assoc, div_div, ← mul_div_assoc]
    rw [← hwant]
    exact hτeq.isEquivalent.trans hdiv

end

end MetaMathlibExt

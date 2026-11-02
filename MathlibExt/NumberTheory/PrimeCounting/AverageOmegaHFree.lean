/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Floor.Semifield

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Finset ArithmeticFunction

section
namespace MetaMathlibExt

-- Node proofs (n1).
-- N1: log N! = Σ Λ(d) * (N/d)
private theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have hcast : ((N.factorial : ℕ) : ℝ) = ∏ m ∈ Finset.Ico 1 (N + 1), (m : ℝ) := by
    have h := Finset.prod_Ico_id_eq_factorial N
    rw [← h, Finset.prod_natCast]
  rw [hcast, Real.log_prod (fun m hm => by
    rw [Finset.mem_Ico] at hm
    exact_mod_cast ne_of_gt hm.1)]
  have h1 : ∀ m ∈ Finset.Ico 1 (N + 1), Real.log (m : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then vonMangoldt d else 0) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmpos : 0 < m := hm.1
    have hmN : m ≤ N := by omega
    have hsub : m.divisors ⊆ Finset.Icc 1 N := by
      intro x hx
      rw [Nat.mem_divisors] at hx
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hx.1 hmpos, le_trans (Nat.le_of_dvd hmpos hx.1) hmN⟩
    have hfilter : m.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ m) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨hsub (Nat.mem_divisors.mpr ⟨hdvd, ne_of_gt hmpos⟩), hdvd⟩
      · rintro ⟨-, hdvd⟩
        exact ⟨hdvd, ne_of_gt hmpos⟩
    conv_lhs => rw [← vonMangoldt_sum (n := m), hfilter, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  have hcard : ({m ∈ Finset.Ico 1 (N + 1) | d ∣ m}.card : ℝ)
      = ((N / d : ℕ) : ℝ) := by
    congr 1
    have hset : {m ∈ Finset.Ico 1 (N + 1) | d ∣ m} = {x ∈ Finset.Ioc 0 N | d ∣ x} := by
      ext x
      simp [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  simp [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

-- N2: Mertens I: |Σ_{n≤x} Λ(n)/n - log x| ≤ log 4 + 6.
private theorem abs_sum_vonMangoldt_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x|
      ≤ Real.log 4 + 6 := by
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNge1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN1 : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
  set A := ∑ d ∈ Finset.Icc 1 N, vonMangoldt d / (d : ℝ) with hAdef
  have hpsi : ∑ d ∈ Finset.Icc 1 N, vonMangoldt d = Chebyshev.psi (N:ℝ) := by
    have h := Chebyshev.psi_eq_sum_Icc (N:ℝ)
    rw [Nat.floor_natCast] at h
    have hsplit : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)] at h
    simp at h
    exact h.symm
  have hNA : Real.log (N.factorial : ℝ) ≤ (N:ℝ) * A := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hle : ((N / d : ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    have hnn : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    calc vonMangoldt d * ((N/d:ℕ):ℝ)
        ≤ vonMangoldt d * ((N:ℝ)/(d:ℝ)) :=
          mul_le_mul_of_nonneg_left hle hnn
      _ = (N:ℝ) * (vonMangoldt d / (d:ℝ)) := by ring
  have hStirl := Stirling.le_log_factorial_stirling (n := N) (by omega)
  have hlogNnn : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNge1R
  have h2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Real.log_nonneg
    have hpi := Real.pi_gt_three
    linarith
  have hlow : (N:ℝ) * Real.log (N:ℝ) - (N:ℝ) ≤ Real.log (N.factorial : ℝ) := by
    linarith
  have hdiff : ∀ d ∈ Finset.Icc 1 N, (N:ℝ)/(d:ℝ) - ((N/d:ℕ):ℝ) ≤ 1 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdposN : 0 < d := by omega
    have hmod : N % d < d := Nat.mod_lt N hdposN
    have hdecomp : d * (N / d) + N % d = N := Nat.div_add_mod N d
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdposN
    have heq : (N:ℝ)/(d:ℝ) - ((N/d:ℕ):ℝ) = ((N % d : ℕ):ℝ)/(d:ℝ) := by
      have hcast : ((d * (N/d) + N % d : ℕ):ℝ) = (N:ℝ) := by rw [hdecomp]
      push_cast at hcast
      field_simp
      linarith
    rw [heq, div_le_one hdR]
    exact_mod_cast le_of_lt hmod
  have hup : (N:ℝ) * A ≤ Real.log (N.factorial : ℝ) + Chebyshev.psi (N:ℝ) := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div, Finset.mul_sum, ← hpsi,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hnn : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    have h1 := hdiff d hd
    have e1 : (N:ℝ) * (vonMangoldt d / (d:ℝ))
        = vonMangoldt d * ((N:ℝ)/(d:ℝ)) := by ring
    rw [e1]
    have hmul := mul_le_mul_of_nonneg_left h1 hnn
    rw [mul_one] at hmul
    have hsub := mul_sub (vonMangoldt d) ((N:ℝ)/(d:ℝ)) ((N/d:ℕ):ℝ)
    linarith
  have hfact : Real.log (N.factorial : ℝ) ≤ (N:ℝ) * Real.log (N:ℝ) := by
    have h := Nat.factorial_le_pow N
    have hpos : (0:ℝ) < (N.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos N
    have hle : ((N.factorial : ℕ):ℝ) ≤ ((N ^ N : ℕ):ℝ) := by exact_mod_cast h
    rw [Nat.cast_pow] at hle
    calc Real.log (N.factorial:ℝ) ≤ Real.log ((N:ℝ)^N) :=
          Real.log_le_log hpos hle
      _ = (N:ℝ) * Real.log (N:ℝ) := by rw [Real.log_pow]
  have hpsile := Chebyshev.psi_le_const_mul_self (x := (N:ℝ)) (le_of_lt hNpos)
  have hAge1 : Real.log (N:ℝ) - 1 ≤ A := by
    have hmul : (N:ℝ) * (Real.log (N:ℝ) - 1) ≤ (N:ℝ) * A := by
      have hexpand : (N:ℝ)*(Real.log (N:ℝ) - 1)
        = (N:ℝ)*Real.log (N:ℝ) - (N:ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left hmul hNpos
  have hAle1 : A ≤ Real.log (N:ℝ) + Real.log 4 + 4 := by
    have hmul : (N:ℝ) * A ≤ (N:ℝ) * (Real.log (N:ℝ) + Real.log 4 + 4) := by
      have hexpand : (N:ℝ)*(Real.log (N:ℝ) + Real.log 4 + 4)
        = (N:ℝ)*Real.log (N:ℝ) + (Real.log 4 + 4)*(N:ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left hmul hNpos
  have hlogNx : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log hNpos hNx
  have hx2N : x ≤ 2 * (N:ℝ) := by linarith
  have hlogx : Real.log x ≤ Real.log (N:ℝ) + Real.log 2 := by
    have h2N : Real.log x ≤ Real.log (2 * (N:ℝ)) :=
      Real.log_le_log (by linarith) hx2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h2N
    linarith
  have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : A - Real.log x ≤ Real.log 4 + 4 := by linarith
  have h2 : -(Real.log 4 + 6) ≤ A - Real.log x := by linarith
  rw [abs_le]
  constructor <;> linarith

-- Node proofs (n3).
open MeasureTheory Set intervalIntegral

-- N3(a): ∫ 1/(t log t) = log log x - log log 2
private theorem integral_inv_mul_log_facts_a (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 2 x, 1 / (t * Real.log t)
      = Real.log (Real.log x) - Real.log (Real.log 2) := by
  rw [← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun t => Real.log (Real.log t)) (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt htpos)
    have h3 := h1.log (ne_of_gt hlogpos)
    have heq : t⁻¹ / Real.log t = 1 / (t * Real.log t) := by field_simp
    rwa [heq] at h3
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t)) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    apply ContinuousOn.div continuousOn_const _ (fun t ht => by
      rw [Set.mem_Icc] at ht
      have h1 : (0:ℝ) < t := by linarith
      have h2 : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
      exact ne_of_gt (by positivity))
    exact continuousOn_id.mul (ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (by linarith : (0:ℝ) < t)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

-- Node proofs (n3b).
open MeasureTheory Set intervalIntegral

-- N3(b): ∫ 1/(t log²t) = 1/log 2 - 1/log x
private theorem integral_inv_mul_log_sq_facts_b (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 2 x, 1 / (t * Real.log t ^ 2)
      = 1 / Real.log 2 - 1 / Real.log x := by
  rw [← intervalIntegral.integral_of_le hx]
  have hderiv : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun t => -(Real.log t)⁻¹) (1 / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have htpos : 0 < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt htpos)
    have h2 := h1.inv (ne_of_gt hlogpos)
    have h3 := h2.neg
    have heq : -(-t⁻¹ / Real.log t ^ 2) = 1 / (t * Real.log t ^ 2) := by field_simp
    rwa [heq] at h3
  have hlog : ContinuousOn (fun t : ℝ => Real.log t ^ 2) (Set.Icc 2 x) := by
    apply ContinuousOn.pow
    apply ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (by linarith : (0:ℝ) < t))
  have hint : IntervalIntegrable (fun t => 1 / (t * Real.log t ^ 2)) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    apply ContinuousOn.div continuousOn_const _ (fun t ht => by
      rw [Set.mem_Icc] at ht
      have h1 : (0:ℝ) < t := by linarith
      have h2 : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
      exact ne_of_gt (by positivity))
    exact continuousOn_id.mul hlog
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [one_div, one_div]
  ring

-- Node proofs (n5).
private theorem geom_prime_pow_le (p N : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 2 N, ((1 : ℝ) / p) ^ k ≤ 2 / (p : ℝ) ^ 2 := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hx0 : (0:ℝ) ≤ 1 / p := by positivity
  have hx1 : (1:ℝ) / p < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < p)]
    linarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) (x := (1:ℝ)/p) hx0 hx1
  rw [Finset.Ico_add_one_right_eq_Icc] at hgeom
  have key : ((1:ℝ)/p)^2 / (1 - 1/p) = 1 / ((p:ℝ) * (p - 1)) := by
    field_simp
  have hfin : (1:ℝ) / ((p:ℝ) * (p - 1)) ≤ 2 / (p:ℝ)^2 := by
    have hA : (0:ℝ) < (p:ℝ) * (p - 1) := mul_pos hp0 (by linarith)
    have hB : (0:ℝ) < (p:ℝ)^2 := by positivity
    rw [le_div_iff₀ hB]
    have e : (1:ℝ) / ((p:ℝ) * (p - 1)) * (p:ℝ)^2
        = (p:ℝ)^2 / ((p:ℝ) * (p - 1)) := by ring
    rw [e, div_le_iff₀ hA]
    nlinarith [mul_nonneg (le_of_lt hp0) (show (0:ℝ) ≤ p - 2 by linarith)]
  rw [key] at hgeom
  exact le_trans hgeom hfin

private theorem nonprime_primePow_eq_prime_pow (N : ℕ) (n : ℕ)
    (hn : n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)) :
    ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ k ≤ N ∧ p ≤ N ∧ p ^ k = n := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨h1, h2⟩, hpp, hnp⟩ := hn
  obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff n |>.mp hpp
  have hk1 : k ≠ 1 := by
    rintro rfl
    simp only [pow_one] at hnp
    exact hnp hp
  have hk2 : 2 ≤ k := by omega
  have hpN : p ≤ N := by
    calc p ≤ p ^ k := Nat.le_self_pow (by omega) p
      _ ≤ N := h2
  have hkN : k ≤ N := by
    apply le_of_lt
    calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ p ^ k := Nat.pow_le_pow_left (Nat.Prime.two_le hp) k
      _ ≤ N := h2
  exact ⟨p, k, hp, hk2, hkN, hpN, rfl⟩

-- N5: sum of 1/n over non-prime prime powers ≤ 2
private theorem sum_inv_nonprime_primePow_le_two (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (1 : ℝ) / n ≤ 2 := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hempty : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, -, -⟩ := hn
      omega
    rw [hempty, Finset.sum_empty]
    norm_num
  · set T : Finset (ℕ × ℕ) :=
      ((Finset.Icc 2 N) ×ˢ (Finset.Icc 2 N)).filter
        (fun q => q.1.Prime ∧ q.1 ^ q.2 ≤ N) with hTdef
    set φ : ℕ × ℕ → ℕ := fun q => q.1 ^ q.2 with hφdef
    have hinj : ∀ a ∈ T, ∀ b ∈ T, φ a = φ b → a = b := by
      intro a ha b hb hab
      rw [hTdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at ha hb
      simp only [hφdef] at hab
      obtain ⟨⟨⟨ha1, -⟩, ⟨ha2, -⟩⟩, haP, -⟩ := ha
      obtain ⟨⟨⟨hb1, -⟩, ⟨hb2, -⟩⟩, hbP, -⟩ := hb
      have h := Nat.Prime.pow_inj' haP hbP (by omega) (by omega) hab
      obtain ⟨h1, h2⟩ := h
      exact Prod.ext h1 h2
    have hmem : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        ∃ q ∈ T, φ q = n := by
      intro n hn
      obtain ⟨p, k, hp, hk2, hkN, hpN, rfl⟩ := nonprime_primePow_eq_prime_pow N n hn
      have hPk : p ^ k ≤ N :=
        (Finset.mem_Icc.mp (Finset.mem_of_mem_filter _ hn)).2
      refine ⟨(p, k), ?_, rfl⟩
      rw [hTdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      change ((2 ≤ p ∧ p ≤ N) ∧ 2 ≤ k ∧ k ≤ N) ∧ p.Prime ∧ p ^ k ≤ N
      exact ⟨⟨⟨hp.two_le, hpN⟩, ⟨hk2, hkN⟩⟩, hp, hPk⟩
    have h1 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (1:ℝ)/n
        ≤ ∑ q ∈ T, (1:ℝ)/(φ q) := by
      have hsub : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
          ⊆ T.image φ := by
        intro n hn
        obtain ⟨q, hqT, rfl⟩ := hmem n hn
        exact Finset.mem_image_of_mem φ hqT
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity : ∀ n ∈ T.image φ, n ∉ _ → (0:ℝ) ≤ 1/(n:ℝ))
      have heq : ∑ x ∈ T.image φ, (1:ℝ)/(x:ℝ) = ∑ q ∈ T, (1:ℝ)/((φ q : ℕ):ℝ) :=
        Finset.sum_image (fun a _ b _ hab => hinj a ‹_› b ‹_› hab)
      rw [heq] at hle
      exact hle
    have h2 : ∑ q ∈ T, (1:ℝ)/(φ q)
        ≤ ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, ((1:ℝ)/p)^k := by
      have hsub2 : T ⊆ (Finset.Icc 2 N) ×ˢ (Finset.Icc 2 N) := by
        rw [hTdef]
        exact Finset.filter_subset _ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (fun q _ _ => by positivity :
          ∀ q ∈ (Finset.Icc 2 N ×ˢ Finset.Icc 2 N), q ∉ T → (0:ℝ) ≤ 1 / (φ q))
      have heq : ∑ q ∈ (Finset.Icc 2 N ×ˢ Finset.Icc 2 N), (1:ℝ)/(φ q)
          = ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, ((1:ℝ)/p)^k := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hp
        have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le (by norm_num) hp.1)
        simp only [hφdef]
        rw [Nat.cast_pow, div_pow, one_pow]
      exact le_trans hle (le_of_eq heq)
    have h3 : ∑ p ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N, ((1:ℝ)/p)^k
        ≤ ∑ p ∈ Finset.Icc 2 N, 2/(p:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mem_Icc] at hp
      exact geom_prime_pow_le p N hp.1
    have h4 : ∑ p ∈ Finset.Icc 2 N, (2:ℝ)/(p:ℝ)^2 ≤ 2 := by
      have hIcc : Finset.Icc 2 N = Finset.Ioc 1 N := by
        ext x
        simp [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hIcc]
      have hsq := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) (by norm_num) hN
      simp only [Nat.cast_one, inv_one] at hsq
      calc ∑ p ∈ Finset.Ioc 1 N, 2/(p:ℝ)^2
          = 2 * ∑ i ∈ Finset.Ioc 1 N, ((i:ℝ)^2)⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
        _ ≤ 2 * (1 - (N:ℝ)⁻¹) := by
            apply mul_le_mul_of_nonneg_left hsq (by norm_num)
        _ ≤ 2 := by
            have hpos : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
            linarith
    exact le_trans (le_trans (le_trans h1 h2) h3) h4

-- Node proofs (n13).
private theorem cardFactors_eq_sum_primeFactors (n : ℕ) :
    ArithmeticFunction.cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, ← Nat.support_factorization]
  rfl

private theorem cardFactors_sub_card_primeFactors_eq (n : ℕ) :
    (ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)
      = ∑ p ∈ n.primeFactors, ((n.factorization p : ℝ) - 1) := by
  rw [cardFactors_eq_sum_primeFactors, Nat.cast_sum, Finset.sum_sub_distrib]
  simp [Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem hfree_term_bound (h N n : ℕ) (hh : 2 ≤ h)
    (hn : n ∈ (Finset.Icc 1 N).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)) :
    0 ≤ (ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)
      ∧ (ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)
        ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (if p ^ 2 ∣ n then ((h : ℝ) - 2) else 0) := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨h1, h2⟩, hfree⟩ := hn
  have hn0 : n ≠ 0 := by omega
  have hsub : n.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpp.one_le, le_trans (Nat.le_of_dvd (by omega) hpd) h2⟩, hpp⟩
  have hnonneg : ∀ p ∈ n.primeFactors, (0:ℝ) ≤ (n.factorization p : ℝ) - 1 := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpos : 0 < n.factorization p :=
      hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    have hc : (1:ℝ) ≤ n.factorization p := by exact_mod_cast hpos
    linarith
  have hterm : ∀ p ∈ n.primeFactors,
      (n.factorization p : ℝ) - 1 ≤ (if p ^ 2 ∣ n then ((h : ℝ) - 2) else 0) := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    by_cases hdiv : p ^ 2 ∣ n
    · rw [ite_eq_left hdiv]
      have hge : 2 ≤ n.factorization p := (hpp.pow_dvd_iff_le_factorization hn0).mp hdiv
      have hlt : n.factorization p < h := hfree p hp
      have hN : n.factorization p ≤ h - 1 := by omega
      have hc : (n.factorization p : ℝ) ≤ ((h - 1 : ℕ) : ℝ) := by exact_mod_cast hN
      rw [Nat.cast_sub (by omega : 1 ≤ h), Nat.cast_one] at hc
      linarith
    · rw [ite_eq_right hdiv]
      have hlt2 : n.factorization p < 2 :=
        lt_of_not_ge (fun hle => hdiv ((hpp.pow_dvd_iff_le_factorization hn0).mpr hle))
      have hpos : 0 < n.factorization p :=
        hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
      have heq : n.factorization p = 1 := by omega
      simp [heq]
  constructor
  · rw [cardFactors_sub_card_primeFactors_eq]
    exact Finset.sum_nonneg (fun p hp => hnonneg p hp)
  · rw [cardFactors_sub_card_primeFactors_eq]
    calc ∑ p ∈ n.primeFactors, ((n.factorization p : ℝ) - 1)
        ≤ ∑ p ∈ n.primeFactors, (if p ^ 2 ∣ n then ((h : ℝ) - 2) else 0) :=
          Finset.sum_le_sum (fun p hp => hterm p hp)
      _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (if p ^ 2 ∣ n then ((h : ℝ) - 2) else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p _ _
          split_ifs with hdiv
          · have hhR : (2:ℝ) ≤ h := by exact_mod_cast hh
            linarith
          · exact le_refl 0

-- Icc 1 N = Ioc 0 N as finsets of naturals.
private theorem Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext x
  simp [Finset.mem_Icc, Finset.mem_Ioc]
  omega

-- Count bound: #{n ∈ H(N) : p² ∣ n} ≤ N / p².
private theorem card_hfree_sq_dvd_le (N p h : ℕ) :
    ({n ∈ (Finset.Icc 1 N).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h) | p ^ 2 ∣ n}.card : ℝ)
      ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
  have hle : {n ∈ (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h) | p ^ 2 ∣ n}.card
      ≤ N / p ^ 2 := by
    calc ({n ∈ (Finset.Icc 1 N).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h) | p ^ 2 ∣ n}.card : ℕ)
          ≤ ({n ∈ Finset.Icc 1 N | p ^ 2 ∣ n}).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      _ = N / p ^ 2 := by
            rw [Icc_one_eq_Ioc_zero]
            exact Nat.Ioc_filter_dvd_card_eq_div N (p ^ 2)
  have hcast : ((N / p ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
    calc ((N / p ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (N : ℝ) / (p : ℝ) ^ 2 := by rw [Nat.cast_pow]
  exact le_trans (by exact_mod_cast hle) hcast

-- Reciprocal square sum over primes ≤ 1.
private theorem sum_inv_sq_primes_le_one (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1:ℝ) / (p:ℝ)^2 ≤ 1 := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := Icc_one_eq_Ioc_zero N
  have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.Ioc 1 N := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpIcc, hpp⟩ := hp
    rw [Finset.mem_Icc] at hpIcc
    rw [Finset.mem_Ioc]
    exact ⟨hpp.one_lt, hpIcc.2⟩
  have hsq := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) (by norm_num) hN
  simp only [Nat.cast_one, inv_one] at hsq
  calc ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1:ℝ) / (p:ℝ)^2
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((p:ℝ)^2)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [one_div]
      _ ≤ ∑ i ∈ Finset.Ioc 1 N, ((i:ℝ)^2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ ≤ 1 := by
        have hpos : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
        linarith

-- N13: total Ω - ω over h-free numbers ≤ (h-2) * N.
private theorem sum_cardFactors_sub_card_primeFactors_hfree_le (h N : ℕ) (hh : 2 ≤ h) :
    0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ))
      ∧ ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ))
        ≤ ((h : ℝ) - 2) * N := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hempty : (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, -⟩ := hn
      omega
    rw [hempty, Finset.sum_empty]
    refine ⟨le_refl 0, ?_⟩
    apply mul_nonneg _ (by positivity)
    have hhR : (2:ℝ) ≤ h := by exact_mod_cast hh
    linarith
  · have hhR : (0:ℝ) ≤ (h : ℝ) - 2 := by
      have : (2:ℝ) ≤ h := by exact_mod_cast hh
      linarith
    have hNR : (0:ℝ) ≤ N := by positivity
    constructor
    · apply Finset.sum_nonneg
      intro n hn
      exact (hfree_term_bound h N n hh hn).1
    · calc ∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ))
          ≤ ∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              (if p ^ 2 ∣ n then ((h : ℝ) - 2) else 0)) :=
            Finset.sum_le_sum (fun n hn => (hfree_term_bound h N n hh hn).2)
        _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (if p ^ 2 ∣ n then ((h : ℝ) - 2) else 0)) := Finset.sum_comm
        _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (((h : ℝ) - 2) * {n ∈ (Finset.Icc 1 N).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)
                | p ^ 2 ∣ n}.card) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (((h : ℝ) - 2) * ((N : ℝ) / (p : ℝ) ^ 2)) := by
            apply Finset.sum_le_sum
            intro p hp
            apply mul_le_mul_of_nonneg_left (card_hfree_sq_dvd_le N p h) hhR
        _ = ((h : ℝ) - 2) * N * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (1:ℝ) / (p:ℝ)^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
        _ ≤ ((h : ℝ) - 2) * N * 1 := by
            apply mul_le_mul_of_nonneg_left (sum_inv_sq_primes_le_one N hN)
            exact mul_nonneg hhR hNR
        _ = ((h : ℝ) - 2) * N := by ring

-- N4: Mertens II, Lambda form (Abel summation).
private theorem abs_sum_vonMangoldt_div_mul_log_sub_loglog_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ))
        - Real.log (Real.log x)| ≤ C := by
  use 1 + 2 * (Real.log 4 + 6) / Real.log 2 + |Real.log (Real.log 2)|
  intro x hx
  have hx1 : 1 ≤ x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hCnn : (0:ℝ) ≤ Real.log 4 + 6 := by
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hSeq : ∀ t : ℝ, 1 ≤ t →
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ))
        = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, vonMangoldt k / (k:ℝ) := by
    intro t ht
    have hM : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
    have hsplit : Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp
  have hRbound : ∀ t : ℝ, 1 ≤ t →
      |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t|
        ≤ Real.log 4 + 6 := by
    intro t ht
    rw [hSeq t ht]
    exact abs_sum_vonMangoldt_div_sub_log_le t ht
  have hc0 : (fun k : ℕ => vonMangoldt k / (k:ℝ)) 0 = 0 := by simp
  have hc1 : (fun k : ℕ => vonMangoldt k / (k:ℝ)) 1 = 0 := by
    simp [vonMangoldt_apply_one]
  have hdiff : ∀ t ∈ Set.Icc (2:ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => (Real.log t)⁻¹) t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htpos : (0:ℝ) < t := by linarith
    have hlog : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < t))
    exact (Real.differentiableAt_log (ne_of_gt htpos)).inv hlog
  have hnum : ContinuousOn (fun t : ℝ => -t⁻¹) (Set.Icc 2 x) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [Set.mem_Icc] at ht
    exact ne_of_gt (by linarith : (0:ℝ) < t)
  have hden : ContinuousOn (fun t : ℝ => Real.log t ^ 2) (Set.Icc 2 x) := by
    apply ContinuousOn.pow
    exact ContinuousOn.log continuousOn_id (fun t ht => by
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (by linarith : (0:ℝ) < t))
  have hfrac : ContinuousOn (fun t : ℝ => -t⁻¹ / Real.log t ^ 2) (Set.Icc 2 x) :=
    hnum.div hden (fun t ht => by
      rw [Set.mem_Icc] at ht
      have hlp : (0:ℝ) < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
      exact ne_of_gt (pow_pos hlp 2))
  have hint : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => (Real.log t)⁻¹))
      (Set.Icc 2 x) MeasureTheory.volume := by
    have hde : deriv (fun t : ℝ => (Real.log t)⁻¹)
        = fun t => -t⁻¹ / Real.log t ^ 2 :=
      funext fun t => Real.deriv_inv_log_apply
    rw [hde]
    exact hfrac.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₁
    (c := fun k : ℕ => vonMangoldt k / (k:ℝ)) hc0 hc1 x hdiff hint
  have hmain : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ)))
      = (fun t : ℝ => (Real.log t)⁻¹) x
        * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
        - ∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) := hAbel
  have hfx : (fun t : ℝ => (Real.log t)⁻¹) x
        * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
      = 1 + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
        / Real.log x := by
    have hbx : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
        = Real.log x + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ))
          - Real.log x) := by ring
    conv_lhs => rw [hbx]
    change (Real.log x)⁻¹ * (Real.log x
      + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x))
      = 1 + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
        / Real.log x
    rw [mul_add, inv_mul_cancel₀ hlogx_ne, inv_mul_eq_div]
  have hDlog_int : MeasureTheory.IntegrableOn
      (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
      (Set.Icc 2 x) MeasureTheory.volume := by
    have hcont : ContinuousOn
        (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
        (Set.Icc 2 x) := by
      have hDf : ContinuousOn
          (fun t : ℝ => deriv (fun t : ℝ => (Real.log t)⁻¹) t) (Set.Icc 2 x) := by
        have hde : (fun t : ℝ => deriv (fun t : ℝ => (Real.log t)⁻¹) t)
            = fun t => -t⁻¹ / Real.log t ^ 2 :=
          funext fun t => Real.deriv_inv_log_apply
        rw [hde]
        exact hfrac
      exact hDf.mul (ContinuousOn.log continuousOn_id (fun t ht => by
        rw [Set.mem_Icc] at ht
        exact ne_of_gt (by linarith : (0:ℝ) < t)))
    exact hcont.integrableOn_Icc
  have hwhole : MeasureTheory.IntegrableOn
      (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
        * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
      (Set.Icc 2 x) MeasureTheory.volume :=
    integrableOn_mul_sum_Icc (fun k : ℕ => vonMangoldt k / (k:ℝ))
      (show (0:ℝ) ≤ 2 by norm_num) hint
  have hR_int : MeasureTheory.IntegrableOn
      (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
        * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t))
      (Set.Icc 2 x) MeasureTheory.volume := by
    have heq : (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t))
          = (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
            * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
            - (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t) := by
      funext t
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact hwhole.sub hDlog_int
  have hDlog_Ioc := hDlog_int.mono_set Set.Ioc_subset_Icc_self
  have hwhole_Ioc := hwhole.mono_set Set.Ioc_subset_Icc_self
  have hR_Ioc := hR_int.mono_set Set.Ioc_subset_Icc_self
  have hsplit : (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
        * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
      = (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
        + (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) := by
    have heq : (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)))
          = (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
            + (fun t => deriv (fun t : ℝ => (Real.log t)⁻¹) t
              * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) := by
      funext t
      simp only [Pi.add_apply]
      ring
    rw [heq]
    exact MeasureTheory.integral_add hDlog_Ioc hR_Ioc
  set IDR : ℝ := (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
    * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) with hIDRdef
  have hDall : ∀ t ∈ Set.Ioc (2:ℝ) x,
      deriv (fun t : ℝ => (Real.log t)⁻¹) t = -t⁻¹ / Real.log t ^ 2 := fun t _ =>
    Real.deriv_inv_log_apply
  have hDlog_pt : ∀ t ∈ Set.Ioc (2:ℝ) x,
      deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t
        = -(1/(t * Real.log t)) := by
    intro t ht
    have ht2 : (2:ℝ) < t ∧ t ≤ x := Set.mem_Ioc.mp ht
    have htpos : (0:ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    rw [hDall t ht]
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
    have h2ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlogne
    field_simp
  have hI1 : (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
      = -((Real.log (Real.log x)) - Real.log (Real.log 2)) := by
    have hcongr : (∫ t in Set.Ioc 2 x,
          deriv (fun t : ℝ => (Real.log t)⁻¹) t * Real.log t)
        = ∫ t in Set.Ioc 2 x, -(1/(t * Real.log t)) :=
      MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
        (Filter.Eventually.of_forall (fun t ht => hDlog_pt t ht))
    rw [hcongr, MeasureTheory.integral_neg, integral_inv_mul_log_facts_a x hx]
  have hDR_pt : ∀ t ∈ Set.Ioc (2:ℝ) x,
      -((Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
        ≤ deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)
        ∧ deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)
          ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) := by
    intro t ht
    have ht2 : (2:ℝ) < t ∧ t ≤ x := Set.mem_Ioc.mp ht
    have htpos : (0:ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
    have hDeq : |deriv (fun t : ℝ => (Real.log t)⁻¹) t|
        = 1/(t * Real.log t ^ 2) := by
      rw [hDall t ht, abs_div, abs_neg, abs_inv, abs_of_pos htpos,
        abs_of_nonneg (pow_nonneg (le_of_lt hlogpos) 2)]
      have htne : t ≠ 0 := ne_of_gt htpos
      have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
      have h2ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlogne
      field_simp
    have hnn : (0:ℝ) ≤ 1/(t * Real.log t ^ 2) := by
      apply div_nonneg (by norm_num)
      apply mul_nonneg (le_of_lt htpos)
      exact pow_nonneg (le_of_lt hlogpos) 2
    have habs : |deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)|
        ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) := by
      have hRt := hRbound t (by linarith)
      rw [abs_mul, hDeq]
      calc (1/(t * Real.log t ^ 2))
            * |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t|
          = |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t|
            * (1/(t * Real.log t ^ 2)) := by ring
        _ ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) :=
          mul_le_mul_of_nonneg_right hRt hnn
    refine ⟨?_, (abs_le.mp habs).2⟩
    calc -((Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
          ≤ -|deriv (fun t : ℝ => (Real.log t)⁻¹) t
            * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)| := by
          linarith [habs]
      _ ≤ deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t) :=
        neg_abs_le _
  have hCh : MeasureTheory.IntegrableOn
      (fun t => (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
      (Set.Icc 2 x) MeasureTheory.volume := by
    apply ContinuousOn.integrableOn_Icc
    refine ContinuousOn.mul continuousOn_const
      (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact continuousOn_id.mul hden
    · intro t ht
      rw [Set.mem_Icc] at ht
      have htpos : (0:ℝ) < t := by linarith
      have hlp : (0:ℝ) < Real.log t := Real.log_pos (by linarith : (1:ℝ) < t)
      exact ne_of_gt (mul_pos htpos (pow_pos hlp 2))
  have hCh_Ioc := hCh.mono_set Set.Ioc_subset_Icc_self
  have hval : (∫ t in Set.Ioc 2 x, (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)))
      = (Real.log 4 + 6) * (1 / Real.log 2 - 1 / Real.log x) := by
    rw [MeasureTheory.integral_const_mul, integral_inv_mul_log_sq_facts_b x hx]
  have hle : (Real.log 4 + 6) * (1 / Real.log 2 - 1 / Real.log x)
      ≤ (Real.log 4 + 6) / Real.log 2 := by
    have h1logx : (0:ℝ) ≤ 1 / Real.log x :=
      div_nonneg (by norm_num) (le_of_lt hlogx_pos)
    calc (Real.log 4 + 6) * (1 / Real.log 2 - 1 / Real.log x)
        = (Real.log 4 + 6) * (1 / Real.log 2)
          - (Real.log 4 + 6) * (1 / Real.log x) := by ring
      _ ≤ (Real.log 4 + 6) * (1 / Real.log 2) :=
        sub_le_self _ (mul_nonneg hCnn h1logx)
      _ = (Real.log 4 + 6) / Real.log 2 := by ring
  have hIDR_le : IDR ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [hIDRdef]
    have hmono := MeasureTheory.setIntegral_mono_on hR_Ioc hCh_Ioc measurableSet_Ioc
      (fun t ht => (hDR_pt t ht).2)
    linarith [hmono, hval, hle]
  have hIDR_ge : -((Real.log 4 + 6) / Real.log 2) ≤ IDR := by
    rw [hIDRdef]
    have hpt : ∀ t ∈ Set.Ioc (2:ℝ) x,
        -(deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t))
          ≤ (Real.log 4 + 6) * (1/(t * Real.log t ^ 2)) := by
      intro t ht
      have h := (hDR_pt t ht).1
      have h2 := neg_le_neg h
      rwa [neg_neg] at h2
    have hRneg_Ioc : MeasureTheory.IntegrableOn
        (fun t => -(deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)))
        (Set.Ioc 2 x) MeasureTheory.volume := hR_Ioc.neg
    have hmono2 := MeasureTheory.setIntegral_mono_on hRneg_Ioc hCh_Ioc
      measurableSet_Ioc hpt
    have hneg : (∫ t in Set.Ioc 2 x, -(deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)))
        = -(∫ t in Set.Ioc 2 x, deriv (fun t : ℝ => (Real.log t)⁻¹) t
          * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k / (k:ℝ)) - Real.log t)) :=
      MeasureTheory.integral_neg _
    linarith [hmono2, hval, hle, hneg]
  have heq : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ)))
      - Real.log (Real.log x)
      = (1 - Real.log (Real.log 2))
        + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x - IDR := by
    have h := hmain
    rw [hfx, hsplit, hI1] at h
    linarith
  have hRx := hRbound x hx1
  have e1 : |1 - Real.log (Real.log 2)| ≤ 1 + |Real.log (Real.log 2)| := by
    calc |1 - Real.log (Real.log 2)| ≤ |1| + |Real.log (Real.log 2)| := abs_sub _ _
      _ = 1 + |Real.log (Real.log 2)| := by rw [abs_one]
  have e2 : |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x|
        / Real.log x ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [div_le_iff₀ hlogx_pos]
    have h1 : (1:ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos, one_mul]
      exact Real.log_le_log (by norm_num) (by linarith)
    calc |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x|
          ≤ Real.log 4 + 6 := hRx
      _ = (Real.log 4 + 6) * 1 := by ring
      _ ≤ (Real.log 4 + 6) * (Real.log x / Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 hCnn
      _ = ((Real.log 4 + 6) / Real.log 2) * Real.log x := by ring
  have e2d : |(((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
        / Real.log x)| ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogx_pos]
    exact e2
  have e3 : |IDR| ≤ (Real.log 4 + 6) / Real.log 2 := by
    rw [abs_le]
    exact ⟨hIDR_ge, hIDR_le⟩
  calc |(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log (n:ℝ))⁻¹ * (vonMangoldt n / (n:ℝ)))
        - Real.log (Real.log x)|
      = |(1 - Real.log (Real.log 2))
        + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x - IDR| := by
        rw [heq]
    _ ≤ |(1 - Real.log (Real.log 2))
        + ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x| + |IDR| :=
      abs_sub _ _
    _ ≤ (|1 - Real.log (Real.log 2)|
        + |(((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / (k:ℝ)) - Real.log x)
          / Real.log x)|) + |IDR| :=
      add_le_add_left (abs_add_le _ _) _
    _ ≤ (1 + |Real.log (Real.log 2)| + (Real.log 4 + 6) / Real.log 2)
        + (Real.log 4 + 6) / Real.log 2 :=
      add_le_add (add_le_add e1 e2d) e3
    _ = 1 + 2 * (Real.log 4 + 6) / Real.log 2 + |Real.log (Real.log 2)| := by
      ring

-- Pointwise form of `Nat.factorization_pow`.
private theorem factorization_pow_apply (d h p : ℕ) :
    (d ^ h).factorization p = h * d.factorization p := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

-- N8(i): summability of the real Möbius-over-power series.
private theorem summable_moebius_div_pow (h : ℕ) (hh : 2 ≤ h) :
    Summable (fun d : ℕ => (moebius d : ℝ) / (d : ℝ) ^ h) := by
  have hsum1 : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^h) :=
    Real.summable_one_div_nat_pow.mpr (by omega : 1 < h)
  have hmuR : ∀ d : ℕ, |(moebius d : ℝ)| ≤ 1 := by
    intro d
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hbound : ∀ d : ℕ, ‖(moebius d : ℝ) / (d:ℝ)^h‖ ≤ (1:ℝ)/(d:ℝ)^h := by
    intro d
    have hnn : (0:ℝ) ≤ (d:ℝ)^h := pow_nonneg (Nat.cast_nonneg d) h
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnn]
    exact div_le_div_of_nonneg_right (hmuR d) hnn
  exact Summable.of_norm_bounded hsum1 hbound

-- N8 helper: `riemannZeta` at a natural is the cast of the real p-series tsum.
private theorem riemannZeta_natCast_eq_ofReal_tsum (h : ℕ) (hh : 2 ≤ h) :
    riemannZeta (h:ℂ) = ((∑' n : ℕ, (1:ℝ)/(n:ℝ)^h : ℝ):ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega : 1 < h), Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast]

-- N8(iii): the zeta value is at least 1.
private theorem one_le_riemannZeta_natCast_re (h : ℕ) (hh : 2 ≤ h) :
    1 ≤ (riemannZeta (h:ℂ)).re := by
  have hsum1 : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^h) :=
    Real.summable_one_div_nat_pow.mpr (by omega : 1 < h)
  have hle := hsum1.le_tsum (1:ℕ) (fun j _ => by positivity)
  have h1 : (1:ℝ) ≤ ∑' n : ℕ, (1:ℝ)/(n:ℝ)^h := by
    simpa using hle
  have hre : (riemannZeta (h:ℂ)).re = ∑' n : ℕ, (1:ℝ)/(n:ℝ)^h := by
    rw [riemannZeta_natCast_eq_ofReal_tsum h hh, Complex.ofReal_re]
  rw [hre]
  exact h1

-- N8(ii): the Möbius tsum is the reciprocal of the zeta value.
private theorem tsum_moebius_div_pow_eq (h : ℕ) (hh : 2 ≤ h) :
    (∑' d : ℕ, (moebius d : ℝ) / (d : ℝ) ^ h)
      = 1 / (riemannZeta (h : ℂ)).re := by
  have hs : 1 < ((h : ℂ)).re := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_re, ← Nat.cast_one, Nat.cast_lt]
    omega
  have hmul := LSeries_zeta_mul_Lseries_moebius (s := (h:ℂ)) hs
  rw [LSeries_zeta_eq_riemannZeta hs] at hmul
  have hcastM : LSeries (fun n : ℕ => ((moebius n : ℤ) : ℂ)) (h:ℂ)
      = ((∑' d : ℕ, (moebius d : ℝ) / (d : ℝ) ^ h : ℝ):ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [LSeries.term_zero]
      have h0 : ((moebius 0 : ℝ) / ((0:ℕ):ℝ)^h : ℝ) = 0 := by
        rw [Nat.cast_zero, zero_pow (by omega : h ≠ 0), div_zero]
      rw [h0, Complex.ofReal_zero]
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast]
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
        Complex.ofReal_intCast]
  rw [hcastM, riemannZeta_natCast_eq_ofReal_tsum h hh] at hmul
  have hZ1 : (1:ℝ) ≤ ∑' n : ℕ, (1:ℝ)/(n:ℝ)^h := by
    have hsum1 : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^h) :=
      Real.summable_one_div_nat_pow.mpr (by omega : 1 < h)
    have hle := hsum1.le_tsum (1:ℕ) (fun j _ => by positivity)
    simpa using hle
  have hZS : (∑' n : ℕ, (1:ℝ)/(n:ℝ)^h) * (∑' d : ℕ, (moebius d:ℝ)/(d:ℝ)^h)
      = 1 := by
    have h := congrArg Complex.re hmul
    rw [← Complex.ofReal_mul, Complex.ofReal_re] at h
    simpa using h
  have hZne : (∑' n : ℕ, (1:ℝ)/(n:ℝ)^h) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) hZ1)
  have hre : (riemannZeta (h:ℂ)).re = ∑' n : ℕ, (1:ℝ)/(n:ℝ)^h := by
    rw [riemannZeta_natCast_eq_ofReal_tsum h hh, Complex.ofReal_re]
  rw [hre, eq_div_iff hZne]
  exact (mul_comm _ _).trans hZS

-- N7: Möbius indicator for h-free numbers.
private theorem sum_moebius_pow_dvd_eq_ite_hfree (h n : ℕ) (hh : 1 ≤ h)
    (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors.filter (fun d => d ^ h ∣ n), moebius d
      = (if (∀ p ∈ n.primeFactors, n.factorization p < h) then (1 : ℤ)
        else 0) := by
  have hn0 : n ≠ 0 := by omega
  have hh0 : 0 < h := by omega
  set g : ℕ →₀ ℕ := Finsupp.mapRange (fun x => x / h) (Nat.zero_div h)
    n.factorization with hgdef
  set r : ℕ := g.prod (· ^ ·) with hrdef
  have hsupp : g.support ⊆ n.primeFactors := by
    have h1 : g.support ⊆ n.factorization.support := Finsupp.support_mapRange
    rwa [Nat.support_factorization] at h1
  have hprime : ∀ p ∈ g.support, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors (hsupp hp)
  have hrfac : r.factorization = g := Nat.prod_pow_factorization_eq_self hprime
  have hrpos : 0 < r := by
    have h0 : 0 ∉ g.support := by
      intro hcon
      have h2 := (hprime 0 hcon).two_le
      omega
    exact Nat.prod_pow_pos_of_zero_notMem_support h0
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hrp : ∀ p : ℕ, r.factorization p = n.factorization p / h := by
    intro p
    have h1 : r.factorization p = g p := by rw [hrfac]
    have h2 : g p = n.factorization p / h := by
      simp only [hgdef, Finsupp.mapRange_apply]
    exact h1.trans h2
  have hrn : r ∣ n := by
    rw [← Nat.factorization_le_iff_dvd hr0 hn0, Finsupp.le_def]
    intro p
    rw [hrp p]
    exact Nat.div_le_self _ _
  have hkey : ∀ d : ℕ, d ≠ 0 → (d ^ h ∣ n ↔ d ∣ r) := by
    intro d hd0
    have hdh0 : d ^ h ≠ 0 := pow_ne_zero h hd0
    rw [← Nat.factorization_le_iff_dvd hdh0 hn0,
      ← Nat.factorization_le_iff_dvd hd0 hr0]
    simp only [Finsupp.le_def]
    apply forall_congr'
    intro p
    rw [factorization_pow_apply, hrp p, mul_comm h]
    exact (Nat.le_div_iff_mul_le hh0).symm
  have hset : n.divisors.filter (fun d => d ^ h ∣ n) = r.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdiv, -⟩, hpow⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
      exact ⟨(hkey d (ne_of_gt hdpos)).mp hpow, hr0⟩
    · rintro ⟨hdivr, -⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdivr hrpos
      exact ⟨⟨dvd_trans hdivr hrn, hn0⟩, (hkey d (ne_of_gt hdpos)).mpr hdivr⟩
  rw [hset]
  have hsum : ∑ d ∈ r.divisors, moebius d = (1 : ArithmeticFunction ℤ) r := by
    have h1 : (zeta * moebius : ArithmeticFunction ℤ) r
        = ∑ d ∈ r.divisors, moebius d :=
      ArithmeticFunction.coe_zeta_mul_apply
    rw [ArithmeticFunction.coe_zeta_mul_moebius] at h1
    exact h1.symm
  rw [hsum, ArithmeticFunction.one_apply]
  by_cases hr1 : r = 1
  · have hcond : ∀ p ∈ n.primeFactors, n.factorization p < h := by
      intro p hp
      have hrfp : r.factorization p = 0 := by
        rw [hr1]
        simp [Nat.factorization_one]
      rw [hrp p] at hrfp
      have hdiv := (Nat.div_eq_zero_iff).mp hrfp
      omega
    rw [ite_eq_left hr1, ite_eq_left hcond]
  · rw [ite_eq_right hr1]
    have hneg : ¬ ∀ p ∈ n.primeFactors, n.factorization p < h := by
      intro hall
      apply hr1
      apply Nat.eq_of_factorization_eq hr0 one_ne_zero
      intro p
      have h1p : (1 : ℕ).factorization p = 0 := by simp [Nat.factorization_one]
      have hzp : n.factorization p / h = 0 := by
        by_cases hmem : p ∈ n.primeFactors
        · exact (Nat.div_eq_zero_iff).mpr (Or.inr (hall p hmem))
        · have hzero : n.factorization p = 0 := by
            have hsup : p ∉ n.factorization.support := by
              rw [Nat.support_factorization]
              exact hmem
            exact Finsupp.notMem_support_iff.mp hsup
          rw [hzero]
          exact Nat.zero_div h
      rw [hrp p, hzp]
      exact h1p.symm
    rw [ite_eq_right hneg]

-- N10: tail bound for the Möbius partial sums.
private theorem abs_tsum_moebius_div_pow_sub_partial_le (h : ℕ) (hh : 2 ≤ h)
    (y : ℝ) (hy : 1 ≤ y) :
    |1 / (riemannZeta (h:ℂ)).re
        - ∑ d ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun d : ℕ => (d:ℝ)^h ≤ y),
          (moebius d : ℝ) / (d:ℝ)^h|
      ≤ 3 / Real.sqrt y := by
  set f : ℕ → ℝ := fun d => (moebius d : ℝ) / (d:ℝ)^h with hfdef
  set D : Finset ℕ := (Finset.Icc 1 ⌊y⌋₊).filter (fun d : ℕ => (d:ℝ)^h ≤ y)
    with hDdef
  set M : ℕ := ⌊Real.sqrt y⌋₊ with hMdef
  have hypos : (0:ℝ) < y := by linarith
  have hSpos : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hypos
  have hSnn : (0:ℝ) ≤ Real.sqrt y := le_of_lt hSpos
  have hS1 : (1:ℝ) ≤ Real.sqrt y := by
    calc (1:ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt y := Real.sqrt_le_sqrt hy
  have hM1 : 1 ≤ M := (Nat.one_le_floor_iff (Real.sqrt y)).mpr hS1
  have hMle : (M:ℝ) ≤ Real.sqrt y := Nat.floor_le hSnn
  have hSy : Real.sqrt y ≤ y := by
    have hy2 : y ≤ y^2 := by
      calc y = y * 1 := (mul_one y).symm
        _ ≤ y * y := mul_le_mul_of_nonneg_left hy (le_of_lt hypos)
        _ = y^2 := (pow_two y).symm
    have hle := Real.sqrt_le_sqrt hy2
    rwa [Real.sqrt_sq (le_of_lt hypos)] at hle
  have hfsum : Summable f := summable_moebius_div_pow h hh
  have hSeq : ∑' d : ℕ, f d = 1 / (riemannZeta (h:ℂ)).re :=
    tsum_moebius_div_pow_eq h hh
  have hf0 : f 0 = 0 := by
    simp only [hfdef]
    rw [Nat.cast_zero, zero_pow (by omega : h ≠ 0), div_zero]
  have hfg : ∀ d : ℕ, |f d| ≤ (1:ℝ)/(d:ℝ)^h := by
    intro d
    have hnn : (0:ℝ) ≤ (d:ℝ)^h := pow_nonneg (Nat.cast_nonneg d) h
    have hmu : |(moebius d : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := d)
      rw [← Int.cast_abs]
      exact_mod_cast h
    simp only [hfdef]
    rw [abs_div, abs_of_nonneg hnn]
    exact div_le_div_of_nonneg_right hmu hnn
  have hDsub : D ⊆ Finset.Icc 1 M := by
    intro d hd
    rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hdh⟩ := hd
    have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
    have h2h : (d:ℝ)^2 ≤ (d:ℝ)^h := pow_le_pow_right₀ hdR1 (by omega : 2 ≤ h)
    have hdy : (d:ℝ)^2 ≤ y := le_trans h2h hdh
    have hsqrt : (d:ℝ) ≤ Real.sqrt y := by
      have h1 : (d:ℝ) = Real.sqrt ((d:ℝ)^2) := (Real.sqrt_sq (by linarith)).symm
      rw [h1]
      exact Real.sqrt_le_sqrt hdy
    have hdM : d ≤ M := Nat.le_floor hsqrt
    exact Finset.mem_Icc.mpr ⟨hd1, hdM⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (M+1))
    (fun d => d ∈ D) f
  have hDeq : (Finset.range (M+1)).filter (fun d => d ∈ D) = D := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hd
      have hdM := hDsub hd
      rw [Finset.mem_Icc] at hdM
      exact ⟨by omega, hd⟩
  rw [hDeq] at hsplit
  set E' : Finset ℕ := (Finset.range (M+1)).filter (fun d => d ∉ D)
    with hEdef
  have hT2 : (∑ d ∈ Finset.range (M+1), f d) - (∑ d ∈ D, f d)
      = ∑ d ∈ E', f d := by
    linarith [hsplit]
  have hEbound : ∀ d ∈ E', d ≠ 0 → |f d| ≤ 1/y := by
    intro d hd hd0
    rw [hEdef, Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨hdM, hdD⟩ := hd
    have hd1 : 1 ≤ d := by omega
    have hdRy : (d:ℝ) ≤ y := by
      have hdM' : d ≤ M := by omega
      have hdR : (d:ℝ) ≤ (M:ℝ) := by exact_mod_cast hdM'
      exact le_trans (le_trans hdR hMle) hSy
    have hdN : d ≤ ⌊y⌋₊ := Nat.le_floor hdRy
    have hdIcc : d ∈ Finset.Icc 1 ⌊y⌋₊ := Finset.mem_Icc.mpr ⟨hd1, hdN⟩
    have hgt : y < (d:ℝ)^h := by
      by_contra hcon
      have hcon' : (d:ℝ)^h ≤ y := le_of_not_gt hcon
      have hdD' : d ∈ D := by
        rw [hDdef]
        exact Finset.mem_filter.mpr ⟨hdIcc, hcon'⟩
      exact hdD hdD'
    have h1 : |f d| ≤ (1:ℝ)/(d:ℝ)^h := hfg d
    have h2 : (1:ℝ)/(d:ℝ)^h < 1/y :=
      one_div_lt_one_div_of_lt hypos hgt
    linarith
  have hMy : (M:ℝ)/y ≤ 1/Real.sqrt y := by
    have hsq : Real.sqrt y * Real.sqrt y = y :=
      Real.mul_self_sqrt (le_of_lt hypos)
    rw [div_le_div_iff₀ hypos hSpos]
    calc (M:ℝ) * Real.sqrt y ≤ Real.sqrt y * Real.sqrt y :=
          mul_le_mul_of_nonneg_right hMle (le_of_lt hSpos)
      _ = y := hsq
      _ = 1 * y := (one_mul y).symm
  have hT2le : |(∑ d ∈ Finset.range (M+1), f d) - (∑ d ∈ D, f d)|
      ≤ 1/Real.sqrt y := by
    rw [hT2]
    have hdrop : ∑ d ∈ E', |f d|
        = ∑ d ∈ E'.filter (fun d => d ≠ 0), |f d| := by
      have hsp := Finset.sum_filter_add_sum_filter_not E' (fun d => d ≠ 0)
        (fun d => |f d|)
      have hz : ∑ d ∈ E'.filter (fun d => ¬ d ≠ 0), |f d| = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        rw [Finset.mem_filter] at hd
        have hd0 : d = 0 := not_not.mp hd.2
        rw [hd0]
        simp [hf0]
      rw [hz, add_zero] at hsp
      exact hsp.symm
    have hEsub : E'.filter (fun d => d ≠ 0) ⊆ Finset.Icc 1 M := by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdE, hd0⟩ := hd
      rw [hEdef, Finset.mem_filter, Finset.mem_range] at hdE
      obtain ⟨hdM, -⟩ := hdE
      have hd1 : 1 ≤ d := by omega
      have hdM' : d ≤ M := by omega
      exact Finset.mem_Icc.mpr ⟨hd1, hdM'⟩
    have hterm : ∀ d ∈ E'.filter (fun d => d ≠ 0), |f d| ≤ 1/y := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact hEbound d hd.1 hd.2
    have hcard : (E'.filter (fun d => d ≠ 0)).card ≤ M := by
      calc (E'.filter (fun d => d ≠ 0)).card ≤ (Finset.Icc 1 M).card :=
            Finset.card_le_card hEsub
        _ = M := by rw [Nat.card_Icc]; omega
    calc |∑ d ∈ E', f d| ≤ ∑ d ∈ E', |f d| :=
          Finset.abs_sum_le_sum_abs f E'
      _ = ∑ d ∈ E'.filter (fun d => d ≠ 0), |f d| := hdrop
      _ ≤ ∑ d ∈ E'.filter (fun d => d ≠ 0), 1/y :=
          Finset.sum_le_sum (fun d hd => hterm d hd)
      _ = ((E'.filter (fun d => d ≠ 0)).card : ℝ)/y := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (M:ℝ)/y :=
          div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hypos)
      _ ≤ 1/Real.sqrt y := hMy
  have hsplitM := Summable.sum_add_tsum_nat_add (M+1) hfsum
  have hT1 : (∑' d : ℕ, f d) - (∑ d ∈ Finset.range (M+1), f d)
      = ∑' i : ℕ, f (i + (M+1)) := by
    linarith [hsplitM]
  have hgsum : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^h) :=
    Real.summable_one_div_nat_pow.mpr (by omega : 1 < h)
  have hgsum' : Summable (fun i : ℕ => (1:ℝ)/((i+(M+1):ℕ):ℝ)^h) := by
    have h := hgsum.comp_injective (add_left_injective (M+1))
    simpa [Function.comp_def] using h
  have hnorm1 : ∀ x : ℝ, ‖‖x‖‖ = ‖x‖ := fun x => by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (norm_nonneg _)
  have hnormsum : Summable (fun i : ℕ => ‖f (i+(M+1))‖) := by
    apply Summable.of_norm_bounded hgsum'
    intro i
    rw [hnorm1, Real.norm_eq_abs]
    exact hfg (i+(M+1))
  have hT1a : |∑' i : ℕ, f (i+(M+1))| ≤ ∑' i : ℕ, ‖f (i+(M+1))‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_tsum_le_tsum_norm hnormsum
  have hT1b : (∑' i : ℕ, ‖f (i+(M+1))‖)
      ≤ ∑' i : ℕ, (1:ℝ)/((i+(M+1):ℕ):ℝ)^h := by
    apply Summable.tsum_le_tsum _ hnormsum hgsum'
    intro i
    rw [Real.norm_eq_abs]
    exact hfg (i+(M+1))
  have hgsum2 : Summable (fun i : ℕ => (1:ℝ)/((i+(M+1):ℕ):ℝ)^2) := by
    have h2 : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have h := h2.comp_injective (add_left_injective (M+1))
    simpa [Function.comp_def] using h
  have hT1c : (∑' i : ℕ, (1:ℝ)/((i+(M+1):ℕ):ℝ)^h)
      ≤ ∑' i : ℕ, (1:ℝ)/((i+(M+1):ℕ):ℝ)^2 := by
    apply Summable.tsum_le_tsum _ hgsum' hgsum2
    intro i
    have hbase : (1:ℝ) ≤ ((i+(M+1):ℕ):ℝ) := by
      have h1 : 1 ≤ i+(M+1) := by omega
      exact_mod_cast h1
    have hle : ((i+(M+1):ℕ):ℝ)^2 ≤ ((i+(M+1):ℕ):ℝ)^h :=
      pow_le_pow_right₀ hbase (by omega : 2 ≤ h)
    have hpos2 : (0:ℝ) < ((i+(M+1):ℕ):ℝ) := by
      have h0 : 0 < i+(M+1) := by omega
      exact_mod_cast h0
    have hpos : (0:ℝ) < ((i+(M+1):ℕ):ℝ)^2 := pow_pos hpos2 2
    exact one_div_le_one_div_of_le hpos hle
  have hM2 : Real.sqrt y ≤ 2*(M:ℝ) := by
    have hlt : Real.sqrt y < (M:ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt y)
    have hM1R : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
    linarith
  have hMbound : 1/(M:ℝ) ≤ 2/Real.sqrt y := by
    have hMpos : (0:ℝ) < (M:ℝ) := by
      have h1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
      linarith
    rw [div_le_div_iff₀ hMpos hSpos]
    linarith [hM2]
  have htail : (∑' i : ℕ, (1:ℝ)/((i+(M+1):ℕ):ℝ)^2) ≤ 2/Real.sqrt y := by
    have hrange : ∀ K : ℕ, ∑ i ∈ Finset.range K, (1:ℝ)/((i+(M+1):ℕ):ℝ)^2
        ≤ 2/Real.sqrt y := by
      intro K
      have hK : M + 1 + K - (M + 1) = K := by omega
      have hre : ∑ i ∈ Finset.range K, (1:ℝ)/((i+(M+1):ℕ):ℝ)^2
          = ∑ j ∈ Finset.Ico (M+1) (M+1+K), (1:ℝ)/(j:ℝ)^2 := by
        have h := Finset.sum_Ico_eq_sum_range
          (fun j : ℕ => (1:ℝ)/(j:ℝ)^2) (M+1) (M+1+K)
        rw [hK] at h
        rw [h]
        apply Finset.sum_congr rfl
        intro i hi
        have he : i+(M+1) = M+1+i := by omega
        rw [he]
      rw [hre]
      have hsub : Finset.Ico (M+1) (M+1+K) ⊆ Finset.Ioc M (M+1+K) := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [Finset.mem_Ioc]
        omega
      have hconv : ∑ j ∈ Finset.Ico (M+1) (M+1+K), (1:ℝ)/(j:ℝ)^2
          = ∑ j ∈ Finset.Ico (M+1) (M+1+K), ((j:ℝ)^2)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [one_div]
      rw [hconv]
      calc ∑ j ∈ Finset.Ico (M+1) (M+1+K), ((j:ℝ)^2)⁻¹
          ≤ ∑ j ∈ Finset.Ioc M (M+1+K), ((j:ℝ)^2)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun j _ _ => by positivity)
        _ ≤ (M:ℝ)⁻¹ - ((M+1+K : ℕ):ℝ)⁻¹ :=
            sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : M ≠ 0)
              (by omega : M ≤ M+1+K)
        _ ≤ (M:ℝ)⁻¹ := by
            have hnn : (0:ℝ) ≤ ((M+1+K:ℕ):ℝ)⁻¹ := by positivity
            linarith
        _ = 1/(M:ℝ) := by rw [one_div]
        _ ≤ 2/Real.sqrt y := hMbound
    have hnn : ∀ i : ℕ, (0:ℝ) ≤ (1:ℝ)/((i+(M+1):ℕ):ℝ)^2 := fun i => by
      positivity
    exact Real.tsum_le_of_sum_range_le hnn hrange
  have hSR : |(∑' d : ℕ, f d) - (∑ d ∈ Finset.range (M+1), f d)|
      ≤ 2/Real.sqrt y := by
    rw [hT1]
    calc |∑' i : ℕ, f (i+(M+1))| ≤ ∑' i : ℕ, ‖f (i+(M+1))‖ := hT1a
      _ ≤ ∑' i : ℕ, (1:ℝ)/((i+(M+1):ℕ):ℝ)^h := hT1b
      _ ≤ ∑' i : ℕ, (1:ℝ)/((i+(M+1):ℕ):ℝ)^2 := hT1c
      _ ≤ 2/Real.sqrt y := htail
  have hdecomp : (1/(riemannZeta (h:ℂ)).re) - (∑ d ∈ D, f d)
      = ((∑' d : ℕ, f d) - (∑ d ∈ Finset.range (M+1), f d))
        + ((∑ d ∈ Finset.range (M+1), f d) - (∑ d ∈ D, f d)) := by
    rw [← hSeq]
    ring
  rw [hdecomp]
  calc |((∑' d : ℕ, f d) - (∑ d ∈ Finset.range (M+1), f d))
        + ((∑ d ∈ Finset.range (M+1), f d) - (∑ d ∈ D, f d))|
      ≤ |(∑' d : ℕ, f d) - (∑ d ∈ Finset.range (M+1), f d)|
        + |(∑ d ∈ Finset.range (M+1), f d) - (∑ d ∈ D, f d)| :=
        abs_add_le _ _
    _ ≤ 2/Real.sqrt y + 1/Real.sqrt y := add_le_add hSR hT2le
    _ = 3/Real.sqrt y := by ring

-- N9: h-free count as a Möbius-weighted divisor sum.
private theorem card_hfree_eq_sum_moebius_mul_div (h N : ℕ) (hh : 1 ≤ h) :
    ((((Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).card : ℕ):ℤ)
      = ∑ d ∈ Finset.Icc 1 N, moebius d * ((N / d ^ h : ℕ) : ℤ) := by
  have hcard : ((((Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).card : ℕ):ℤ)
      = ∑ n ∈ Finset.Icc 1 N,
        (if (∀ p ∈ n.primeFactors, n.factorization p < h) then (1:ℤ)
          else 0) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  have hinner : ∀ n ∈ Finset.Icc 1 N,
      (∑ d ∈ n.divisors.filter (fun d => d ^ h ∣ n), moebius d)
        = ∑ d ∈ Finset.Icc 1 N,
          (if d ^ h ∣ n then moebius d else 0) := by
    intro n hn
    have hnIcc := Finset.mem_Icc.mp hn
    have hset : n.divisors.filter (fun d => d ^ h ∣ n)
        = (Finset.Icc 1 N).filter (fun d => d ^ h ∣ n) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hdiv, -⟩, hpow⟩
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
        have hle : d ≤ n := Nat.le_of_dvd (by omega) hdiv
        exact ⟨⟨hdpos, le_trans hle hnIcc.2⟩, hpow⟩
      · rintro ⟨⟨h1, hN⟩, hpow⟩
        have hdvd : d ∣ n := by
          have hpowle : d ^ 1 ∣ d ^ h := pow_dvd_pow d (by omega : 1 ≤ h)
          rw [pow_one] at hpowle
          exact dvd_trans hpowle hpow
        exact ⟨⟨hdvd, by omega⟩, hpow⟩
    rw [hset, Finset.sum_filter]
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      (if (∀ p ∈ n.primeFactors, n.factorization p < h) then (1:ℤ) else 0)
        = ∑ d ∈ Finset.Icc 1 N,
          (if d ^ h ∣ n then moebius d else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    calc (if (∀ p ∈ n.primeFactors, n.factorization p < h) then (1:ℤ) else 0)
        = ∑ d ∈ n.divisors.filter (fun d => d ^ h ∣ n), moebius d :=
          (sum_moebius_pow_dvd_eq_ite_hfree h n hh hn1).symm
      _ = ∑ d ∈ Finset.Icc 1 N, (if d ^ h ∣ n then moebius d else 0) :=
          hinner n hn
  have hswap : (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        (if d ^ h ∣ n then moebius d else 0))
      = ∑ d ∈ Finset.Icc 1 N, moebius d * ((N / d ^ h : ℕ) : ℤ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hcardd : (Finset.filter (fun n => d ^ h ∣ n) (Finset.Icc 1 N)).card
        = N / d ^ h := by
      rw [Icc_one_eq_Ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcardd]
    ring
  calc ((((Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).card : ℕ):ℤ)
      = ∑ n ∈ Finset.Icc 1 N,
        (if (∀ p ∈ n.primeFactors, n.factorization p < h) then (1:ℤ)
          else 0) := hcard
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        (if d ^ h ∣ n then moebius d else 0) :=
        Finset.sum_congr rfl hstep
    _ = ∑ d ∈ Finset.Icc 1 N, moebius d * ((N / d ^ h : ℕ) : ℤ) := hswap

-- N6: Mertens II for primes, from the von Mangoldt form (N4) and the
-- prime-power correction (N5).
private theorem abs_sum_prime_inv_sub_loglog_le :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p
        - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C4, hC4⟩ := abs_sum_vonMangoldt_div_mul_log_sub_loglog_le
  refine ⟨C4 + 2, fun x hx => ?_⟩
  set N := ⌊x⌋₊ with hNdef
  set f : ℕ → ℝ := fun n => (Real.log (n : ℝ))⁻¹ * (vonMangoldt n / (n : ℝ))
    with hfdef
  have h4 : |∑ n ∈ Finset.Icc 0 N, f n - Real.log (Real.log x)| ≤ C4 := hC4 x hx
  have hsplit1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 N)
    IsPrimePow f
  have hzero : ∑ n ∈ (Finset.Icc 0 N).filter (fun n => ¬ IsPrimePow n), f n
      = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    have hL : vonMangoldt n = 0 := by
      rw [vonMangoldt_apply, ite_eq_right hn.2]
    simp only [hfdef, hL, zero_div, mul_zero]
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 0 N).filter IsPrimePow) Nat.Prime f
  have eS1 : ((Finset.Icc 0 N).filter IsPrimePow).filter Nat.Prime
      = (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime) := by
    rw [Finset.filter_filter]
  have eS2 : ((Finset.Icc 0 N).filter IsPrimePow).filter (fun n => ¬ Nat.Prime n)
      = (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
    rw [Finset.filter_filter]
  rw [eS1, eS2] at hsplit2
  have hS1 : (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime)
      = (Finset.Icc 1 N).filter Nat.Prime := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hN⟩, -, hpp⟩
      exact ⟨⟨hpp.one_le, hN⟩, hpp⟩
    · rintro ⟨⟨h1, hN⟩, hpp⟩
      exact ⟨⟨by omega, hN⟩, hpp.isPrimePow, hpp⟩
  have hS2 : (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
      = (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hN⟩, hpp, hnp⟩
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact not_isPrimePow_zero hpp
      exact ⟨⟨by omega, hN⟩, hpp, hnp⟩
    · rintro ⟨⟨h1, hN⟩, hpp, hnp⟩
      exact ⟨⟨by omega, hN⟩, hpp, hnp⟩
  have hterm1 : ∀ p ∈ (Finset.Icc 0 N).filter
      (fun n => IsPrimePow n ∧ n.Prime), f p = (1 : ℝ) / (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpIcc, -, hpp⟩ := hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
    simp only [hfdef, vonMangoldt_apply_prime hpp, ← mul_div_assoc,
      inv_mul_cancel₀ hlog]
  have hterm2 : ∀ n ∈ (Finset.Icc 0 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime),
      0 ≤ f n ∧ f n ≤ (1 : ℝ) / (n : ℝ) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnIcc, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff n |>.mp hpp
    have hk1 : 1 ≤ k := hk
    have hpk2 : 2 ≤ p ^ k := by
      calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp.two_le
        _ ≤ p ^ k := pow_le_pow_right₀ hp.one_le hk1
    have hnpos : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hpk2
      linarith
    have hlogpos : 0 < Real.log ((p ^ k : ℕ) : ℝ) := by
      apply Real.log_pos
      have h2 : (2 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hpk2
      linarith
    have hlogne : Real.log ((p ^ k : ℕ) : ℝ) ≠ 0 := ne_of_gt hlogpos
    have hLnn : 0 ≤ vonMangoldt (p ^ k) := vonMangoldt_nonneg
    have hLle : vonMangoldt (p ^ k) ≤ Real.log ((p ^ k : ℕ) : ℝ) :=
      vonMangoldt_le_log
    have hlognn : (0 : ℝ) ≤ (Real.log ((p ^ k : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr (le_of_lt hlogpos)
    have hdiv : vonMangoldt (p ^ k) / ((p ^ k : ℕ) : ℝ)
        ≤ Real.log ((p ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) :=
      (div_le_div_iff_of_pos_right hnpos).mpr hLle
    have h2 : (Real.log ((p ^ k : ℕ) : ℝ))⁻¹
          * (Real.log ((p ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))
        = 1 / ((p ^ k : ℕ) : ℝ) := by
      rw [← mul_div_assoc, inv_mul_cancel₀ hlogne]
    constructor
    · simp only [hfdef]
      exact mul_nonneg hlognn (div_nonneg hLnn (le_of_lt hnpos))
    · have h1 : f (p ^ k) ≤ (Real.log ((p ^ k : ℕ) : ℝ))⁻¹
          * (Real.log ((p ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ)) := by
        simp only [hfdef]
        exact mul_le_mul_of_nonneg_left hdiv hlognn
      rw [h2] at h1
      exact h1
  have hmem : ∀ n ∈ (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime),
      n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
    intro n hn
    rw [hS2]
    exact hn
  have h1 : ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime), f n
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p := by
    rw [hS1]
    apply Finset.sum_congr rfl
    intro p hp
    apply hterm1
    rw [hS1]
    exact hp
  have h2 : ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), f n
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        f n := by
    rw [hS2]
  have htot : ∑ n ∈ Finset.Icc 0 N, f n
      = ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ n.Prime), f n
        + ∑ n ∈ (Finset.Icc 0 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n := by
    have h0 : ∑ n ∈ (Finset.Icc 0 N).filter IsPrimePow, f n
        = ∑ n ∈ Finset.Icc 0 N, f n := by
      rw [hzero, add_zero] at hsplit1
      exact hsplit1
    rw [← h0, ← hsplit2]
  have hPE : ∑ n ∈ Finset.Icc 0 N, f n
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p)
        + ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n := by
    rw [htot, h1, h2]
  have hEnn : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime), f n := by
    apply Finset.sum_nonneg
    intro n hn
    exact (hterm2 n (hmem n hn)).1
  have hEle : ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n => IsPrimePow n ∧ ¬ n.Prime), f n ≤ 2 := by
    calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), f n
        ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          (1 : ℝ) / n :=
          Finset.sum_le_sum (fun n hn => (hterm2 n (hmem n hn)).2)
      _ ≤ 2 := sum_inv_nonprime_primePow_le_two N
  have hdecomp : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p)
        - Real.log (Real.log x)
      = ((∑ n ∈ Finset.Icc 0 N, f n) - Real.log (Real.log x))
        - ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n := by
    rw [hPE]
    ring
  rw [hdecomp]
  calc |((∑ n ∈ Finset.Icc 0 N, f n) - Real.log (Real.log x))
        - ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n|
      ≤ |∑ n ∈ Finset.Icc 0 N, f n - Real.log (Real.log x)|
        + |∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
          f n| := abs_sub _ _
    _ ≤ C4 + 2 := by
        have habs : |∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => IsPrimePow n ∧ ¬ n.Prime), f n| ≤ 2 := by
          rw [abs_of_nonneg hEnn]
          exact hEle
        linarith [h4, habs]

-- Helper: partial sums of 1/√n are at most 2√N.
private theorem sum_inv_sqrt_le_two_sqrt (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/Real.sqrt (n:ℝ) ≤ 2*Real.sqrt (N:ℝ) := by
  induction N with
  | zero =>
    have hempty : Finset.Icc (1:ℕ) 0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    rw [hempty, Finset.sum_empty]
    positivity
  | succ N ih =>
    have hle : (1:ℕ) ≤ N + 1 := by omega
    rw [Finset.sum_Icc_succ_top hle _]
    have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hN1pos : (0:ℝ) < ((N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos N
    have hN1nn : (0:ℝ) ≤ ((N+1:ℕ):ℝ) := le_of_lt hN1pos
    have hcast : ((N+1:ℕ):ℝ) = (N:ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    set a : ℝ := Real.sqrt ((N+1:ℕ):ℝ) with ha
    set b : ℝ := Real.sqrt (N:ℝ) with hb
    have ha_pos : 0 < a := Real.sqrt_pos.mpr hN1pos
    have hb_nn : 0 ≤ b := Real.sqrt_nonneg (N:ℝ)
    have hble : b ≤ a :=
      Real.sqrt_le_sqrt (by rw [hcast]; linarith)
    have hsq : a^2 - b^2 = 1 := by
      rw [ha, hb, Real.sq_sqrt hN1nn, Real.sq_sqrt hNnn, hcast]
      ring
    have hsum_pos : 0 < a + b := by linarith
    have hsum_ne : a + b ≠ 0 := ne_of_gt hsum_pos
    have hfactor : (a-b)*(a+b) = 1 := by
      have h : (a-b)*(a+b) = a^2 - b^2 := by ring
      rw [h, hsq]
    have hdiff : a - b = 1/(a+b) := (eq_div_iff hsum_ne).mpr hfactor
    have hkey : 1/a ≤ 2*(a-b) := by
      rw [hdiff, mul_one_div, div_le_div_iff₀ ha_pos hsum_pos, one_mul]
      linarith
    linarith [ih, hkey]

-- Helper: natural division approximates real division within 1.
private theorem abs_nat_div_sub_div_le_one (M b : ℕ) (hb : 0 < b) :
    |(((M/b : ℕ)):ℝ) - (M:ℝ)/(b:ℝ)| ≤ 1 := by
  have hbRpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hbRne : (b:ℝ) ≠ 0 := ne_of_gt hbRpos
  have hle : (((M/b : ℕ)):ℝ) ≤ (M:ℝ)/(b:ℝ) := Nat.cast_div_le
  have hdm := Nat.div_add_mod M b
  have hdmR : (b:ℝ) * (((M/b:ℕ)):ℝ) + (((M%b:ℕ)):ℝ) = (M:ℝ) := by
    exact_mod_cast hdm
  have hmod : M % b < b := Nat.mod_lt M hb
  have hmodR : (((M%b:ℕ)):ℝ) < (b:ℝ) := by exact_mod_cast hmod
  have hcancel : (b:ℝ) * (((M/b:ℕ)):ℝ) / (b:ℝ) = (((M/b:ℕ)):ℝ) := by
    field_simp
  have heq : (M:ℝ)/(b:ℝ) = (((M/b:ℕ)):ℝ) + (((M%b:ℕ)):ℝ)/(b:ℝ) := by
    have h : (M:ℝ) = (b:ℝ) * (((M/b:ℕ)):ℝ) + (((M%b:ℕ)):ℝ) := hdmR.symm
    rw [h, add_div, hcancel]
  have hfrac : (((M%b:ℕ)):ℝ)/(b:ℝ) < 1 := (div_lt_one hbRpos).mpr hmodR
  have habs : |(((M/b:ℕ)):ℝ) - (M:ℝ)/(b:ℝ)| = (M:ℝ)/(b:ℝ) - (((M/b:ℕ)):ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  rw [habs]
  have hdiff : (M:ℝ)/(b:ℝ) - (((M/b:ℕ)):ℝ) = (((M%b:ℕ)):ℝ)/(b:ℝ) := by
    linarith [heq]
  rw [hdiff]
  exact le_of_lt hfrac

-- N11: h-free counting function `x/ζ(h) + O(√x)`.
private theorem abs_card_hfree_sub_le (h : ℕ) (hh : 2 ≤ h) (y : ℝ) (hy : 0 ≤ y) :
    |((((Finset.Icc 1 ⌊y⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).card : ℕ) : ℝ)
      - y / (riemannZeta (h : ℂ)).re| ≤ 4 * Real.sqrt y := by
  have hZ1 : (1:ℝ) ≤ (riemannZeta (h : ℂ)).re :=
    one_le_riemannZeta_natCast_re h hh
  have hZpos : (0:ℝ) < (riemannZeta (h : ℂ)).re :=
    lt_of_lt_of_le (by norm_num) hZ1
  have hZinv_le : (1:ℝ) / (riemannZeta (h : ℂ)).re ≤ 1 := by
    rw [div_le_one hZpos]
    exact hZ1
  by_cases hy1 : y < 1
  · have hN0 : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy1
    have hempty : Finset.Icc (1:ℕ) (0:ℕ) = ∅ := by decide
    rw [hN0, hempty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      zero_sub]
    rw [abs_neg, abs_of_nonneg (div_nonneg hy (le_of_lt hZpos))]
    have hdiv_le : y / (riemannZeta (h : ℂ)).re ≤ y := by
      calc y / (riemannZeta (h : ℂ)).re = y * (1 / (riemannZeta (h : ℂ)).re) := by
            ring
        _ ≤ y * 1 := mul_le_mul_of_nonneg_left hZinv_le hy
        _ = y := mul_one y
    have hysq : y ^ 2 ≤ y := by
      calc y ^ 2 = y * y := by ring
        _ ≤ 1 * y := mul_le_mul_of_nonneg_right (le_of_lt hy1) hy
        _ = y := one_mul y
    have hyle : y ≤ Real.sqrt y := by
      have heq : y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy).symm
      calc y = Real.sqrt (y ^ 2) := heq
        _ ≤ Real.sqrt y := Real.sqrt_le_sqrt hysq
    have hsqrt_nn : (0:ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg y
    linarith
  · have hy1le : (1:ℝ) ≤ y := le_of_not_gt hy1
    have hypos : (0:ℝ) < y := lt_of_lt_of_le (by norm_num) hy1le
    have hSpos : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hypos
    have hSnn : (0:ℝ) ≤ Real.sqrt y := le_of_lt hSpos
    have hS1 : (1:ℝ) ≤ Real.sqrt y := by
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt y := Real.sqrt_le_sqrt hy1le
    set N : ℕ := ⌊y⌋₊ with hNdef
    set D : Finset ℕ := (Finset.Icc 1 N).filter (fun d : ℕ => (d:ℝ)^h ≤ y) with hDdef
    have hNy : (N:ℝ) ≤ y := Nat.floor_le hy
    have hN9 := card_hfree_eq_sum_moebius_mul_div h N (by omega : 1 ≤ h)
    have hN9R : ((((Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).card : ℕ) : ℝ)
        = ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) * (((N / d ^ h : ℕ) : ℝ)) := by
      have hcon := congrArg (Int.cast (R := ℝ)) hN9
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hcon
      exact hcon
    have hN_eq : (Finset.Icc 1 ⌊y⌋₊) = Finset.Icc 1 N := by rw [hNdef]
    rw [hN_eq, hN9R]
    have hDsub : D ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
    have hvanish : ∀ d ∈ Finset.Icc 1 N, d ∉ D →
        (moebius d : ℝ) * (((N / d ^ h : ℕ) : ℝ)) = 0 := by
      intro d hd hdD
      have hdR1 : (1:ℝ) ≤ (d:ℝ) := by
        rw [Finset.mem_Icc] at hd
        exact_mod_cast hd.1
      have hgt : y < (d:ℝ)^h := lt_of_not_ge (fun hle => hdD (Finset.mem_filter.mpr ⟨hd, hle⟩))
      have hcast : ((d ^ h : ℕ):ℝ) = (d:ℝ)^h := Nat.cast_pow d h
      have hlt : N < d ^ h := by
        have hNRlt : (N:ℝ) < ((d ^ h : ℕ):ℝ) := lt_of_le_of_lt hNy (hcast ▸ hgt)
        exact_mod_cast hNRlt
      have hdiv0 : N / d ^ h = 0 := Nat.div_eq_of_lt hlt
      rw [hdiv0, Nat.cast_zero, mul_zero]
    have hsumD : ∑ d ∈ Finset.Icc 1 N, (moebius d : ℝ) * (((N / d ^ h : ℕ) : ℝ))
        = ∑ d ∈ D, (moebius d : ℝ) * (((N / d ^ h : ℕ) : ℝ)) :=
      (Finset.sum_subset hDsub (fun d hd hdD => hvanish d hd hdD)).symm
    rw [hsumD]
    have hpart := abs_tsum_moebius_div_pow_sub_partial_le h hh y hy1le
    have hDdef2 : (Finset.Icc 1 ⌊y⌋₊).filter (fun d : ℕ => (d:ℝ)^h ≤ y) = D := by
      rw [hDdef, hNdef]
    rw [hDdef2] at hpart
    have htheta_nn : ∀ d ∈ D, (0:ℝ) ≤ y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ) := by
      intro d hd
      rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, -⟩, -⟩ := hd
      have hdiv_pos : (0:ℝ) < ((d ^ h : ℕ):ℝ) := by
        have hpos : 0 < d ^ h := pow_pos (by omega : 0 < d) h
        exact_mod_cast hpos
      have hfl : ((N / d ^ h : ℕ):ℝ) ≤ y / ((d ^ h : ℕ):ℝ) := by
        have h1 : N / d ^ h = ⌊y / ((d ^ h : ℕ):ℝ)⌋₊ := by
          rw [hNdef]
          exact (Nat.floor_div_natCast y (d ^ h)).symm
        rw [h1]
        exact Nat.floor_le (div_nonneg hy (le_of_lt hdiv_pos))
      linarith
    have htheta_lt : ∀ d ∈ D, y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ) < 1 := by
      intro d hd
      have h1 : N / d ^ h = ⌊y / ((d ^ h : ℕ):ℝ)⌋₊ := by
        rw [hNdef]
        exact (Nat.floor_div_natCast y (d ^ h)).symm
      have hlt := Nat.lt_floor_add_one (y / ((d ^ h : ℕ):ℝ))
      rw [← h1] at hlt
      linarith
    have hrewrite : ∀ d ∈ D, (moebius d : ℝ) * (((N / d ^ h : ℕ) : ℝ))
        = y * ((moebius d : ℝ) / (d:ℝ)^h)
          - (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ)) := by
      intro d hd
      rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, -⟩, -⟩ := hd
      have hcast : ((d ^ h : ℕ):ℝ) = (d:ℝ)^h := Nat.cast_pow d h
      rw [hcast]
      ring
    have hQeq : ∑ d ∈ D, (moebius d : ℝ) * (((N / d ^ h : ℕ) : ℝ))
        = y * (∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h)
          - ∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      exact hrewrite d hd
    rw [hQeq]
    have htail : |y * ((∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re)|
        ≤ 3 * Real.sqrt y := by
      have habs : |(∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re|
          ≤ 3 / Real.sqrt y := by
        rw [abs_sub_comm]
        exact hpart
      calc |y * ((∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re)|
            = y * |(∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re| := by
            rw [abs_mul, abs_of_nonneg hy]
        _ ≤ y * (3 / Real.sqrt y) := mul_le_mul_of_nonneg_left habs hy
        _ = 3 * Real.sqrt y := by
            have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
            field_simp
            linarith [hsq]
    have hmu_le : ∀ d ∈ D, |(moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))| ≤ 1 := by
      intro d hd
      have hmu : |(moebius d : ℝ)| ≤ 1 := by
        have hle := ArithmeticFunction.abs_moebius_le_one (n := d)
        rw [← Int.cast_abs]
        exact_mod_cast hle
      have hth_nn := htheta_nn d hd
      have hth_lt := htheta_lt d hd
      have hth_abs : |y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ)| ≤ 1 := by
        rw [abs_of_nonneg hth_nn]
        exact le_of_lt hth_lt
      calc |(moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))|
            = |(moebius d : ℝ)| * |y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hmu hth_abs (abs_nonneg _) (by norm_num)
        _ = 1 := mul_one 1
    have hcard_le : (D.card : ℝ) ≤ Real.sqrt y := by
      set M : ℕ := ⌊Real.sqrt y⌋₊ with hMdef
      have hM1 : 1 ≤ M := (Nat.one_le_floor_iff (Real.sqrt y)).mpr hS1
      have hMle : (M:ℝ) ≤ Real.sqrt y := Nat.floor_le hSnn
      have hsub : D ⊆ Finset.Icc 1 M := by
        intro d hd
        rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, -⟩, hdh⟩ := hd
        have hdR1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
        have h2h : (d:ℝ)^2 ≤ (d:ℝ)^h := pow_le_pow_right₀ hdR1 (by omega : 2 ≤ h)
        have hdy : (d:ℝ)^2 ≤ y := le_trans h2h hdh
        have hd_nn : (0:ℝ) ≤ (d:ℝ) := by positivity
        have hsqrt : (d:ℝ) ≤ Real.sqrt y := by
          have heq : (d:ℝ) = Real.sqrt ((d:ℝ)^2) := (Real.sqrt_sq hd_nn).symm
          rw [heq]
          exact Real.sqrt_le_sqrt hdy
        have hdM : d ≤ M := Nat.le_floor hsqrt
        exact Finset.mem_Icc.mpr ⟨hd1, hdM⟩
      have hcard : D.card ≤ M := by
        calc D.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hsub
          _ = M := by rw [Nat.card_Icc]; omega
      calc (D.card : ℝ) ≤ (M:ℝ) := by exact_mod_cast hcard
        _ ≤ Real.sqrt y := hMle
    have herr_le : |∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))|
        ≤ Real.sqrt y := by
      calc |∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))|
            ≤ ∑ d ∈ D, |(moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ D, 1 := Finset.sum_le_sum (fun d hd => hmu_le d hd)
        _ = D.card := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ Real.sqrt y := hcard_le
    have hfinal : |y * (∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h)
          - ∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))
          - y / (riemannZeta (h : ℂ)).re| ≤ 4 * Real.sqrt y := by
      have heq : y * (∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h)
            - ∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))
            - y / (riemannZeta (h : ℂ)).re
          = (y * ((∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re))
            - (∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))) := by
        have hdiv : y / (riemannZeta (h : ℂ)).re = y * (1 / (riemannZeta (h : ℂ)).re) := by ring
        rw [hdiv]
        ring
      rw [heq]
      calc |(y * ((∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re))
            - (∑ d ∈ D, (moebius d : ℝ) * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ)))|
            ≤ |y * ((∑ d ∈ D, (moebius d : ℝ) / (d:ℝ)^h) - 1 / (riemannZeta (h : ℂ)).re)|
              + |∑ d ∈ D, (moebius d : ℝ)
                * (y / ((d ^ h : ℕ):ℝ) - ((N / d ^ h : ℕ):ℝ))| := abs_sub _ _
        _ ≤ 3 * Real.sqrt y + Real.sqrt y := add_le_add htail herr_le
        _ = 4 * Real.sqrt y := by ring
    exact hfinal

-- N14: prime-weighted h-free counts against the main term.
private theorem abs_sum_prime_card_hfree_sub_main_le (h : ℕ) (hh : 2 ≤ h)
    (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        ((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
      - (x / (riemannZeta (h : ℂ)).re)
        * ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1:ℝ) / (p:ℝ)|
      ≤ 8 * x := by
  have hx0 : (0:ℝ) ≤ x := le_trans (by norm_num) hx
  have hSx : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  set N : ℕ := ⌊x⌋₊ with hNdef
  set S : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime with hSdef
  have hNx : (N:ℝ) ≤ x := Nat.floor_le hx0
  have hsqrtN_le : Real.sqrt (N:ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
  have hterm : ∀ p ∈ S,
      |((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
        - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re|
        ≤ 4 * Real.sqrt (x / (p:ℝ)) := by
    intro p hp
    rw [hSdef, Finset.mem_filter] at hp
    obtain ⟨-, hpp⟩ := hp
    have hppos : (0:ℝ) < (p:ℝ) := by
      have h2 := hpp.two_le
      have h0 : 0 < p := by omega
      exact_mod_cast h0
    have hy0 : (0:ℝ) ≤ x / (p:ℝ) := div_nonneg hx0 (le_of_lt hppos)
    exact abs_card_hfree_sub_le h hh (x / (p:ℝ)) hy0
  have hmain : (x / (riemannZeta (h : ℂ)).re)
        * ∑ p ∈ S, (1:ℝ) / (p:ℝ)
        = ∑ p ∈ S, (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hdecomp : ∑ p ∈ S,
        ((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
        - (x / (riemannZeta (h : ℂ)).re) * ∑ p ∈ S, (1:ℝ) / (p:ℝ)
        = ∑ p ∈ S, (((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
          - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re) := by
    rw [hmain, ← Finset.sum_sub_distrib]
  have hbound_each : ∀ p ∈ S,
      |((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
        - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re|
        ≤ 4 * Real.sqrt x * ((1:ℝ) / Real.sqrt (p:ℝ)) := by
    intro p hp
    have hle_term := hterm p hp
    have hsqrt_eq : Real.sqrt (x / (p:ℝ)) = Real.sqrt x / Real.sqrt (p:ℝ) :=
      Real.sqrt_div hx0 (p:ℝ)
    calc |((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
          - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re|
          ≤ 4 * Real.sqrt (x / (p:ℝ)) := hle_term
        _ = 4 * Real.sqrt x * ((1:ℝ) / Real.sqrt (p:ℝ)) := by
            rw [hsqrt_eq]
            ring
  have hsum_le : ∑ p ∈ S,
        |((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
          - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re|
        ≤ 4 * Real.sqrt x * (2 * Real.sqrt (N:ℝ)) := by
    have hle : ∑ p ∈ S, (4 * Real.sqrt x * ((1:ℝ) / Real.sqrt (p:ℝ)))
        = 4 * Real.sqrt x * ∑ p ∈ S, ((1:ℝ) / Real.sqrt (p:ℝ)) := by
      rw [Finset.mul_sum]
    have hsub : ∑ p ∈ S, ((1:ℝ) / Real.sqrt (p:ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 N, ((1:ℝ) / Real.sqrt (n:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro i _ _
        positivity
    have hsqrt_sum := sum_inv_sqrt_le_two_sqrt N
    calc ∑ p ∈ S,
            |((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
              - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re|
          ≤ ∑ p ∈ S, (4 * Real.sqrt x * ((1:ℝ) / Real.sqrt (p:ℝ))) :=
            Finset.sum_le_sum (fun p hp => hbound_each p hp)
        _ = 4 * Real.sqrt x * ∑ p ∈ S, ((1:ℝ) / Real.sqrt (p:ℝ)) := hle
        _ ≤ 4 * Real.sqrt x * (∑ n ∈ Finset.Icc 1 N, ((1:ℝ) / Real.sqrt (n:ℝ))) := by
            apply mul_le_mul_of_nonneg_left hsub
            positivity
        _ ≤ 4 * Real.sqrt x * (2 * Real.sqrt (N:ℝ)) := by
            apply mul_le_mul_of_nonneg_left hsqrt_sum
            positivity
  have hfinal_le : 4 * Real.sqrt x * (2 * Real.sqrt (N:ℝ)) ≤ 8 * x := by
    have hmul : Real.sqrt x * Real.sqrt (N:ℝ) ≤ x := by
      calc Real.sqrt x * Real.sqrt (N:ℝ)
            ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_left hsqrtN_le hSx
        _ = x := hsqx
    linarith
  calc |∑ p ∈ S,
          ((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
        - (x / (riemannZeta (h : ℂ)).re) * ∑ p ∈ S, (1:ℝ) / (p:ℝ)|
        = |∑ p ∈ S, (((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
            - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re)| := by
          rw [hdecomp]
      _ ≤ ∑ p ∈ S,
          |((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
            - (x / (p:ℝ)) / (riemannZeta (h : ℂ)).re| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ 4 * Real.sqrt x * (2 * Real.sqrt (N:ℝ)) := hsum_le
      _ ≤ 8 * x := hfinal_le

-- N12: double counting of prime factors over h-free numbers.
private theorem sum_card_primeFactors_hfree_double_count (h : ℕ)
    (hh : 2 ≤ h) (x : ℝ) (hx : 0 ≤ x) :
    ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      (n.primeFactors.card : ℝ)
      ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        ((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
    ∧ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        ((((Finset.Icc 1 ⌊x / (p:ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)
      - ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (n.primeFactors.card : ℝ) ≤ x := by
  set N : ℕ := ⌊x⌋₊ with hNdef
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hIe : Finset.Icc (1 : ℕ) N = ∅ := by
      rw [hN0]
      decide
    have hH0 : (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h) = ∅ := by
      simp only [hIe, Finset.filter_empty]
    have hP0 : (Finset.Icc 1 N).filter Nat.Prime = ∅ := by
      simp only [hIe, Finset.filter_empty]
    rw [hH0, hP0, Finset.sum_empty, Finset.sum_empty, sub_zero]
    exact ⟨le_refl 0, hx⟩
  · have hN1 : 1 ≤ N := by omega
    have hNx : (N : ℝ) ≤ x := by
      rw [hNdef]
      exact Nat.floor_le hx
    have hn0 : ∀ n ∈ (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h), n ≠ 0 := by
      intro n hn
      have hn1 : (1 : ℕ) ≤ n :=
        (Finset.mem_Icc.mp (Finset.mem_of_subset (Finset.filter_subset _ _) hn)).1
      omega
    have hprimeP : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime, p.Prime := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hsubP : ∀ n ∈ (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        n.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
      intro n hn q hq
      obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
      have hnIcc : n ∈ Finset.Icc 1 N :=
        Finset.mem_of_subset (Finset.filter_subset _ _) hn
      have hn12 := Finset.mem_Icc.mp hnIcc
      have hqle : q ≤ N := le_trans (Nat.le_of_dvd (by omega) hqdvd) hn12.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.one_le, hqle⟩, hqp⟩
    have hterm : ∀ n ∈ (Finset.Icc 1 N).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        ((n.primeFactors.card : ℕ) : ℝ)
          = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (if p ∈ n.primeFactors then (1 : ℝ) else 0) := by
      intro n hn
      have hsub := hsubP n hn
      have eif : (∑ _x ∈ n.primeFactors, (1 : ℝ))
          = ∑ p ∈ n.primeFactors, (if p ∈ n.primeFactors then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (ite_eq_left hp).symm
      have esub : (∑ p ∈ n.primeFactors, (if p ∈ n.primeFactors then (1 : ℝ) else 0))
          = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (if p ∈ n.primeFactors then (1 : ℝ) else 0) := by
        apply Finset.sum_subset hsub
        intro p _ hp
        exact ite_eq_right hp
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      exact eif.trans esub
    have hA : (∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((n.primeFactors.card : ℕ) : ℝ))
        = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (((((Finset.Icc 1 N).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
            (fun n => p ∣ n)).card : ℕ) : ℝ) := by
      calc ∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              ((n.primeFactors.card : ℕ) : ℝ)
          = ∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              (if p ∈ n.primeFactors then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl (fun n hn => hterm n hn)
        _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              ∑ n ∈ (Finset.Icc 1 N).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (if p ∈ n.primeFactors then (1 : ℝ) else 0) :=
            Finset.sum_comm
        _ = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              (((((Finset.Icc 1 N).filter
                (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
                (fun n => p ∣ n)).card : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpp := hprimeP p hp
            have epred : ∀ n ∈ (Finset.Icc 1 N).filter
                (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
                (p ∈ n.primeFactors) = (p ∣ n) := by
              intro n hn
              apply propext
              constructor
              · exact Nat.dvd_of_mem_primeFactors
              · intro hdvd
                exact hpp.mem_primeFactors hdvd (hn0 n hn)
            have efil : (∑ n ∈ (Finset.Icc 1 N).filter
                  (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
                  (if p ∈ n.primeFactors then (1 : ℝ) else 0))
                = ∑ n ∈ (Finset.Icc 1 N).filter
                  (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
                  (if p ∣ n then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              simp only [epred n hn]
            rw [efil, Finset.sum_boole]
    have hfloor : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ⌊x / (p : ℝ)⌋₊ = N / p := by
      intro p _
      rw [Nat.floor_div_natCast]
    have hQ : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ)
        = (((((Finset.Icc 1 (N / p)).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ) := by
      intro p hp
      rw [hfloor p hp]
    have hcard_eq : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ((((Finset.Icc 1 N).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
          (fun n => p ∣ n)).card)
        = (((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h)).card) := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : 0 < p := hpp.pos
      symm
      apply Finset.card_nbij' (fun m => p * m) (fun n => n / p)
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨hm1, hm2⟩, hfree⟩ := hm
        apply Finset.mem_coe.mpr
        simp only [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨⟨?_, ?_⟩, hfree⟩, dvd_mul_right p m⟩
        · have hp2 : 2 ≤ p := hpp.two_le
          calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
            _ ≤ p * m := Nat.mul_le_mul (by omega : (1 : ℕ) ≤ p) hm1
        · calc p * m ≤ p * (N / p) := Nat.mul_le_mul (le_refl p) hm2
            _ ≤ N := Nat.mul_div_le N p
      · intro n hn
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨⟨hn1, hn2⟩, hfreeN⟩, hdvd⟩ := hn
        obtain ⟨k, rfl⟩ := hdvd
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · rw [h, mul_zero] at hn1
            omega
          · exact h
        have hkN : k ≤ N / p := by
          rw [Nat.le_div_iff_mul_le hp0, mul_comm]
          exact hn2
        have hkk2 : p * k / p = k := Nat.mul_div_cancel_left k hp0
        have hmem : p * k / p ∈ ((Finset.Icc 1 (N / p)).filter
          (fun (m : ℕ) => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h)) := by
          rw [hkk2]
          simp only [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hk1, hkN⟩, hfreeN⟩
        exact Finset.mem_coe.mpr hmem
      · intro m _
        change (p * m) / p = m
        exact Nat.mul_div_cancel_left m hp0
      · intro n hn
        simp only [Finset.mem_coe, Finset.mem_filter] at hn
        obtain ⟨-, hdvd⟩ := hn
        change p * (n / p) = n
        exact Nat.mul_div_cancel' hdvd
    have hDsub : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h))
        ⊆ ((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ m.primeFactors, m.factorization q < h)) := by
      intro p hp m hm
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : 0 < p := hpp.pos
      obtain ⟨hmIcc, hfree⟩ := Finset.mem_filter.mp hm
      have hm0 : m ≠ 0 := by
        have hm1 : (1 : ℕ) ≤ m := (Finset.mem_Icc.mp hmIcc).1
        omega
      have hpm0 : p * m ≠ 0 := mul_ne_zero (ne_of_gt hp0) hm0
      apply Finset.mem_filter.mpr
      refine ⟨hmIcc, fun q hq => ?_⟩
      have hqmem : q ∈ (p * m).primeFactors :=
        (Nat.prime_of_mem_primeFactors hq).mem_primeFactors
          (dvd_trans (Nat.dvd_of_mem_primeFactors hq) (dvd_mul_left m p)) hpm0
      have hlt := hfree q hqmem
      have hfac : (p * m).factorization q
          = p.factorization q + m.factorization q := by
        rw [Nat.factorization_mul (ne_of_gt hp0) hm0, Finsupp.add_apply]
      omega
    have hbad : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∀ m ∈ (((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ m.primeFactors, m.factorization q < h))
          \ ((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h))),
        p ^ (h - 1) ∣ m := by
      intro p hp m hm
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : 0 < p := hpp.pos
      rw [Finset.mem_sdiff] at hm
      obtain ⟨hmH2, hmDn⟩ := hm
      obtain ⟨hmIcc, hfreeM⟩ := Finset.mem_filter.mp hmH2
      have hm0 : m ≠ 0 := by
        have hm1 : (1 : ℕ) ≤ m := (Finset.mem_Icc.mp hmIcc).1
        omega
      have hpm0 : p * m ≠ 0 := mul_ne_zero (ne_of_gt hp0) hm0
      have hnot : ¬ ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h := by
        intro hall
        exact hmDn (Finset.mem_filter.mpr ⟨hmIcc, hall⟩)
      obtain ⟨q, hqmem, hqle⟩ : ∃ q ∈ (p * m).primeFactors,
          h ≤ (p * m).factorization q := by
        by_contra hcon
        apply hnot
        intro q hqmem
        by_contra hle
        exact hcon ⟨q, hqmem, le_of_not_gt hle⟩
      have hpf : (p * m).primeFactors = {p} ∪ m.primeFactors := by
        rw [Nat.primeFactors_mul (ne_of_gt hp0) hm0, hpp.primeFactors]
      have hqp : q = p := by
        rw [hpf, Finset.mem_union, Finset.mem_singleton] at hqmem
        rcases hqmem with hqp | hqM
        · exact hqp
        · by_cases hqp2 : q = p
          · exact hqp2
          · exfalso
            have hltM := hfreeM q hqM
            have hfac : (p * m).factorization q
                = p.factorization q + m.factorization q := by
              rw [Nat.factorization_mul (ne_of_gt hp0) hm0, Finsupp.add_apply]
            have hpq0 : p.factorization q = 0 := by
              by_contra hcon
              have hsup : q ∈ p.factorization.support :=
                Finsupp.mem_support_iff.mpr hcon
              have hmem : q ∈ p.primeFactors := by
                rwa [Nat.support_factorization] at hsup
              rw [hpp.primeFactors, Finset.mem_singleton] at hmem
              exact hqp2 hmem
            omega
      rw [hqp] at hqle
      have hfacp : (p * m).factorization p = m.factorization p + 1 := by
        have hfac : (p * m).factorization p
            = p.factorization p + m.factorization p := by
          rw [Nat.factorization_mul (ne_of_gt hp0) hm0, Finsupp.add_apply]
        rw [hfac, hpp.factorization_self, add_comm]
      have hMp : m.factorization p = h - 1 := by
        by_cases hmem : p ∈ m.primeFactors
        · have hlt := hfreeM p hmem
          omega
        · have h0 : m.factorization p = 0 := by
            have hsup : p ∉ m.factorization.support := by
              rw [Nat.support_factorization]
              exact hmem
            exact Finsupp.notMem_support_iff.mp hsup
          omega
      exact (hpp.pow_dvd_iff_le_factorization hm0).mpr (by omega)
    have hcard_le : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ((((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ m.primeFactors, m.factorization q < h))
          \ ((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h))).card)
        ≤ (N / p) / p ^ (h - 1) := by
      intro p hp
      calc ((((Finset.Icc 1 (N / p)).filter
            (fun m => ∀ q ∈ m.primeFactors, m.factorization q < h))
            \ ((Finset.Icc 1 (N / p)).filter
            (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h))).card)
          ≤ ((((Finset.Icc 1 (N / p)).filter (fun m => p ^ (h - 1) ∣ m)).card)) := by
            apply Finset.card_le_card
            intro m hm
            have hdvd := hbad p hp m hm
            have hmIcc : m ∈ Finset.Icc 1 (N / p) :=
              Finset.mem_of_subset (Finset.filter_subset _ _)
                (Finset.mem_of_subset Finset.sdiff_subset hm)
            exact Finset.mem_filter.mpr ⟨hmIcc, hdvd⟩
        _ = ((N / p) / p ^ (h - 1)) := by
            rw [Icc_one_eq_Ioc_zero]
            exact Nat.Ioc_filter_dvd_card_eq_div _ _
    have hreal : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (((N / p) / p ^ (h - 1) : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hpR1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
      have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hph : (p : ℝ) * (p : ℝ) ^ (h - 1) = (p : ℝ) ^ h := by
        conv_rhs => rw [show h = (h - 1) + 1 from by omega, pow_succ']
      have h5 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ h := pow_le_pow_right₀ hpR1 hh
      have e1 : (((N / p) / p ^ (h - 1) : ℕ) : ℝ)
          ≤ ((N / p : ℕ) : ℝ) / (((p ^ (h - 1) : ℕ) : ℝ)) :=
        Nat.cast_div_le
      have e2 : (((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ)) := Nat.cast_div_le
      have e3 : (((p ^ (h - 1) : ℕ) : ℝ) = (p : ℝ) ^ (h - 1)) :=
        Nat.cast_pow p (h - 1)
      have epos : (0 : ℝ) < (p : ℝ) ^ (h - 1) := pow_pos hpR _
      have e4 : (((N / p : ℕ) : ℝ) / (((p ^ (h - 1) : ℕ) : ℝ)))
          ≤ (((N : ℝ) / (p : ℝ)) / (p : ℝ) ^ (h - 1)) := by
        rw [e3]
        exact div_le_div_of_nonneg_right e2 (le_of_lt epos)
      have e5 : ((((N : ℝ) / (p : ℝ)) / (p : ℝ) ^ (h - 1)) = (N : ℝ) / (p : ℝ) ^ h) := by
        rw [div_div, hph]
      have e6 : ((N : ℝ) / (p : ℝ) ^ h ≤ (N : ℝ) / (p : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hNR (pow_pos hpR 2) h5
      calc (((N / p) / p ^ (h - 1) : ℕ) : ℝ)
          ≤ (((N / p : ℕ) : ℝ) / (((p ^ (h - 1) : ℕ) : ℝ))) := e1
        _ ≤ ((((N : ℝ) / (p : ℝ)) / (p : ℝ) ^ (h - 1))) := e4
        _ = ((N : ℝ) / (p : ℝ) ^ h) := e5
        _ ≤ ((N : ℝ) / (p : ℝ) ^ 2) := e6
    have hgap : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (((((Finset.Icc 1 (N / p)).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ)
        - ((((((Finset.Icc 1 N).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
          (fun n => p ∣ n)).card : ℕ)) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := by
      intro p hp
      have hCC : ((((((Finset.Icc 1 N).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
          (fun n => p ∣ n)).card : ℕ)) : ℝ)
          = (((((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h)).card
            : ℕ)) : ℝ) := by
        rw [hcard_eq p hp]
      have hsd : (((((Finset.Icc 1 (N / p)).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ)
          - (((((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h)).card
            : ℕ)) : ℝ)
          = (((((((Finset.Icc 1 (N / p)).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h))
          \ ((Finset.Icc 1 (N / p)).filter
          (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h))).card
            : ℕ)) : ℝ)) := by
        rw [Finset.card_sdiff_of_subset (hDsub p hp),
          Nat.cast_sub (Finset.card_le_card (hDsub p hp))]
      rw [hCC, hsd]
      calc (((((((Finset.Icc 1 (N / p)).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h))
            \ ((Finset.Icc 1 (N / p)).filter
            (fun m => ∀ q ∈ (p * m).primeFactors, (p * m).factorization q < h))).card
              : ℕ)) : ℝ))
          ≤ (((((N / p) / p ^ (h - 1) : ℕ))) : ℝ) :=
            Nat.cast_le.mpr (hcard_le p hp)
        _ ≤ ((N : ℝ) / (p : ℝ) ^ 2) := hreal p hp
    have hsq1 : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 :=
      sum_inv_sq_primes_le_one N hN1
    constructor
    · rw [hA]
      apply Finset.sum_le_sum
      intro p hp
      rw [hQ p hp, hcard_eq p hp]
      exact Nat.cast_le.mpr (Finset.card_le_card (hDsub p hp))
    · have hBB : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ))
          - (∑ n ∈ (Finset.Icc 1 N).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((n.primeFactors.card : ℕ) : ℝ))
          = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ((((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ)
            - ((((((Finset.Icc 1 N).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
              (fun n => p ∣ n)).card : ℕ)) : ℝ)) := by
        rw [hA, ← Finset.sum_sub_distrib]
      rw [hBB]
      calc ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
              ((((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ)) : ℝ)
              - ((((((Finset.Icc 1 N).filter
                (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h)).filter
                (fun n => p ∣ n)).card : ℕ)) : ℝ))
          ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((N : ℝ) / (p : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            rw [hQ p hp]
            exact hgap p hp
        _ = (N : ℝ) * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ((1 : ℝ) / (p : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            rw [div_eq_mul_one_div]
        _ ≤ (N : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hsq1 (Nat.cast_nonneg N)
        _ = (N : ℝ) := mul_one _
        _ ≤ x := hNx

/--
**Average number of prime factors of h-free integers.** Let $h \ge 2$ be an integer. Call a
positive integer $n$ $h$-free if every prime occurs in the factorization of $n$ with exponent less
than $h$, and write $\Omega(n)$ for the number of prime factors of $n$ counted with multiplicity
and $\zeta$ for the Riemann zeta function. Then, as the real number $x$ tends to infinity,
$$
\sum_{\substack{1 \le n \le x \\ n \ h\text{-free}}} \Omega(n)
= \frac{x \log\log x}{\zeta(h)} + O(x).
$$

Proves `Wanted` entry `average_cardFactors_over_h_free`.

Source: Rafael Jakimczuk and Matilde Lalín, "The Number of Prime Factors on
Average in Certain Integer Sequences," Journal of Integer Sequences 25 (2022),
Article 22.2.3, Theorem (label `thmhfree`), lines 110–117,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Lalin/lalin2.tex
-/
theorem average_cardFactors_over_h_free
    (h : ℕ) (hh : 2 ≤ h) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ =>
        (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (ArithmeticFunction.cardFactors n : ℝ)) -
          (1 / (riemannZeta (h : ℂ)).re) * x * Real.log (Real.log x))
      (fun x : ℝ => x) := by
  obtain ⟨C6, hC6⟩ := abs_sum_prime_inv_sub_loglog_le
  have hZ1 : (1 : ℝ) ≤ (riemannZeta (h : ℂ)).re :=
    one_le_riemannZeta_natCast_re h hh
  have hZpos : (0 : ℝ) < (riemannZeta (h : ℂ)).re :=
    lt_of_lt_of_le (by norm_num) hZ1
  have hZinv_le : (1 : ℝ) / (riemannZeta (h : ℂ)).re ≤ 1 := by
    rw [div_le_one hZpos]
    exact hZ1
  refine Asymptotics.IsBigO.of_bound ((h : ℝ) + 7 + |C6|) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hN13 := sum_cardFactors_sub_card_primeFactors_hfree_le h ⌊x⌋₊ hh
  have hN12 := sum_card_primeFactors_hfree_double_count h hh x hx0
  have hN14 := abs_sum_prime_card_hfree_sub_main_le h hh x hx1
  have hN6 := hC6 x hx
  have hSA : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
      = (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (ArithmeticFunction.cardFactors n : ℝ))
        - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (n.primeFactors.card : ℝ)) := by
    rw [Finset.sum_sub_distrib]
  have hE1nn : (0 : ℝ) ≤ (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ))) :=
    hN13.1
  have hE1le : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
      ≤ ((h : ℝ) - 2) * (⌊x⌋₊ : ℝ) :=
    hN13.2
  have hAleB : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      (n.primeFactors.card : ℝ))
      ≤ (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ)) :=
    hN12.1
  have hE2le : (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
        ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
          (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
      - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (n.primeFactors.card : ℝ)) ≤ x :=
    hN12.2
  have hE2nn : (0 : ℝ) ≤ (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
        (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
      - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      (n.primeFactors.card : ℝ)) :=
    sub_nonneg.mpr hAleB
  have hE3 : |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
        (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
      - (x / (riemannZeta (h : ℂ)).re)
        * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))|
      ≤ 8 * x :=
    hN14
  have hE4 : |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      - Real.log (Real.log x)| ≤ C6 :=
    hN6
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hhR : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hE1x : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
      ≤ ((h : ℝ) - 2) * x :=
    le_trans hE1le (mul_le_mul_of_nonneg_left hNx (by linarith))
  have hbd1 : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))|
      ≤ ((h : ℝ) - 2) * x := by
    rw [abs_of_nonneg hE1nn]
    exact hE1x
  have hbd2 : |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
        (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
      - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
      (n.primeFactors.card : ℝ))| ≤ x := by
    rw [abs_of_nonneg hE2nn]
    exact hE2le
  have hZdiv_nn : (0 : ℝ) ≤ x / (riemannZeta (h : ℂ)).re :=
    div_nonneg hx0 (le_of_lt hZpos)
  have hbd4 : |(x / (riemannZeta (h : ℂ)).re)
      * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        - Real.log (Real.log x))| ≤ |C6| * x := by
    have eabs : |(x / (riemannZeta (h : ℂ)).re)
        * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          - Real.log (Real.log x))|
        = (x / (riemannZeta (h : ℂ)).re)
          * |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            - Real.log (Real.log x)| := by
      rw [abs_mul, abs_of_nonneg hZdiv_nn]
    have ele : |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        - Real.log (Real.log x)| ≤ |C6| :=
      le_trans hE4 (le_abs_self C6)
    have hle : (x / (riemannZeta (h : ℂ)).re)
        * |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          - Real.log (Real.log x)|
        ≤ (x / (riemannZeta (h : ℂ)).re) * |C6| :=
      mul_le_mul_of_nonneg_left ele hZdiv_nn
    have hxZ : x / (riemannZeta (h : ℂ)).re ≤ x := by
      calc x / (riemannZeta (h : ℂ)).re
          = x * (1 / (riemannZeta (h : ℂ)).re) := by ring
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hZinv_le hx0
        _ = x := mul_one x
    have hfin : (x / (riemannZeta (h : ℂ)).re) * |C6| ≤ |C6| * x := by
      calc (x / (riemannZeta (h : ℂ)).re) * |C6|
          = |C6| * (x / (riemannZeta (h : ℂ)).re) := mul_comm _ _
        _ ≤ |C6| * x := mul_le_mul_of_nonneg_left hxZ (abs_nonneg _)
    rw [eabs]
    exact le_trans hle hfin
  have hdecomp : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (ArithmeticFunction.cardFactors n : ℝ))
        - (1 / (riemannZeta (h : ℂ)).re) * x * Real.log (Real.log x)
      = (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
        - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
          - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          (n.primeFactors.card : ℝ)))
        + ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
          ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
            (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
          - (x / (riemannZeta (h : ℂ)).re)
            * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))
        + ((x / (riemannZeta (h : ℂ)).re)
          * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            - Real.log (Real.log x))) := by
    rw [hSA]
    ring
  have hexpand : ((h : ℝ) + 7 + |C6|) * x
      = ((h : ℝ) - 2) * x + x + 8 * x + |C6| * x := by ring
  have htot : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (ArithmeticFunction.cardFactors n : ℝ))
        - (1 / (riemannZeta (h : ℂ)).re) * x * Real.log (Real.log x)|
      ≤ ((h : ℝ) + 7 + |C6|) * x := by
    have g1 : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
          - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (n.primeFactors.card : ℝ)))|
        ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))|
          + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (n.primeFactors.card : ℝ))| :=
      abs_sub _ _
    have g2 : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
          - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (n.primeFactors.card : ℝ)))
          + ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (x / (riemannZeta (h : ℂ)).re)
              * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))|
        ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))|
          + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (n.primeFactors.card : ℝ))|
          + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (x / (riemannZeta (h : ℂ)).re)
              * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))| := by
      calc |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
            - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (n.primeFactors.card : ℝ)))
            + ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (x / (riemannZeta (h : ℂ)).re)
                * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))|
          ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
            - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (n.primeFactors.card : ℝ)))|
            + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (x / (riemannZeta (h : ℂ)).re)
                * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))| :=
            abs_add_le _ _
        _ ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))|
            + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (n.primeFactors.card : ℝ))|
            + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (x / (riemannZeta (h : ℂ)).re)
                * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))| :=
            by linarith [g1]
    have g3 : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
          - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (n.primeFactors.card : ℝ)))
          + ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (x / (riemannZeta (h : ℂ)).re)
              * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))
          + ((x / (riemannZeta (h : ℂ)).re)
            * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
              - Real.log (Real.log x)))|
        ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
          ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))|
          + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            (n.primeFactors.card : ℝ))|
          + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
            ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
              (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
            - (x / (riemannZeta (h : ℂ)).re)
              * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))|
          + |(x / (riemannZeta (h : ℂ)).re)
            * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
              - Real.log (Real.log x))| := by
      calc |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
            - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (n.primeFactors.card : ℝ)))
            + ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (x / (riemannZeta (h : ℂ)).re)
                * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))
            + ((x / (riemannZeta (h : ℂ)).re)
              * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                - Real.log (Real.log x)))|
          ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))
            - ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (n.primeFactors.card : ℝ)))
            + ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (x / (riemannZeta (h : ℂ)).re)
                * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))|
            + |(x / (riemannZeta (h : ℂ)).re)
              * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                - Real.log (Real.log x))| :=
            abs_add_le _ _
        _ ≤ |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
            ((ArithmeticFunction.cardFactors n : ℝ) - (n.primeFactors.card : ℝ)))|
            + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
              (n.primeFactors.card : ℝ))|
            + |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ((((Finset.Icc 1 ⌊x / (p : ℝ)⌋₊).filter
                (fun n => ∀ q ∈ n.primeFactors, n.factorization q < h)).card : ℕ) : ℝ))
              - (x / (riemannZeta (h : ℂ)).re)
                * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))|
            + |(x / (riemannZeta (h : ℂ)).re)
              * ((∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
                - Real.log (Real.log x))| :=
            by linarith [g2]
    rw [hdecomp, hexpand]
    linarith [g3, hbd1, hbd2, hE3, hbd4]
  have hnorm : ‖(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, n.factorization p < h),
        (ArithmeticFunction.cardFactors n : ℝ))
        - (1 / (riemannZeta (h : ℂ)).re) * x * Real.log (Real.log x)‖
      ≤ ((h : ℝ) + 7 + |C6|) * ‖x‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact htot
  exact hnorm

end MetaMathlibExt
end

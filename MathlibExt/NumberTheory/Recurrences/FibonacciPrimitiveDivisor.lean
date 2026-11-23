/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.PrimitiveDivisor
public import Mathlib.Data.Nat.Fib.Basic
import MathlibExt.NumberTheory.Padics.FibonomialPrimePowerValuation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- N1(a): Möbius-weighted divisor sum of the identity equals the totient. -/
private theorem moebiusTotient_antidiagonal (n : ℕ) (hn : 1 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * (x.2 : ℤ) = (Nat.totient n : ℤ) := by
  have hbase : ∀ (m : ℕ), 0 < m → ∑ i ∈ m.divisors, (Nat.totient i : ℤ) = (m : ℤ) := by
    intro m _
    have h := congrArg (Nat.cast : ℕ → ℤ) (Nat.sum_totient m)
    simpa using h
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun i => (Nat.totient i : ℤ)) (g := fun i => (i : ℤ))).mp hbase n hn
  simpa using h

/-- N1(b): Möbius sum over an antidiagonal is the unit indicator. -/
private theorem moebiusUnit_antidiagonal (n : ℕ) (hn : 1 ≤ n) :
    ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) =
      (if n = 1 then (1 : ℤ) else 0) := by
  have hfun := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hfun
  have hz : ∀ x ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 = 1 := by
    intro x hx
    have hmem := Nat.mem_divisorsAntidiagonal.mp hx
    have hx2 : x.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmem
      omega
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hx2,
      Nat.cast_one]
  have h2 : (∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2)
      = ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hz x hx, mul_one]
  rw [h2] at hfun
  simpa using hfun

/-- N2: Möbius sum of a gcd-closed, up-closed predicate indicator. -/
private theorem moebiusIte_gcdClosed (n : ℕ) (hn : 1 ≤ n) (P : ℕ → Prop)
    [DecidablePred P]
    (hgcd : ∀ a b, P a → P b → P (Nat.gcd a b))
    (hup : ∀ a b, P a → a ∣ b → P b) :
    ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (if P x.2 then (1 : ℤ) else 0)
      = (if (P n ∧ ∀ d ∈ n.divisors, d < n → ¬ P d) then (1 : ℤ) else 0) := by
  have hSTEP : (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (if P x.2 then (1 : ℤ) else 0))
      = (∑ b ∈ n.divisors,
        (ArithmeticFunction.moebius (n / b) : ℤ) * (if P b then (1 : ℤ) else 0)) :=
    Nat.sum_divisorsAntidiagonal'
      (fun a b => (ArithmeticFunction.moebius a : ℤ) * (if P b then (1 : ℤ) else 0))
      (n := n)
  rw [hSTEP]
  by_cases hno : ∀ d ∈ n.divisors, ¬ P d
  · have hPn : ¬ P n := hno n (Nat.mem_divisors_self n (by omega))
    have hc0 : ¬ (P n ∧ ∀ d ∈ n.divisors, d < n → ¬ P d) := fun h => hPn h.1
    rw [ite_eq_right hc0]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [ite_eq_right (hno b hb), mul_zero]
  · have hex2 : ∃ d ∈ n.divisors, P d := by
      by_contra hc
      exact hno (fun d hd hPd => hc ⟨d, hd, hPd⟩)
    obtain ⟨d0, hd0mem, hd0P⟩ := hex2
    have hex : ∃ d, d ∣ n ∧ P d := ⟨d0, (Nat.mem_divisors.mp hd0mem).1, hd0P⟩
    set r := Nat.find hex with hr_def
    have hrP : P r := (Nat.find_spec hex).2
    have hrn : r ∣ n := (Nat.find_spec hex).1
    have hrne : r ≠ 0 := by
      intro hr0
      rw [hr0] at hrn
      simp only [zero_dvd_iff] at hrn
      omega
    have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
    have hnrpos : 0 < n / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrn) hrpos
    have hkey : ∀ d, d ∣ n → (P d ↔ r ∣ d) := by
      intro d hdn
      constructor
      · intro hPd
        have hdpos : 0 < d := by
          rcases Nat.eq_zero_or_pos d with rfl | h
          · exfalso
            simp only [zero_dvd_iff] at hdn
            omega
          · exact h
        have hg : P (Nat.gcd r d) := hgcd r d hrP hPd
        have hgdvd : Nat.gcd r d ∣ n := (Nat.gcd_dvd_right r d).trans hdn
        have hle : r ≤ Nat.gcd r d := Nat.find_min' hex ⟨hgdvd, hg⟩
        have hge : Nat.gcd r d ≤ r := Nat.le_of_dvd hrpos (Nat.gcd_dvd_left r d)
        have heq : Nat.gcd r d = r := le_antisymm hge hle
        rw [← heq]
        exact Nat.gcd_dvd_right r d
      · intro hrd
        obtain ⟨c, rfl⟩ := hrd
        exact hup r (r * c) hrP (dvd_mul_right r c)
    have hterm : ∀ b ∈ n.divisors,
        (ArithmeticFunction.moebius (n / b) : ℤ) * (if P b then (1 : ℤ) else 0)
          = (ArithmeticFunction.moebius (n / b) : ℤ) *
            (if r ∣ b then (1 : ℤ) else 0) := by
      intro b hb
      have hbd : b ∣ n := (Nat.mem_divisors.mp hb).1
      by_cases hPb : P b
      · have hrb : r ∣ b := (hkey b hbd).mp hPb
        rw [ite_eq_left hPb, ite_eq_left hrb]
      · have hrb : ¬ r ∣ b := fun h => hPb ((hkey b hbd).mpr h)
        rw [ite_eq_right hPb, ite_eq_right hrb]
    trans ∑ b ∈ n.divisors, (ArithmeticFunction.moebius (n / b) : ℤ) *
      (if r ∣ b then (1 : ℤ) else 0)
    · exact Finset.sum_congr rfl hterm
    have hite : ∀ b : ℕ,
        (ArithmeticFunction.moebius (n / b) : ℤ) * (if r ∣ b then (1 : ℤ) else 0)
          = (if r ∣ b then (ArithmeticFunction.moebius (n / b) : ℤ) else 0) := by
      intro b
      by_cases h : r ∣ b <;> simp [h]
    trans ∑ b ∈ n.divisors, (if r ∣ b then
      (ArithmeticFunction.moebius (n / b) : ℤ) else 0)
    · exact Finset.sum_congr rfl (fun b _ => hite b)
    rw [← Finset.sum_filter]
    have hdiv_iff : ∀ e : ℕ, (e ∣ n / r ↔ r * e ∣ n) :=
      fun e => Nat.dvd_div_iff_mul_dvd hrn
    have himage : n.divisors.filter (fun b => r ∣ b)
        = (n / r).divisors.image (fun e => r * e) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hbn, -⟩, hrb⟩
        obtain ⟨e, rfl⟩ := hrb
        exact ⟨e, ⟨(hdiv_iff e).mpr hbn, ne_of_gt hnrpos⟩, rfl⟩
      · rintro ⟨e, ⟨hem, -⟩, rfl⟩
        exact ⟨⟨(hdiv_iff e).mp hem, ne_of_gt (by omega : 0 < n)⟩,
          dvd_mul_right r e⟩
    have hinj : ∀ e1 ∈ (n / r).divisors, ∀ e2 ∈ (n / r).divisors,
        r * e1 = r * e2 → e1 = e2 := by
      intro e1 _ e2 _ h
      exact mul_left_cancel₀ hrne h
    rw [himage, Finset.sum_image hinj]
    have hdiv2 : ∀ e ∈ (n / r).divisors, n / (r * e) = (n / r) / e := by
      intro e _
      exact (Nat.div_div_eq_div_mul n r e).symm
    have hsum : (∑ e ∈ (n / r).divisors,
          (ArithmeticFunction.moebius (n / (r * e)) : ℤ))
        = (∑ e ∈ (n / r).divisors,
          (ArithmeticFunction.moebius ((n / r) / e) : ℤ)) := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hdiv2 e he]
    rw [hsum]
    have hrev : (∑ y ∈ (n / r).divisorsAntidiagonal,
          (ArithmeticFunction.moebius y.1 : ℤ))
        = (∑ i ∈ (n / r).divisors,
          (ArithmeticFunction.moebius ((n / r) / i) : ℤ)) :=
      Nat.sum_divisorsAntidiagonal'
        (fun a _ => (ArithmeticFunction.moebius a : ℤ)) (n := n / r)
    have hN1 := moebiusUnit_antidiagonal (n / r) hnrpos
    have hrcond : (r = n) ↔ (P n ∧ ∀ d ∈ n.divisors, d < n → ¬ P d) := by
      constructor
      · intro h
        refine ⟨by rw [← h]; exact hrP, fun d hd hdn hPd => ?_⟩
        have hbd : d ∣ n := (Nat.mem_divisors.mp hd).1
        have hdpos : 0 < d := by
          rcases Nat.eq_zero_or_pos d with rfl | hh
          · exfalso
            simp only [zero_dvd_iff] at hbd
            omega
          · exact hh
        have hle : r ≤ d := Nat.le_of_dvd hdpos ((hkey d hbd).mp hPd)
        omega
      · intro h
        by_contra hne
        have hlt : r < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hrn) hne
        exact (h.2 r (Nat.mem_divisors.mpr ⟨hrn, by omega⟩) hlt) hrP
    have hrn1 : (n / r = 1) ↔ (r = n) := by
      constructor
      · intro h
        have h2 := Nat.div_mul_cancel hrn
        rw [h, one_mul] at h2
        exact h2
      · intro h
        rw [h]
        exact Nat.div_self (by omega)
    rw [← hrev, hN1]
    by_cases h1 : n / r = 1
    · have hc : (P n ∧ ∀ d ∈ n.divisors, d < n → ¬ P d) := hrcond.mp (hrn1.mp h1)
      rw [ite_eq_left h1, ite_eq_left hc]
    · have hc : ¬ (P n ∧ ∀ d ∈ n.divisors, d < n → ¬ P d) :=
        fun h => h1 (hrn1.mpr (hrcond.mpr h))
      rw [ite_eq_right h1, ite_eq_right hc]

/-- N3 auxiliary: layer-cake formula for padic valuations. -/
private theorem padicVal_layerCake (p b K : ℕ) [Fact (Nat.Prime p)]
    (hb : Nat.fib b ≠ 0) (hK : padicValNat p (Nat.fib b) ≤ K) :
    (padicValNat p (Nat.fib b) : ℤ)
      = ∑ j ∈ Finset.range K, (if p ^ (j + 1) ∣ Nat.fib b then (1 : ℤ) else 0) := by
  have hfilter : (Finset.range K).filter (fun j => p ^ (j + 1) ∣ Nat.fib b)
      = Finset.range (padicValNat p (Nat.fib b)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      have hle : j + 1 ≤ padicValNat p (Nat.fib b) := (padicValNat_dvd_iff_le hb).mp h.2
      omega
    · intro h
      refine ⟨by omega, (padicValNat_dvd_iff_le hb).mpr (by omega)⟩
  rw [Finset.sum_boole, hfilter, Finset.card_range]

/-- N3 auxiliary: uniform bound v_p(F_b) ≤ F_n + 1 for b ∣ n. -/
private theorem padicVal_fib_le (n : ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (b : ℕ) (hbn : b ∣ n) (hn : 1 ≤ n) :
    padicValNat p (Nat.fib b) ≤ Nat.fib n + 1 := by
  have hpprime : p.Prime := Fact.out
  have hnpos : 0 < n := by omega
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · exfalso
      rw [zero_dvd_iff] at hbn
      omega
    · exact hpos
  have hFbpos : 0 < Nat.fib b := Nat.fib_pos.mpr hbpos
  have hle1 : p ^ padicValNat p (Nat.fib b) ≤ Nat.fib b :=
    Nat.le_of_dvd hFbpos pow_padicValNat_dvd
  have hlt : padicValNat p (Nat.fib b) < p ^ padicValNat p (Nat.fib b) :=
    Nat.lt_pow_self hpprime.one_lt
  have hle2 : Nat.fib b ≤ Nat.fib n := Nat.fib_mono (Nat.le_of_dvd hnpos hbn)
  omega

/-- N3: Möbius-weighted valuation sum bounded by the drop at a proper divisor. -/
private theorem moebiusVal_le (n : ℕ) (hn : 1 ≤ n) (p : ℕ) [Fact (Nat.Prime p)]
    (d : ℕ) (hd : d ∈ n.divisors) (hdn : d < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (padicValNat p (Nat.fib x.2) : ℤ)
      ≤ (padicValNat p (Nat.fib n) : ℤ) - (padicValNat p (Nat.fib d) : ℤ) := by
  have hdn' : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · exfalso
      rw [zero_dvd_iff] at hdn'
      omega
    · exact hpos
  have hFne_d : Nat.fib d ≠ 0 := (Nat.fib_pos.mpr hdpos).ne'
  have hFne_n : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr (by omega : 0 < n)).ne'
  have hFdn : Nat.fib d ∣ Nat.fib n := Nat.fib_dvd _ _ hdn'
  have hle : padicValNat p (Nat.fib d) ≤ padicValNat p (Nat.fib n) :=
    (padicValNat_dvd_iff_le hFne_n).mp (pow_padicValNat_dvd.trans hFdn)
  set K := Nat.fib n + 1 with hKdef
  have hx2pos : ∀ x ∈ n.divisorsAntidiagonal, 0 < x.2 := by
    intro x hx
    have hmem := Nat.mem_divisorsAntidiagonal.mp hx
    rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
    · exfalso
      rw [h0, mul_zero] at hmem
      omega
    · exact hpos
  have hne_b : ∀ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ≠ 0 := by
    intro x hx
    exact (Nat.fib_pos.mpr (hx2pos x hx)).ne'
  have hK : ∀ x ∈ n.divisorsAntidiagonal, padicValNat p (Nat.fib x.2) ≤ K := by
    intro x hx
    have hmem := Nat.mem_divisorsAntidiagonal.mp hx
    have hdvdx : x.2 ∣ n := by
      rw [← hmem.1]
      exact Nat.dvd_mul_left x.2 x.1
    exact padicVal_fib_le n p x.2 hdvdx hn
  have hPgcd : ∀ j a b, p ^ (j + 1) ∣ Nat.fib a → p ^ (j + 1) ∣ Nat.fib b →
      p ^ (j + 1) ∣ Nat.fib (Nat.gcd a b) := by
    intro j a b ha hb
    have h : p ^ (j + 1) ∣ Nat.gcd (Nat.fib a) (Nat.fib b) := Nat.dvd_gcd ha hb
    rwa [← Nat.fib_gcd] at h
  have hPup : ∀ j a b, p ^ (j + 1) ∣ Nat.fib a → a ∣ b → p ^ (j + 1) ∣ Nat.fib b := by
    intro j a b ha hab
    exact ha.trans (Nat.fib_dvd _ _ hab)
  have hN2 : ∀ j : ℕ, (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ)
          * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0))
      = (if (p ^ (j + 1) ∣ Nat.fib n)
          ∧ ∀ b ∈ n.divisors, b < n → ¬ p ^ (j + 1) ∣ Nat.fib b
        then (1 : ℤ) else 0) := by
    intro j
    exact moebiusIte_gcdClosed n hn (fun b => p ^ (j + 1) ∣ Nat.fib b) (hPgcd j) (hPup j)
  have hswap : (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (padicValNat p (Nat.fib x.2) : ℤ))
      = ∑ j ∈ Finset.range K, ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ)
          * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0) := by
    have h1 : ∀ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (padicValNat p (Nat.fib x.2) : ℤ)
          = ∑ j ∈ Finset.range K,
            (ArithmeticFunction.moebius x.1 : ℤ)
              * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0) := by
      intro x hx
      rw [padicVal_layerCake p x.2 K (hne_b x hx) (hK x hx), Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have hI01 : ∀ j ∈ Finset.range K,
      (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ)
          * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0))
      ≤ (if padicValNat p (Nat.fib d) ≤ j ∧ j < padicValNat p (Nat.fib n)
        then (1 : ℤ) else 0) := by
    intro j _
    by_cases hC : ((p ^ (j + 1) ∣ Nat.fib n)
      ∧ ∀ b ∈ n.divisors, b < n → ¬ p ^ (j + 1) ∣ Nat.fib b)
    · have hvd : padicValNat p (Nat.fib d) ≤ j := by
        have hnd : ¬ p ^ (j + 1) ∣ Nat.fib d := hC.2 d hd hdn
        rw [padicValNat_dvd_iff_le hFne_d] at hnd
        omega
      have hvn : j < padicValNat p (Nat.fib n) := by
        have h1 : j + 1 ≤ padicValNat p (Nat.fib n) :=
          (padicValNat_dvd_iff_le hFne_n).mp hC.1
        omega
      rw [hN2 j, ite_eq_left hC, ite_eq_left ⟨hvd, hvn⟩]
    · rw [hN2 j, ite_eq_right hC]
      split_ifs with hV
      · exact zero_le_one
      · exact le_refl _
  have hcard : (∑ j ∈ Finset.range K,
        (∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ)
            * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0)))
      ≤ ((Finset.Ico (padicValNat p (Nat.fib d))
        (padicValNat p (Nat.fib n))).card : ℤ) := by
    have hpt : ∀ j ∈ Finset.range K,
        (∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ)
            * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0))
        ≤ (if j ∈ Finset.Ico (padicValNat p (Nat.fib d))
          (padicValNat p (Nat.fib n)) then (1 : ℤ) else 0) := by
      intro j hj
      simpa [Finset.mem_Ico] using hI01 j hj
    calc (∑ j ∈ Finset.range K, (∑ x ∈ n.divisorsAntidiagonal,
            (ArithmeticFunction.moebius x.1 : ℤ)
              * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0)))
          ≤ ∑ j ∈ Finset.range K,
            (if j ∈ Finset.Ico (padicValNat p (Nat.fib d))
              (padicValNat p (Nat.fib n)) then (1 : ℤ) else 0) :=
            Finset.sum_le_sum hpt
      _ = (((Finset.range K).filter
          (· ∈ Finset.Ico (padicValNat p (Nat.fib d))
            (padicValNat p (Nat.fib n)))).card : ℤ) := by
          rw [Finset.sum_boole]
      _ ≤ ((Finset.Ico (padicValNat p (Nat.fib d))
          (padicValNat p (Nat.fib n))).card : ℤ) := by
          norm_cast
          apply Finset.card_le_card
          intro j hj
          exact (Finset.mem_filter.mp hj).2
  have hfinal : ((Finset.Ico (padicValNat p (Nat.fib d))
      (padicValNat p (Nat.fib n))).card : ℤ)
      = (padicValNat p (Nat.fib n) : ℤ) - (padicValNat p (Nat.fib d) : ℤ) := by
    rw [Nat.card_Ico, Nat.cast_sub hle]
  calc (∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ)
            * (padicValNat p (Nat.fib x.2) : ℤ))
      = ∑ j ∈ Finset.range K, ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ)
          * (if p ^ (j + 1) ∣ Nat.fib x.2 then (1 : ℤ) else 0) := hswap
    _ ≤ ((Finset.Ico (padicValNat p (Nat.fib d))
        (padicValNat p (Nat.fib n))).card : ℤ) := hcard
    _ = (padicValNat p (Nat.fib n) : ℤ) - (padicValNat p (Nat.fib d) : ℤ) := hfinal


/-- N4 auxiliary: odd-index Fibonacci numbers are 1 or 2 mod 4. -/
private theorem fibOdd_modFour : ∀ n : ℕ, Odd n → Nat.fib n % 4 = 1 ∨ Nat.fib n % 4 = 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ k ihk =>
    intro hodd
    by_cases hk6 : 6 ≤ k
    · have hsub : k - 6 < k := by omega
      have hjodd : Odd (k - 6) := by
        obtain ⟨t, rfl⟩ := hodd
        have ht3 : 3 ≤ t := by omega
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
        have he : 2 * (s + 3) + 1 - 6 = 2 * s + 1 := by omega
        rw [he]
        exact ⟨s, rfl⟩
      have hIH := ihk (k - 6) hsub hjodd
      have hfib : Nat.fib k = Nat.fib (k - 6) * 5 + Nat.fib (k - 6 + 1) * 8 := by
        have h := Nat.fib_add (k - 6) 5
        have e1 : k - 6 + 5 + 1 = k := by omega
        rw [e1] at h
        have h5 : Nat.fib 5 = 5 := by decide
        have h6 : Nat.fib (5 + 1) = 8 := by decide
        rw [h5, h6] at h
        exact h
      have hmod : Nat.fib k % 4 = Nat.fib (k - 6) % 4 := by omega
      rcases hIH with h1 | h2
      · rw [hmod]; exact Or.inl h1
      · rw [hmod]; exact Or.inr h2
    · have hk5 : k ≤ 5 := by omega
      interval_cases k
      all_goals revert hodd
      all_goals decide

/-- N4(a): the 2-adic valuation at odd index is at most 1. -/
private theorem twoAdic_fib_odd (n : ℕ) (hodd : Odd n) :
    padicValNat 2 (Nat.fib n) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 0 < n := by
    obtain ⟨t, rfl⟩ := hodd
    omega
  have hne : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr hn).ne'
  have hmod := fibOdd_modFour n hodd
  have hnot : ¬ (2 ^ 2 ∣ Nat.fib n) := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    omega
  rw [padicValNat_dvd_iff_le hne (p := 2) (n := 2)] at hnot
  omega

/-- N4 auxiliary: the doubling bracket is never 0 mod 8. -/
private theorem bracket_modEight_ne : ∀ m : ℕ, 1 ≤ m →
    (2 * Nat.fib (m + 1) - Nat.fib m) % 8 ≠ 0 := by
  have hF12 : ∀ k, Nat.fib (k + 12) = 89 * Nat.fib k + 144 * Nat.fib (k + 1) := by
    intro k
    have h := Nat.fib_add k 11
    have e : k + 11 + 1 = k + 12 := by omega
    rw [e] at h
    have h11 : Nat.fib 11 = 89 := by decide
    have h12 : Nat.fib (11 + 1) = 144 := by decide
    rw [h11, h12] at h
    linear_combination h
  intro m
  induction m using Nat.strong_induction_on with
  | _ k ihk =>
    intro hk
    by_cases hk13 : 13 ≤ k
    · have hsub : k - 12 < k := by omega
      have hk1 : 1 ≤ k - 12 := by omega
      have e1 : Nat.fib k = 89 * Nat.fib (k - 12) + 144 * Nat.fib (k - 12 + 1) := by
        have h := hF12 (k - 12)
        rw [show k - 12 + 12 = k from by omega] at h
        exact h
      have e2 : Nat.fib (k + 1)
          = 89 * Nat.fib (k - 12 + 1) + 144 * Nat.fib (k - 12 + 2) := by
        have h := hF12 (k - 12 + 1)
        rw [show k - 12 + 1 + 12 = k + 1 from by omega,
          show k - 12 + 1 + 1 = k - 12 + 2 from by omega] at h
        exact h
      have h1 : Nat.fib (k - 12) ≤ 2 * Nat.fib (k - 12 + 1) := by
        have hmono := Nat.fib_le_fib_succ (n := k - 12)
        omega
      have h2 : Nat.fib k ≤ 2 * Nat.fib (k + 1) := by
        have hmono := Nat.fib_le_fib_succ (n := k)
        omega
      have hmod : (2 * Nat.fib (k + 1) - Nat.fib k) % 8
          = (2 * Nat.fib (k - 12 + 1) - Nat.fib (k - 12)) % 8 := by
        set K1 := Nat.fib (k + 1) with hK1
        set K := Nat.fib k with hK
        set B := Nat.fib (k - 12 + 1) with hB
        set A := Nat.fib (k - 12) with hA
        set C := Nat.fib (k - 12 + 2) with hC
        omega
      have hIH := ihk (k - 12) hsub hk1
      rw [hmod]
      exact hIH
    · have hk12 : k ≤ 12 := by omega
      interval_cases k
      all_goals decide

/-- N4(b): doubling adds at most 2 to the 2-adic valuation. -/
private theorem twoAdic_fib_twoMul (m : ℕ) (hm : 1 ≤ m) :
    padicValNat 2 (Nat.fib (2 * m)) ≤ padicValNat 2 (Nat.fib m) + 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFpos : 0 < Nat.fib m := Nat.fib_pos.mpr hm
  have hFne : Nat.fib m ≠ 0 := hFpos.ne'
  have hFm : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_le_fib_succ (n := m)
  have hBpos : 0 < 2 * Nat.fib (m + 1) - Nat.fib m := by omega
  have hBne : (2 * Nat.fib (m + 1) - Nat.fib m) ≠ 0 := hBpos.ne'
  have hFib : Nat.fib (2 * m) = Nat.fib m * (2 * Nat.fib (m + 1) - Nat.fib m) :=
    Nat.fib_two_mul m
  have hBmod := bracket_modEight_ne m hm
  have hBnot : ¬ (2 ^ 3 ∣ (2 * Nat.fib (m + 1) - Nat.fib m)) := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    omega
  have hle : ¬ (3 ≤ padicValNat 2 (2 * Nat.fib (m + 1) - Nat.fib m)) := by
    rw [← padicValNat_dvd_iff_le hBne (p := 2) (n := 3)]
    exact hBnot
  rw [hFib, padicValNat.mul hFne hBne]
  omega


/-- N5: Fibonacci LTE at a prime multiplier, inequality form. -/
private theorem lteVal_fib_mulPrime (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (d : ℕ) (hd : 1 ≤ d) (hdiv : p ∣ Nat.fib d) (q : ℕ) (hq : q.Prime) :
    padicValNat p (Nat.fib (d * q))
      ≤ padicValNat p (Nat.fib d) + padicValNat p q := by
  exact le_of_eq (padicValNat_fib_mul p hp2 d hd hdiv q hq.one_lt.le)

/-- N6: a proper divisor absorbing the valuation growth. -/
private theorem properDivisor_valLe (n : ℕ) (hn : 7 ≤ n) (p : ℕ) (hp : p.Prime)
    (hnot : ¬ LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) 5 n p) :
    ∃ d ∈ n.divisors, d < n ∧
      padicValNat p (Nat.fib n)
        ≤ padicValNat p (Nat.fib d) + padicValNat p (2 * n) := by
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hdiv : p ∣ Nat.fib n
  · by_cases hp2 : p = 2
    · subst hp2
      rcases Nat.even_or_odd n with heven | hodd
      · -- n even: take d = n / 2
        have h2dvd : 2 ∣ n := even_iff_two_dvd.mp heven
        have hnm : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even heven
        have hd1 : 1 ≤ n / 2 := by omega
        have hN4 := twoAdic_fib_twoMul (n / 2) hd1
        rw [hnm] at hN4
        have hv2n : 2 ≤ padicValNat 2 (2 * n) := by
          have h1 : padicValNat 2 (2 * n) = padicValNat 2 2 + padicValNat 2 n :=
            padicValNat.mul (by omega) (by omega)
          have h2 : padicValNat 2 2 = 1 := padicValNat_self
          have h3 : 1 ≤ padicValNat 2 n := by
            have h21 : (2 : ℕ) ^ 1 ∣ n := by simpa using h2dvd
            exact (padicValNat_dvd_iff_le (by omega : n ≠ 0) (p := 2) (n := 1)).mp h21
          omega
        have hdvd : n / 2 ∣ n := ⟨2, (Nat.div_mul_cancel h2dvd).symm⟩
        refine ⟨n / 2, Nat.mem_divisors.mpr ⟨hdvd, by omega⟩,
          Nat.div_lt_self (by omega) (by omega), ?_⟩
        omega
      · -- n odd: take d = 1
        have h2n : ¬ (2 ∣ n) := by
          intro hdvd
          obtain ⟨t, rfl⟩ := hodd
          omega
        have hv1 : padicValNat 2 (Nat.fib n) ≤ 1 := twoAdic_fib_odd n hodd
        have hv2n : padicValNat 2 (2 * n) = 1 := by
          have h1 : padicValNat 2 (2 * n) = padicValNat 2 2 + padicValNat 2 n :=
            padicValNat.mul (by omega) (by omega)
          have h2 : padicValNat 2 2 = 1 := padicValNat_self
          have h3 : padicValNat 2 n = 0 := padicValNat.eq_zero_of_not_dvd h2n
          omega
        refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩, by omega, ?_⟩
        omega
    · -- p odd: find k, then g = gcd k n, then q ∣ n / g, d = n / q
      have hexk : ∃ k, 1 ≤ k ∧ k < n ∧ p ∣ Nat.fib k := by
        by_cases hp5 : p = 5
        · subst hp5
          exact ⟨5, by omega, by omega, by decide⟩
        · have h4 : (p : ℤ) ∣ 5 * ∏ k ∈ Finset.Ico 1 n, ((fun k => (Nat.fib k : Int)) k) := by
            by_contra hc
            apply hnot
            simp only [LucasSequence.IsPrimitiveDivisor]
            refine ⟨by omega, hp, Int.natCast_dvd_natCast.mpr hdiv, hc⟩
          have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
          have hp5int : ¬ ((p : ℤ) ∣ 5) := by
            intro hdvd
            have hndvd : p ∣ 5 := Int.natCast_dvd_natCast.mp (by simpa using hdvd)
            have heq : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hndvd
            exact hp5 heq
          have hprod : (p : ℤ)
              ∣ ∏ k ∈ Finset.Ico 1 n, ((fun k => (Nat.fib k : Int)) k) := by
            rcases hprime.dvd_or_dvd h4 with h | h
            · exact absurd h hp5int
            · exact h
          obtain ⟨k, hk, hkdvd⟩ := (hprime.dvd_finsetProd_iff _).mp hprod
          have hk12 : 1 ≤ k ∧ k < n := Finset.mem_Ico.mp hk
          have hkdvd' : (p : ℤ) ∣ ((Nat.fib k : ℕ) : ℤ) := hkdvd
          exact ⟨k, hk12.1, hk12.2, Int.natCast_dvd_natCast.mp hkdvd'⟩
      obtain ⟨k, hk1, hkn, hkfib⟩ := hexk
      have hgdvd : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
      have hgpos : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_right k (by omega : 0 < n)
      have hgltn : Nat.gcd k n < n := by
        have h1 : Nat.gcd k n ≤ k := Nat.le_of_dvd hk1 (Nat.gcd_dvd_left k n)
        omega
      have hpg : p ∣ Nat.fib (Nat.gcd k n) := by
        rw [Nat.fib_gcd]
        exact Nat.dvd_gcd hkfib hdiv
      have hgne1 : n / Nat.gcd k n ≠ 1 := by
        intro h
        have h2 := Nat.div_mul_cancel hgdvd
        rw [h, one_mul] at h2
        omega
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgne1
      have hqg : q * Nat.gcd k n ∣ n := by
        obtain ⟨t, ht⟩ := hqdvd
        have h1 := Nat.div_mul_cancel hgdvd
        use t
        nth_rewrite 1 [← h1]
        rw [ht]
        ring
      have hqn : q ∣ n := (dvd_mul_right q _).trans hqg
      have hqd : n / q * q = n := Nat.div_mul_cancel hqn
      have hdvd : n / q ∣ n := ⟨q, hqd.symm⟩
      have hd1 : 1 ≤ n / q :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hqn) hq.pos
      have hgd : Nat.gcd k n ∣ n / q :=
        (Nat.dvd_div_iff_mul_dvd hqn).mpr hqg
      have hpd : p ∣ Nat.fib (n / q) := hpg.trans (Nat.fib_dvd _ _ hgd)
      have hN5 := lteVal_fib_mulPrime p hp2 (n / q) hd1 hpd q hq
      rw [Nat.div_mul_cancel hqn] at hN5
      by_cases hqp : q = p
      · rw [hqp] at hqn hN5 hdvd hd1
        have hvq : padicValNat p p = 1 := padicValNat_self
        have h1n : 1 ≤ padicValNat p (2 * n) := by
          have h2n : p ∣ 2 * n := hqn.trans (dvd_mul_left n 2)
          have h21 : p ^ 1 ∣ 2 * n := by simpa using h2n
          exact (padicValNat_dvd_iff_le (by omega : 2 * n ≠ 0) (p := p) (n := 1)).mp h21
        refine ⟨n / p, Nat.mem_divisors.mpr ⟨hdvd, by omega⟩,
          Nat.div_lt_self (by omega) hp.one_lt, ?_⟩
        omega
      · have hfactq : Fact (Nat.Prime q) := ⟨hq⟩
        have hvq : padicValNat p q = 0 := padicValNat_primes (Ne.symm hqp)
        refine ⟨n / q, Nat.mem_divisors.mpr ⟨hdvd, by omega⟩,
          Nat.div_lt_self (by omega) hq.two_le, ?_⟩
        omega
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩, by omega, ?_⟩
    rw [padicValNat.eq_zero_of_not_dvd hdiv]
    omega


/-- N8 auxiliary: products of integer powers accumulate in the exponent. -/
private theorem zpowProd_accum (c : ℝ) (hc : c ≠ 0) (e : ℕ × ℕ → ℤ) (s : Finset (ℕ × ℕ)) :
    ∏ x ∈ s, c ^ e x = c ^ (∑ x ∈ s, e x) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has, ih, zpow_add₀ hc]

/-- N7 auxiliary: second components of the antidiagonal are positive. -/
private theorem antidiag_snd_pos (n : ℕ) (hn : 1 ≤ n) (x : ℕ × ℕ)
    (hx : x ∈ n.divisorsAntidiagonal) : 0 < x.2 := by
  have hmem := Nat.mem_divisorsAntidiagonal.mp hx
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · exfalso
    rw [h0, mul_zero] at hmem
    omega
  · exact hpos

/-- N7 auxiliary: the positive Möbius part of the Fibonacci primitive part. -/
private def fibMoebiusPos (n : ℕ) : ℕ :=
  ∏ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ^ (ArithmeticFunction.moebius x.1).toNat

/-- N7 auxiliary: the negative Möbius part of the Fibonacci primitive part. -/
private def fibMoebiusNeg (n : ℕ) : ℕ :=
  ∏ x ∈ n.divisorsAntidiagonal, Nat.fib x.2 ^ (-ArithmeticFunction.moebius x.1).toNat

/-- N7: no primitive divisor forces A(n) ∣ 2·n·B(n). -/
private theorem fibDiv_le (n : ℕ) (hn : 7 ≤ n)
    (hno : ∀ p, ¬ LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) 5 n p) :
    fibMoebiusPos n ∣ 2 * n * fibMoebiusNeg n := by
  have hnpos : 0 < n := by omega
  have hfibpos : ∀ x ∈ n.divisorsAntidiagonal, 0 < Nat.fib x.2 := by
    intro x hx
    exact Nat.fib_pos.mpr (antidiag_snd_pos n (by omega) x hx)
  have hApos : 0 < fibMoebiusPos n := by
    apply Finset.prod_pos
    intro x hx
    exact pow_pos (hfibpos x hx) _
  have hBpos : 0 < fibMoebiusNeg n := by
    apply Finset.prod_pos
    intro x hx
    exact pow_pos (hfibpos x hx) _
  have h2nBpos : 0 < 2 * n * fibMoebiusNeg n :=
    Nat.mul_pos (Nat.mul_pos (by omega) hnpos) hBpos
  rw [← Nat.factorization_prime_le_iff_dvd hApos.ne' h2nBpos.ne']
  intro p hp
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨d, hd, hdn, hN6d⟩ := properDivisor_valLe n hn p hp (hno p)
  have hN3 := moebiusVal_le n (by omega) p d hd hdn
  have hA : (fibMoebiusPos n).factorization p
      = ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) := by
    have e1 : (fibMoebiusPos n).factorization p
        = ∑ x ∈ n.divisorsAntidiagonal,
          (Nat.fib x.2 ^ (ArithmeticFunction.moebius x.1).toNat).factorization p :=
      Nat.factorization_prod_apply (fun x hx => ne_of_gt (pow_pos (hfibpos x hx) _))
    have e2 : ∀ x ∈ n.divisorsAntidiagonal,
        (Nat.fib x.2 ^ (ArithmeticFunction.moebius x.1).toNat).factorization p
          = (ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) := by
      intro x _
      rw [Nat.factorization_def _ hp, padicValNat.pow]
    rw [e1]
    exact Finset.sum_congr rfl e2
  have hR : (2 * n * fibMoebiusNeg n).factorization p
      = padicValNat p (2 * n)
        + ∑ x ∈ n.divisorsAntidiagonal,
          (-ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) := by
    have e1 : (2 * n * fibMoebiusNeg n).factorization p
        = (2 * n).factorization p + (fibMoebiusNeg n).factorization p := by
      rw [Nat.factorization_mul (by omega) hBpos.ne', Finsupp.add_apply]
    have e2 : (fibMoebiusNeg n).factorization p
        = ∑ x ∈ n.divisorsAntidiagonal,
          (-ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) := by
      have f1 : (fibMoebiusNeg n).factorization p
          = ∑ x ∈ n.divisorsAntidiagonal,
            (Nat.fib x.2 ^ (-ArithmeticFunction.moebius x.1).toNat).factorization p :=
        Nat.factorization_prod_apply (fun x hx => ne_of_gt (pow_pos (hfibpos x hx) _))
      have f2 : ∀ x ∈ n.divisorsAntidiagonal,
          (Nat.fib x.2 ^ (-ArithmeticFunction.moebius x.1).toNat).factorization p
            = (-ArithmeticFunction.moebius x.1).toNat
              * padicValNat p (Nat.fib x.2) := by
        intro x _
        rw [Nat.factorization_def _ hp, padicValNat.pow]
      rw [f1]
      exact Finset.sum_congr rfl f2
    rw [e1, e2, Nat.factorization_def _ hp]
  have hcomb : ((∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) : ℕ) : ℤ)
      - ((∑ x ∈ n.divisorsAntidiagonal,
        (-ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) : ℕ) : ℤ)
      = ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * (padicValNat p (Nat.fib x.2) : ℤ) := by
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.cast_mul, Nat.cast_mul, ← sub_mul, Int.toNat_sub_toNat_neg]
  have hN6dZ : ((padicValNat p (Nat.fib n) : ℕ) : ℤ)
      ≤ ((padicValNat p (Nat.fib d) : ℕ) : ℤ)
        + ((padicValNat p (2 * n) : ℕ) : ℤ) := by
    exact_mod_cast hN6d
  rw [hA, hR]
  have hgoal : ((∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) : ℕ) : ℤ)
      ≤ ((padicValNat p (2 * n)
        + ∑ x ∈ n.divisorsAntidiagonal,
          (-ArithmeticFunction.moebius x.1).toNat * padicValNat p (Nat.fib x.2) : ℕ) : ℤ) := by
    rw [Nat.cast_add]
    omega
  exact Nat.cast_le.mp hgoal

/-- N8: real Binet formula for the Möbius-weighted Fibonacci product. -/
private theorem fibMoebius_real_eq (n : ℕ) (hn : 2 ≤ n) :
    ((fibMoebiusPos n : ℕ) : ℝ) = ((fibMoebiusNeg n : ℕ) : ℝ)
      * Real.goldenRatio ^ Nat.totient n
      * ∏ x ∈ n.divisorsAntidiagonal,
        (1 - (Real.goldenConj / Real.goldenRatio) ^ x.2)
          ^ (ArithmeticFunction.moebius x.1 : ℤ) := by
  have hphi : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hne : ∀ x ∈ n.divisorsAntidiagonal, (((Nat.fib x.2 : ℕ) : ℝ)) ≠ 0 := by
    intro x hx
    exact ne_of_gt (Nat.cast_pos.mpr (Nat.fib_pos.mpr (antidiag_snd_pos n (by omega) x hx)))
  have hBinet : ∀ b : ℕ, 1 ≤ b → (((Nat.fib b : ℕ) : ℝ))
      = Real.goldenRatio ^ b * (1 - (Real.goldenConj / Real.goldenRatio) ^ b)
        / Real.sqrt 5 := by
    intro b hb
    have h := Real.coe_fib_eq b
    have hphib : Real.goldenRatio ^ b ≠ 0 := pow_ne_zero b Real.goldenRatio_ne_zero
    have hpsi : Real.goldenConj ^ b
        = Real.goldenRatio ^ b * (Real.goldenConj / Real.goldenRatio) ^ b := by
      rw [div_pow Real.goldenConj Real.goldenRatio]
      exact (mul_div_cancel₀ _ hphib).symm
    rw [hpsi] at h
    rw [h]
    ring
  have hsplit : ∀ x : ℕ × ℕ, (((Nat.fib x.2 : ℕ) : ℝ)) ≠ 0 →
      (((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1).toNat
        = (((Nat.fib x.2 : ℕ) : ℝ)) ^ (-ArithmeticFunction.moebius x.1).toNat
          * ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)) := by
    intro x hx0
    have hMN : ((ArithmeticFunction.moebius x.1).toNat : ℤ)
        = ((-ArithmeticFunction.moebius x.1).toNat : ℤ)
          + (ArithmeticFunction.moebius x.1 : ℤ) := by
      have h := Int.toNat_sub_toNat_neg (ArithmeticFunction.moebius x.1)
      omega
    calc (((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1).toNat
        = (((Nat.fib x.2 : ℕ) : ℝ))
          ^ (((-ArithmeticFunction.moebius x.1).toNat : ℤ)
            + ArithmeticFunction.moebius x.1) := by
          rw [← hMN, zpow_natCast]
      _ = (((Nat.fib x.2 : ℕ) : ℝ)) ^ (-ArithmeticFunction.moebius x.1).toNat
          * ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)) := by
          rw [zpow_add₀ hx0, zpow_natCast]
  have hAB : ((fibMoebiusPos n : ℕ) : ℝ)
      = ((fibMoebiusNeg n : ℕ) : ℝ)
        * ∏ x ∈ n.divisorsAntidiagonal,
          ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)) := by
    change ((∏ x ∈ n.divisorsAntidiagonal,
        Nat.fib x.2 ^ (ArithmeticFunction.moebius x.1).toNat : ℕ) : ℝ)
      = ((∏ x ∈ n.divisorsAntidiagonal,
        Nat.fib x.2 ^ (-ArithmeticFunction.moebius x.1).toNat : ℕ) : ℝ)
        * ∏ x ∈ n.divisorsAntidiagonal,
          ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))
    rw [Nat.cast_prod, Nat.cast_prod]
    simp only [Nat.cast_pow]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun x hx => hsplit x (hne x hx))
  have hph : ∀ (b : ℕ) (z : ℤ), ((Real.goldenRatio ^ b : ℝ)) ^ z
      = Real.goldenRatio ^ (z * (b : ℤ)) := by
    intro b z
    rw [← zpow_natCast (Real.goldenRatio) b, ← zpow_mul, mul_comm ((b : ℤ)) z]
  have hphi_prod : ∏ x ∈ n.divisorsAntidiagonal,
        ((Real.goldenRatio ^ x.2 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)
      = Real.goldenRatio ^ ((Nat.totient n : ℕ) : ℤ) := by
    have h1 : ∏ x ∈ n.divisorsAntidiagonal,
          ((Real.goldenRatio ^ x.2 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)
        = ∏ x ∈ n.divisorsAntidiagonal,
          Real.goldenRatio ^ ((ArithmeticFunction.moebius x.1 : ℤ) * (x.2 : ℤ)) := by
      apply Finset.prod_congr rfl
      intro x _
      exact hph x.2 _
    rw [h1, zpowProd_accum _ hphi _ _,
      moebiusTotient_antidiagonal n (by omega)]
  have hsqrt : Real.sqrt 5 ≠ 0 := by positivity
  have hsqrt_prod : ∏ x ∈ n.divisorsAntidiagonal,
        ((Real.sqrt 5 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ) = 1 := by
    rw [zpowProd_accum _ hsqrt _ _,
      moebiusUnit_antidiagonal n (by omega),
      ite_eq_right (by omega : ¬ n = 1), zpow_zero]
  have hsub : ∀ x ∈ n.divisorsAntidiagonal,
      ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))
        = (((Real.goldenRatio ^ x.2 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))
          * (((1 - (Real.goldenConj / Real.goldenRatio) ^ x.2 : ℝ))
            ^ (ArithmeticFunction.moebius x.1 : ℤ)
            / (((Real.sqrt 5 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))) := by
    intro x hx
    have hb : 1 ≤ x.2 := antidiag_snd_pos n (by omega) x hx
    rw [hBinet x.2 hb, div_zpow, mul_zpow, mul_div_assoc]
  have hprod : ∏ x ∈ n.divisorsAntidiagonal,
        ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))
      = (∏ x ∈ n.divisorsAntidiagonal,
          ((Real.goldenRatio ^ x.2 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))
        * (∏ x ∈ n.divisorsAntidiagonal,
          (((1 - (Real.goldenConj / Real.goldenRatio) ^ x.2 : ℝ))
            ^ (ArithmeticFunction.moebius x.1 : ℤ)
            / (((Real.sqrt 5 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun x hx => hsub x hx)
  have hdiv : ∏ x ∈ n.divisorsAntidiagonal,
        (((1 - (Real.goldenConj / Real.goldenRatio) ^ x.2 : ℝ))
          ^ (ArithmeticFunction.moebius x.1 : ℤ)
          / (((Real.sqrt 5 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)))
      = ∏ x ∈ n.divisorsAntidiagonal,
        ((1 - (Real.goldenConj / Real.goldenRatio) ^ x.2 : ℝ))
          ^ (ArithmeticFunction.moebius x.1 : ℤ) := by
    rw [Finset.prod_div_distrib, hsqrt_prod, div_one]
  calc ((fibMoebiusPos n : ℕ) : ℝ)
      = ((fibMoebiusNeg n : ℕ) : ℝ)
        * ∏ x ∈ n.divisorsAntidiagonal,
          ((((Nat.fib x.2 : ℕ) : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ)) := hAB
    _ = ((fibMoebiusNeg n : ℕ) : ℝ)
        * ((∏ x ∈ n.divisorsAntidiagonal,
            ((Real.goldenRatio ^ x.2 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))
          * (∏ x ∈ n.divisorsAntidiagonal,
            (((1 - (Real.goldenConj / Real.goldenRatio) ^ x.2 : ℝ))
              ^ (ArithmeticFunction.moebius x.1 : ℤ)
              / (((Real.sqrt 5 : ℝ)) ^ (ArithmeticFunction.moebius x.1 : ℤ))))) := by
        rw [hprod]
    _ = ((fibMoebiusNeg n : ℕ) : ℝ) * Real.goldenRatio ^ Nat.totient n
        * ∏ x ∈ n.divisorsAntidiagonal,
          (1 - (Real.goldenConj / Real.goldenRatio) ^ x.2)
            ^ (ArithmeticFunction.moebius x.1 : ℤ) := by
        rw [hphi_prod, hdiv, zpow_natCast, mul_assoc]

/-- N9: the Möbius correction product is bounded below by `φ ^ (-2 : ℤ)`. -/
private theorem prod_one_sub_ratio_zpow_ge (S : Finset ℕ) (hS : 0 ∉ S)
    (e : ℕ → ℤ) (he : ∀ b ∈ S, e b = -1 ∨ e b = 0 ∨ e b = 1) :
    Real.goldenRatio ^ (-2 : ℤ)
      ≤ ∏ b ∈ S, (1 - (Real.goldenConj / Real.goldenRatio) ^ b) ^ (e b) := by
  set r : ℝ := Real.goldenConj / Real.goldenRatio with hr
  set x : ℝ := |r| with hx
  have hphipos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hφne : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hφ2 := Real.goldenRatio_sq
  have hpsi_abs : |Real.goldenConj| = Real.goldenRatio⁻¹ := by
    have h := Real.inv_goldenRatio
    rw [← abs_neg Real.goldenConj, ← h, abs_of_pos (inv_pos.mpr hphipos)]
  have hx2 : x = (Real.goldenRatio ^ 2)⁻¹ := by
    rw [hx, hr, abs_div, hpsi_abs, abs_of_pos hphipos, pow_two, mul_inv,
      div_eq_mul_inv]
  have hx0 : 0 ≤ x := abs_nonneg _
  have hx_half : x ≤ 1 / 2 := by
    rw [hx2, one_div, inv_le_inv₀ (pow_pos hphipos 2) two_pos,
      Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hx1 : x < 1 := lt_of_le_of_lt hx_half (by norm_num)
  have hb1 : ∀ b ∈ S, 1 ≤ b := by
    intro b hb
    rcases Nat.eq_zero_or_pos b with rfl | hpos
    · exact absurd hb hS
    · exact hpos
  have hxb : ∀ b : ℕ, 1 ≤ b → x ^ b ≤ x := by
    intro b hb
    rw [← Nat.add_sub_cancel' hb, pow_add, pow_one]
    calc x * x ^ (b - 1) ≤ x * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1.le) hx0
      _ = x := mul_one x
  have hab : ∀ b ∈ S, x ^ b ≤ 1 / 2 :=
    fun b hb => (hxb b (hb1 b hb)).trans hx_half
  have hrb : ∀ b ∈ S, r ^ b ≤ x ^ b := by
    intro b _
    have h : r ^ b ≤ |r| ^ b := by
      have h := le_abs_self (r ^ b)
      rwa [abs_pow] at h
    rwa [← hx] at h
  have hmrb : ∀ b ∈ S, -(x ^ b) ≤ r ^ b := by
    intro b _
    have h : -(|r| ^ b) ≤ r ^ b := by
      have h := neg_abs_le (r ^ b)
      rwa [abs_pow] at h
    rwa [← hx] at h
  have hfac0 : ∀ b ∈ S, 0 ≤ 1 - x ^ b := by
    intro b hb
    linarith [hab b hb]
  have hfac : ∀ b ∈ S, 1 - x ^ b ≤ (1 - r ^ b) ^ (e b) := by
    intro b hb
    have h1r : 0 < 1 - r ^ b := by
      have h1 := hrb b hb
      have h2 := hab b hb
      linarith
    have h1a : 0 < 1 + x ^ b := by
      have h := pow_nonneg hx0 b
      linarith
    rcases he b hb with h | h | h
    · rw [h, zpow_neg_one]
      have hsq : (1 - x ^ b) * (1 - r ^ b) ≤ 1 := by
        have hu : 0 ≤ x ^ b := pow_nonneg hx0 b
        nlinarith [mul_nonneg (show (0:ℝ) ≤ r ^ b + x ^ b by linarith [hmrb b hb])
          (show (0:ℝ) ≤ 1 - x ^ b by linarith [hab b hb]), sq_nonneg (x ^ b)]
      calc 1 - x ^ b = ((1 - x ^ b) * (1 - r ^ b)) * (1 - r ^ b)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ h1r.ne', mul_one]
        _ ≤ 1 * (1 - r ^ b)⁻¹ :=
            mul_le_mul_of_nonneg_right hsq (le_of_lt (inv_pos.mpr h1r))
        _ = (1 - r ^ b)⁻¹ := one_mul _
    · rw [h, zpow_zero]
      have h := pow_nonneg hx0 b
      linarith [hab b hb]
    · rw [h, zpow_one]
      have h := hrb b hb
      linarith
  have hprod : ∏ b ∈ S, (1 - x ^ b) ≤ ∏ b ∈ S, (1 - r ^ b) ^ (e b) :=
    Finset.prod_le_prod₀ hfac0 hfac
  have hPle1 : ∀ T : Finset ℕ, ∏ b ∈ T, (1 - x ^ b) ≤ 1 := by
    intro T
    refine Finset.prod_le_one₀ (fun b _ => ?_) (fun b _ => ?_)
    · have h1 : x ^ b ≤ 1 := pow_le_one₀ hx0 hx1.le
      have h0 : 0 ≤ x ^ b := pow_nonneg hx0 _
      linarith
    · have h0 : 0 ≤ x ^ b := pow_nonneg hx0 _
      linarith
  have hwei : ∀ T : Finset ℕ, 1 - ∑ b ∈ T, x ^ b ≤ ∏ b ∈ T, (1 - x ^ b) := by
    intro T
    induction T using Finset.induction with
    | empty => simp
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hP1 := hPle1 T
      have ha0 : 0 ≤ x ^ a := pow_nonneg hx0 _
      have hnn : 0 ≤ x ^ a * (1 - ∏ b ∈ T, (1 - x ^ b)) :=
        mul_nonneg ha0 (sub_nonneg.mpr hP1)
      nlinarith [ih]
  have hsub : S ⊆ Finset.Ico 1 (S.sup id + 1) := by
    intro b hb
    rw [Finset.mem_Ico]
    have hle : b ≤ S.sup id := Finset.le_sup (f := id) hb
    exact ⟨hb1 b hb, Nat.lt_succ_of_le hle⟩
  have hsum_le : ∑ b ∈ S, x ^ b ≤ ∑ i ∈ Finset.Ico 1 (S.sup id + 1), x ^ i := by
    have h := Finset.sum_sdiff (f := fun b => x ^ b) hsub
    have hnn : 0 ≤ ∑ i ∈ (Finset.Ico 1 (S.sup id + 1) \ S), x ^ i :=
      Finset.sum_nonneg (fun b _ => pow_nonneg hx0 _)
    linarith
  have hgeom : ∑ i ∈ Finset.Ico 1 (S.sup id + 1), x ^ i ≤ x ^ 1 / (1 - x) :=
    geom_sum_Ico_le_of_lt_one hx0 hx1
  have h1 : (1 : ℝ) - (Real.goldenRatio ^ 2)⁻¹ = Real.goldenRatio⁻¹ := by
    have hφ2ne : Real.goldenRatio ^ 2 ≠ 0 := pow_ne_zero 2 hφne
    have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [sub_eq_iff_eq_add]
    field_simp
    linear_combination hsq5
  have h2 : (Real.goldenRatio ^ 2)⁻¹ / Real.goldenRatio⁻¹
      = Real.goldenRatio⁻¹ := by
    rw [div_eq_mul_inv, inv_inv, pow_two, mul_inv, mul_assoc,
      inv_mul_cancel₀ hφne, mul_one]
  have hval : x ^ 1 / (1 - x) ≤ 1 / Real.goldenRatio := by
    have e : x ^ 1 / (1 - x) = 1 / Real.goldenRatio := by
      rw [hx2, pow_one, h1, h2]
      exact (one_div _).symm
    exact le_of_eq e
  have hz : Real.goldenRatio ^ (-2 : ℤ) = (Real.goldenRatio ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
  rw [hz]
  have hbound : ∑ b ∈ S, x ^ b ≤ 1 / Real.goldenRatio :=
    (hsum_le.trans hgeom).trans hval
  calc (Real.goldenRatio ^ 2)⁻¹ = 1 - 1 / Real.goldenRatio := by
        rw [one_div, ← h1]; ring
    _ ≤ 1 - ∑ b ∈ S, x ^ b := by linarith [hbound]
    _ ≤ ∏ b ∈ S, (1 - x ^ b) := hwei S
    _ ≤ ∏ b ∈ S, (1 - r ^ b) ^ (e b) := hprod

/-- N10: analytic lower bound `A(n) ≥ φ ^ (tot n - 2) * B(n)`. -/
private theorem fibMoebius_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.goldenRatio ^ ((Nat.totient n : ℤ) - 2) * ((fibMoebiusNeg n : ℕ) : ℝ)
      ≤ ((fibMoebiusPos n : ℕ) : ℝ) := by
  have hphipos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have h0 : (0 : ℕ) ∉ n.divisors := by
    intro h
    have hd := (Nat.mem_divisors.mp h).1
    rw [zero_dvd_iff] at hd
    omega
  have he : ∀ b ∈ n.divisors,
      (ArithmeticFunction.moebius (n / b) : ℤ) = -1
        ∨ (ArithmeticFunction.moebius (n / b) : ℤ) = 0
        ∨ (ArithmeticFunction.moebius (n / b) : ℤ) = 1 := by
    intro b _
    rcases ArithmeticFunction.moebius_eq_or (n / b) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  have hN9 := prod_one_sub_ratio_zpow_ge n.divisors h0
    (fun b => (ArithmeticFunction.moebius (n / b) : ℤ)) he
  have hprod_eq : (∏ x ∈ n.divisorsAntidiagonal,
        (1 - (Real.goldenConj / Real.goldenRatio) ^ x.2)
          ^ (ArithmeticFunction.moebius x.1 : ℤ))
      = ∏ b ∈ n.divisors, (1 - (Real.goldenConj / Real.goldenRatio) ^ b)
          ^ (ArithmeticFunction.moebius (n / b) : ℤ) :=
    Nat.prod_divisorsAntidiagonal'
      (fun a b => (1 - (Real.goldenConj / Real.goldenRatio) ^ b)
        ^ (ArithmeticFunction.moebius a : ℤ))
  have hN8 := fibMoebius_real_eq n hn
  rw [hprod_eq] at hN8
  have hexp : Real.goldenRatio ^ ((Nat.totient n : ℤ) - 2)
      = Real.goldenRatio ^ Nat.totient n * Real.goldenRatio ^ (-2 : ℤ) := by
    rw [sub_eq_add_neg, zpow_add₀ Real.goldenRatio_ne_zero, zpow_natCast]
  have hBnn : (0:ℝ) ≤ ((fibMoebiusNeg n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hφnn : (0:ℝ) ≤ Real.goldenRatio ^ Nat.totient n :=
    pow_nonneg hphipos.le _
  rw [hexp]
  calc Real.goldenRatio ^ Nat.totient n * Real.goldenRatio ^ (-2 : ℤ)
        * ((fibMoebiusNeg n : ℕ) : ℝ)
      = (Real.goldenRatio ^ Nat.totient n * ((fibMoebiusNeg n : ℕ) : ℝ))
        * Real.goldenRatio ^ (-2 : ℤ) := by ring
    _ ≤ (Real.goldenRatio ^ Nat.totient n * ((fibMoebiusNeg n : ℕ) : ℝ))
        * (∏ b ∈ n.divisors, (1 - (Real.goldenConj / Real.goldenRatio) ^ b)
          ^ (ArithmeticFunction.moebius (n / b) : ℤ)) :=
        mul_le_mul_of_nonneg_left hN9 (mul_nonneg hφnn hBnn)
    _ = ((fibMoebiusNeg n : ℕ) : ℝ) * Real.goldenRatio ^ Nat.totient n
        * (∏ b ∈ n.divisors, (1 - (Real.goldenConj / Real.goldenRatio) ^ b)
          ^ (ArithmeticFunction.moebius (n / b) : ℤ)) := by ring
    _ = ((fibMoebiusPos n : ℕ) : ℝ) := hN8.symm

/-- N11: explicit totient lower bound `n ^ 3 ≤ 16 * (tot n) ^ 4`. -/
private theorem cube_le_sixteen_mul_totient_pow_four (n : ℕ) (hn : 1 ≤ n) :
    n ^ 3 ≤ 16 * (Nat.totient n) ^ 4 := by
  set S := n.primeFactors with hSdef
  set P : ℕ := ∏ p ∈ S, p with hPdef
  set Q : ℕ := ∏ p ∈ S, (p - 1) with hQdef
  have hPQ : Nat.totient n * P = n * Q := by
    have h := Nat.totient_mul_prod_primeFactors n
    rwa [← hSdef, ← hPdef, ← hQdef] at h
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hPpos : 0 < P := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hPn : P ≤ n := by
    have hdvd := Nat.prod_primeFactors_dvd n
    rw [← hSdef, ← hPdef] at hdvd
    exact Nat.le_of_dvd hn hdvd
  have hper : ∀ p ∈ S,
      p ^ 3 ≤ ((if p = 2 then 8 else 1) * (if p = 3 then 2 else 1)) * (p - 1) ^ 4 := by
    intro p hp
    have hpprime := hprime p hp
    by_cases h2 : p = 2
    · subst h2; decide
    · by_cases h3 : p = 3
      · subst h3; decide
      · have h4 : p ≠ 4 := fun h => by rw [h] at hpprime; norm_num at hpprime
        have h5 : 5 ≤ p := by have h1 := hpprime.two_le; omega
        rw [ite_eq_right h2, ite_eq_right h3, one_mul]
        obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h5
        have hsub : 5 + q - 1 = 4 + q := by omega
        rw [hsub]
        have hq3 : 0 ≤ q ^ 3 := by positivity
        have hq4 : 0 ≤ q ^ 4 := by positivity
        nlinarith [hq3, hq4, sq_nonneg (q ^ 2), sq_nonneg q, Nat.zero_le q]
  have hU : ∏ p ∈ S, (if p = 2 then (8:ℕ) else 1) ≤ 8 := by
    by_cases h2 : (2:ℕ) ∈ S
    · have herase : ∏ p ∈ S.erase 2, (if p = 2 then (8:ℕ) else 1) = 1 :=
        Finset.prod_eq_one (fun p hp => ite_eq_right (Finset.ne_of_mem_erase hp))
      have hsplit : 8 * ∏ p ∈ S.erase 2, (if p = 2 then (8:ℕ) else 1)
          = ∏ p ∈ S, (if p = 2 then (8:ℕ) else 1) :=
        Finset.mul_prod_erase S (fun p => (if p = 2 then (8:ℕ) else 1)) h2
      rw [herase, mul_one] at hsplit
      exact le_of_eq hsplit.symm
    · have hone : ∏ p ∈ S, (if p = 2 then (8:ℕ) else 1) = 1 :=
        Finset.prod_eq_one (fun p hp =>
          ite_eq_right (by intro hcon; subst hcon; exact h2 hp))
      rw [hone]
      norm_num
  have hV : ∏ p ∈ S, (if p = 3 then (2:ℕ) else 1) ≤ 2 := by
    by_cases h3 : (3:ℕ) ∈ S
    · have herase : ∏ p ∈ S.erase 3, (if p = 3 then (2:ℕ) else 1) = 1 :=
        Finset.prod_eq_one (fun p hp => ite_eq_right (Finset.ne_of_mem_erase hp))
      have hsplit : 2 * ∏ p ∈ S.erase 3, (if p = 3 then (2:ℕ) else 1)
          = ∏ p ∈ S, (if p = 3 then (2:ℕ) else 1) :=
        Finset.mul_prod_erase S (fun p => (if p = 3 then (2:ℕ) else 1)) h3
      rw [herase, mul_one] at hsplit
      exact le_of_eq hsplit.symm
    · have hone : ∏ p ∈ S, (if p = 3 then (2:ℕ) else 1) = 1 :=
        Finset.prod_eq_one (fun p hp =>
          ite_eq_right (by intro hcon; subst hcon; exact h3 hp))
      rw [hone]
      norm_num
  have h1 : P ^ 3 ≤ 16 * Q ^ 4 := by
    have hUV : (∏ p ∈ S, ((if p = 2 then (8:ℕ) else 1)
        * (if p = 3 then (2:ℕ) else 1))) ≤ 16 := by
      rw [Finset.prod_mul_distrib]
      have h := Nat.mul_le_mul hU hV
      simpa using h
    calc P ^ 3 = ∏ p ∈ S, p ^ 3 := by rw [Finset.prod_pow]
      _ ≤ ∏ p ∈ S, (((if p = 2 then (8:ℕ) else 1)
          * (if p = 3 then (2:ℕ) else 1)) * (p - 1) ^ 4) :=
          Finset.prod_le_prod₀ (fun p _ => by positivity) hper
      _ = (∏ p ∈ S, ((if p = 2 then (8:ℕ) else 1)
          * (if p = 3 then (2:ℕ) else 1))) * Q ^ 4 := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow]
      _ ≤ 16 * Q ^ 4 := Nat.mul_le_mul hUV (le_refl _)
  have hP4 : 0 < P ^ 4 := by positivity
  apply le_of_mul_le_mul_right (a := P ^ 4) _ hP4
  have h3 : (n * Q) ^ 4 = (Nat.totient n * P) ^ 4 := by rw [← hPQ]
  rw [mul_pow, mul_pow] at h3
  calc n ^ 3 * P ^ 4 = (n ^ 3 * P) * P ^ 3 := by ring
    _ ≤ (n ^ 3 * n) * (16 * Q ^ 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hPn) h1
    _ = 16 * (n ^ 4 * Q ^ 4) := by ring
    _ = 16 * ((Nat.totient n) ^ 4 * P ^ 4) := by rw [h3]
    _ = 16 * (Nat.totient n) ^ 4 * P ^ 4 := by ring

/-- N12: exponential dominates quartic from `t = 13` on. -/
private theorem goldenRatio_pow_gt (t : ℕ) (ht : 13 ≤ t) :
    (128 : ℝ) * (t : ℝ) ^ 4 < Real.goldenRatio ^ (3 * (t - 2)) := by
  have hphipos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hsqrt : (2.2 : ℝ) < Real.sqrt 5 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hφ16 : (1.6 : ℝ) < Real.goldenRatio := by
    change (1.6 : ℝ) < (1 + Real.sqrt 5) / 2
    linarith
  have hφ3 : (4 : ℝ) < Real.goldenRatio ^ 3 := by
    calc (4 : ℝ) < 1.6 ^ 3 := by norm_num
      _ ≤ Real.goldenRatio ^ 3 := pow_le_pow_left₀ (by norm_num) hφ16.le 3
  induction t, ht using Nat.le_induction with
  | base =>
    have h33 : 3 * (13 - 2) = 33 := rfl
    rw [h33]
    calc (128 : ℝ) * ((13 : ℕ) : ℝ) ^ 4 < 1.6 ^ 33 := by norm_num
      _ ≤ Real.goldenRatio ^ 33 := pow_le_pow_left₀ (by norm_num) hφ16.le 33
  | succ n hn IH =>
    have hexp : 3 * ((n + 1) - 2) = 3 * (n - 2) + 3 := by omega
    rw [hexp, Nat.cast_add_one, pow_add]
    have hsq : ((n : ℝ) + 1) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
      have hn13 : (13 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith [mul_nonneg hnn (show (0:ℝ) ≤ (n:ℝ) - 13 by linarith)]
    have ht4 : ((n : ℝ) + 1) ^ 4 ≤ 4 * (n : ℝ) ^ 4 := by
      calc ((n : ℝ) + 1) ^ 4 = (((n : ℝ) + 1) ^ 2) ^ 2 := by ring
        _ ≤ (2 * (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
        _ = 4 * (n : ℝ) ^ 4 := by ring
    have hstep : (128 : ℝ) * ((n : ℝ) + 1) ^ 4 ≤ 4 * (128 * (n : ℝ) ^ 4) := by
      calc (128 : ℝ) * ((n : ℝ) + 1) ^ 4 ≤ 128 * (4 * (n : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left ht4 (by norm_num)
        _ = 4 * (128 * (n : ℝ) ^ 4) := by ring
    have key : 4 * (128 * (n : ℝ) ^ 4)
        < Real.goldenRatio ^ (3 * (n - 2)) * Real.goldenRatio ^ 3 := by
      have h := mul_lt_mul hφ3 IH.le (by positivity) (pow_nonneg hphipos.le 3)
      linear_combination h
    exact lt_of_le_of_lt hstep key

/-- N13 auxiliary: witness criterion for a Fibonacci primitive divisor. -/
private theorem primDiv_of_witness (n m : ℕ) (hn : 0 < n) (hm1 : m ≠ 1)
    (hdvd : m ∣ Nat.fib n) (h5 : Nat.Coprime m 5)
    (hcop : ∀ k < n, k = 0 ∨ Nat.gcd m (Nat.fib k) = 1) :
    ∃ p, LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) (5 : Int)
      n p := by
  set p := Nat.minFac m with hpdef
  have hpprime : p.Prime := Nat.minFac_prime hm1
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hpfib : p ∣ Nat.fib n := hpm.trans hdvd
  have hterm : (p : ℤ) ∣ (fun k => (Nat.fib k : Int)) n :=
    Int.natCast_dvd_natCast.mpr hpfib
  refine ⟨p, hn, hpprime, hterm, ?_⟩
  intro hcon
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
  rcases hprime.dvd_or_dvd hcon with h5dvd | hproddvd
  · have h5nat : (p : ℤ) ∣ ((5 : ℕ) : ℤ) := by simpa using h5dvd
    have hpdvd5 : p ∣ 5 := Int.natCast_dvd_natCast.mp h5nat
    have hcop5 : Nat.Coprime p 5 := h5.coprime_dvd_left hpm
    exact (hpprime.coprime_iff_not_dvd.mp hcop5) hpdvd5
  · obtain ⟨k, hk, hkdvd⟩ := (hprime.dvd_finsetProd_iff _).mp hproddvd
    have hk12 : 1 ≤ k ∧ k < n := Finset.mem_Ico.mp hk
    have hkdvd' : (p : ℤ) ∣ ((Nat.fib k : ℕ) : ℤ) := hkdvd
    have hkdvd_nat : p ∣ Nat.fib k := Int.natCast_dvd_natCast.mp hkdvd'
    rcases hcop k hk12.2 with h0 | hgcd
    · omega
    · have hpdvd : p ∣ Nat.gcd m (Nat.fib k) := Nat.dvd_gcd hpm hkdvd_nat
      rw [hgcd] at hpdvd
      have heq : p = 1 := Nat.dvd_one.mp hpdvd
      exact hpprime.ne_one heq

/-- N13: small cases `7 ≤ n ≤ 69`, `n ≠ 12`, by explicit witnesses. -/
private theorem smallCases_witness (n : ℕ) (hn : 7 ≤ n) (hle : n ≤ 69)
    (hne : n ≠ 12) :
    ∃ p, LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) (5 : Int)
      n p := by
  interval_cases n
  · refine primDiv_of_witness 7 13 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 8 7 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 9 17 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 10 11 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 11 89 ?_ ?_ ?_ ?_ ?_ <;> decide
  · exact absurd rfl hne
  · refine primDiv_of_witness 13 233 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 14 29 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 15 61 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 16 47 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 17 1597 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 18 19 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 19 37 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 20 41 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 21 421 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 22 199 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 23 28657 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 24 23 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 25 3001 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 26 521 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 27 53 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 28 281 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 29 514229 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 30 31 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 31 557 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 32 2207 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 33 19801 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 34 3571 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 35 141961 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 36 107 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 37 73 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 38 9349 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 39 135721 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 40 2161 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 41 2789 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 42 211 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 43 433494437 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 44 43 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 45 109441 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 46 139 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 47 2971215073 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 48 1103 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 49 97 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 50 101 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 51 6376021 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 52 90481 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 53 953 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 54 5779 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 55 661 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 56 14503 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 57 797 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 58 59 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 59 353 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 60 2521 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 61 4513 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 62 3010349 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 63 35239681 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 64 1087 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 65 14736206161 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 66 9901 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 67 269 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 68 67 ?_ ?_ ?_ ?_ ?_ <;> decide
  · refine primDiv_of_witness 69 137 ?_ ?_ ?_ ?_ ?_ <;> decide

/-- **Primitive divisors of Fibonacci numbers.** Write $F_j$ for the $j$-th Fibonacci number.
For every natural number $n \ge 7$ with $n \ne 12$, $F_n$ has a primitive divisor with respect
to the discriminant $5$: there is a prime $p$ that divides $F_n$ but does not divide
$5 F_1 F_2 \cdots F_{n-1}$.

This is the Fibonacci case of Carmichael's theorem on Lucas sequences, with
$\alpha = (1 + \sqrt{5})/2$ and $\beta = (1 - \sqrt{5})/2$, so that $(\alpha - \beta)^2 = 5$.

Proves `Wanted` entry `exists_isPrimitiveDivisor_fib`.

Source: Haojie Hong, *On big primitive divisors of Fibonacci numbers*, arXiv:2312.04354v1,
`bigPFn.tex` lines 153–158 (<https://arxiv.org/abs/2312.04354>); R. D. Carmichael, *On the
numerical factors of the arithmetic forms αⁿ±βⁿ*, Ann. of Math. (2) 15 (1913), 30–70. -/
theorem exists_isPrimitiveDivisor_fib {n : Nat} (hn : 7 ≤ n) (hne : n ≠ 12) :
    ∃ p, LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) (5 : Int) n p := by
  by_cases h69 : n ≤ 69
  · exact smallCases_witness n hn h69 hne
  · by_contra hno
    have hall : ∀ p, ¬ LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int))
        (5 : Int) n p := fun p hp => hno ⟨p, hp⟩
    have hphipos : 0 < Real.goldenRatio := Real.goldenRatio_pos
    have hBpos : 0 < fibMoebiusNeg n := by
      apply Finset.prod_pos
      intro x hx
      exact pow_pos (Nat.fib_pos.mpr (antidiag_snd_pos n (by omega) x hx)) _
    have hdiv := fibDiv_le n hn hall
    have h2nB : 0 < 2 * n * fibMoebiusNeg n :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hBpos
    have hAle : fibMoebiusPos n ≤ 2 * n * fibMoebiusNeg n :=
      Nat.le_of_dvd h2nB hdiv
    have hAleR : ((fibMoebiusPos n : ℕ) : ℝ)
        ≤ ((2 * n * fibMoebiusNeg n : ℕ) : ℝ) := Nat.cast_le.mpr hAle
    have hN10 := fibMoebius_lower_bound n (by omega)
    have hBposR : (0:ℝ) < ((fibMoebiusNeg n : ℕ) : ℝ) := Nat.cast_pos.mpr hBpos
    have hφle : Real.goldenRatio ^ (((Nat.totient n : ℤ)) - 2) ≤ 2 * (n:ℝ) := by
      have h := le_trans hN10 hAleR
      have h2 : ((2 * n * fibMoebiusNeg n : ℕ) : ℝ)
          = (2 * (n:ℝ)) * ((fibMoebiusNeg n : ℕ):ℝ) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [h2] at h
      exact le_of_mul_le_mul_right h hBposR
    have hN11 := cube_le_sixteen_mul_totient_pow_four n (by omega)
    by_cases ht12 : Nat.totient n ≤ 12
    · have h70 : 70 ≤ n := by omega
      have h16 := Nat.mul_le_mul (le_refl 16) (Nat.pow_le_pow_left ht12 4)
      have h343 := Nat.pow_le_pow_left h70 3
      norm_num at h16 h343
      omega
    · have ht13 : 13 ≤ Nat.totient n := by omega
      have h2 : 2 ≤ Nat.totient n := by omega
      have hexp : ((Nat.totient n : ℤ) - 2)
          = (((Nat.totient n - 2 : ℕ)) : ℤ) := by
        rw [Nat.cast_sub h2]
        simp
      rw [hexp, zpow_natCast] at hφle
      have hcubed : Real.goldenRatio ^ (3 * (Nat.totient n - 2))
          ≤ 8 * (n:ℝ)^3 := by
        have h3 : (Real.goldenRatio ^ (Nat.totient n - 2))^3 ≤ (2 * (n:ℝ))^3 :=
          pow_le_pow_left₀ (pow_nonneg hphipos.le _) hφle 3
        rw [← pow_mul] at h3
        have e : 3 * (Nat.totient n - 2) = (Nat.totient n - 2) * 3 :=
          mul_comm _ _
        rw [e]
        calc Real.goldenRatio ^ ((Nat.totient n - 2) * 3)
            ≤ (2 * (n:ℝ))^3 := h3
          _ = 8 * (n:ℝ)^3 := by ring
      have hN11R : (8 * (n:ℝ)^3) ≤ 128 * ((Nat.totient n : ℝ))^4 := by
        have h := cube_le_sixteen_mul_totient_pow_four n (by omega)
        have hR : ((n^3 : ℕ):ℝ) ≤ ((16 * (Nat.totient n)^4 : ℕ):ℝ) :=
          Nat.cast_le.mpr h
        push_cast at hR
        linarith [hR]
      have hN12 := goldenRatio_pow_gt (Nat.totient n) ht13
      have hle := le_trans hcubed hN11R
      linarith

end MetaMathlibExt

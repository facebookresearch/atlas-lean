/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.Quantum.ShorGoodUnits

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Success probability of Shor's order-to-factor reduction

For an odd modulus with `k` distinct prime factors, `Cslib.Shor.card_units_good_for_factoring_ge`
gives the lower bound `1 - 1 / 2 ^ (k - 1)` on the fraction of units with even order `r` and
half-order power different from `-1`.
-/

namespace Cslib.Shor

namespace card_units_good_for_factoring_ge

private theorem dvd_half_iff {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) (he : Even b) :
    a ∣ b / 2 ↔ a.factorization 2 < b.factorization 2 := by
  have ha : a ≠ 0 := ne_zero_of_dvd_ne_zero hb hab
  have hhalf : b / 2 ≠ 0 := by
    obtain ⟨k, hk⟩ := he
    omega
  have hle := (Nat.factorization_le_iff_dvd ha hb).2 hab
  rw [← Nat.factorization_le_iff_dvd ha hhalf, Nat.factorization_div (even_iff_two_dvd.mp he),
    Finsupp.le_def]
  simp only [Finsupp.tsub_apply]
  constructor
  · intro h
    have h₂ := h 2
    have hb₂ := Nat.prime_two.factorization_pos_of_dvd hb (even_iff_two_dvd.mp he)
    rw [Nat.prime_two.factorization_self] at h₂
    omega
  · intro h p
    by_cases hp : p = 2
    · subst p
      rw [Nat.prime_two.factorization_self]
      omega
    · simpa [Nat.prime_two.factorization, Finsupp.single_eq_of_ne hp] using hle p

private theorem factorization_two_orderOf_apply_eq {ι : Type*} [Finite ι]
    {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    {x : ∀ i, G i} {z : ∀ i, G i} (hz : ∀ i, z i ≠ 1)
    (hbad : ¬ (Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ z)) (i : ι) :
    (orderOf (x i)).factorization 2 = (orderOf x).factorization 2 := by
  classical
  have hpos := (orderOf_pos x).ne'
  have hdvd := orderOf_apply_dvd_orderOf (x := x) i
  have hle := (Nat.factorization_le_iff_dvd (orderOf_pos (x i)).ne' hpos).2 hdvd 2
  by_cases he : Even (orderOf x)
  · have hpow : x ^ (orderOf x / 2) = z := by
      by_contra h
      exact hbad ⟨he, h⟩
    apply le_antisymm hle
    by_contra! hlt
    have h := (dvd_half_iff hpos hdvd he).2 hlt
    exact hz i ((congrFun hpow i).symm.trans (orderOf_dvd_iff_pow_eq_one.mp h))
  · have hzero := Nat.factorization_eq_zero_of_not_dvd (mt even_iff_two_dvd.mpr he)
    omega

private theorem pow_half_eq_of_factorization_eq {G : Type*} [CommGroup G] [Fintype G]
    [IsCyclic G] (he : Even (Fintype.card G)) {x y : G}
    (hxy : (orderOf x).factorization 2 = (orderOf y).factorization 2) :
    x ^ (Fintype.card G / 2) = y ^ (Fintype.card G / 2) := by
  classical
  have hiff : x ^ (Fintype.card G / 2) = 1 ↔ y ^ (Fintype.card G / 2) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one,
      dvd_half_iff Fintype.card_ne_zero (orderOf_dvd_card (x := x)) he,
      dvd_half_iff Fintype.card_ne_zero (orderOf_dvd_card (x := y)) he, hxy]
  by_cases hx : x ^ (Fintype.card G / 2) = 1
  · rw [hx, hiff.mp hx]
  have ht : 2 ∣ Fintype.card G := even_iff_two_dvd.mp he
  have horder (a : G) (ha : a ^ (Fintype.card G / 2) ≠ 1) :
      orderOf (a ^ (Fintype.card G / 2)) = 2 := by
    apply orderOf_eq_prime (p := 2) ?_ ha
    rw [← pow_mul, Nat.div_mul_cancel ht, pow_card_eq_one]
  have hcard := IsCyclic.card_orderOf_eq_totient ht
  rw [Nat.totient_two, Finset.card_eq_one] at hcard
  obtain ⟨g, hg⟩ := hcard
  have hin (a : G) (ha : a ^ (Fintype.card G / 2) ≠ 1) : a ^ (Fintype.card G / 2) = g := by
    simpa [hg] using
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, horder a ha⟩ :
        a ^ (Fintype.card G / 2) ∈ Finset.univ.filter (fun b : G => orderOf b = 2))
  exact (hin x hx).trans (hin y (mt hiff.mpr hx)).symm

-- Keep one coordinate fixed and let one bit govern translation in each other group.
-- Raising to half the group cardinality distinguishes the two choices because the
-- fixed coordinate determines the original value of this power in every group.
private theorem card_matching_two_parts_mul_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
    [∀ i, IsCyclic (G i)] (he : ∀ i, Even (Fintype.card (G i))) (anchor : ι)
    [Fintype {x : ∀ i, G i // ∀ i,
      (orderOf (x i)).factorization 2 = (orderOf (x anchor)).factorization 2}] :
    Fintype.card {x : ∀ i, G i // ∀ i,
      (orderOf (x i)).factorization 2 = (orderOf (x anchor)).factorization 2} *
      2 ^ (Fintype.card ι - 1) ≤ Fintype.card (∀ i, G i) := by
  classical
  let S := {x : ∀ i, G i // ∀ i,
    (orderOf (x i)).factorization 2 = (orderOf (x anchor)).factorization 2}
  let Bits := {i // i ≠ anchor} → Bool
  have hg (i : ι) : ∃ g : G i, g ^ (Fintype.card (G i) / 2) ≠ 1 := by
    rw [← Nat.card_eq_fintype_card]
    have hc : Nat.card (G i) ≠ 0 := by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
    have hci := he i
    rw [← Nat.card_eq_fintype_card] at hci
    obtain ⟨k, hk⟩ := hci
    exact exists_pow_ne_one_of_isCyclic (by omega) (by omega)
  choose g hg using hg
  let f (v : S × Bits) (i : ι) : G i :=
    if hi : i ≠ anchor then v.1.val i * (if v.2 ⟨i, hi⟩ then g i else 1) else v.1.val i
  have hinj : Function.Injective f := by
    intro a b hab
    have hanchor : a.1.val anchor = b.1.val anchor := by
      simpa [f] using congrFun hab anchor
    have hcoord (i : ι) (hi : i ≠ anchor) :
        a.1.val i = b.1.val i ∧ a.2 ⟨i, hi⟩ = b.2 ⟨i, hi⟩ := by
      have hlevel := (a.1.property i).trans ((congrArg (fun x =>
        (orderOf x).factorization 2) hanchor).trans (b.1.property i).symm)
      have hp := pow_half_eq_of_factorization_eq (he i) hlevel
      have hv := congrFun hab i
      simp only [f, dite_eq_left hi] at hv
      have hb : a.2 ⟨i, hi⟩ = b.2 ⟨i, hi⟩ := by
        have hw := congrArg (fun x : G i => x ^ (Fintype.card (G i) / 2)) hv
        simp only [mul_pow, hp, mul_right_inj] at hw
        cases ha : a.2 ⟨i, hi⟩ <;> cases hb : b.2 ⟨i, hi⟩
        · rfl
        · exact (hg i (by simpa [ha, hb] using hw.symm)).elim
        · exact (hg i (by simpa [ha, hb] using hw)).elim
        · rfl
      rw [hb, mul_left_inj] at hv
      exact ⟨hv, hb⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      by_cases hi : i = anchor
      · subst i
        exact hanchor
      · exact (hcoord i hi).1
    · funext i
      exact (hcoord i.val i.property).2
  have hbits : Fintype.card Bits = 2 ^ (Fintype.card ι - 1) := by
    rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ]
    rw [Fintype.card_subtype_compl (fun i : ι => i = anchor), Fintype.card_subtype_eq,
      Fintype.card_bool]
  simpa only [Fintype.card_prod, hbits] using Fintype.card_le_of_injective f hinj

end card_units_good_for_factoring_ge

@[expose] public section

open card_units_good_for_factoring_ge

/-- **Most units give a factor in Shor's reduction.** Let `n` be an odd positive integer with
`k` distinct prime factors. Among the units `x` modulo `n`, those whose multiplicative order `r`
is even and satisfies `x ^ (r / 2) ≠ -1` form a fraction at least `1 - 1 / 2 ^ (k - 1)` of all
units. For such `x`, `gcd (x ^ (r / 2) - 1, n)` is a nontrivial factor of `n`
(`Cslib.Shor.gcd_factor_of_order`), so a random unit yields a factor with probability at least
`1 - 1 / 2 ^ (k - 1)`, which is at least `1 / 2` when `n` is not a prime power (P. W. Shor,
SIAM J. Comput. 26 (1997), Section 5: "this procedure, when applied to a random `x (mod n)`,
yields a factor of `n` with probability at least `1 - 1/2^{k-1}`, where `k` is the number of
distinct odd prime factors of `n`"). -/
theorem card_units_good_for_factoring_ge {n : ℕ} [NeZero n] (hn : Odd n) :
    (1 - 1 / (2 : ℝ) ^ (n.primeFactors.card - 1)) * Fintype.card (ZMod n)ˣ ≤
      ((Finset.univ.filter fun x : (ZMod n)ˣ =>
        Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1).card : ℝ) := by
  classical
  let I := n.primeFactors
  by_cases hI : I.Nonempty
  · let anchor : I := ⟨hI.choose, hI.choose_spec⟩
    let m (p : I) := (p : ℕ) ^ n.factorization p
    have hp (p : I) : Nat.Prime p := Nat.prime_of_mem_primeFactors p.property
    have hpn (p : I) : (p : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors p.property
    have hp2 (p : I) : (p : ℕ) ≠ 2 := hn.ne_two_of_dvd_nat (hpn p)
    have hm (p : I) : 1 < m p :=
      one_lt_pow₀ (hp p).one_lt (Nat.Prime.factorization_pos_of_dvd (hp p) (NeZero.ne n)
        (hpn p)).ne'
    have (p : I) : NeZero (m p) := ⟨(hm p).ne_zero⟩
    have (p : I) : Fact (1 < m p) := ⟨hm p⟩
    let G (p : I) := (ZMod (m p))ˣ
    have (p : I) : IsCyclic (G p) :=
      ZMod.isCyclic_units_of_prime_pow p (hp p) (hp2 p) _
    have hm2 (p : I) : m p ≠ 2 := by
      have hodd : Odd (m p) := (hn.of_dvd_nat (hpn p)).pow
      exact hodd.ne_two_of_dvd_nat dvd_rfl
    have hzorder (p : I) : orderOf (-1 : G p) = 2 := by
      change orderOf (-1 : (ZMod (m p))ˣ) = 2
      rw [Units.orderOf_neg_one, ZMod.ringChar_zmod_n, ite_eq_right (hm2 p)]
    have hz (p : I) : (-1 : G p) ≠ 1 := by
      intro h
      simpa [h] using hzorder p
    have he (p : I) : Even (Fintype.card (G p)) := by
      rw [even_iff_two_dvd, ← hzorder p]
      exact orderOf_dvd_card
    let r : ZMod n ≃+* ∀ p : I, ZMod (m p) := ZMod.equivPi n (NeZero.ne n)
    let e : (ZMod n)ˣ ≃* ∀ p : I, G p :=
      (Units.mapEquiv r.toMulEquiv).trans MulEquiv.piUnits
    have heneg : e (-1) = fun p => (-1 : G p) := by
      have h : r (-1) = -1 := by simp
      funext p
      apply Units.ext
      exact congrFun h p
    let good (x : (ZMod n)ˣ) := Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1
    let S := {x : ∀ p, G p // ∀ p,
      (orderOf (x p)).factorization 2 = (orderOf (x anchor)).factorization 2}
    have hmatch (x : (ZMod n)ˣ) (hx : ¬ good x) : ∀ p,
        (orderOf (e x p)).factorization 2 = (orderOf (e x anchor)).factorization 2 := by
      have hbad : ¬ (Even (orderOf (e x)) ∧ (e x) ^ (orderOf (e x) / 2) ≠
          fun p => (-1 : G p)) := by
        simpa only [e.orderOf_eq, ← heneg, ← map_pow, ne_eq, e.injective.eq_iff] using hx
      intro p
      exact (factorization_two_orderOf_apply_eq hz hbad p).trans
        (factorization_two_orderOf_apply_eq hz hbad anchor).symm
    have hbad_card : Fintype.card {x // ¬ good x} ≤ Fintype.card S :=
      Fintype.card_le_of_injective
        (fun x : {x // ¬ good x} => (⟨e x.val, hmatch x.val x.property⟩ : S))
        (fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)))
    have hbound := (Nat.mul_le_mul_right (2 ^ (Fintype.card I - 1)) hbad_card).trans
      (card_matching_two_parts_mul_pow_le he anchor)
    rw [← Fintype.card_congr e.toEquiv, Fintype.card_coe, Fintype.card_subtype] at hbound
    change (1 - 1 / (2 : ℝ) ^ (I.card - 1)) * Fintype.card (ZMod n)ˣ ≤
      ((Finset.univ.filter good).card : ℝ)
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ) good
    rw [Finset.card_univ] at hsplit
    have hboundR : ((Finset.univ.filter fun x => ¬ good x).card : ℝ) *
        (2 : ℝ) ^ (I.card - 1) ≤ Fintype.card (ZMod n)ˣ := by
      exact_mod_cast hbound
    have hsplitR : ((Finset.univ.filter good).card : ℝ) +
        ((Finset.univ.filter fun x => ¬ good x).card : ℝ) = Fintype.card (ZMod n)ˣ := by
      exact_mod_cast hsplit
    have hfail := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (I.card - 1))).2 hboundR
    rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    linarith only [hsplitR, hfail]
  · have hz : n.primeFactors.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hI)
    simp [hz]

end

end Cslib.Shor

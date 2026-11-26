/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Fermat
public import MathlibExt.NumberTheory.FermatNumberStrongPseudoprimeAddSub
public import MathlibExt.NumberTheory.FermatNumberStrongPseudoprimeTwoPow
public import MathlibExt.NumberTheory.StrongPseudoprime
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

/-!
# A subgroup of strong pseudoprime bases of a composite Fermat number

Let `F_k = Nat.fermatNumber k` be composite and `S_k` the set of residues `2 ^ t`,
`2 ^ (2 ^ (k - 1) + t) + 2 ^ t` and `2 ^ (2 ^ (k - 1) + t) - 2 ^ t` in `ZMod F_k`.
The units lying in `S_k` form a subgroup of `(ZMod F_k)ˣ` of order `2 ^ (k + 2)`,
and `F_k` is a strong pseudoprime to every base in `S_k`
(`MetaMathlibExt.fermatNumber_strongPseudoprime_bases_subgroup`).

Statements from Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24
(2024), Article A23.
-/

namespace MetaMathlibExt

private theorem two_le_of_not_prime_fermatNumber {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) : 2 ≤ k := by
  by_contra! h
  interval_cases k <;> exact hk (by decide)

private noncomputable def u2 (k : ℕ) : (ZMod (Nat.fermatNumber k))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (Nat.odd_fermatNumber k))

private theorem coe_u2 (k : ℕ) :
    ((u2 k) : ZMod (Nat.fermatNumber k)) = 2 := by
  simp [u2]

private def e (k : ℕ) : ℕ := 2 ^ (k - 1)

private def a (k : ℕ) : ZMod (Nat.fermatNumber k) := 2 ^ e k

private theorem two_pow_eq_neg_one (k : ℕ) :
    (2 : ZMod (Nat.fermatNumber k)) ^ 2 ^ k = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  exact_mod_cast ZMod.natCast_self (Nat.fermatNumber k)

private theorem a_sq (k : ℕ) (hk2 : 2 ≤ k) : a k ^ 2 = -1 := by
  simp only [a]
  rw [← pow_mul]
  have hk1 : 1 ≤ k := by omega
  have he : e k * 2 = 2 ^ k := by
    simp only [e]
    rw [← pow_succ, Nat.sub_add_cancel hk1]
  rw [he, two_pow_eq_neg_one]

private theorem isUnit_two (k : ℕ) :
    IsUnit (2 : ZMod (Nat.fermatNumber k)) := by
  have h : ((u2 k) : ZMod (Nat.fermatNumber k)) = 2 := coe_u2 k
  rw [← h]
  exact (u2 k).isUnit

private theorem isUnit_add (k : ℕ) (hk2 : 2 ≤ k) :
    IsUnit (a k + 1) := by
  have hneg2 : IsUnit (-2 : ZMod (Nat.fermatNumber k)) :=
    (isUnit_two k).neg
  have hx : a k ^ 2 = -1 := a_sq k hk2
  have hprod : IsUnit ((a k + 1) * (a k - 1)) := by
    have h : (a k + 1) * (a k - 1) = -2 := by linear_combination hx
    rw [h]
    exact hneg2
  exact isUnit_of_mul_isUnit_left hprod

private noncomputable def v1 (k : ℕ) (hk2 : 2 ≤ k) :
    (ZMod (Nat.fermatNumber k))ˣ :=
  (isUnit_add k hk2).unit

private theorem coe_v1 (k : ℕ) (hk2 : 2 ≤ k) :
    ((v1 k hk2) : ZMod (Nat.fermatNumber k)) = a k + 1 :=
  IsUnit.unit_spec _

private theorem sq_add_eq (k : ℕ) (hk2 : 2 ≤ k) :
    (a k + 1) ^ 2 = 2 ^ (e k + 1) := by
  have hx : a k ^ 2 = -1 := a_sq k hk2
  have hpow : (2 : ZMod (Nat.fermatNumber k)) ^ (e k + 1) = 2 * a k := by
    rw [pow_succ']
    rfl
  rw [hpow]
  linear_combination hx

private theorem v1_sq (k : ℕ) (hk2 : 2 ≤ k) :
    v1 k hk2 ^ 2 = u2 k ^ (e k + 1) := by
  ext
  simp only [Units.val_pow_eq_pow_val, coe_v1, coe_u2]
  exact sq_add_eq k hk2

private theorem u2_pow_card (k : ℕ) : u2 k ^ 2 ^ (k + 1) = 1 := by
  ext
  simp only [Units.val_pow_eq_pow_val, coe_u2, Units.val_one]
  rw [pow_succ, pow_mul, two_pow_eq_neg_one, neg_one_sq]

private theorem u2_pow_half_ne_one (k : ℕ) : u2 k ^ 2 ^ k ≠ 1 := by
  intro h
  have hval := congrArg Units.val h
  simp only [Units.val_pow_eq_pow_val, coe_u2, Units.val_one] at hval
  rw [two_pow_eq_neg_one] at hval
  have hfact : Fact (2 < Nat.fermatNumber k) :=
    ⟨Nat.two_lt_fermatNumber k⟩
  exact ZMod.neg_one_ne_one hval

private theorem orderOf_u2 (k : ℕ) :
    orderOf (u2 k) = 2 ^ (k + 1) :=
  orderOf_eq_prime_pow (u2_pow_half_ne_one k) (u2_pow_card k)

private theorem pow_mod_eq (k t : ℕ) :
    u2 k ^ t = u2 k ^ (t % 2 ^ (k + 1)) := by
  have hdiv :
      2 ^ (k + 1) * (t / 2 ^ (k + 1)) + t % 2 ^ (k + 1) = t :=
    Nat.div_add_mod t _
  have hrewrite : u2 k ^ t =
      u2 k ^ (2 ^ (k + 1) * (t / 2 ^ (k + 1)) + t % 2 ^ (k + 1)) := by
    rw [hdiv]
  rw [hrewrite, pow_add, pow_mul, u2_pow_card, one_pow, one_mul]

private theorem odd_e_add_one (k : ℕ) (hk2 : 2 ≤ k) :
    Odd (e k + 1) := by
  have heven : Even (e k) := by
    simp only [e]
    obtain ⟨m, hm⟩ : ∃ m, k - 1 = m + 1 := ⟨k - 2, by omega⟩
    rw [hm, pow_succ]
    exact even_iff_two_dvd.mpr (dvd_mul_left 2 _)
  exact heven.add_odd odd_one

private theorem v1_ne_pow (k : ℕ) (hk2 : 2 ≤ k) (m : ℕ) :
    v1 k hk2 ≠ u2 k ^ m := by
  intro hcontra
  have hred := pow_mod_eq k m
  set r := m % 2 ^ (k + 1) with hr
  have hv : v1 k hk2 = u2 k ^ r := by rw [hcontra, hred]
  have hpow_eq : u2 k ^ (e k + 1) = u2 k ^ (2 * r) := by
    have h1 : v1 k hk2 ^ 2 = u2 k ^ (2 * r) := by
      rw [hv, ← pow_mul, mul_comm r 2]
    rw [v1_sq k hk2] at h1
    exact h1
  have hord := orderOf_u2 k
  have h2dvd : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
  have hodd : Odd (e k + 1) := odd_e_add_one k hk2
  have heven : Even (2 * r) := even_two_mul r
  rcases le_total (e k + 1) (2 * r) with hle | hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hpow : u2 k ^ d = 1 := by
      have hcancel :
          u2 k ^ (e k + 1) * u2 k ^ d = u2 k ^ (e k + 1) * 1 := by
        rw [← pow_add, ← hd, mul_one]
        exact hpow_eq.symm
      exact mul_left_cancel hcancel
    have hdvd : 2 ^ (k + 1) ∣ d := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpow
    have h2ddvd : 2 ∣ d := dvd_trans h2dvd hdvd
    have hdeq : d = 2 * r - (e k + 1) := by omega
    have hoddd : Odd d := by
      rw [hdeq]
      exact Nat.Even.sub_odd hle heven hodd
    exact (Nat.not_even_iff_odd.mpr hoddd) (even_iff_two_dvd.mpr h2ddvd)
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hpow : u2 k ^ d = 1 := by
      have hcancel :
          u2 k ^ (2 * r) * u2 k ^ d = u2 k ^ (2 * r) * 1 := by
        rw [← pow_add, ← hd, mul_one]
        exact hpow_eq
      exact mul_left_cancel hcancel
    have hdvd : 2 ^ (k + 1) ∣ d := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpow
    have h2ddvd : 2 ∣ d := dvd_trans h2dvd hdvd
    have hdeq : d = e k + 1 - 2 * r := by omega
    have hoddd : Odd d := by
      rw [hdeq]
      exact Nat.Odd.sub_even hle hodd heven
    exact (Nat.not_even_iff_odd.mpr hoddd) (even_iff_two_dvd.mpr h2ddvd)

private theorem add_factor (k t : ℕ) :
    (2 : ZMod (Nat.fermatNumber k)) ^ (e k + t) + 2 ^ t =
      2 ^ t * (a k + 1) := by
  simp only [a, e]
  rw [pow_add]
  ring

private theorem sub_factor (k t : ℕ) :
    (2 : ZMod (Nat.fermatNumber k)) ^ (e k + t) - 2 ^ t =
      2 ^ t * (a k - 1) := by
  simp only [a, e]
  rw [pow_add]
  ring

private theorem mul_add_eq (k t : ℕ) :
    (2 : ZMod (Nat.fermatNumber k)) ^ t * (a k + 1) =
      2 ^ (e k + t) + 2 ^ t := by
  simp only [a, e]
  rw [pow_add]
  ring

private theorem mem_S_iff (k : ℕ) (hk2 : 2 ≤ k)
    (x : ZMod (Nat.fermatNumber k)) :
    ((∃ t : ℕ, x = 2 ^ t) ∨
      ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
        x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t)
    ↔ (∃ t : ℕ, x = 2 ^ t) ∨ (∃ t : ℕ, x = 2 ^ t * (a k + 1)) := by
  constructor
  · rintro (⟨t, rfl⟩ | ⟨t, h | h⟩)
    · exact Or.inl ⟨t, rfl⟩
    · have hf :
          (2 : ZMod (Nat.fermatNumber k)) ^ (2 ^ (k - 1) + t) + 2 ^ t =
            2 ^ t * (a k + 1) := by
        have := add_factor k t
        simpa [e] using this
      exact Or.inr ⟨t, h.trans hf⟩
    · have hf :
          (2 : ZMod (Nat.fermatNumber k)) ^ (2 ^ (k - 1) + t) - 2 ^ t =
            2 ^ (t + e k) * (a k + 1) := by
        have h1 := sub_factor k t
        have hsub : a k - 1 = (a k + 1) * 2 ^ e k := by
          have hx : a k ^ 2 = -1 := a_sq k hk2
          have ha : a k = (2 : ZMod (Nat.fermatNumber k)) ^ e k := rfl
          have h : (a k + 1) * a k = a k - 1 := by linear_combination hx
          rw [ha] at h
          exact h.symm
        calc (2 : ZMod (Nat.fermatNumber k)) ^ (2 ^ (k - 1) + t) - 2 ^ t
            = 2 ^ t * (a k - 1) := by simpa [e] using h1
          _ = 2 ^ t * ((a k + 1) * 2 ^ e k) := by rw [hsub]
          _ = 2 ^ (t + e k) * (a k + 1) := by rw [pow_add]; ring
      exact Or.inr ⟨t + e k, h.trans hf⟩
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl ⟨t, rfl⟩
    · right
      refine ⟨t, Or.inl ?_⟩
      have h := mul_add_eq k t
      simpa [e] using h

private theorem val_pow_u2 (k t : ℕ) :
    ((u2 k ^ t : (ZMod (Nat.fermatNumber k))ˣ) :
      ZMod (Nat.fermatNumber k)) = 2 ^ t := by
  rw [Units.val_pow_eq_pow_val, coe_u2]

private theorem val_mul_v1 (k : ℕ) (hk2 : 2 ≤ k) (t : ℕ) :
    ((u2 k ^ t * v1 k hk2 : (ZMod (Nat.fermatNumber k))ˣ) :
      ZMod (Nat.fermatNumber k)) = 2 ^ t * (a k + 1) := by
  rw [Units.val_mul, val_pow_u2, coe_v1]

private theorem mem_carrier_iff (k : ℕ) (hk2 : 2 ≤ k)
    (u : (ZMod (Nat.fermatNumber k))ˣ) :
    ((u : ZMod (Nat.fermatNumber k)) ∈
      ({x | (∃ t : ℕ, x = 2 ^ t) ∨
        ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
          x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
        Set (ZMod (Nat.fermatNumber k))))
    ↔ (∃ t : ℕ, u = u2 k ^ t) ∨
      (∃ t : ℕ, u = u2 k ^ t * v1 k hk2) := by
  have hiff := mem_S_iff k hk2 (u : ZMod (Nat.fermatNumber k))
  simp only [Set.mem_ofPred_eq] at hiff ⊢
  rw [hiff]
  constructor
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · left
      refine ⟨t, Units.ext ?_⟩
      rw [val_pow_u2]
      exact ht
    · right
      refine ⟨t, Units.ext ?_⟩
      rw [val_mul_v1]
      exact ht
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact Or.inl ⟨t, val_pow_u2 k t⟩
    · exact Or.inr ⟨t, val_mul_v1 k hk2 t⟩

private theorem mul_closed (k : ℕ) (hk2 : 2 ≤ k)
    (u v : (ZMod (Nat.fermatNumber k))ˣ)
    (hu : (∃ t : ℕ, u = u2 k ^ t) ∨
      (∃ t : ℕ, u = u2 k ^ t * v1 k hk2))
    (hv : (∃ t : ℕ, v = u2 k ^ t) ∨
      (∃ t : ℕ, v = u2 k ^ t * v1 k hk2)) :
    (∃ t : ℕ, u * v = u2 k ^ t) ∨
      (∃ t : ℕ, u * v = u2 k ^ t * v1 k hk2) := by
  rcases hu with ⟨t1, rfl⟩ | ⟨t1, rfl⟩ <;> rcases hv with ⟨t2, rfl⟩ | ⟨t2, rfl⟩
  · exact Or.inl ⟨t1 + t2, by rw [← pow_add]⟩
  · exact Or.inr ⟨t1 + t2, by rw [← mul_assoc, ← pow_add]⟩
  · exact Or.inr ⟨t1 + t2, by rw [mul_right_comm, ← pow_add]⟩
  · have hsq := v1_sq k hk2
    refine Or.inl ⟨t1 + t2 + (e k + 1), ?_⟩
    have hcomm : (u2 k ^ t1 * v1 k hk2) * (u2 k ^ t2 * v1 k hk2)
        = (u2 k ^ t1 * u2 k ^ t2) * (v1 k hk2 * v1 k hk2) := by
      rw [mul_mul_mul_comm]
    rw [hcomm, ← pow_two, hsq, ← pow_add, ← pow_add]

private theorem inv_pow_u2 (k t : ℕ) :
    ∃ s : ℕ, (u2 k ^ t)⁻¹ = u2 k ^ s := by
  have hNpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
  have hle : t ≤ 2 ^ (k + 1) * (t + 1) :=
    le_trans (Nat.le_succ t) (Nat.le_mul_of_pos_left _ hNpos)
  have hadd : t + (2 ^ (k + 1) * (t + 1) - t) = 2 ^ (k + 1) * (t + 1) :=
    Nat.add_sub_cancel' hle
  have hpow : u2 k ^ (2 ^ (k + 1) * (t + 1)) = 1 := by
    rw [pow_mul, u2_pow_card, one_pow]
  have hmul : u2 k ^ t * u2 k ^ (2 ^ (k + 1) * (t + 1) - t) = 1 := by
    rw [← pow_add, hadd, hpow]
  exact ⟨_, inv_eq_of_mul_eq_one_right hmul⟩

private theorem inv_closed (k : ℕ) (hk2 : 2 ≤ k)
    (u : (ZMod (Nat.fermatNumber k))ˣ)
    (hu : (∃ t : ℕ, u = u2 k ^ t) ∨
      (∃ t : ℕ, u = u2 k ^ t * v1 k hk2)) :
    (∃ t : ℕ, u⁻¹ = u2 k ^ t) ∨
      (∃ t : ℕ, u⁻¹ = u2 k ^ t * v1 k hk2) := by
  rcases hu with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := inv_pow_u2 k t
    exact Or.inl ⟨s, hs⟩
  · obtain ⟨s1, hs1⟩ := inv_pow_u2 k t
    obtain ⟨s3, hs3⟩ := inv_pow_u2 k (e k + 1)
    have hmul1 : v1 k hk2 * (v1 k hk2 * u2 k ^ s3) = 1 := by
      rw [← mul_assoc, ← pow_two, v1_sq, ← hs3, mul_inv_cancel]
    have hvinv : (v1 k hk2)⁻¹ = v1 k hk2 * u2 k ^ s3 :=
      inv_eq_of_mul_eq_one_right hmul1
    have hinv : (u2 k ^ t * v1 k hk2)⁻¹ = u2 k ^ (s1 + s3) * v1 k hk2 := by
      rw [mul_inv, hs1, hvinv, mul_left_comm, ← pow_add, mul_comm]
    exact Or.inr ⟨s1 + s3, hinv⟩

private theorem pow_inj_on_range (k : ℕ) {t1 t2 : ℕ}
    (h1 : t1 < 2 ^ (k + 1)) (h2 : t2 < 2 ^ (k + 1))
    (h : u2 k ^ t1 = u2 k ^ t2) : t1 = t2 := by
  have hord := orderOf_u2 k
  rcases le_total t1 t2 with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hpow : u2 k ^ d = 1 := by
      have hcancel : u2 k ^ t1 * u2 k ^ d = u2 k ^ t1 * 1 := by
        rw [← pow_add, mul_one]
        exact h.symm
      exact mul_left_cancel hcancel
    have hdvd : 2 ^ (k + 1) ∣ d := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hlt : d < 2 ^ (k + 1) := by omega
    have hzero : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hpow : u2 k ^ d = 1 := by
      have hcancel : u2 k ^ t2 * u2 k ^ d = u2 k ^ t2 * 1 := by
        rw [← pow_add, mul_one]
        exact h
      exact mul_left_cancel hcancel
    have hdvd : 2 ^ (k + 1) ∣ d := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hlt : d < 2 ^ (k + 1) := by omega
    have hzero : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

private noncomputable def H (k : ℕ) (hk2 : 2 ≤ k) :
    Subgroup (ZMod (Nat.fermatNumber k))ˣ where
  carrier := {u | (u : ZMod (Nat.fermatNumber k)) ∈
    ({x | (∃ t : ℕ, x = 2 ^ t) ∨
      ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
        x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
      Set (ZMod (Nat.fermatNumber k)))}
  one_mem' := by
    have hmem :
        ((1 : (ZMod (Nat.fermatNumber k))ˣ) :
          ZMod (Nat.fermatNumber k)) ∈
        ({x | (∃ t : ℕ, x = 2 ^ t) ∨
          ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
            x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
          Set (ZMod (Nat.fermatNumber k))) := by
      rw [mem_carrier_iff k hk2]
      exact Or.inl ⟨0, (pow_zero _).symm⟩
    exact hmem
  mul_mem' := by
    intro u v hu hv
    have huS : (u : ZMod (Nat.fermatNumber k)) ∈
        ({x | (∃ t : ℕ, x = 2 ^ t) ∨
          ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
            x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
          Set (ZMod (Nat.fermatNumber k))) := hu
    have hvS : (v : ZMod (Nat.fermatNumber k)) ∈
        ({x | (∃ t : ℕ, x = 2 ^ t) ∨
          ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
            x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
          Set (ZMod (Nat.fermatNumber k))) := hv
    have hmem : (((u * v : (ZMod (Nat.fermatNumber k))ˣ)) :
        ZMod (Nat.fermatNumber k)) ∈
        ({x | (∃ t : ℕ, x = 2 ^ t) ∨
          ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
            x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
          Set (ZMod (Nat.fermatNumber k))) := by
      rw [mem_carrier_iff k hk2] at huS hvS ⊢
      exact mul_closed k hk2 u v huS hvS
    exact hmem
  inv_mem' := by
    intro u hu
    have huS : (u : ZMod (Nat.fermatNumber k)) ∈
        ({x | (∃ t : ℕ, x = 2 ^ t) ∨
          ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
            x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
          Set (ZMod (Nat.fermatNumber k))) := hu
    have hmem : (((u⁻¹ : (ZMod (Nat.fermatNumber k))ˣ)) :
        ZMod (Nat.fermatNumber k)) ∈
        ({x | (∃ t : ℕ, x = 2 ^ t) ∨
          ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
            x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
          Set (ZMod (Nat.fermatNumber k))) := by
      rw [mem_carrier_iff k hk2] at huS ⊢
      exact inv_closed k hk2 u huS
    exact hmem

private theorem mem_H_iff (k : ℕ) (hk2 : 2 ≤ k)
    (u : (ZMod (Nat.fermatNumber k))ˣ) :
    u ∈ H k hk2 ↔ (u : ZMod (Nat.fermatNumber k)) ∈
      ({x | (∃ t : ℕ, x = 2 ^ t) ∨
        ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
          x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
        Set (ZMod (Nat.fermatNumber k))) :=
  Iff.rfl

private noncomputable def cardFun (k : ℕ) (hk2 : 2 ≤ k) :
    Fin (2 ^ (k + 1)) × Bool → H k hk2
  | (t, false) => ⟨u2 k ^ t.val, by
      have hmem :
          ((u2 k ^ t.val : (ZMod (Nat.fermatNumber k))ˣ) :
            ZMod (Nat.fermatNumber k)) ∈
          ({x | (∃ t : ℕ, x = 2 ^ t) ∨
            ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
              x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
            Set (ZMod (Nat.fermatNumber k))) := by
        rw [mem_carrier_iff k hk2]
        exact Or.inl ⟨t.val, rfl⟩
      exact hmem⟩
  | (t, true) => ⟨u2 k ^ t.val * v1 k hk2, by
      have hmem :
          (((u2 k ^ t.val * v1 k hk2 :
            (ZMod (Nat.fermatNumber k))ˣ)) :
            ZMod (Nat.fermatNumber k)) ∈
          ({x | (∃ t : ℕ, x = 2 ^ t) ∨
            ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
              x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
            Set (ZMod (Nat.fermatNumber k))) := by
        rw [mem_carrier_iff k hk2]
        exact Or.inr ⟨t.val, rfl⟩
      exact hmem⟩

private theorem cardFun_injective (k : ℕ) (hk2 : 2 ≤ k) :
    Function.Injective (cardFun k hk2) := by
  intro p1 p2 heq
  obtain ⟨t1, b1⟩ := p1
  obtain ⟨t2, b2⟩ := p2
  have hvalG := congrArg Subtype.val heq
  simp only [cardFun] at hvalG
  cases b1 <;> cases b2 <;> simp only at hvalG ⊢
  · have hval' : t1.val = t2.val :=
      pow_inj_on_range k t1.is_lt t2.is_lt hvalG
    have hfin : t1 = t2 := Fin.ext hval'
    rw [hfin]
  · exfalso
    obtain ⟨s2, hs2⟩ := inv_pow_u2 k t2.val
    have hleft : (u2 k ^ t2.val)⁻¹ * (u2 k ^ t1.val) = v1 k hk2 := by
      rw [hvalG, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hs2, ← pow_add] at hleft
    exact v1_ne_pow k hk2 _ hleft.symm
  · exfalso
    obtain ⟨s1, hs1⟩ := inv_pow_u2 k t1.val
    have hleft : (u2 k ^ t1.val)⁻¹ * (u2 k ^ t2.val) = v1 k hk2 := by
      have hbase :
          (u2 k ^ t1.val)⁻¹ * (u2 k ^ t1.val * v1 k hk2) = v1 k hk2 := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [hvalG] at hbase
      exact hbase
    rw [hs1, ← pow_add] at hleft
    exact v1_ne_pow k hk2 _ hleft.symm
  · have hcancel : u2 k ^ t1.val = u2 k ^ t2.val :=
      mul_right_cancel hvalG
    have hval' : t1.val = t2.val :=
      pow_inj_on_range k t1.is_lt t2.is_lt hcancel
    have hfin : t1 = t2 := Fin.ext hval'
    rw [hfin]

private theorem cardFun_surjective (k : ℕ) (hk2 : 2 ≤ k) :
    Function.Surjective (cardFun k hk2) := by
  intro uH
  have huS : ((uH.val : (ZMod (Nat.fermatNumber k))ˣ) :
      ZMod (Nat.fermatNumber k)) ∈
      ({x | (∃ t : ℕ, x = 2 ^ t) ∨
        ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
          x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
        Set (ZMod (Nat.fermatNumber k))) :=
    uH.property
  rw [mem_carrier_iff k hk2] at huS
  rcases huS with ⟨t0, ht0⟩ | ⟨t0, ht0⟩
  · have hred := pow_mod_eq k t0
    set r := t0 % 2 ^ (k + 1) with hr
    have hrlt : r < 2 ^ (k + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hu_eq : (uH.val : (ZMod (Nat.fermatNumber k))ˣ) = u2 k ^ r := by
      rw [ht0, hred]
    refine ⟨(⟨r, hrlt⟩, false), ?_⟩
    apply Subtype.ext
    simpa [cardFun] using hu_eq.symm
  · have hred := pow_mod_eq k t0
    set r := t0 % 2 ^ (k + 1) with hr
    have hrlt : r < 2 ^ (k + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hu_eq : (uH.val : (ZMod (Nat.fermatNumber k))ˣ) =
        u2 k ^ r * v1 k hk2 := by
      rw [ht0, hred]
    refine ⟨(⟨r, hrlt⟩, true), ?_⟩
    apply Subtype.ext
    simpa [cardFun] using hu_eq.symm

private theorem card_H (k : ℕ) (hk2 : 2 ≤ k) :
    Nat.card (H k hk2) = 2 ^ (k + 2) := by
  classical
  have hbij : Function.Bijective (cardFun k hk2) :=
    ⟨cardFun_injective k hk2, cardFun_surjective k hk2⟩
  have hequiv : Fin (2 ^ (k + 1)) × Bool ≃ H k hk2 :=
    Equiv.ofBijective _ hbij
  have hcard : Nat.card (H k hk2) =
      Nat.card (Fin (2 ^ (k + 1)) × Bool) :=
    Nat.card_congr hequiv.symm
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, ← pow_succ]

private theorem spsp_all (k : ℕ) (hk : ¬(Nat.fermatNumber k).Prime)
    (x : ZMod (Nat.fermatNumber k))
    (hx : x ∈ ({x | (∃ t : ℕ, x = 2 ^ t) ∨
      ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
        x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t} :
      Set (ZMod (Nat.fermatNumber k)))) :
    IsStrongPseudoprime (Nat.fermatNumber k) x := by
  have hx' : (∃ t : ℕ, x = 2 ^ t) ∨
      ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
        x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t := hx
  rcases hx' with ⟨t, rfl⟩ | ⟨t, rfl | rfl⟩
  · have h :=
      fermatNumber_isStrongPseudoprime_two_zpow hk (u2 k) (coe_u2 k) (t : ℤ)
    have hval :
        (((u2 k ^ (t : ℤ) : (ZMod (Nat.fermatNumber k))ˣ)) :
          ZMod (Nat.fermatNumber k)) = (2 ^ t : ZMod (Nat.fermatNumber k)) := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_u2]
    rw [hval] at h
    exact h
  · exact (fermatNumber_isStrongPseudoprime_two_pow_add_sub hk t).1
  · exact (fermatNumber_isStrongPseudoprime_two_pow_add_sub hk t).2

/-- **A subgroup of strong pseudoprime bases of a composite Fermat number.** Let $k$ be a natural
number such that the Fermat number $F_k = 2^{2^k} + 1$ is composite, and let $S_k$ be the set of
residues modulo $F_k$ of the form $2^t$, $2^{2^{k-1}+t} + 2^t$ or $2^{2^{k-1}+t} - 2^t$ with $t$ a
natural number. Then the units of $\mathbb{Z}/F_k\mathbb{Z}$ that lie in $S_k$ form a subgroup of
the unit group of order $2^{k+2}$, and $F_k$ is a strong pseudoprime to every base in $S_k$.

The source also asserts that this subgroup is isomorphic to $C_{2^{k+1}} \times C_2$. This is
false: the residue $2^{16} + 1$ has multiplicative order $128 = 2^{k+2}$ modulo $F_5$, so the
subgroup is cyclic for $k = 5$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 8 (`integers-2024-A23-thm-8`). -/
public theorem fermatNumber_strongPseudoprime_bases_subgroup {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) :
    let S : Set (ZMod (Nat.fermatNumber k)) :=
      {x | (∃ t : ℕ, x = 2 ^ t) ∨
        ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨
          x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t}
    ∃ H : Subgroup (ZMod (Nat.fermatNumber k))ˣ,
      (∀ u : (ZMod (Nat.fermatNumber k))ˣ, u ∈ H ↔ (u : ZMod (Nat.fermatNumber k)) ∈ S) ∧
      Nat.card H = 2 ^ (k + 2) ∧
      ∀ x ∈ S, IsStrongPseudoprime (Nat.fermatNumber k) x := by
  have hk2 : 2 ≤ k := two_le_of_not_prime_fermatNumber hk
  refine ⟨H k hk2, mem_H_iff k hk2, card_H k hk2, ?_⟩
  intro x hx
  exact spsp_all k hk x hx

end MetaMathlibExt

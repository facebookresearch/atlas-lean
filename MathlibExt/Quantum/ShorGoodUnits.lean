/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Shor good-unit density for `N = p * q`

For distinct odd primes `p`, `q`, at least half of the units
modulo `p * q` are good for Shor's factoring algorithm: their
multiplicative order is even and the half power is not `-1`, so
`gcd (a^(r/2) - 1, N)` and `gcd (a^(r/2) + 1, N)` give a nontrivial
factor. This is the counting core of roadmap package QCI-10 of the
Atlas TCS canon roadmap.

Source: Shor (1997), Section 5; Nielsen and Chuang, Quantum
Computation and Quantum Information, Section 5.3.
-/

open Finset
/-- Every positive natural has an exact 2-adic level. -/
private theorem two_level_exists {n : ℕ} (hn : n ≠ 0) :
    ∃ j, 2 ^ j ∣ n ∧ ¬ 2 ^ (j + 1) ∣ n := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  refine ⟨k, dvd_mul_right _ _, ?_⟩
  rw [pow_succ]
  intro h
  obtain ⟨t, ht⟩ := h
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hm2 : m = 2 * t := by
    have h' : 2 ^ k * m = 2 ^ k * (2 * t) := by rw [ht]; ring
    exact Nat.mul_left_cancel hpos h'
  have h2 : 2 ∣ m := ⟨t, hm2⟩
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

/-- A power of two divides an lcm iff it divides one of the sides. -/
private theorem two_pow_dvd_lcm_iff {a b k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    2 ^ k ∣ Nat.lcm a b ↔ 2 ^ k ∣ a ∨ 2 ^ k ∣ b := by
  have h0 : Nat.lcm a b ≠ 0 := by
    intro h
    rw [Nat.lcm_eq_zero_iff] at h
    rcases h with rfl | rfl
    · exact ha rfl
    · exact hb rfl
  rw [(Nat.prime_two).pow_dvd_iff_le_factorization h0,
    (Nat.prime_two).pow_dvd_iff_le_factorization ha,
    (Nat.prime_two).pow_dvd_iff_le_factorization hb,
    Nat.factorization_lcm ha hb, Finsupp.sup_apply]
  rcases le_total (a.factorization 2) (b.factorization 2) with h | h
  · rw [sup_eq_right.mpr h]
    exact ⟨fun hk => Or.inr hk, fun h' => h'.elim (fun hh => le_trans hh h) id⟩
  · rw [sup_eq_left.mpr h]
    exact ⟨fun hk => Or.inl hk, fun h' => h'.elim id (fun hh => le_trans hh h)⟩

/-- `-1 ≠ 1` in units of `ZMod n` when `n ∤ 2`. -/
private theorem units_neg_one_ne_one {n : ℕ} [NeZero n] (h2 : ¬ n ∣ 2) :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h
  have hv : ((-1 : (ZMod n)ˣ) : ZMod n) = 1 := by rw [h]; simp
  simp only [Units.val_neg, Units.val_one] at hv
  have h11 : (1 : ZMod n) + 1 = 0 := by
    have hcon := congrArg (· + (1 : ZMod n)) hv
    simpa using hcon.symm
  have h20 : ((2 : ℕ) : ZMod n) = 0 := by
    calc ((2 : ℕ) : ZMod n) = (1 : ZMod n) + 1 := by push_cast; ring
    _ = 0 := h11
  exact h2 ((CharP.cast_eq_zero_iff (ZMod n) n 2).mp h20)

/-- In `(ZMod p)ˣ` for prime `p`, the only square roots of 1 are `±1`. -/
private theorem sq_eq_one_units {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) (h : u ^ 2 = 1) :
    u = 1 ∨ u = -1 := by
  have hv : (u : ZMod p) ^ 2 = 1 := by
    have hcon := congrArg Units.val h
    simpa using hcon
  have h' : (u : ZMod p) = 1 ∨ (u : ZMod p) = -1 := sq_eq_one_iff.mp hv
  rcases h' with h1 | h1
  · exact Or.inl (Units.ext (by rw [Units.val_one]; exact h1))
  · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; exact h1))

/-- CRT equivalence on unit groups. -/
private noncomputable def crtUnits {p q : ℕ} (h : p.Coprime q) :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- The CRT equivalence sends `-1` to `-1`. -/
private theorem crtUnits_neg_one {p q : ℕ} (h : p.Coprime q) :
    crtUnits h (-1) = -1 := by
  have hR1 : (ZMod.chineseRemainder h) ((-1 : ZMod (p * q))) = -1 := by
    rw [map_neg, map_one]
  apply Prod.ext
  · apply Units.ext
    calc ((((crtUnits h (-1)).1 : (ZMod p)ˣ) : ZMod p))
        = (((ZMod.chineseRemainder h) ((-1 : ZMod (p * q)))).1) := rfl
      _ = ((-1 : ZMod p × ZMod q).1) := by rw [hR1]
      _ = (((-1 : (ZMod p)ˣ × (ZMod q)ˣ).1 : (ZMod p)ˣ) : ZMod p) := rfl
  · apply Units.ext
    calc ((((crtUnits h (-1)).2 : (ZMod q)ˣ) : ZMod q))
        = (((ZMod.chineseRemainder h) ((-1 : ZMod (p * q)))).2) := rfl
      _ = ((-1 : ZMod p × ZMod q).2) := by rw [hR1]
      _ = (((-1 : (ZMod p)ˣ × (ZMod q)ˣ).2 : (ZMod q)ˣ) : ZMod q) := rfl

/-- Goodness transfers across the CRT equivalence. -/
private theorem good_transfer {p q : ℕ} (h : p.Coprime q) (a : (ZMod (p * q))ˣ) :
    (Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1) ↔
      (Even (orderOf (crtUnits h a)) ∧
        (crtUnits h a) ^ (orderOf (crtUnits h a) / 2) ≠ -1) := by
  have hord : orderOf (crtUnits h a) = orderOf a :=
    orderOf_injective (crtUnits h).toMonoidHom (crtUnits h).injective a
  have hneg : crtUnits h (-1) = -1 := crtUnits_neg_one h
  rw [hord]
  constructor
  · rintro ⟨hev, hne⟩
    refine ⟨hev, ?_⟩
    intro hcon
    apply hne
    apply (crtUnits h).injective
    rw [map_pow, hcon]
    exact hneg.symm
  · rintro ⟨hev, hne⟩
    refine ⟨hev, ?_⟩
    intro hcon
    apply hne
    have h3 := congrArg (crtUnits h) hcon
    rwa [map_pow, hneg] at h3

/-- If `x ^ (r/2) = -1` (with `r = orderOf x * m`), then `m` is odd and both
`orderOf x` and `r` are even. -/
private theorem comp_odd_of_pow_half_eq_neg_one {p : ℕ} [Fact p.Prime] (x : (ZMod p)ˣ)
    {r m : ℕ} (hr : r = orderOf x * m)
    (hne : (-1 : (ZMod p)ˣ) ≠ 1) (h : x ^ (r / 2) = -1) :
    Odd m ∧ Even (orderOf x) ∧ Even r := by
  have hsq : (-1 : (ZMod p)ˣ) ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, pow_two, neg_mul_neg, mul_one]
  have h2t : x ^ (2 * (r / 2)) = 1 := by
    have e : 2 * (r / 2) = (r / 2) * 2 := mul_comm _ _
    rw [e, pow_mul, h, hsq]
  have hdvd : orderOf x ∣ 2 * (r / 2) := orderOf_dvd_iff_pow_eq_one.mpr h2t
  have hndvd : ¬ orderOf x ∣ r / 2 :=
    fun hd => hne (h.symm.trans (orderOf_dvd_iff_pow_eq_one.mp hd))
  have hr1dvd : orderOf x ∣ r := ⟨m, hr⟩
  rcases Nat.even_or_odd r with hevr | hrodd
  · have hmodd : Odd m := by
      by_contra hcon
      rcases Nat.even_or_odd m with hevm | hom
      · obtain ⟨t, ht⟩ := even_iff_two_dvd.mp hevm
        have hr2' : r = 2 * (orderOf x * t) := by rw [hr, ht]; ring
        have hdiv : r / 2 = orderOf x * t := by omega
        exact hndvd ⟨t, hdiv⟩
      · exact absurd hom hcon
    have hevr1 : Even (orderOf x) := by
      by_contra hcon
      rcases Nat.even_or_odd (orderOf x) with he1 | ho1
      · exact absurd he1 hcon
      · have hrodd' : Odd r := by rw [hr]; exact ho1.mul hmodd
        exact (Nat.not_even_iff_odd.mpr hrodd') hevr
    exact ⟨hmodd, hevr1, hevr⟩
  · have hr1odd : Odd (orderOf x) := by
      rcases Nat.even_or_odd (orderOf x) with he1 | ho1
      · exfalso
        have hevr' : Even r :=
          even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp he1) hr1dvd)
        exact (Nat.not_even_iff_odd.mpr hrodd) hevr'
      · exact ho1
    have h2n : ¬ 2 ∣ orderOf x :=
      fun hd => (Nat.not_even_iff_odd.mpr hr1odd) (even_iff_two_dvd.mpr hd)
    have hcop : (orderOf x).Coprime 2 :=
      Nat.coprime_comm.mp ((Nat.prime_two).coprime_iff_not_dvd.mpr h2n)
    have hd : orderOf x ∣ r / 2 := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
    exact absurd hd hndvd

/-- If `r = orderOf x * m` with `r`, `orderOf x` even and `m` odd, then
`x ^ (r/2) = -1`. -/
private theorem comp_pow_half_eq_neg_one_of {p : ℕ} [Fact p.Prime] (x : (ZMod p)ˣ)
    {r m : ℕ} (hr : r = orderOf x * m) (hevr : Even r) (hmodd : Odd m)
    (hevr1 : Even (orderOf x)) :
    x ^ (r / 2) = -1 := by
  have hr1dvd : orderOf x ∣ r := ⟨m, hr⟩
  have hxr : x ^ r = 1 := orderOf_dvd_iff_pow_eq_one.mp hr1dvd
  have hsq : (x ^ (r / 2)) ^ 2 = 1 := by
    obtain ⟨t, ht⟩ := hevr
    have e : r / 2 * 2 = r := by rw [ht]; omega
    calc (x ^ (r / 2)) ^ 2 = x ^ (r / 2 * 2) := (pow_mul x (r / 2) 2).symm
    _ = x ^ r := by rw [e]
    _ = 1 := hxr
  have hcase := sq_eq_one_units (x ^ (r / 2)) hsq
  rcases hcase with h1 | h1
  · exfalso
    have hd : orderOf x ∣ r / 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    obtain ⟨s, hs⟩ := hevr1
    have hrs : r / 2 = s * m := by
      have hr2 : r = 2 * (s * m) := by rw [hr, hs]; ring
      omega
    have hspos : 0 < s := by
      have h1' : 0 < orderOf x := orderOf_pos x
      omega
    have hd2 : 2 * s ∣ m * s := by
      have hdm : orderOf x ∣ s * m := by rw [← hrs]; exact hd
      have e1 : s + s = 2 * s := by ring
      have e2 : s * m = m * s := mul_comm _ _
      rw [hs, e1, e2] at hdm
      exact hdm
    have h2m : 2 ∣ m := (Nat.mul_dvd_mul_iff_right hspos).mp hd2
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h2m)
  · exact h1

/-- If `a` has exact 2-level `j` and `2 ^ (j+1) ∣ a * c`, then `2 ∣ c`. -/
private theorem two_dvd_cofactor {a c j : ℕ}
    (h : 2 ^ j ∣ a ∧ ¬ 2 ^ (j + 1) ∣ a)
    (hd : 2 ^ (j + 1) ∣ a * c) : 2 ∣ c := by
  obtain ⟨o, ho⟩ := h.1
  have hoodd : Odd o := by
    by_contra hcon
    rcases Nat.even_or_odd o with hevo | hoo
    · obtain ⟨t, ht⟩ := even_iff_two_dvd.mp hevo
      have hcon' : 2 ^ (j + 1) ∣ a := by
        rw [pow_succ, ho, ht]
        exact mul_dvd_mul_left (2 ^ j) (dvd_mul_right 2 t)
      exact absurd hcon' h.2
    · exact absurd hoo hcon
  have hd2 : 2 ^ j * 2 ∣ 2 ^ j * (o * c) := by
    have hd' : 2 ^ j * 2 ∣ 2 ^ j * o * c := by
      rw [pow_succ, ho] at hd
      exact hd
    rwa [mul_assoc] at hd'
  obtain ⟨t, ht⟩ := hd2
  have hpos : 0 < 2 ^ j := pow_pos (by norm_num) j
  have hoc : o * c = 2 * t := by
    have h' : 2 ^ j * (o * c) = 2 ^ j * (2 * t) := by rw [ht]; ring
    exact Nat.mul_left_cancel hpos h'
  have hev : Even (o * c) := ⟨t, by rw [hoc, two_mul]⟩
  rcases Nat.even_or_odd c with hevc | hoc'
  · exact even_iff_two_dvd.mp hevc
  · exfalso
    exact (Nat.not_even_iff_odd.mpr (hoodd.mul hoc')) hev

/-- A pair is bad iff the exact 2-levels of the component orders agree. -/
private theorem bad_iff_levels_eq {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) {j1 j2 : ℕ}
    (h1 : 2 ^ j1 ∣ orderOf x ∧ ¬ 2 ^ (j1 + 1) ∣ orderOf x)
    (h2 : 2 ^ j2 ∣ orderOf y ∧ ¬ 2 ^ (j2 + 1) ∣ orderOf y)
    (hne1 : (-1 : (ZMod p)ˣ) ≠ 1) (hne2 : (-1 : (ZMod q)ˣ) ≠ 1) :
    (Odd (Nat.lcm (orderOf x) (orderOf y)) ∨
      (x ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1 ∧
       y ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1)) ↔ j1 = j2 := by
  have hr1 : orderOf x ≠ 0 := ne_of_gt (orderOf_pos x)
  have hr2 : orderOf y ≠ 0 := ne_of_gt (orderOf_pos y)
  set r1 := orderOf x with hr1def
  set r2 := orderOf y with hr2def
  set r := Nat.lcm r1 r2 with hrdef
  have hm1 : r = r1 * (r / r1) := (Nat.mul_div_cancel' (Nat.dvd_lcm_left _ _)).symm
  have hm2 : r = r2 * (r / r2) := (Nat.mul_div_cancel' (Nat.dvd_lcm_right _ _)).symm
  constructor
  · rintro (hrodd | ⟨hx, hy⟩)
    · have h2r : ¬ 2 ∣ r :=
        fun hd => (Nat.not_even_iff_odd.mpr hrodd) (even_iff_two_dvd.mpr hd)
      have h2r1 : ¬ 2 ∣ r1 := fun hd => h2r (dvd_trans hd (Nat.dvd_lcm_left _ _))
      have h2r2 : ¬ 2 ∣ r2 := fun hd => h2r (dvd_trans hd (Nat.dvd_lcm_right _ _))
      have j1eq : j1 = 0 := by
        by_contra hj
        have hpos : 0 < j1 := Nat.pos_of_ne_zero hj
        have hd : 2 ∣ r1 := by
          calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ∣ 2 ^ j1 := pow_dvd_pow 2 hpos
          _ ∣ r1 := h1.1
        exact h2r1 hd
      have j2eq : j2 = 0 := by
        by_contra hj
        have hpos : 0 < j2 := Nat.pos_of_ne_zero hj
        have hd : 2 ∣ r2 := by
          calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ∣ 2 ^ j2 := pow_dvd_pow 2 hpos
          _ ∣ r2 := h2.1
        exact h2r2 hd
      exact j1eq.trans j2eq.symm
    · have hC1 := comp_odd_of_pow_half_eq_neg_one x hm1 hne1 hx
      have hC2 := comp_odd_of_pow_half_eq_neg_one y hm2 hne2 hy
      rcases lt_trichotomy j1 j2 with hlt | heq | hgt
      · exfalso
        have hle : j1 + 1 ≤ j2 := by omega
        have h2k : 2 ^ (j1 + 1) ∣ r1 * (r / r1) := by
          have h1' : 2 ^ (j1 + 1) ∣ 2 ^ j2 := pow_dvd_pow 2 hle
          have h2' : (2 : ℕ) ^ j2 ∣ r := dvd_trans h2.1 (Nat.dvd_lcm_right _ _)
          have h3 : (2 : ℕ) ^ (j1 + 1) ∣ r := dvd_trans h1' h2'
          rwa [hm1] at h3
        have hd2 : 2 ∣ r / r1 := two_dvd_cofactor h1 h2k
        exact (Nat.not_even_iff_odd.mpr hC1.1) (even_iff_two_dvd.mpr hd2)
      · exact heq
      · exfalso
        have hle : j2 + 1 ≤ j1 := by omega
        have h2k : 2 ^ (j2 + 1) ∣ r2 * (r / r2) := by
          have h1' : 2 ^ (j2 + 1) ∣ 2 ^ j1 := pow_dvd_pow 2 hle
          have h2' : (2 : ℕ) ^ j1 ∣ r := dvd_trans h1.1 (Nat.dvd_lcm_left _ _)
          have h3 : (2 : ℕ) ^ (j2 + 1) ∣ r := dvd_trans h1' h2'
          rwa [hm2] at h3
        have hd2 : 2 ∣ r / r2 := two_dvd_cofactor h2 h2k
        exact (Nat.not_even_iff_odd.mpr hC2.1) (even_iff_two_dvd.mpr hd2)
  · intro heq
    subst heq
    by_cases hj : j1 = 0
    · subst hj
      have h2r1 : ¬ 2 ∣ r1 := by simpa using h1.2
      have h2r2 : ¬ 2 ∣ r2 := by simpa using h2.2
      have h2r : ¬ 2 ∣ r := by
        intro hd
        have hd' : (2 : ℕ) ^ 1 ∣ r := by simpa using hd
        have := (two_pow_dvd_lcm_iff hr1 hr2).mp hd'
        rcases this with h | h
        · exact h2r1 (by simpa using h)
        · exact h2r2 (by simpa using h)
      exact Or.inl (Nat.not_even_iff_odd.mp (fun he => h2r (even_iff_two_dvd.mp he)))
    · have hpos : 1 ≤ j1 := Nat.pos_of_ne_zero hj
      have hevr1 : Even r1 := by
        apply even_iff_two_dvd.mpr
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ∣ 2 ^ j1 := pow_dvd_pow 2 hpos
        _ ∣ r1 := h1.1
      have hevr2 : Even r2 := by
        apply even_iff_two_dvd.mpr
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ∣ 2 ^ j1 := pow_dvd_pow 2 hpos
        _ ∣ r2 := h2.1
      have hevr : Even r :=
        even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hevr1) (Nat.dvd_lcm_left _ _))
      have hm1odd : Odd (r / r1) := by
        by_contra hcon
        rcases Nat.even_or_odd (r / r1) with hevm | hom
        · have h2m : 2 ∣ r / r1 := even_iff_two_dvd.mp hevm
          have hdvd : 2 ^ (j1 + 1) ∣ r := by
            have hmul : 2 ^ j1 * 2 ∣ r1 * (r / r1) := mul_dvd_mul h1.1 h2m
            rw [← pow_succ, ← hm1] at hmul
            exact hmul
          have := (two_pow_dvd_lcm_iff hr1 hr2).mp hdvd
          rcases this with h | h
          · exact absurd h h1.2
          · exact absurd h h2.2
        · exact absurd hom hcon
      have hm2odd : Odd (r / r2) := by
        by_contra hcon
        rcases Nat.even_or_odd (r / r2) with hevm | hom
        · have h2m : 2 ∣ r / r2 := even_iff_two_dvd.mp hevm
          have hdvd : 2 ^ (j1 + 1) ∣ r := by
            have hmul : 2 ^ j1 * 2 ∣ r2 * (r / r2) := mul_dvd_mul h2.1 h2m
            rw [← pow_succ, ← hm2] at hmul
            exact hmul
          have := (two_pow_dvd_lcm_iff hr1 hr2).mp hdvd
          rcases this with h | h
          · exact absurd h h1.2
          · exact absurd h h2.2
        · exact absurd hom hcon
      have hx : x ^ (r / 2) = -1 := comp_pow_half_eq_neg_one_of x hm1 hevr hm1odd hevr1
      have hy : y ^ (r / 2) = -1 := comp_pow_half_eq_neg_one_of y hm2 hevr hm2odd hevr2
      exact Or.inr ⟨hx, hy⟩

/-- A fiber of a power map is no larger than its kernel. -/
private theorem fiber_pow_card_le {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (e : ℕ) (c : G) :
    (Finset.univ.filter (fun x : G => x ^ e = c)).card ≤
      (Finset.univ.filter (fun x : G => x ^ e = 1)).card := by
  by_cases hne : ∃ x, x ^ e = c
  · obtain ⟨x0, hx0⟩ := hne
    have hsub : (Finset.univ.filter (fun x : G => x ^ e = c)).image (fun y => x0⁻¹ * y)
        ⊆ Finset.univ.filter (fun x : G => x ^ e = 1) := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mul_pow, inv_pow, hx0, hy, inv_mul_cancel]
    have hinj : Function.Injective (fun y : G => x0⁻¹ * y) := by
      intro a b hab
      exact mul_left_cancel hab
    calc (Finset.univ.filter (fun x : G => x ^ e = c)).card
        = ((Finset.univ.filter (fun x : G => x ^ e = c)).image (fun y => x0⁻¹ * y)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.univ.filter (fun x : G => x ^ e = 1)).card := Finset.card_le_card hsub
  · have hempty : Finset.univ.filter (fun x : G => x ^ e = c) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
      exact ⟨fun hy => hne ⟨y, hy⟩, fun h => h.elim⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- The kernel of a power map on `(ZMod p)ˣ` has at most `e` elements. -/
private theorem units_pow_eq_one_card_le {p : ℕ} [Fact p.Prime] {e : ℕ} (he : 1 ≤ e) :
    (Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ e = 1)).card ≤ e := by
  set P : Polynomial (ZMod p) := Polynomial.X ^ e - Polynomial.C 1 with hP
  have hP0 : P ≠ 0 := by
    have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C 1 (by omega : e ≠ 0)
    exact hmonic.ne_zero
  have hdeg : P.natDegree = e := Polynomial.natDegree_X_pow_sub_C
  have hsub : ((Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ e = 1)).image
      (fun x : (ZMod p)ˣ => (x : ZMod p))) ⊆ P.roots.toFinset := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have hx' : (x : ZMod p) ^ e = 1 := by
      have hcon := congrArg Units.val hx
      simpa using hcon
    rw [hx', sub_self]
  have hinj : Function.Injective (fun x : (ZMod p)ˣ => (x : ZMod p)) :=
    fun a b hab => Units.ext hab
  calc (Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ e = 1)).card
      = (((Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ e = 1)).image
        (fun x : (ZMod p)ˣ => (x : ZMod p)))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = e := hdeg

/-- An odd divisor of `t = 2^s * m` divides `m`. -/
private theorem odd_dvd_of_dvd_pred {t s m d : ℕ} (hpm : t = 2 ^ s * m)
    (hodd : Odd d) (hd : d ∣ t) : d ∣ m := by
  have h2n : ¬ 2 ∣ d := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hcop : d.Coprime 2 :=
    Nat.coprime_comm.mp ((Nat.prime_two).coprime_iff_not_dvd.mpr h2n)
  have hcop2 : Nat.Coprime 2 d := Nat.coprime_comm.mp hcop
  have hcop3 : Nat.Coprime (2 ^ s) d := hcop2.pow_left s
  have hcop' : d.Coprime (2 ^ s) := Nat.coprime_comm.mp hcop3
  have h1 : d ∣ 2 ^ s * m := by rw [← hpm]; exact hd
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop' h1

/-- Each exact 2-level occupies at most half of `(ZMod p)ˣ`. -/
private theorem level_card_le {p : ℕ} [Fact p.Prime] (hp : p.Prime) {s m : ℕ}
    (hodd : Odd m) (hs : 1 ≤ s) (hpm : p - 1 = 2 ^ s * m) (j : ℕ) :
    2 * (Finset.univ.filter (fun x : (ZMod p)ˣ =>
      2 ^ j ∣ orderOf x ∧ ¬ 2 ^ (j + 1) ∣ orderOf x)).card ≤ p - 1 := by
  have hnpos : p ≠ 0 := hp.ne_zero
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    have h := @ZMod.card_units_eq_totient p ⟨hnpos⟩ inferInstance
    rw [h, Nat.totient_prime hp]
  have hmpos : 1 ≤ m := hodd.pos
  have hmodd2 : ¬ 2 ∣ m :=
    fun hd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  have hcop2m : Nat.Coprime 2 m := (Nat.prime_two).coprime_iff_not_dvd.mpr hmodd2
  have hord_dvd : ∀ x : (ZMod p)ˣ, orderOf x ∣ p - 1 := fun x => by
    rw [← hcard]; exact orderOf_dvd_card
  cases j with
  | zero =>
    have hsub : Finset.univ.filter (fun x : (ZMod p)ˣ =>
          2 ^ 0 ∣ orderOf x ∧ ¬ 2 ^ (0 + 1) ∣ orderOf x)
        ⊆ Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ m = 1) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have h2n : ¬ 2 ∣ orderOf x := by simpa using hx.2
      have hodd' : Odd (orderOf x) :=
        Nat.not_even_iff_odd.mp (fun he => h2n (even_iff_two_dvd.mp he))
      have hdvd : orderOf x ∣ m := odd_dvd_of_dvd_pred hpm hodd' (hord_dvd x)
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have h2s : (2 : ℕ) ≤ 2 ^ s := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    calc 2 * (Finset.univ.filter (fun x : (ZMod p)ˣ =>
            2 ^ 0 ∣ orderOf x ∧ ¬ 2 ^ (0 + 1) ∣ orderOf x)).card
        ≤ 2 * (Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ m = 1)).card :=
          Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)
      _ ≤ 2 * m := Nat.mul_le_mul_left 2 (units_pow_eq_one_card_le hmpos)
      _ ≤ 2 ^ s * m := Nat.mul_le_mul_right m h2s
      _ = p - 1 := hpm.symm
  | succ j' =>
    by_cases hle : j' + 1 ≤ s
    · have hsub : Finset.univ.filter (fun x : (ZMod p)ˣ =>
            2 ^ (j' + 1) ∣ orderOf x ∧ ¬ 2 ^ (j' + 1 + 1) ∣ orderOf x)
          ⊆ Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ (2 ^ j' * m) = -1) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have h2e : (x ^ (2 ^ j' * m)) ^ 2 = 1 := by
          have e2 : 2 * (2 ^ j' * m) = 2 ^ (j' + 1) * m := by rw [pow_succ']; ring
          have hdvd : orderOf x ∣ 2 ^ (j' + 1) * m := by
            obtain ⟨o, ho⟩ := hx.1
            have ho_odd : Odd o := by
              by_contra hcon
              rcases Nat.even_or_odd o with hevo | hoo
              · obtain ⟨t, ht⟩ := even_iff_two_dvd.mp hevo
                have hcon' : 2 ^ (j' + 1 + 1) ∣ orderOf x := by
                  rw [pow_succ, ho, ht]
                  exact mul_dvd_mul_left (2 ^ (j' + 1)) (dvd_mul_right 2 t)
                exact absurd hcon' hx.2
              · exact absurd hoo hcon
            have ho_pred : o ∣ p - 1 :=
              dvd_trans (by rw [ho]; exact dvd_mul_left o _) (hord_dvd x)
            have hodvd : o ∣ m := odd_dvd_of_dvd_pred hpm ho_odd ho_pred
            obtain ⟨c, hc⟩ := hodvd
            exact ⟨c, by rw [ho, hc]; ring⟩
          have e3 : (2 ^ j' * m) * 2 = 2 * (2 ^ j' * m) := mul_comm _ _
          calc (x ^ (2 ^ j' * m)) ^ 2 = x ^ ((2 ^ j' * m) * 2) := (pow_mul x _ 2).symm
          _ = x ^ (2 * (2 ^ j' * m)) := by rw [e3]
          _ = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [e2]; exact hdvd)
        have hne1 : x ^ (2 ^ j' * m) ≠ 1 := by
          intro hcon
          have hd : orderOf x ∣ 2 ^ j' * m := orderOf_dvd_iff_pow_eq_one.mpr hcon
          have hd2 : 2 ^ (j' + 1) ∣ 2 ^ j' * m := dvd_trans hx.1 hd
          have hd3 : 2 ^ j' * 2 ∣ 2 ^ j' * m := by rwa [pow_succ] at hd2
          obtain ⟨t, ht⟩ := hd3
          have hpos : 0 < 2 ^ j' := pow_pos (by norm_num) j'
          have hm2 : m = 2 * t := by
            have h' : 2 ^ j' * m = 2 ^ j' * (2 * t) := by rw [ht]; ring
            exact Nat.mul_left_cancel hpos h'
          exact hmodd2 ⟨t, hm2⟩
        have hcase := sq_eq_one_units (x ^ (2 ^ j' * m)) h2e
        rcases hcase with h1 | h1
        · exact absurd h1 hne1
        · exact h1
      have hepos : 1 ≤ 2 ^ j' * m := by
        have h1 : 0 < 2 ^ j' * m :=
          mul_pos (pow_pos (by norm_num) j') (by omega : 0 < m)
        omega
      have hle2 : 2 ^ (j' + 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hle
      have e : 2 * (2 ^ j' * m) = 2 ^ (j' + 1) * m := by rw [pow_succ']; ring
      calc 2 * (Finset.univ.filter (fun x : (ZMod p)ˣ =>
              2 ^ (j' + 1) ∣ orderOf x ∧ ¬ 2 ^ (j' + 1 + 1) ∣ orderOf x)).card
          ≤ 2 * (Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ (2 ^ j' * m) = -1)).card :=
            Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)
        _ ≤ 2 * (2 ^ j' * m) :=
            Nat.mul_le_mul_left 2 (le_trans (fiber_pow_card_le _ _) (units_pow_eq_one_card_le hepos))
        _ ≤ 2 ^ s * m := by rw [e]; exact Nat.mul_le_mul_right m hle2
        _ = p - 1 := hpm.symm
    · have hempty : Finset.univ.filter (fun x : (ZMod p)ˣ =>
            2 ^ (j' + 1) ∣ orderOf x ∧ ¬ 2 ^ (j' + 1 + 1) ∣ orderOf x) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
        constructor
        · rintro ⟨hdvd, -⟩
          exfalso
          have hd1 : 2 ^ (j' + 1) ∣ 2 ^ s * m := by
            rw [← hpm]; exact dvd_trans hdvd (hord_dvd x)
          have hcop : Nat.Coprime (2 ^ (j' + 1)) m := hcop2m.pow_left (j' + 1)
          have hd2 : 2 ^ (j' + 1) ∣ 2 ^ s :=
            Nat.Coprime.dvd_of_dvd_mul_right hcop hd1
          have hle' : j' + 1 ≤ s :=
            (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2
          exact absurd hle' hle
        · intro h; exact h.elim
      rw [hempty, Finset.card_empty, mul_zero]
      exact Nat.zero_le _

/-- Exact 2-levels are unique. -/
private theorem two_level_unique {n j1 j2 : ℕ}
    (h1 : 2 ^ j1 ∣ n ∧ ¬ 2 ^ (j1 + 1) ∣ n)
    (h2 : 2 ^ j2 ∣ n ∧ ¬ 2 ^ (j2 + 1) ∣ n) : j1 = j2 := by
  rcases lt_trichotomy j1 j2 with hlt | heq | hgt
  · exfalso
    exact h1.2 (dvd_trans (pow_dvd_pow 2 (by omega : j1 + 1 ≤ j2)) h2.1)
  · exact heq
  · exfalso
    exact h2.2 (dvd_trans (pow_dvd_pow 2 (by omega : j2 + 1 ≤ j1)) h1.1)

/-- A pair is good iff the second component avoids the first's 2-level. -/
private theorem pair_good_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ)
    (hne1 : (-1 : (ZMod p)ˣ) ≠ 1) (hne2 : (-1 : (ZMod q)ˣ) ≠ 1)
    {j1 : ℕ} (h1 : 2 ^ j1 ∣ orderOf x ∧ ¬ 2 ^ (j1 + 1) ∣ orderOf x) :
    (Even (orderOf (x, y)) ∧ (x, y) ^ (orderOf (x, y) / 2) ≠ -1) ↔
      ¬ (2 ^ j1 ∣ orderOf y ∧ ¬ 2 ^ (j1 + 1) ∣ orderOf y) := by
  obtain ⟨j2, hj2⟩ := two_level_exists (ne_of_gt (orderOf_pos y))
  have hbad := bad_iff_levels_eq x y h1 hj2 hne1 hne2
  have hord : orderOf (x, y) = Nat.lcm (orderOf x) (orderOf y) := Prod.orderOf_mk
  have hpp : ((x, y) ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1) ↔
      (x ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1 ∧
       y ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1) := by
    have e1 : ((x, y) ^ (Nat.lcm (orderOf x) (orderOf y) / 2)).1 =
        x ^ (Nat.lcm (orderOf x) (orderOf y) / 2) :=
      map_pow (MonoidHom.fst _ _) (x, y) _
    have e2 : ((x, y) ^ (Nat.lcm (orderOf x) (orderOf y) / 2)).2 =
        y ^ (Nat.lcm (orderOf x) (orderOf y) / 2) :=
      map_pow (MonoidHom.snd _ _) (x, y) _
    have n1 : (-1 : (ZMod p)ˣ × (ZMod q)ˣ).1 = -1 := rfl
    have n2 : (-1 : (ZMod p)ˣ × (ZMod q)ˣ).2 = -1 := rfl
    rw [Prod.ext_iff, e1, e2, n1, n2]
  rw [hord]
  have huniq : (2 ^ j1 ∣ orderOf y ∧ ¬ 2 ^ (j1 + 1) ∣ orderOf y) ↔ j1 = j2 :=
    ⟨fun h => two_level_unique h hj2, fun heq => by subst heq; exact hj2⟩
  rw [huniq]
  constructor
  · rintro ⟨hev, hne⟩ heq
    subst heq
    have hbad' := hbad.mpr rfl
    rcases hbad' with ho | ⟨hx, hy⟩
    · exact (Nat.not_even_iff_odd.mpr ho) hev
    · apply hne
      rw [hpp]
      exact ⟨hx, hy⟩
  · intro hne12
    have hbad' : ¬ (Odd (Nat.lcm (orderOf x) (orderOf y)) ∨
        (x ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1 ∧
         y ^ (Nat.lcm (orderOf x) (orderOf y) / 2) = -1)) :=
      fun h => hne12 (hbad.mp h)
    have hev : Even (Nat.lcm (orderOf x) (orderOf y)) := by
      by_contra hcon
      exact hbad' (Or.inl (Nat.not_even_iff_odd.mp hcon))
    have hne : (x, y) ^ (Nat.lcm (orderOf x) (orderOf y) / 2) ≠ -1 := by
      intro hcon
      exact hbad' (Or.inr (hpp.mp hcon))
    exact ⟨hev, hne⟩

/-- Counting a filter on a product by rows. -/
private theorem card_filter_product_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (Q : α × β → Prop) [DecidablePred Q] [∀ x, DecidablePred (fun y => Q (x, y))] :
    ((Finset.univ ×ˢ Finset.univ).filter Q).card =
      ∑ x : α, (Finset.univ.filter (fun y => Q (x, y))).card := by
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

/-- Shor good-unit density (two-prime case, counting form). Let
`N = p * q` with `p`, `q` distinct odd primes. For a uniform random
unit `a` modulo `N`, let `r` be the multiplicative order of `a`.
Then at least half of the units have `r` even and
`a ^ (r / 2) ≠ -1` in `ZMod N` (such units yield a nontrivial
factor of `N` from `gcd (a^(r/2) ± 1, N)`). Counting form: the
number of good units is at least half of all units. -/
theorem shor_good_units {p q : ℕ} [NeZero (p * q)] (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    (2 : ℝ) * ((Finset.univ.filter (fun a : (ZMod (p * q))ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℝ) ≥
      ((Finset.univ : Finset (ZMod (p * q))ˣ).card : ℝ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hp3 : 3 ≤ p := by
    have h2le := hp.two_le
    omega
  have hq3 : 3 ≤ q := by
    have h2le := hq.two_le
    omega
  have hne_p : (-1 : (ZMod p)ˣ) ≠ 1 :=
    @units_neg_one_ne_one p ⟨hp.ne_zero⟩ (fun hd => by
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      omega)
  have hne_q : (-1 : (ZMod q)ˣ) ≠ 1 :=
    @units_neg_one_ne_one q ⟨hq.ne_zero⟩ (fun hd => by
      have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      omega)
  obtain ⟨s, m, hmodd, hpm⟩ := Nat.exists_eq_two_pow_mul_odd (show p - 1 ≠ 0 by omega)
  obtain ⟨t, n, hnodd, hqn⟩ := Nat.exists_eq_two_pow_mul_odd (show q - 1 ≠ 0 by omega)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hs : 1 ≤ s := by
    by_contra hcon
    have hs0 : s = 0 := by omega
    subst hs0
    simp only [pow_zero, one_mul] at hpm
    have hev : Even (p - 1) := by
      obtain ⟨k, hk⟩ := hpodd
      exact ⟨k, by omega⟩
    have hevm : Even m := by rw [← hpm]; exact hev
    exact (Nat.not_even_iff_odd.mpr hmodd) hevm
  have ht : 1 ≤ t := by
    by_contra hcon
    have ht0 : t = 0 := by omega
    subst ht0
    simp only [pow_zero, one_mul] at hqn
    have hev : Even (q - 1) := by
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k, by omega⟩
    have hevn : Even n := by rw [← hqn]; exact hev
    exact (Nat.not_even_iff_odd.mpr hnodd) hevn
  have hcard_p : Fintype.card (ZMod p)ˣ = p - 1 := by
    have h := @ZMod.card_units_eq_totient p ⟨hp.ne_zero⟩ inferInstance
    rw [h, Nat.totient_prime hp]
  have hcard_q : Fintype.card (ZMod q)ˣ = q - 1 := by
    have h := @ZMod.card_units_eq_totient q ⟨hq.ne_zero⟩ inferInstance
    rw [h, Nat.totient_prime hq]
  have hcardU : (Finset.univ.filter (fun a : (ZMod (p * q))ˣ =>
        Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card =
      ((Finset.univ ×ˢ Finset.univ).filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
        Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1)).card := by
    apply Finset.card_bij' (fun a _ => crtUnits hcop a)
      (fun z _ => (crtUnits hcop).symm z)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact (good_transfer hcop a).mp ha
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : crtUnits hcop ((crtUnits hcop).symm z) = z :=
        MulEquiv.apply_symm_apply _ _
      rw [← h1] at hz
      exact (good_transfer hcop ((crtUnits hcop).symm z)).mpr hz
    · intro a _
      exact MulEquiv.symm_apply_apply _ _
    · intro z _
      exact MulEquiv.apply_symm_apply _ _
  have htot : ((Finset.univ ×ˢ Finset.univ) :
      Finset ((ZMod p)ˣ × (ZMod q)ˣ)).card = (p - 1) * (q - 1) := by
    rw [Finset.card_product, Finset.card_univ, Finset.card_univ, hcard_p, hcard_q]
  have hPB : ((Finset.univ ×ˢ Finset.univ).filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
        Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1)).card +
      ((Finset.univ ×ˢ Finset.univ).filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
        ¬ (Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1))).card = (p - 1) * (q - 1) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ ×ˢ Finset.univ : Finset ((ZMod p)ˣ × (ZMod q)ˣ)))
      (fun z : (ZMod p)ˣ × (ZMod q)ˣ => Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1)
    rw [htot] at h
    exact h
  have hB : ((Finset.univ ×ˢ Finset.univ).filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
        ¬ (Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1))).card =
      ∑ x : (ZMod p)ˣ, (Finset.univ.filter (fun y : (ZMod q)ˣ =>
        ¬ (Even (orderOf (x, y)) ∧ (x, y) ^ (orderOf (x, y) / 2) ≠ -1))).card :=
    card_filter_product_eq_sum (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
      ¬ (Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1))
  have hper : ∀ x : (ZMod p)ˣ, 2 * (Finset.univ.filter (fun y : (ZMod q)ˣ =>
      ¬ (Even (orderOf (x, y)) ∧ (x, y) ^ (orderOf (x, y) / 2) ≠ -1))).card ≤ q - 1 := by
    intro x
    obtain ⟨j1, hj1⟩ := two_level_exists (ne_of_gt (orderOf_pos x))
    have hfib : Finset.univ.filter (fun y : (ZMod q)ˣ =>
        ¬ (Even (orderOf (x, y)) ∧ (x, y) ^ (orderOf (x, y) / 2) ≠ -1)) =
        Finset.univ.filter (fun y : (ZMod q)ˣ =>
          2 ^ j1 ∣ orderOf y ∧ ¬ 2 ^ (j1 + 1) ∣ orderOf y) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hgood := pair_good_iff x y hne_p hne_q hj1
      rw [hgood]
      exact not_not
    rw [hfib]
    exact level_card_le hq hnodd ht hqn j1
  have h2B : 2 * ((Finset.univ ×ˢ Finset.univ).filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
      ¬ (Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1))).card ≤ (p - 1) * (q - 1) := by
    rw [hB, Finset.mul_sum]
    have hsum : (∑ x : (ZMod p)ˣ, 2 * (Finset.univ.filter (fun y : (ZMod q)ˣ =>
        ¬ (Even (orderOf (x, y)) ∧ (x, y) ^ (orderOf (x, y) / 2) ≠ -1))).card) ≤
        ∑ x : (ZMod p)ˣ, (q - 1) :=
      Finset.sum_le_sum (fun x _ => hper x)
    have hconst : (∑ x : (ZMod p)ˣ, (q - 1)) = (p - 1) * (q - 1) := by
      rw [Finset.sum_const, Finset.card_univ, hcard_p, smul_eq_mul]
    exact le_trans hsum (le_of_eq hconst)
  have htotU : (Finset.univ : Finset (ZMod (p * q))ˣ).card = (p - 1) * (q - 1) := by
    rw [Finset.card_univ, Fintype.card_congr (crtUnits hcop).toEquiv, Fintype.card_prod,
      hcard_p, hcard_q]
  have hmain : (p - 1) * (q - 1) ≤ 2 * ((Finset.univ ×ˢ Finset.univ).filter
      (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
        Even (orderOf z) ∧ z ^ (orderOf z / 2) ≠ -1)).card := by
    omega
  rw [hcardU, htotU]
  exact_mod_cast hmain

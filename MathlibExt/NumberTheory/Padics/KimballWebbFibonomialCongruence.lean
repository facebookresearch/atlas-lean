/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

-- Helper: parity and size facts for rho = p - eps.
private theorem rho_facts (p rho : ℕ) (ε : ℤ) (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε) :
    Odd p ∧ Even rho ∧ 6 ≤ rho ∧ 1 ≤ rho := by
  have hmod : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hodd : Odd p := Nat.odd_iff.mpr hmod
  obtain ⟨t, ht⟩ := hodd
  rcases hε with rfl | rfl
  · have hr : rho = p - 1 := by omega
    subst hr
    exact ⟨Nat.odd_iff.mpr hmod, ⟨t, by omega⟩, by omega, by omega⟩
  · have hr : rho = p + 1 := by omega
    subst hr
    exact ⟨Nat.odd_iff.mpr hmod, (Nat.odd_iff.mpr hmod).add_one, by omega, by omega⟩

-- Helper: (1+y)^m = 1 + m*y when y^2 = 0.
private theorem one_add_pow_of_sq_eq_zero {R : Type*} [CommRing R] (y : R) (hy : y ^ 2 = 0) :
    ∀ m : ℕ, (1 + y) ^ m = 1 + (m : R) * y
  | 0 => by simp
  | m + 1 => by
      have ih := one_add_pow_of_sq_eq_zero y hy m
      calc (1 + y) ^ (m + 1) = (1 + y) ^ m * (1 + y) := by ring
        _ = (1 + (m : R) * y) * (1 + y) := by rw [ih]
        _ = 1 + (((m + 1 : ℕ)) : R) * y := by
            push_cast
            linear_combination (m : R) * hy

-- Helper: t^3 = 0 implies t^4 = 0 and related vanishing (Steps 2-3).
private theorem cube_zero_pow_four (R : Type*) [CommRing R] (t : R) (ht : t ^ 3 = 0) :
    t ^ 4 = 0 := by
  have : t ^ 4 = t * t ^ 3 := by ring
  rw [this, ht, mul_zero]

private theorem cube_zero_sq_mul (R : Type*) [CommRing R] (t z : R) (ht : t ^ 3 = 0) :
    t ^ 2 * (t * z) = 0 := by
  have h : t ^ 2 * (t * z) = t ^ 3 * z := by ring
  rw [h, ht, zero_mul]

-- Helper: (1 + 5b^2)(1 - 5b^2) = 1 when b^4 = 0 (Step 2a unit fact).
private theorem one_add_five_sq_unit (R : Type*) [CommRing R] (b : R) (hb : b ^ 4 = 0) :
    (1 + 5 * b ^ 2) * (1 - 5 * b ^ 2) = 1 := by
  linear_combination (-(25 * hb))

-- Helper: Cassini corollary at even n (Step 2a core identity).
private theorem cassini_even_int (n : ℤ) (heven : Even n) :
    Int.fib (n - 1) ^ 2 + Int.fib (n - 1) * Int.fib n - Int.fib n ^ 2 = 1 := by
  have hcas := Int.fib_succ_mul_fib_pred_sub_fib_sq n
  have hsign : ((-1 : ℤ) ^ n.natAbs) = 1 := by
    have hev : Even n.natAbs := by
      rcases heven with ⟨r, hr⟩
      use r.natAbs
      omega
    exact Even.neg_one_pow hev
  rw [hsign] at hcas
  have hsplit : Int.fib (n + 1) = Int.fib (n - 1) + Int.fib n := by
    have h := Int.fib_add n 1
    simp at h
    linarith
  rw [hsplit] at hcas
  linarith

-- Helper: projection R = ZMod (p^3) -> K = ZMod p.
private def piHom (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num)) (ZMod p)

private theorem piHom_natCast (p a : ℕ) :
    piHom p (a : ZMod (p ^ 3)) = (a : ZMod p) :=
  map_natCast _ _

private theorem piHom_intCast (p : ℕ) (a : ℤ) :
    piHom p (a : ZMod (p ^ 3)) = (a : ZMod p) :=
  map_intCast _ _

private theorem piHom_eq_zero_of_dvd (p a : ℕ) (h : p ∣ a) :
    piHom p (a : ZMod (p ^ 3)) = 0 := by
  rw [piHom_natCast, ZMod.natCast_eq_zero_iff]
  exact h

private theorem piHom_eq_zero_iff_dvd_val (p : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (x : ZMod (p ^ 3)) : piHom p x = 0 ↔ p ∣ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x, piHom_natCast, ZMod.natCast_eq_zero_iff]

private theorem small_exists_mul_p (p : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (x : ZMod (p ^ 3)) (h : piHom p x = 0) :
    ∃ y : ZMod (p ^ 3), x = (p : ZMod (p ^ 3)) * y := by
  rw [piHom_eq_zero_iff_dvd_val] at h
  obtain ⟨q, hq⟩ := h
  exact ⟨(q : ZMod (p ^ 3)), by rw [← ZMod.natCast_zmod_val x, hq, Nat.cast_mul]⟩

private theorem pow_three_prime_pow_eq_zero (p : ℕ) :
    ((p : ZMod (p ^ 3)) ^ 3 = 0) := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private theorem small_triple_eq_zero (p : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (x y z : ZMod (p ^ 3))
    (hx : piHom p x = 0) (hy : piHom p y = 0) (hz : piHom p z = 0) :
    x * y * z = 0 := by
  obtain ⟨x', rfl⟩ := small_exists_mul_p p x hx
  obtain ⟨y', rfl⟩ := small_exists_mul_p p y hy
  obtain ⟨z', rfl⟩ := small_exists_mul_p p z hz
  have h3 := pow_three_prime_pow_eq_zero p
  calc ((p : ZMod (p ^ 3)) * x') * ((p : ZMod (p ^ 3)) * y') *
      ((p : ZMod (p ^ 3)) * z')
      = (p : ZMod (p ^ 3)) ^ 3 * (x' * y' * z') := by ring
    _ = 0 := by rw [h3, zero_mul]

private theorem small_sq_mul_eq (p : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (t z z' : ZMod (p ^ 3)) (ht : piHom p t = 0)
    (hzz : piHom p (z - z') = 0) : t ^ 2 * z = t ^ 2 * z' := by
  have htri : t * t * (z - z') = 0 :=
    small_triple_eq_zero p t t (z - z') ht ht hzz
  have hcon : t ^ 2 * (z - z') = 0 := by
    have heq : t ^ 2 * (z - z') = t * t * (z - z') := by ring
    rw [heq, htri]
  have hsub : t ^ 2 * z - t ^ 2 * z' = 0 := by
    rw [← mul_sub, hcon]
  exact sub_eq_zero.mp hsub

private theorem fib_unit_R (p rho i : ℕ) (hp : Nat.Prime p)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hi0 : 0 < i) (hiR : i < rho) :
    IsUnit ((Nat.fib i : ℕ) : ZMod (p ^ 3)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (by norm_num)]
  exact hmin i hi0 hiR

private theorem fib_ne_zero_K (p rho i : ℕ)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hi0 : 0 < i) (hiR : i < rho) :
    ((Nat.fib i : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact hmin i hi0 hiR h

private theorem two_unit_R (p : ℕ) (hodd : Odd p) :
    IsUnit ((2 : ℕ) : ZMod (p ^ 3)) := by
  rw [ZMod.isUnit_prime_iff_not_dvd Nat.prime_two]
  exact hodd.pow.not_two_dvd_nat

private theorem prod_one_add_t_mul {R : Type*} [CommRing R] {ι : Type*}
    (t h : R) (ht : t ^ 3 = 0) (hh : 2 * h = 1)
    (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + t * f i)
      = 1 + t * (∑ i ∈ s, f i)
        + t ^ 2 * h * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    linear_combination
      (h * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2) * f a) * ht
      - (t ^ 2 * (∑ i ∈ s, f i) * f a) * hh

-- Helper: Fibonomial integrality. D(j) = prod_{i<j} F(i+1) divides P(m,j).
private theorem fib_shift_prod_dvd : ∀ (m j : ℕ),
    (Finset.prod (Finset.range j) (fun i => Nat.fib (i + 1))) ∣
      (Finset.prod (Finset.range j) (fun i => Nat.fib (m + i + 1))) := by
  intro m
  induction m with
  | zero =>
    intro j
    simp only [Nat.zero_add]
    exact dvd_refl _
  | succ m ihm =>
    intro j
    induction j with
    | zero => exact dvd_refl _
    | succ j ihj =>
      have hD : (Finset.prod (Finset.range (j + 1)) (fun i => Nat.fib (i + 1)))
          = (Finset.prod (Finset.range j) (fun i => Nat.fib (i + 1))) * Nat.fib (j + 1) :=
        Finset.prod_range_succ _ _
      -- key fib identity at (m+1, j): F_{m+j+2} = F_{m+1} F_j + F_{m+2} F_{j+1}
      have hfib : Nat.fib (m + 1 + j + 1) =
          Nat.fib (m + 1) * Nat.fib j + Nat.fib (m + 2) * Nat.fib (j + 1) := by
        have h := Nat.fib_add (m + 1) j
        have heq : m + 1 + j + 1 = (m + 1) + j + 1 := by ring
        rw [heq, h]
      -- peel the last factor off P(m+1, j+1)
      have hPs : (Finset.prod (Finset.range (j + 1)) (fun i => Nat.fib (m + 1 + i + 1)))
          = (Finset.prod (Finset.range j) (fun i => Nat.fib (m + 1 + i + 1))) *
            Nat.fib (m + 1 + j + 1) :=
        Finset.prod_range_succ _ _
      -- peel the first factor off P(m, j+1): P(m,j+1) = Pshift * F_{m+1}
      have hshift : (Finset.prod (Finset.range (j + 1)) (fun i => Nat.fib (m + i + 1)))
          = (Finset.prod (Finset.range j) (fun k => Nat.fib (m + (k + 1) + 1))) *
            Nat.fib (m + 1) :=
        Finset.prod_range_succ' _ _
      have hshift2 : (Finset.prod (Finset.range j) (fun k => Nat.fib (m + (k + 1) + 1)))
          = (Finset.prod (Finset.range j) (fun i => Nat.fib (m + 1 + i + 1))) :=
        Finset.prod_congr rfl (fun i _ => by congr 1; omega)
      have hP : (Finset.prod (Finset.range (j + 1)) (fun i => Nat.fib (m + 1 + i + 1)))
          = Nat.fib j *
              (Finset.prod (Finset.range (j + 1)) (fun i => Nat.fib (m + i + 1)))
            + Nat.fib (m + 2) * Nat.fib (j + 1) *
              (Finset.prod (Finset.range j) (fun i => Nat.fib (m + 1 + i + 1))) := by
        rw [hPs, hfib, hshift, hshift2]
        ring
      obtain ⟨a, ha⟩ := ihm (j + 1)
      obtain ⟨b, hb⟩ := ihj
      rw [hD] at ha
      have hd1 : (Finset.prod (Finset.range j) (fun i => Nat.fib (i + 1))) * Nat.fib (j + 1) ∣
          Nat.fib j * (Finset.prod (Finset.range (j + 1)) (fun i => Nat.fib (m + i + 1))) :=
        ⟨Nat.fib j * a, by rw [ha]; ring⟩
      have hd2 : (Finset.prod (Finset.range j) (fun i => Nat.fib (i + 1))) * Nat.fib (j + 1) ∣
          Nat.fib (m + 2) * Nat.fib (j + 1) *
            (Finset.prod (Finset.range j) (fun i => Nat.fib (m + 1 + i + 1))) :=
        ⟨Nat.fib (m + 2) * b, by rw [hb]; ring⟩
      rw [hP, hD]
      exact dvd_add hd1 hd2

private theorem fib_add_shift (n i : ℕ) (hn : 1 ≤ n) :
    Nat.fib (n + i) = Nat.fib (n - 1) * Nat.fib i + Nat.fib n * Nat.fib (i + 1) := by
  have h := Nat.fib_add (n - 1) i
  have heq1 : n - 1 + i + 1 = n + i := by omega
  have heq2 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [heq1, heq2] at h
  exact h

private theorem fib_add_shift_R (p n i : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (n + i) : ZMod (p ^ 3))
      = (Nat.fib (n - 1) : ZMod (p ^ 3)) * (Nat.fib i : ZMod (p ^ 3))
        + (Nat.fib n : ZMod (p ^ 3)) * (Nat.fib (i + 1) : ZMod (p ^ 3)) := by
  have h := fib_add_shift n i hn
  calc (Nat.fib (n + i) : ZMod (p ^ 3))
      = ((Nat.fib (n - 1) * Nat.fib i + Nat.fib n * Nat.fib (i + 1) : ℕ)
        : ZMod (p ^ 3)) := by rw [h]
    _ = (Nat.fib (n - 1) : ZMod (p ^ 3)) * (Nat.fib i : ZMod (p ^ 3))
        + (Nat.fib n : ZMod (p ^ 3)) * (Nat.fib (i + 1) : ZMod (p ^ 3)) := by
      push_cast
      ring

private theorem cassini_even_R (p n : ℕ) (heven : Even n) (hn : 1 ≤ n) :
    (((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3)) ^ 2
      + (((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3)) * (((Nat.fib n : ℕ)) : ZMod (p ^ 3))
      - (((Nat.fib n : ℕ)) : ZMod (p ^ 3)) ^ 2 = 1 := by
  have hevenZ : Even (n : ℤ) := by
    obtain ⟨r, hr⟩ := heven
    exact ⟨(r : ℤ), by rw [hr, Nat.cast_add]⟩
  have hcas := cassini_even_int (n : ℤ) hevenZ
  have hfib_n : Int.fib (n : ℤ) = (Nat.fib n : ℤ) := Int.fib_natCast n
  have hcast_sub : (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 := by
    have h := Nat.cast_sub (R := ℤ) (m := 1) (n := n) hn
    simpa using h
  have hfib_nm1 : Int.fib ((n : ℤ) - 1) = (Nat.fib (n - 1) : ℤ) := by
    rw [← hcast_sub, Int.fib_natCast]
  rw [hfib_nm1, hfib_n] at hcas
  have hR := congrArg (Int.cast : ℤ → ZMod (p ^ 3)) hcas
  push_cast at hR
  exact hR

private theorem fib_split_succ (i j : ℕ) (hij : i ≤ j) :
    Nat.fib (j + 1)
      = Nat.fib (j - i) * Nat.fib i + Nat.fib (j - i + 1) * Nat.fib (i + 1) := by
  have h := Nat.fib_add (j - i) i
  have heq : j - i + i + 1 = j + 1 := by omega
  rw [heq] at h
  exact h

private theorem fib_split (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    Nat.fib j
      = Nat.fib (j - i) * Nat.fib (i - 1) + Nat.fib (j - i + 1) * Nat.fib i := by
  have h := Nat.fib_add (j - i) (i - 1)
  have heq1 : j - i + (i - 1) + 1 = j := by omega
  have heq2 : i - 1 + 1 = i := Nat.sub_add_cancel hi
  rw [heq1, heq2] at h
  exact h

private theorem fib_succ_eq (j : ℕ) (hj : 1 ≤ j) :
    Nat.fib (j + 1) = Nat.fib j + Nat.fib (j - 1) := by
  have hm1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hm2 : j - 1 + 2 = j + 1 := by omega
  have h := Nat.fib_add_two (n := j - 1)
  rw [hm1, hm2] at h
  exact h.trans (Nat.add_comm _ _)

private theorem fib_pair_nat (rho i : ℕ) (hiR : i < rho) :
    Nat.fib rho
      = Nat.fib i * Nat.fib (rho - i - 1) + Nat.fib (i + 1) * Nat.fib (rho - i) := by
  have h := Nat.fib_add i (rho - i - 1)
  have heq1 : i + (rho - i - 1) + 1 = rho := by omega
  have heq2 : rho - i - 1 + 1 = rho - i := by omega
  rw [heq1, heq2] at h
  exact h

private theorem fib_succ_split (rho i : ℕ) (hiR : i < rho) :
    Nat.fib (rho - i + 1) = Nat.fib (rho - i) + Nat.fib (rho - i - 1) := by
  have hm1 : rho - i - 1 + 1 = rho - i := by omega
  have hm2 : rho - i - 1 + 2 = rho - i + 1 := by omega
  have h := Nat.fib_add_two (n := rho - i - 1)
  rw [hm1, hm2] at h
  exact h.trans (Nat.add_comm _ _)

private theorem cassini_K (p i : ℕ) :
    ((((Nat.fib (i + 1) : ℕ)) : ZMod p)) ^ 2
      - ((((Nat.fib (i + 1) : ℕ)) : ZMod p)) * ((((Nat.fib i : ℕ)) : ZMod p))
      - ((((Nat.fib i : ℕ)) : ZMod p)) ^ 2 = (-1 : ZMod p) ^ i := by
  have hcas := Int.fib_succ_mul_fib_pred_sub_fib_sq (i : ℤ)
  have hsplit : Int.fib ((i : ℤ) + 1) = Int.fib ((i : ℤ) - 1) + Int.fib (i : ℤ) := by
    have h := Int.fib_add_two ((i : ℤ) - 1)
    have e1 : ((i : ℤ) - 1) + 2 = (i : ℤ) + 1 := by ring
    have e2 : ((i : ℤ) - 1) + 1 = (i : ℤ) := by ring
    rw [e1, e2] at h
    exact h
  have hgoal_int : Int.fib ((i : ℤ) + 1) ^ 2
      - Int.fib ((i : ℤ) + 1) * Int.fib (i : ℤ) - Int.fib (i : ℤ) ^ 2
      = (-1 : ℤ) ^ (i : ℤ).natAbs := by
    linear_combination hcas + Int.fib ((i : ℤ) + 1) * hsplit
  have hcast1 : (i : ℤ) + 1 = (((i + 1 : ℕ)) : ℤ) := by push_cast; ring
  have hfib1 : Int.fib ((i : ℤ) + 1) = (Nat.fib (i + 1) : ℤ) := by
    rw [hcast1, Int.fib_natCast]
  have hfib0 : Int.fib (i : ℤ) = (Nat.fib i : ℤ) := Int.fib_natCast i
  have hnat : (i : ℤ).natAbs = i := rfl
  rw [hfib1, hfib0, hnat] at hgoal_int
  have hR := congrArg (Int.cast : ℤ → ZMod p) hgoal_int
  push_cast at hR
  exact hR

private theorem cassini_mul_K (p i : ℕ) (hi : 1 ≤ i) :
    ((((Nat.fib (i + 1) : ℕ)) : ZMod p)) * ((((Nat.fib (i - 1) : ℕ)) : ZMod p))
      - ((((Nat.fib i : ℕ)) : ZMod p)) ^ 2 = (-1 : ZMod p) ^ i := by
  have hcas := Int.fib_succ_mul_fib_pred_sub_fib_sq (i : ℤ)
  have hfib1 : Int.fib ((i : ℤ) + 1) = (Nat.fib (i + 1) : ℤ) := by
    have hcast1 : (i : ℤ) + 1 = (((i + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [hcast1, Int.fib_natCast]
  have hfib0 : Int.fib (i : ℤ) = (Nat.fib i : ℤ) := Int.fib_natCast i
  have hcast_sub : (((i - 1 : ℕ)) : ℤ) = (i : ℤ) - 1 := by
    have h := Nat.cast_sub (R := ℤ) (m := 1) (n := i) hi
    simpa using h
  have hfibm1 : Int.fib ((i : ℤ) - 1) = (Nat.fib (i - 1) : ℤ) := by
    rw [← hcast_sub, Int.fib_natCast]
  have hnat : (i : ℤ).natAbs = i := rfl
  rw [hfib1, hfibm1, hfib0, hnat] at hcas
  have hR := congrArg (Int.cast : ℤ → ZMod p) hcas
  push_cast at hR
  exact hR

private theorem docagne_K (p i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
    ((((Nat.fib (j + 1) : ℕ)) : ZMod p)) * ((((Nat.fib i : ℕ)) : ZMod p))
      - ((((Nat.fib (i + 1) : ℕ)) : ZMod p)) * ((((Nat.fib j : ℕ)) : ZMod p))
      = (-1 : ZMod p) ^ (i + 1) * ((((Nat.fib (j - i) : ℕ)) : ZMod p)) := by
  have hNat1 := fib_split_succ i j hij
  have h1 : ((((Nat.fib (j + 1) : ℕ)) : ZMod p))
      = ((((Nat.fib (j - i) : ℕ)) : ZMod p))
        * ((((Nat.fib i : ℕ)) : ZMod p))
        + ((((Nat.fib (j - i + 1) : ℕ)) : ZMod p))
        * ((((Nat.fib (i + 1) : ℕ)) : ZMod p)) := by
    have hR := congrArg (Nat.cast : ℕ → ZMod p) hNat1
    push_cast at hR
    exact hR
  have hNat2 := fib_split i j hi hij
  have h2 : ((((Nat.fib j : ℕ)) : ZMod p))
      = ((((Nat.fib (j - i) : ℕ)) : ZMod p))
        * ((((Nat.fib (i - 1) : ℕ)) : ZMod p))
        + ((((Nat.fib (j - i + 1) : ℕ)) : ZMod p))
        * ((((Nat.fib i : ℕ)) : ZMod p)) := by
    have hR := congrArg (Nat.cast : ℕ → ZMod p) hNat2
    push_cast at hR
    exact hR
  have hcas := cassini_mul_K p i hi
  have hpow : (-1 : ZMod p) ^ (i + 1) + (-1 : ZMod p) ^ i = 0 := by
    rw [pow_succ]
    ring
  linear_combination (((Nat.fib i : ℕ)) : ZMod p) * h1
    - (((Nat.fib (i + 1) : ℕ)) : ZMod p) * h2
    - (((Nat.fib (j - i) : ℕ)) : ZMod p) * hcas
    - (((Nat.fib (j - i) : ℕ)) : ZMod p) * hpow

private def qFun (p i : ℕ) : ZMod p :=
  (((Nat.fib (i + 1) : ℕ)) : ZMod p) * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹

private def gFun (p : ℕ) (x : ZMod p) : ZMod p :=
  x ^ 2 - x - 1

private theorem q_injective (p rho i j : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hi0 : 0 < i) (hiR : i < rho) (hj0 : 0 < j) (hjR : j < rho)
    (hij : i < j) : qFun p i ≠ qFun p j := by
  intro heq
  have hne_i : ((((Nat.fib i : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho i hmin hi0 hiR
  have hne_j : ((((Nat.fib j : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho j hmin hj0 hjR
  have hdiv : ((((Nat.fib (i + 1) : ℕ)) : ZMod p))
      / ((((Nat.fib i : ℕ)) : ZMod p))
      = ((((Nat.fib (j + 1) : ℕ)) : ZMod p))
      / ((((Nat.fib j : ℕ)) : ZMod p)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    unfold qFun at heq
    exact heq
  rw [div_eq_div_iff hne_i hne_j] at hdiv
  have hdoc := docagne_K p i j hi0 hij.le
  have hzero : ((((Nat.fib (j + 1) : ℕ)) : ZMod p))
      * ((((Nat.fib i : ℕ)) : ZMod p))
      - ((((Nat.fib (i + 1) : ℕ)) : ZMod p))
      * ((((Nat.fib j : ℕ)) : ZMod p)) = 0 :=
    sub_eq_zero.mpr hdiv.symm
  rw [hzero] at hdoc
  have hneg : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hpow_ne : (-1 : ZMod p) ^ (i + 1) ≠ 0 :=
    pow_ne_zero _ hneg
  have hfib0 : ((((Nat.fib (j - i) : ℕ)) : ZMod p)) = 0 := by
    have hmul : (-1 : ZMod p) ^ (i + 1)
        * ((((Nat.fib (j - i) : ℕ)) : ZMod p)) = 0 := hdoc.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hpow_ne
    · exact h
  have hdvd : p ∣ Nat.fib (j - i) := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact hfib0
  exact hmin (j - i) (by omega) (by omega) hdvd

private def QSet (p rho : ℕ) : Finset (ZMod p) :=
  (Finset.range (rho - 1)).image (fun i => qFun p (i + 1))

private theorem q_rho_sub_one_eq_zero (p rho : ℕ) [Fact p.Prime]
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) :
    qFun p (rho - 1) = 0 := by
  have hEq : rho - 1 + 1 = rho := Nat.sub_add_cancel hrho1
  have hdvd : p ∣ Nat.fib rho := Nat.dvd_of_mod_eq_zero hfib0
  have hzero : ((((Nat.fib rho : ℕ)) : ZMod p)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdvd
  unfold qFun
  have hcast : ((((Nat.fib (rho - 1 + 1) : ℕ)) : ZMod p))
      = ((((Nat.fib rho : ℕ)) : ZMod p)) := by rw [hEq]
  rw [hcast, hzero, zero_mul]

private theorem q_one_eq_one (p : ℕ) [Fact p.Prime] : qFun p 1 = 1 := by
  have h1 : Nat.fib 1 = 1 := rfl
  have h2 : Nat.fib 2 = 1 := rfl
  unfold qFun
  have hcast1 : ((((Nat.fib (1 + 1) : ℕ)) : ZMod p)) = 1 := by
    have : Nat.fib (1 + 1) = 1 := by
      have : (1 + 1 : ℕ) = 2 := rfl
      rw [this, h2]
    rw [this]
    simp
  have hcast2 : ((((Nat.fib 1 : ℕ)) : ZMod p)) = 1 := by
    rw [h1]
    simp
  rw [hcast1, hcast2, inv_one, mul_one]

private theorem zero_mem_Q (p rho : ℕ) [Fact p.Prime]
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    (0 : ZMod p) ∈ QSet p rho := by
  have hmem_range : rho - 2 ∈ Finset.range (rho - 1) :=
    Finset.mem_range.mpr (by omega)
  have hEq : rho - 2 + 1 = rho - 1 := by omega
  have hQ : qFun p (rho - 1) ∈ QSet p rho := by
    unfold QSet
    rw [Finset.mem_image]
    exact ⟨rho - 2, hmem_range, by rw [hEq]⟩
  have h0 := q_rho_sub_one_eq_zero p rho hfib0 hrho1
  rw [h0] at hQ
  exact hQ

private theorem one_mem_Q (p rho : ℕ) [Fact p.Prime] (hrho2 : 2 ≤ rho) :
    (1 : ZMod p) ∈ QSet p rho := by
  have hmem_range : 0 ∈ Finset.range (rho - 1) :=
    Finset.mem_range.mpr (by omega)
  have hQ : qFun p 1 ∈ QSet p rho := by
    unfold QSet
    rw [Finset.mem_image]
    exact ⟨0, hmem_range, rfl⟩
  have h1 := q_one_eq_one p
  rw [h1] at hQ
  exact hQ

private def CSet (p rho : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ \ QSet p rho

private theorem q_mem_Q (p rho j : ℕ) (hj0 : 0 < j) (hjR : j < rho)
    (hrho1 : 1 ≤ rho) : qFun p j ∈ QSet p rho := by
  have hmem_range : j - 1 ∈ Finset.range (rho - 1) :=
    Finset.mem_range.mpr (by omega)
  have hEq : j - 1 + 1 = j := Nat.sub_add_cancel hj0
  unfold QSet
  rw [Finset.mem_image]
  exact ⟨j - 1, hmem_range, by rw [hEq]⟩

private theorem Q_card (p rho : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) : Finset.card (QSet p rho) = rho - 1 := by
  have hinj : Set.InjOn (fun i => qFun p (i + 1)) ↑(Finset.range (rho - 1)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    by_contra hne
    have hne' : a + 1 ≠ b + 1 := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact absurd hab
        (q_injective p rho (a + 1) (b + 1) hmin (Nat.succ_pos a) (by omega)
          (Nat.succ_pos b) (by omega) hlt)
    · exact absurd hab.symm
        (q_injective p rho (b + 1) (a + 1) hmin (Nat.succ_pos b) (by omega)
          (Nat.succ_pos a) (by omega) hgt)
  rw [QSet, Finset.card_image_of_injOn hinj, Finset.card_range]

private theorem C_card (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) :
    Finset.card (CSet p rho) = p - (rho - 1) := by
  unfold CSet
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_univ, ZMod.card, Q_card p rho hmin hrho1]

private theorem q_ne_zero_of_lt (p rho j : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hj0 : 0 < j) (hjR1 : j + 1 < rho) : qFun p j ≠ 0 := by
  have hjR : j < rho := by omega
  have hj10 : 0 < j + 1 := by omega
  have hne_j1 : ((((Nat.fib (j + 1) : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho (j + 1) hmin hj10 hjR1
  have hne_j : ((((Nat.fib j : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho j hmin hj0 hjR
  unfold qFun
  exact mul_ne_zero hne_j1 (inv_ne_zero hne_j)

private def TFun (p : ℕ) (x : ZMod p) : ZMod p :=
  1 + x⁻¹

private theorem q_succ_eq_T (p rho j : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hj2 : 2 ≤ j) (hjR : j < rho) :
    qFun p j = TFun p (qFun p (j - 1)) := by
  have hj1 : 1 ≤ j := by omega
  have hjm1_0 : 0 < j - 1 := by omega
  have hjm1_R : j - 1 < rho := by omega
  have hj0 : 0 < j := by omega
  have hne_j : ((((Nat.fib j : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho j hmin hj0 hjR
  have hne_jm1 : ((((Nat.fib (j - 1) : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho (j - 1) hmin hjm1_0 hjm1_R
  have hNat := fib_succ_eq j hj1
  have hFib : ((((Nat.fib (j + 1) : ℕ)) : ZMod p))
      = ((((Nat.fib j : ℕ)) : ZMod p))
        + ((((Nat.fib (j - 1) : ℕ)) : ZMod p)) := by
    have hR := congrArg (Nat.cast : ℕ → ZMod p) hNat
    push_cast at hR
    exact hR
  have hj_eq : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  have hq_ne : qFun p (j - 1) ≠ 0 := by
    unfold qFun
    rw [hj_eq]
    apply mul_ne_zero hne_j (inv_ne_zero hne_jm1)
  unfold qFun TFun
  rw [hj_eq]
  field_simp
  linear_combination hFib

private theorem T_inj (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    (h : TFun p a = TFun p b) : a = b := by
  unfold TFun at h
  have h2 : a⁻¹ = b⁻¹ := add_left_cancel_iff.mp h
  exact inv_injective h2

private theorem T_mem_C (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (c : ZMod p) (hc : c ∈ CSet p rho) : TFun p c ∈ CSet p rho := by
  have hcQ : c ∉ QSet p rho := by
    unfold CSet at hc
    rw [Finset.mem_sdiff] at hc
    exact hc.2
  have h0Q := zero_mem_Q p rho hfib0 hrho1 hrho2
  have hc_ne : c ≠ 0 := by
    intro h
    rw [h] at hcQ
    exact hcQ h0Q
  have hT_notQ : TFun p c ∉ QSet p rho := by
    intro hTQ
    unfold QSet at hTQ
    rw [Finset.mem_image] at hTQ
    obtain ⟨a, ha_range, ha_eq⟩ := hTQ
    rw [Finset.mem_range] at ha_range
    have hj0 : 0 < a + 1 := Nat.succ_pos a
    have hjR : a + 1 < rho := by omega
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · have hq1 := q_one_eq_one p
      have hTc : TFun p c = 1 := by
        have : qFun p (0 + 1) = TFun p c := ha_eq
        simp only [Nat.zero_add] at this
        rw [hq1] at this
        exact this.symm
      unfold TFun at hTc
      have hinv0 : c⁻¹ = 0 := by
        have hTc' : (1 : ZMod p) + c⁻¹ = 1 + 0 := by
          rw [add_zero]
          exact hTc
        exact add_left_cancel_iff.mp hTc'
      have hc0 : c = 0 := inv_eq_zero.mp hinv0
      exact hc_ne hc0
    · have hj2 : 2 ≤ a + 1 := by omega
      have hqT := q_succ_eq_T p rho (a + 1) hmin hj2 hjR
      have hTeq : TFun p c = TFun p (qFun p (a + 1 - 1)) := by
        rw [← hqT]
        exact ha_eq.symm
      have hc_eq : c = qFun p (a + 1 - 1) := T_inj p c _ hTeq
      have hjm1_0 : 0 < a + 1 - 1 := by omega
      have hjm1_R : a + 1 - 1 < rho := by omega
      have hmem := q_mem_Q p rho (a + 1 - 1) hjm1_0 hjm1_R hrho1
      rw [← hc_eq] at hmem
      exact hcQ hmem
  unfold CSet
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, hT_notQ⟩

private theorem mem_C_ne_zero (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (c : ZMod p) (hc : c ∈ CSet p rho) : c ≠ 0 := by
  have hcQ : c ∉ QSet p rho := by
    unfold CSet at hc
    rw [Finset.mem_sdiff] at hc
    exact hc.2
  have h0Q := zero_mem_Q p rho hfib0 hrho1 hrho2
  intro h
  rw [h] at hcQ
  exact hcQ h0Q

private theorem mem_C_ne_neg_one (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (c : ZMod p) (hc : c ∈ CSet p rho) : c ≠ -1 := by
  have hTc_mem := T_mem_C p rho hmin hfib0 hrho1 hrho2 c hc
  have hTc_ne := mem_C_ne_zero p rho hfib0 hrho1 hrho2 _ hTc_mem
  intro h
  have hT0 : TFun p c = 0 := by
    rw [h]
    unfold TFun
    rw [ZMod.inv_neg_one]
    exact add_neg_cancel _
  rw [hT0] at hTc_ne
  exact hTc_ne rfl

private theorem TT_eq_of_mem_C_two (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (hC2 : Finset.card (CSet p rho) = 2)
    (c : ZMod p) (hc : c ∈ CSet p rho) : TFun p (TFun p c) = c := by
  obtain ⟨x, y, hxy, hC⟩ := Finset.card_eq_two.mp hC2
  have hx_mem : x ∈ CSet p rho := by
    rw [hC]
    exact Finset.mem_insert_self x {y}
  have hy_mem : y ∈ CSet p rho := by
    rw [hC]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have hTx_mem := T_mem_C p rho hmin hfib0 hrho1 hrho2 x hx_mem
  have hTy_mem := T_mem_C p rho hmin hfib0 hrho1 hrho2 y hy_mem
  have hTx_or : TFun p x = x ∨ TFun p x = y := by
    rw [hC] at hTx_mem
    rcases Finset.mem_insert.mp hTx_mem with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hTy_or : TFun p y = x ∨ TFun p y = y := by
    rw [hC] at hTy_mem
    rcases Finset.mem_insert.mp hTy_mem with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hc_or : c = x ∨ c = y := by
    rw [hC] at hc
    rcases Finset.mem_insert.mp hc with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  rcases hc_or with hcr | hcr
  · rw [hcr]
    rcases hTx_or with hTx | hTx
    · rw [hTx]
      exact hTx
    · have hTy : TFun p y = x := by
        rcases hTy_or with h | h
        · exact h
        · exfalso
          have h_eq : TFun p x = TFun p y := by rw [hTx, h]
          exact hxy (T_inj p x y h_eq)
      rw [hTx]
      exact hTy
  · rw [hcr]
    rcases hTy_or with hTy | hTy
    · have hTx : TFun p x = y := by
        rcases hTx_or with h | h
        · exfalso
          have h_eq : TFun p x = TFun p y := by rw [h, hTy]
          exact hxy (T_inj p x y h_eq)
        · exact h
      rw [hTy]
      exact hTx
    · rw [hTy]
      exact hTy

private theorem g_eq_zero_of_mem_C_two (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (hC2 : Finset.card (CSet p rho) = 2)
    (c : ZMod p) (hc : c ∈ CSet p rho) : gFun p c = 0 := by
  have hc_ne := mem_C_ne_zero p rho hfib0 hrho1 hrho2 c hc
  have hc1 := mem_C_ne_neg_one p rho hmin hfib0 hrho1 hrho2 c hc
  have hc1' : c + 1 ≠ 0 := fun h => hc1 (eq_neg_of_add_eq_zero_left h)
  have hTc_mem := T_mem_C p rho hmin hfib0 hrho1 hrho2 c hc
  have hTc_ne := mem_C_ne_zero p rho hfib0 hrho1 hrho2 _ hTc_mem
  have hTT := TT_eq_of_mem_C_two p rho hmin hfib0 hrho1 hrho2 hC2 c hc
  unfold TFun at hTT
  field_simp at hTT
  unfold gFun
  linear_combination -hTT

private theorem telescoping_Q (p rho m : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) :
    m + 1 < rho →
      ∏ i ∈ Finset.range m, qFun p (i + 1)
        = ((((Nat.fib (m + 1) : ℕ)) : ZMod p))
          / ((((Nat.fib 1 : ℕ)) : ZMod p)) := by
  induction m with
  | zero =>
    intro hm
    rw [Finset.prod_range_zero]
    have hne1 : ((((Nat.fib 1 : ℕ)) : ZMod p)) ≠ 0 :=
      fib_ne_zero_K p rho 1 hmin (by omega) (by omega)
    rw [div_self hne1]
  | succ m ihm =>
    intro hm
    have hm' : m + 1 < rho := by omega
    have ih := ihm hm'
    rw [Finset.prod_range_succ, ih]
    have hne_m1 : ((((Nat.fib (m + 1) : ℕ)) : ZMod p)) ≠ 0 :=
      fib_ne_zero_K p rho (m + 1) hmin (Nat.succ_pos m) (by omega)
    have hne1 : ((((Nat.fib 1 : ℕ)) : ZMod p)) ≠ 0 :=
      fib_ne_zero_K p rho 1 hmin (by omega) (by omega)
    unfold qFun
    field_simp

private theorem prod_nonzero_eq_neg_one (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∏ x ∈ Finset.univ \ {0}, (x : ZMod p) = -1 := by
  have hprod_units := FiniteField.prod_univ_units_id_eq_neg_one (K := ZMod p)
  have hval : ((((∏ x : (ZMod p)ˣ, x) : (ZMod p)ˣ)) : ZMod p) = -1 := by
    rw [hprod_units]
    exact Units.coe_neg_one
  have hmap : ((((∏ x : (ZMod p)ˣ, x) : (ZMod p)ˣ)) : ZMod p)
      = ∏ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p) := by
    have h := map_prod (Units.coeHom (ZMod p))
      (fun x : (ZMod p)ˣ => x) Finset.univ
    simp only [Units.coeHom_apply] at h
    exact h
  have hprod_val : ∏ x : (ZMod p)ˣ, ((x : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [← hmap, hval]
  have himage : Finset.image ((fun u : (ZMod p)ˣ => (u : ZMod p))) Finset.univ
      = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton]
    constructor
    · rintro ⟨u, rfl⟩
      exact u.ne_zero
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hinjSet : Set.InjOn ((fun u : (ZMod p)ˣ => (u : ZMod p)))
      ↑(Finset.univ : Finset (ZMod p)ˣ) := by
    intro x _ y _ h
    simp only at h
    exact Units.val_injective h
  have hprod_image : ∏ x ∈ Finset.image ((fun u : (ZMod p)ˣ => (u : ZMod p)))
      (Finset.univ : Finset (ZMod p)ˣ), x
      = ∏ u ∈ (Finset.univ : Finset (ZMod p)ˣ),
        ((u : (ZMod p)ˣ) : ZMod p) :=
    Finset.prod_image hinjSet
  rw [himage] at hprod_image
  rw [hprod_image]
  exact hprod_val

private def SDef (p rho : ℕ) : ZMod p :=
  ∑ i ∈ Finset.range (rho - 1),
    (-1 : ZMod p) ^ (i + 1) * ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2

private theorem g_q_eq (p rho i : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hi0 : 0 < i) (hiR : i < rho) :
    gFun p (qFun p i)
      = (-1 : ZMod p) ^ i * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹ ^ 2 := by
  have hne : ((((Nat.fib i : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho i hmin hi0 hiR
  have hcas := cassini_K p i
  have hunit : ((((Nat.fib i : ℕ)) : ZMod p))
      * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹ = 1 :=
    mul_inv_cancel₀ hne
  unfold qFun gFun
  linear_combination ((((Nat.fib i : ℕ)) : ZMod p))⁻¹ ^ 2 * hcas
    + (((((Nat.fib (i + 1) : ℕ)) : ZMod p))
      * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹
      + (((Nat.fib i : ℕ)) : ZMod p)
      * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹ + 1) * hunit

private theorem S_eq_sum_Q (p rho : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) :
    SDef p rho = ∑ q ∈ QSet p rho, gFun p q := by
  have hinj : ∀ x ∈ Finset.range (rho - 1), ∀ y ∈ Finset.range (rho - 1),
      (fun i => qFun p (i + 1)) x = (fun i => qFun p (i + 1)) y → x = y := by
    intro a ha b hb hab
    simp only at hab
    rw [Finset.mem_range] at ha hb
    by_contra hne
    have hne' : a + 1 ≠ b + 1 := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact absurd hab
        (q_injective p rho (a + 1) (b + 1) hmin (Nat.succ_pos a) (by omega)
          (Nat.succ_pos b) (by omega) hlt)
    · exact absurd hab.symm
        (q_injective p rho (b + 1) (a + 1) hmin (Nat.succ_pos b) (by omega)
          (Nat.succ_pos a) (by omega) hgt)
  rw [QSet, Finset.sum_image hinj]
  unfold SDef
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact (g_q_eq p rho (i + 1) hmin (Nat.succ_pos i) (by omega)).symm

private theorem S_eq_zero (p rho : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hε : ε = 1 ∨ ε = -1)
    (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (hfib0 : Nat.fib rho % p = 0)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) :
    SDef p rho = 0 := by
  obtain ⟨hodd, heven, h6, h1⟩ := rho_facts p rho ε hp hp7 hε hrho
  have hrho2 : 2 ≤ rho := by omega
  have hC_card := C_card p rho hmin h1
  have hC_sum : ∑ c ∈ CSet p rho, gFun p c = 0 := by
    rcases hε with rfl | rfl
    · have hC2 : Finset.card (CSet p rho) = 2 := by
        rw [hC_card]
        omega
      exact Finset.sum_eq_zero fun c hc =>
        g_eq_zero_of_mem_C_two p rho hmin hfib0 h1 hrho2 hC2 c hc
    · have hC0 : Finset.card (CSet p rho) = 0 := by
        rw [hC_card]
        omega
      have hCempty : CSet p rho = ∅ := Finset.card_eq_zero.mp hC0
      rw [hCempty, Finset.sum_empty]
  have hQsub : QSet p rho ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ c ∈ CSet p rho, gFun p c)
      + (∑ q ∈ QSet p rho, gFun p q)
      = ∑ x ∈ Finset.univ, gFun p x := by
    have h := Finset.sum_sdiff (s₁ := QSet p rho) (s₂ := Finset.univ)
      (f := gFun p) hQsub
    unfold CSet at ⊢
    exact h
  rw [hC_sum, zero_add] at hsum
  have hS_Q := S_eq_sum_Q p rho hmin h1
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h1_lt : 1 < Fintype.card (ZMod p) - 1 := by
    rw [hcard]
    omega
  have h2_lt : 2 < Fintype.card (ZMod p) - 1 := by
    rw [hcard]
    omega
  have hsum1 := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 1 h1_lt
  have hsum2 := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 h2_lt
  have h1_pow : ∑ x ∈ Finset.univ, (x : ZMod p) = 0 := by
    simpa [pow_one] using hsum1
  have h2_pow : ∑ x ∈ Finset.univ, (x : ZMod p) ^ 2 = 0 := hsum2
  have h1_const : ∑ _x : ZMod p, (1 : ZMod p) = 0 := by
    rw [Finset.sum_const, Finset.card_univ, hcard]
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
  have h_univ : ∑ x ∈ Finset.univ, gFun p x = 0 := by
    unfold gFun
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [h2_pow, h1_pow, h1_const, sub_zero, sub_zero]
  rw [hS_Q, hsum]
  exact h_univ

private theorem pair_sum_eq (p rho i : ℕ) (hiR : i < rho)
    (hu1 : IsUnit (((Nat.fib i : ℕ)) : ZMod (p ^ 3)))
    (hu2 : IsUnit (((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3))) :
    ((2 * (((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))
      - (((Nat.fib i : ℕ)) : ZMod (p ^ 3)))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹)
    + ((2 * (((Nat.fib (rho - i + 1) : ℕ)) : ZMod (p ^ 3))
      - (((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))
      * ((((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))⁻¹)
    = 2 * (((Nat.fib rho : ℕ)) : ZMod (p ^ 3))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹
      * ((((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))⁻¹ := by
  have hNat := fib_pair_nat rho i hiR
  have hAdd : (((Nat.fib rho : ℕ)) : ZMod (p ^ 3))
      = (((Nat.fib i : ℕ)) : ZMod (p ^ 3))
        * (((Nat.fib (rho - i - 1) : ℕ)) : ZMod (p ^ 3))
        + (((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))
        * (((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)) := by
    have hR := congrArg (Nat.cast : ℕ → ZMod (p ^ 3)) hNat
    push_cast at hR
    exact hR
  have hNat2 := fib_succ_split rho i hiR
  have hSucc : (((Nat.fib (rho - i + 1) : ℕ)) : ZMod (p ^ 3))
      = (((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3))
        + (((Nat.fib (rho - i - 1) : ℕ)) : ZMod (p ^ 3)) := by
    have hR := congrArg (Nat.cast : ℕ → ZMod (p ^ 3)) hNat2
    push_cast at hR
    exact hR
  have hunit1 : (((Nat.fib i : ℕ)) : ZMod (p ^ 3))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu1
  have hunit2 : (((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3))
      * ((((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu2
  linear_combination (-2 * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹
      * ((((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))⁻¹) * hAdd
    + (2 * ((((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))⁻¹) * hSucc
    + (-2 * (((Nat.fib (rho - i - 1) : ℕ)) : ZMod (p ^ 3))
      * ((((Nat.fib (rho - i) : ℕ)) : ZMod (p ^ 3)))⁻¹ - 1) * hunit1
    + (1 - 2 * (((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹) * hunit2

private theorem cassini_R (p i : ℕ) :
    ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) ^ 2
      - ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))
      - ((((Nat.fib i : ℕ)) : ZMod (p ^ 3))) ^ 2 = (-1 : ZMod (p ^ 3)) ^ i := by
  have hcas := Int.fib_succ_mul_fib_pred_sub_fib_sq (i : ℤ)
  have hsplit : Int.fib ((i : ℤ) + 1) = Int.fib ((i : ℤ) - 1) + Int.fib (i : ℤ) := by
    have h := Int.fib_add_two ((i : ℤ) - 1)
    have e1 : ((i : ℤ) - 1) + 2 = (i : ℤ) + 1 := by ring
    have e2 : ((i : ℤ) - 1) + 1 = (i : ℤ) := by ring
    rw [e1, e2] at h
    exact h
  have hgoal_int : Int.fib ((i : ℤ) + 1) ^ 2
      - Int.fib ((i : ℤ) + 1) * Int.fib (i : ℤ) - Int.fib (i : ℤ) ^ 2
      = (-1 : ℤ) ^ (i : ℤ).natAbs := by
    linear_combination hcas + Int.fib ((i : ℤ) + 1) * hsplit
  have hcast1 : (i : ℤ) + 1 = (((i + 1 : ℕ)) : ℤ) := by push_cast; ring
  have hfib1 : Int.fib ((i : ℤ) + 1) = (Nat.fib (i + 1) : ℤ) := by
    rw [hcast1, Int.fib_natCast]
  have hfib0 : Int.fib (i : ℤ) = (Nat.fib i : ℤ) := Int.fib_natCast i
  have hnat : (i : ℤ).natAbs = i := rfl
  rw [hfib1, hfib0, hnat] at hgoal_int
  have hR := congrArg (Int.cast : ℤ → ZMod (p ^ 3)) hgoal_int
  push_cast at hR
  exact hR

private theorem r_sq_eq (p i : ℕ) (hu : IsUnit ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))) :
    ((2 * ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) - ((((Nat.fib i : ℕ)) : ZMod (p ^ 3))))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹) ^ 2
      = 5 + 4 * (-1 : ZMod (p ^ 3)) ^ i * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2 := by
  have hcas := cassini_R p i
  have hunit : ((((Nat.fib i : ℕ)) : ZMod (p ^ 3))) * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu
  linear_combination (4 * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2) * hcas
    + (5 * (((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹ + 1)) * hunit

private theorem a_sq_eq (p n : ℕ) (half : ZMod (p ^ 3)) (hh : 2 * half = 1)
    (heven : Even n) (hn : 1 ≤ n) :
    ((((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3)) + half * (((Nat.fib n : ℕ)) : ZMod (p ^ 3))) ^ 2
      = 1 + 5 * (half * (((Nat.fib n : ℕ)) : ZMod (p ^ 3))) ^ 2 := by
  have hcas := cassini_even_R p n heven hn
  linear_combination hcas
    + ((((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3)) * (((Nat.fib n : ℕ)) : ZMod (p ^ 3))
      - (((Nat.fib n : ℕ)) : ZMod (p ^ 3)) ^ 2
      - 2 * half * (((Nat.fib n : ℕ)) : ZMod (p ^ 3)) ^ 2) * hh

private theorem linear_factor (p n i : ℕ) (half : ZMod (p ^ 3))
    (hn : 1 ≤ n) (hu : IsUnit ((Nat.fib i : ℕ) : ZMod (p ^ 3)))
    (hh : 2 * half = 1) :
    ((Nat.fib (n + i) : ℕ) : ZMod (p ^ 3)) * (((Nat.fib i : ℕ) : ZMod (p ^ 3)))⁻¹
      = (((Nat.fib (n - 1) : ℕ) : ZMod (p ^ 3)) + half * ((Nat.fib n : ℕ) : ZMod (p ^ 3)))
        + (half * ((Nat.fib n : ℕ) : ZMod (p ^ 3))) *
          ((2 * (((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)) - ((Nat.fib i : ℕ) : ZMod (p ^ 3))) *
            ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹) := by
  have hfib := fib_add_shift_R p n i hn
  have hunit : ((Nat.fib i : ℕ) : ZMod (p ^ 3)) * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu
  linear_combination (((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹) * hfib
    + ((((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3)) + half * (((Nat.fib n : ℕ)) : ZMod (p ^ 3))) * hunit
    - ((((Nat.fib n : ℕ)) : ZMod (p ^ 3)) * (((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))
      * ((((Nat.fib i : ℕ)) : ZMod (p ^ 3)))⁻¹) * hh

private theorem nat_div_eq_prod_ratios (p rho n : ℕ) (hp : Nat.Prime p)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) :
    ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) /
        Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)
        : ZMod (p ^ 3))
      = ∏ i ∈ Finset.range (rho - 1),
        ((Nat.fib (n + i + 1) : ZMod (p ^ 3)) * ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹) := by
  have hYdvdX := fib_shift_prod_dvd n (rho - 1)
  have hBmul : (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) /
      Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1))) *
      Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1))
      = Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) :=
    Nat.div_mul_cancel hYdvdX
  have hcast : ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) /
      Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)
      : ZMod (p ^ 3))
      * ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)
        : ZMod (p ^ 3))
      = ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) : ℕ)
        : ZMod (p ^ 3)) := by
    rw [← Nat.cast_mul, hBmul]
  have hYunit : IsUnit (((Finset.prod (Finset.range (rho - 1))
      (fun i => Nat.fib (i + 1)) : ℕ)) : ZMod (p ^ 3)) := by
    rw [Nat.cast_prod]
    rw [IsUnit.prod_iff]
    intro i hi
    simp only [Finset.mem_range] at hi
    exact fib_unit_R p rho (i + 1) hp hmin (Nat.succ_pos i) (by omega)
  have hprod : (∏ i ∈ Finset.range (rho - 1),
      ((Nat.fib (n + i + 1) : ZMod (p ^ 3)) * ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹))
      * ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)
        : ZMod (p ^ 3))
      = ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) : ℕ)
        : ZMod (p ^ 3)) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have hu := fib_unit_R p rho (i + 1) hp hmin (Nat.succ_pos i) (by omega)
    have hinv : ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹ * (Nat.fib (i + 1) : ZMod (p ^ 3)) = 1 :=
      ZMod.inv_mul_of_unit _ hu
    calc ((Nat.fib (n + i + 1) : ZMod (p ^ 3)) * ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹) *
          (Nat.fib (i + 1) : ZMod (p ^ 3))
        = (Nat.fib (n + i + 1) : ZMod (p ^ 3)) *
          (((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹ * (Nat.fib (i + 1) : ZMod (p ^ 3))) := by ring
      _ = (Nat.fib (n + i + 1) : ZMod (p ^ 3)) := by rw [hinv, mul_one]
  exact hYunit.mul_right_cancel (hcast.trans hprod.symm)

-- Helper: p divides Fib rho and its multiples.
private theorem fib_rho_dvd (p rho : ℕ) (hfib0 : Nat.fib rho % p = 0) :
    p ∣ Nat.fib rho :=
  Nat.dvd_of_mod_eq_zero hfib0

private theorem fib_k_rho_dvd (p rho k : ℕ) (hfib0 : Nat.fib rho % p = 0) :
    p ∣ Nat.fib (k * rho) := by
  have h1 : p ∣ Nat.fib rho := Nat.dvd_of_mod_eq_zero hfib0
  have h2 : Nat.fib rho ∣ Nat.fib (k * rho) :=
    Nat.fib_dvd rho (k * rho) (Nat.dvd_mul_left rho k)
  exact h1.trans h2

-- Helper: the k = 0 case of the congruence (both sides equal 1).
private theorem fibonomial_zero_case (p rho : ℕ) (ε : ℤ) (k : ℕ) (hk : k = 0)
    (_hp : Nat.Prime p) (_hp7 : 7 ≤ p)
    (_hε : ε = 1 ∨ ε = -1) (_hrho : (rho : ℤ) = (p : ℤ) - ε)
    (_hfib0 : Nat.fib rho % p = 0)
    (_hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) :
    Int.ModEq ((p : ℤ) ^ 3)
      (((Finset.prod (Finset.range ((k + 1) * rho - 1)) (fun i => Nat.fib (i + 1)) /
        (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) *
          Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1)))) : ℕ) : ℤ)
      (ε ^ k) := by
  subst hk
  have hpos : 0 < Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) :=
    Finset.prod_pos (fun i _ => Nat.fib_pos.mpr (Nat.succ_pos i))
  simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Finset.prod_range_zero, mul_one]
  rw [Nat.div_self hpos, Nat.cast_one, pow_zero]

private theorem piHom_inv_of_unit (p : ℕ) [Fact p.Prime] (x : ZMod (p ^ 3))
    (hu : IsUnit x) :
    piHom p (x⁻¹) = (piHom p x)⁻¹ := by
  have h1 : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hu
  have hpi : piHom p x * piHom p (x⁻¹) = 1 := by
    rw [← map_mul, h1, map_one]
  exact eq_inv_of_mul_eq_one_right hpi

private theorem isUnit_of_pi_ne_zero (p : ℕ) (hp : Nat.Prime p) [NeZero p]
    [NeZero (p ^ 3)] (x : ZMod (p ^ 3)) (hx : piHom p x ≠ 0) : IsUnit x := by
  have hx_eq : x = ((x.val : ℕ) : ZMod (p ^ 3)) := (ZMod.natCast_zmod_val x).symm
  rw [hx_eq, ZMod.isUnit_iff_coprime]
  have hndvd : ¬ p ∣ x.val := by
    intro hdvd
    apply hx
    rw [← ZMod.natCast_zmod_val x, piHom_natCast, ZMod.natCast_eq_zero_iff]
    exact hdvd
  have hcop : Nat.Coprime x.val p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).symm
  exact Nat.Coprime.pow_right 3 hcop

private theorem half_spec (p : ℕ) (hodd : Odd p) :
    2 * ((2 : ZMod (p ^ 3))⁻¹) = 1 := by
  have hu := two_unit_R p hodd
  exact ZMod.mul_inv_of_unit _ hu

private theorem a_isUnit_of_sq (p : ℕ) (a b : ZMod (p ^ 3))
    (hb : b ^ 4 = 0) (hsq : a ^ 2 = 1 + 5 * b ^ 2) : IsUnit a := by
  have hunit : (1 + 5 * b ^ 2) * (1 - 5 * b ^ 2) = 1 :=
    one_add_five_sq_unit (ZMod (p ^ 3)) b hb
  have hsq2 : a ^ 2 * (1 - 5 * b ^ 2) = 1 := by
    rw [hsq]
    exact hunit
  have h1 : a * (a * (1 - 5 * b ^ 2)) = 1 := by
    have : a * (a * (1 - 5 * b ^ 2)) = a ^ 2 * (1 - 5 * b ^ 2) := by ring
    rw [this, hsq2]
  rw [isUnit_iff_exists]
  exact ⟨a * (1 - 5 * b ^ 2), h1, by rw [mul_comm]; exact h1⟩

private theorem a_inv_sq_eq (p : ℕ) (a b : ZMod (p ^ 3))
    (hb : b ^ 4 = 0) (hsq : a ^ 2 = 1 + 5 * b ^ 2) (hu : IsUnit a) :
    (a⁻¹) ^ 2 = 1 - 5 * b ^ 2 := by
  have hunit : (1 + 5 * b ^ 2) * (1 - 5 * b ^ 2) = 1 :=
    one_add_five_sq_unit (ZMod (p ^ 3)) b hb
  have hsq2 : a ^ 2 * (1 - 5 * b ^ 2) = 1 := by
    rw [hsq]
    exact hunit
  have ha : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a hu
  have hsq_inv : (a⁻¹) ^ 2 * a ^ 2 = 1 := by
    have hring : (a⁻¹) ^ 2 * a ^ 2 = (a * a⁻¹) ^ 2 := by ring
    rw [hring, ha, one_pow]
  calc (a⁻¹) ^ 2 = (a⁻¹) ^ 2 * 1 := by ring
    _ = (a⁻¹) ^ 2 * (a ^ 2 * (1 - 5 * b ^ 2)) := by rw [hsq2]
    _ = ((a⁻¹) ^ 2 * a ^ 2) * (1 - 5 * b ^ 2) := by ring
    _ = 1 * (1 - 5 * b ^ 2) := by rw [hsq_inv]
    _ = 1 - 5 * b ^ 2 := by ring

private theorem pow_three_eq_zero_of_small (p : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (b : ZMod (p ^ 3)) (hb : piHom p b = 0) : b ^ 3 = 0 := by
  have h3 : b * b * b = 0 := small_triple_eq_zero p b b b hb hb hb
  have heq : b ^ 3 = b * b * b := by ring
  rw [heq, h3]

private theorem t_cube_eq_zero (R : Type*) [CommRing R] (b ainv : R)
    (hb3 : b ^ 3 = 0) : (b * ainv) ^ 3 = 0 := by
  rw [mul_pow, hb3, zero_mul]

private def rFun (p j : ℕ) : ZMod (p ^ 3) :=
  (2 * (((Nat.fib (j + 1) : ℕ)) : ZMod (p ^ 3)) - (((Nat.fib j : ℕ)) : ZMod (p ^ 3))) *
    ((((Nat.fib j : ℕ)) : ZMod (p ^ 3)))⁻¹

private def e1Def (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1), rFun p (i + 1)

private def p2Def (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1), (rFun p (i + 1)) ^ 2

private def WDef (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1),
    ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
      ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹

private def SRDef (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1),
    (-1 : ZMod (p ^ 3)) ^ (i + 1) * ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2

private theorem reflect_r_sum (p rho : ℕ) (hrho1 : 1 ≤ rho) :
    ∑ i ∈ Finset.range (rho - 1), rFun p (rho - (i + 1)) = e1Def p rho := by
  have hbase := Finset.sum_range_reflect (fun j => rFun p (j + 1)) (rho - 1)
  have href : (∑ i ∈ Finset.range (rho - 1), rFun p ((rho - 1 - 1 - i) + 1))
      = e1Def p rho := by
    have h2 : (∑ i ∈ Finset.range (rho - 1), (fun j => rFun p (j + 1)) (rho - 1 - 1 - i))
        = e1Def p rho := by
      rw [hbase]
      rfl
    simpa only [] using h2
  rw [← href]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  congr 1
  omega

private theorem e1_eq_fib_rho_mul_W (p rho : ℕ) (hp : Nat.Prime p)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) (hodd : Odd p) :
    e1Def p rho
      = (((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) * WDef p rho := by
  have hpair : ∀ i ∈ Finset.range (rho - 1),
      rFun p (i + 1) + rFun p (rho - (i + 1))
        = 2 * (((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi0 : 0 < i + 1 := Nat.succ_pos i
    have hiR : i + 1 < rho := by omega
    have hj0 : 0 < rho - (i + 1) := by omega
    have hjR : rho - (i + 1) < rho := by omega
    have hu1 : IsUnit ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) :=
      fib_unit_R p rho (i + 1) hp hmin hi0 hiR
    have hu2 : IsUnit ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3))) :=
      fib_unit_R p rho (rho - (i + 1)) hp hmin hj0 hjR
    have h := pair_sum_eq p rho (i + 1) hiR hu1 hu2
    unfold rFun
    exact h
  have hsum : (∑ i ∈ Finset.range (rho - 1),
        (rFun p (i + 1) + rFun p (rho - (i + 1))))
      = ∑ i ∈ Finset.range (rho - 1),
        (2 * (((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹) :=
    Finset.sum_congr rfl hpair
  rw [Finset.sum_add_distrib] at hsum
  have href := reflect_r_sum p rho hrho1
  have he1 : (∑ i ∈ Finset.range (rho - 1), rFun p (i + 1)) = e1Def p rho := rfl
  rw [he1, href] at hsum
  have hRHS : (∑ i ∈ Finset.range (rho - 1),
        (2 * (((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹))
      = 2 * ((((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) * WDef p rho) := by
    have hfactor : ∀ i ∈ Finset.range (rho - 1),
        (2 * (((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹)
        = (2 * (((Nat.fib rho : ℕ)) : ZMod (p ^ 3))) *
          (((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
            ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹) := by
      intro i _
      ring
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
    unfold WDef
    ring
  rw [hRHS] at hsum
  have h2 : 2 * e1Def p rho
      = 2 * ((((Nat.fib rho : ℕ)) : ZMod (p ^ 3)) * WDef p rho) := by
    have htwo : e1Def p rho + e1Def p rho = 2 * e1Def p rho := by ring
    rw [← htwo]
    exact hsum
  have hu2 : IsUnit ((2 : ZMod (p ^ 3))) := two_unit_R p hodd
  have hinv : ((2 : ZMod (p ^ 3)))⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit _ hu2
  have hmul : ((2 : ZMod (p ^ 3)))⁻¹ * (2 * e1Def p rho)
      = ((2 : ZMod (p ^ 3)))⁻¹ * (2 * (((Nat.fib rho : ℕ) : ZMod (p ^ 3)) * WDef p rho)) := by
    rw [h2]
  rwa [← mul_assoc, ← mul_assoc, hinv, one_mul, one_mul] at hmul

private theorem fib_rho_sub_K (p rho i : ℕ) [Fact p.Prime]
    (hi0 : 1 ≤ i) (hiR : i < rho) (hrho1 : 1 ≤ rho) :
    ((((Nat.fib (rho - i) : ℕ)) : ZMod p))
      = (-1 : ZMod p) ^ (i + 1) * ((((Nat.fib (rho - 1) : ℕ)) : ZMod p))
          * ((((Nat.fib i : ℕ)) : ZMod p))
        + (-1 : ZMod p) ^ i * ((((Nat.fib rho : ℕ)) : ZMod p))
          * ((((Nat.fib (i - 1) : ℕ)) : ZMod p)) := by
  have hij : i ≤ rho := by omega
  have hInt := Int.fib_add (rho : ℤ) (-(i : ℤ))
  have hsum : (rho : ℤ) + (-(i : ℤ)) = (((rho - i : ℕ)) : ℤ) := by
    have hsub : (((rho - i : ℕ)) : ℤ) = (rho : ℤ) - (i : ℤ) :=
      Nat.cast_sub hij
    rw [hsub]
    ring
  have hrho_sub : (rho : ℤ) - 1 = (((rho - 1 : ℕ)) : ℤ) := by
    have hsub : (((rho - 1 : ℕ)) : ℤ) = (rho : ℤ) - 1 := Nat.cast_sub hrho1
    exact hsub.symm
  have hneg1 : (-(i : ℤ) + 1) = -((((i - 1 : ℕ)) : ℤ)) := by
    have hsub : (((i - 1 : ℕ)) : ℤ) = (i : ℤ) - 1 := Nat.cast_sub hi0
    rw [hsub]
    ring
  have hfib_rho_i : Int.fib ((rho : ℤ) + (-(i : ℤ))) = (Nat.fib (rho - i) : ℤ) := by
    rw [hsum, Int.fib_natCast]
  have hfib_rho1 : Int.fib ((rho : ℤ) - 1) = (Nat.fib (rho - 1) : ℤ) := by
    rw [hrho_sub, Int.fib_natCast]
  have hfib_rho : Int.fib (rho : ℤ) = (Nat.fib rho : ℤ) := Int.fib_natCast rho
  have hfib_neg : Int.fib (-(i : ℤ)) = (-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ) := by
    have h := Int.fib_neg_natCast i
    simpa only [Nat.cast_id] using h
  have hfib_neg1 : Int.fib (-(i : ℤ) + 1) = (-1 : ℤ) ^ i * (Nat.fib (i - 1) : ℤ) := by
    rw [hneg1, Int.fib_neg_natCast]
    have hi_eq : i - 1 + 1 = i := Nat.sub_add_cancel hi0
    rw [hi_eq]
  rw [hfib_rho_i, hfib_rho1, hfib_rho, hfib_neg, hfib_neg1] at hInt
  have hR := congrArg (Int.cast : ℤ → ZMod p) hInt
  push_cast at hR
  linear_combination hR

private theorem fib_rho_sub_K_eq (p rho i : ℕ) [Fact p.Prime]
    (hi0 : 1 ≤ i) (hiR : i < rho) (hrho1 : 1 ≤ rho)
    (hfib0 : Nat.fib rho % p = 0) :
    ((((Nat.fib (rho - i) : ℕ)) : ZMod p))
      = (-1 : ZMod p) ^ (i + 1) * ((((Nat.fib (rho - 1) : ℕ)) : ZMod p))
        * ((((Nat.fib i : ℕ)) : ZMod p)) := by
  have hfull := fib_rho_sub_K p rho i hi0 hiR hrho1
  have h0 : ((((Nat.fib rho : ℕ)) : ZMod p)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero hfib0
  rw [hfull, h0, mul_zero, zero_mul, add_zero]

private theorem pi_W_eq_zero (p rho : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    [NeZero (p ^ 3)] (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (hfib0 : Nat.fib rho % p = 0)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    piHom p (WDef p rho) = 0 := by
  have hS0 : SDef p rho = 0 := S_eq_zero p rho ε hp hp7 hε hrho hfib0 hmin
  have hc_ne : ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) ≠ 0 :=
    fib_ne_zero_K p rho (rho - 1) hmin (by omega) (by omega)
  have hpiW : piHom p (WDef p rho)
      = ∑ i ∈ Finset.range (rho - 1),
        ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod p))⁻¹ := by
    unfold WDef
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi0 : 0 < i + 1 := Nat.succ_pos i
    have hiR : i + 1 < rho := by omega
    have hj0 : 0 < rho - (i + 1) := by omega
    have hjR : rho - (i + 1) < rho := by omega
    have hu1 : IsUnit ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) :=
      fib_unit_R p rho (i + 1) hp hmin hi0 hiR
    have hu2 : IsUnit ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3))) :=
      fib_unit_R p rho (rho - (i + 1)) hp hmin hj0 hjR
    rw [map_mul, piHom_inv_of_unit p _ hu1, piHom_inv_of_unit p _ hu2,
      piHom_natCast, piHom_natCast]
  have hterm : ∀ i ∈ Finset.range (rho - 1),
      ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod p))⁻¹
        = (-((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹) *
          ((-1 : ZMod p) ^ (i + 1) *
            ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi0 : 1 ≤ i + 1 := Nat.succ_pos i
    have hiR : i + 1 < rho := by omega
    have hFib := fib_rho_sub_K_eq p rho (i + 1) hi0 hiR hrho1 hfib0
    have hF_ne : ((((Nat.fib (i + 1) : ℕ)) : ZMod p)) ≠ 0 :=
      fib_ne_zero_K p rho (i + 1) hmin (Nat.succ_pos i) hiR
    have hneg_self : (((-1 : ZMod p) ^ (i + 1 + 1))⁻¹)
        = (-1 : ZMod p) ^ (i + 1 + 1) := by
      rw [← inv_pow, inv_neg_one]
    have hGinv : ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod p))⁻¹
        = (-1 : ZMod p) ^ (i + 1 + 1) *
          ((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹ *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ := by
      rw [hFib, mul_inv, mul_inv, hneg_self]
    have hpow : (-1 : ZMod p) ^ (i + 1 + 1) = -(-1 : ZMod p) ^ (i + 1) := by
      rw [pow_succ, mul_neg, mul_one]
    calc ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ *
            ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod p))⁻¹
        = ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ *
            ((-1 : ZMod p) ^ (i + 1 + 1) *
              ((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹ *
              ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹) := by rw [hGinv]
      _ = (-1 : ZMod p) ^ (i + 1 + 1) *
            ((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹ *
            ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2 := by ring
      _ = -(-1 : ZMod p) ^ (i + 1) *
            ((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹ *
            ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2 := by rw [hpow]
      _ = (-((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹) *
            ((-1 : ZMod p) ^ (i + 1) *
              ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2) := by ring
  have hsum : (∑ i ∈ Finset.range (rho - 1),
        ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ *
          ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod p))⁻¹)
      = (-((((Nat.fib (rho - 1) : ℕ)) : ZMod p))⁻¹) * SDef p rho := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    rfl
  rw [hpiW, hsum, hS0, mul_zero]

private theorem pi_SR_eq_S (p rho : ℕ) [Fact p.Prime] (hp : Nat.Prime p)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) :
    piHom p (SRDef p rho) = SDef p rho := by
  unfold SRDef SDef
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi0 : 0 < i + 1 := Nat.succ_pos i
  have hiR : i + 1 < rho := by omega
  have hu : IsUnit ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) :=
    fib_unit_R p rho (i + 1) hp hmin hi0 hiR
  have hneg : piHom p (-1 : ZMod (p ^ 3)) = (-1 : ZMod p) := by
    rw [map_neg, map_one]
  have hpow : piHom p ((-1 : ZMod (p ^ 3)) ^ (i + 1))
      = (-1 : ZMod p) ^ (i + 1) := by
    rw [map_pow, hneg]
  have hF : piHom p ((Nat.fib (i + 1) : ZMod (p ^ 3)))
      = ((Nat.fib (i + 1) : ZMod p)) := piHom_natCast p _
  have hFinv : piHom p (((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹)
      = (((Nat.fib (i + 1) : ZMod p))⁻¹) := by
    rw [piHom_inv_of_unit p _ hu, hF]
  rw [map_mul, hpow, map_pow, hFinv]

private theorem p2_eq (p rho : ℕ) (hp : Nat.Prime p)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) :
    p2Def p rho
      = 5 * ((((rho - 1 : ℕ)) : ZMod (p ^ 3))) + 4 * SRDef p rho := by
  have hterm : ∀ i ∈ Finset.range (rho - 1),
      (rFun p (i + 1)) ^ 2
        = 5 + 4 * ((-1 : ZMod (p ^ 3)) ^ (i + 1) *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi0 : 0 < i + 1 := Nat.succ_pos i
    have hiR : i + 1 < rho := by omega
    have hu : IsUnit ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3))) :=
      fib_unit_R p rho (i + 1) hp hmin hi0 hiR
    have h := r_sq_eq p (i + 1) hu
    unfold rFun at h ⊢
    linear_combination h
  have hsum : p2Def p rho
      = (∑ i ∈ Finset.range (rho - 1), (5 : ZMod (p ^ 3)))
        + ∑ i ∈ Finset.range (rho - 1),
          (4 * ((-1 : ZMod (p ^ 3)) ^ (i + 1) *
            ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2)) := by
    unfold p2Def
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  rw [hsum]
  have hconst : (∑ _i ∈ Finset.range (rho - 1), (5 : ZMod (p ^ 3)))
      = 5 * ((((rho - 1 : ℕ)) : ZMod (p ^ 3))) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hmul : (∑ i ∈ Finset.range (rho - 1),
        (4 * ((-1 : ZMod (p ^ 3)) ^ (i + 1) *
          ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2)))
      = 4 * SRDef p rho := by
    rw [← Finset.mul_sum]
    rfl
  rw [hconst, hmul]

private theorem t_mul_e1_eq_zero (p rho : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (t : ZMod (p ^ 3)) (ht : piHom p t = 0)
    (hF : piHom p ((((Nat.fib rho : ℕ)) : ZMod (p ^ 3))) = 0)
    (hW : piHom p (WDef p rho) = 0)
    (he1 : e1Def p rho
      = ((((Nat.fib rho : ℕ)) : ZMod (p ^ 3))) * WDef p rho) :
    t * e1Def p rho = 0 := by
  rw [he1, ← mul_assoc]
  exact small_triple_eq_zero p t _ _ ht hF hW

private theorem b_mul_e1_eq_zero (p : ℕ) (a b : ZMod (p ^ 3))
    (e1 : ZMod (p ^ 3)) (hu : IsUnit a)
    (ht0 : (b * a⁻¹) * e1 = 0) : b * e1 = 0 := by
  have ha : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a hu
  have hab : a * (b * a⁻¹) = b := by
    have hring : a * (b * a⁻¹) = b * (a * a⁻¹) := by ring
    rw [hring, ha, mul_one]
  have h : a * ((b * a⁻¹) * e1) = b * e1 := by
    rw [← mul_assoc, hab]
  rw [ht0, mul_zero] at h
  exact h.symm

private theorem b_sq_mul_e1_sq_eq_zero (p : ℕ) (b e1 : ZMod (p ^ 3))
    (hb0 : b * e1 = 0) : b ^ 2 * e1 ^ 2 = 0 := by
  have hpow : b ^ 2 * e1 ^ 2 = (b * e1) ^ 2 := by ring
  rw [hpow, hb0, pow_two, mul_zero]

private theorem b_sq_mul_SR_eq_zero (p rho : ℕ) [NeZero p] [NeZero (p ^ 3)]
    (b : ZMod (p ^ 3)) (hb : piHom p b = 0)
    (hSR : piHom p (SRDef p rho) = 0) : b ^ 2 * SRDef p rho = 0 := by
  have h3 : b * b * SRDef p rho = 0 :=
    small_triple_eq_zero p b b (SRDef p rho) hb hb hSR
  have heq : b ^ 2 * SRDef p rho = b * b * SRDef p rho := by ring
  rw [heq, h3]

private theorem t_sq_eq_b_sq (p : ℕ) (a b : ZMod (p ^ 3))
    (hb4 : b ^ 4 = 0) (hsq : a ^ 2 = 1 + 5 * b ^ 2) (hu : IsUnit a) :
    (b * a⁻¹) ^ 2 = b ^ 2 := by
  have ha_inv : (a⁻¹) ^ 2 = 1 - 5 * b ^ 2 := a_inv_sq_eq p a b hb4 hsq hu
  have hmul : (b * a⁻¹) ^ 2 = b ^ 2 * (1 - 5 * b ^ 2) := by
    rw [mul_pow, ha_inv]
  rw [hmul]
  linear_combination (-5 * hb4)

private theorem B_eq_prod_linear (p rho n : ℕ) (hp : Nat.Prime p)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hn : 1 ≤ n) (half : ZMod (p ^ 3)) (hh : 2 * half = 1) :
    (∏ i ∈ Finset.range (rho - 1),
        ((Nat.fib (n + i + 1) : ZMod (p ^ 3)) * ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹))
      = ∏ i ∈ Finset.range (rho - 1),
        (((((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3)) + half * (((Nat.fib n : ℕ)) : ZMod (p ^ 3)))
          + (half * (((Nat.fib n : ℕ)) : ZMod (p ^ 3))) * rFun p (i + 1)) := by
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi0 : 0 < i + 1 := Nat.succ_pos i
  have hiR : i + 1 < rho := by omega
  have hu : IsUnit ((Nat.fib (i + 1) : ZMod (p ^ 3))) :=
    fib_unit_R p rho (i + 1) hp hmin hi0 hiR
  have heq : n + i + 1 = n + (i + 1) := by ring
  have h := linear_factor p n (i + 1) half hn hu hh
  have hcast : ((Nat.fib (n + i + 1) : ZMod (p ^ 3)))
      = ((Nat.fib (n + (i + 1)) : ZMod (p ^ 3))) := by rw [heq]
  rw [hcast]
  unfold rFun
  exact h

private theorem factor_a_add (p : ℕ) (a b r : ZMod (p ^ 3)) (hu : IsUnit a) :
    a + b * r = a * (1 + (b * a⁻¹) * r) := by
  have ha : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a hu
  have hab : a * (b * a⁻¹) = b := by
    have hring : a * (b * a⁻¹) = b * (a * a⁻¹) := by ring
    rw [hring, ha, mul_one]
  have hring : a * (1 + (b * a⁻¹) * r) = a + (a * (b * a⁻¹)) * r := by ring
  rw [hring, hab]

private theorem prod_linear_eq_expansion (p rho : ℕ)
    (a b t half : ZMod (p ^ 3))
    (ht_def : t = b * a⁻¹) (hu : IsUnit a)
    (ht3 : t ^ 3 = 0) (hh : 2 * half = 1) :
    (∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)))
      = a ^ (rho - 1)
        * (1 + t * e1Def p rho
          + t ^ 2 * half * ((e1Def p rho) ^ 2 - p2Def p rho)) := by
  have hfactor : ∀ i ∈ Finset.range (rho - 1),
      (a + b * rFun p (i + 1)) = a * (1 + t * rFun p (i + 1)) := by
    intro i _
    rw [ht_def]
    exact factor_a_add p a b _ hu
  have hprod : (∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)))
      = (∏ i ∈ Finset.range (rho - 1), a)
        * ∏ i ∈ Finset.range (rho - 1), (1 + t * rFun p (i + 1)) := by
    rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib]
  have hconst : (∏ _i ∈ Finset.range (rho - 1), a) = a ^ (rho - 1) := by
    rw [Finset.prod_const, Finset.card_range]
  have hexp : (∏ i ∈ Finset.range (rho - 1), (1 + t * rFun p (i + 1)))
      = 1 + t * e1Def p rho
        + t ^ 2 * half * ((e1Def p rho) ^ 2 - p2Def p rho) := by
    have h := prod_one_add_t_mul t half ht3 hh
      (Finset.range (rho - 1)) (fun i => rFun p (i + 1))
    exact h
  rw [hprod, hconst, hexp]

private theorem pow_mul_one_add_sq_eq_one (p rho : ℕ)
    (a b half : ZMod (p ^ 3))
    (hb4 : b ^ 4 = 0) (hsq : a ^ 2 = 1 + 5 * b ^ 2) (hh : 2 * half = 1) :
    (a ^ (rho - 1) * (1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2))) ^ 2
      = 1 := by
  have hy2 : (5 * b ^ 2) ^ 2 = 0 := by
    linear_combination 25 * hb4
  have hpow_y : (1 + 5 * b ^ 2) ^ (rho - 1)
      = 1 + ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * (5 * b ^ 2) :=
    one_add_pow_of_sq_eq_zero (5 * b ^ 2) hy2 (rho - 1)
  have hpow_a : (a ^ (rho - 1)) ^ 2 = (a ^ 2) ^ (rho - 1) := by
    have h1 : (a ^ (rho - 1)) ^ 2 = a ^ ((rho - 1) * 2) :=
      (pow_mul a (rho - 1) 2).symm
    have h2 : (a ^ 2) ^ (rho - 1) = a ^ (2 * (rho - 1)) :=
      (pow_mul a 2 (rho - 1)).symm
    rw [h1, h2, mul_comm]
  have ha_sq : (a ^ (rho - 1)) ^ 2
      = 1 + ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * (5 * b ^ 2) := by
    rw [hpow_a, hsq, hpow_y]
  have hX2 : (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2) ^ 2 = 0 := by
    linear_combination ((-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3))) ^ 2 * hb4)
  have h1X : (1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2)) ^ 2
      = 1 + 2 * (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2) := by
    linear_combination hX2
  have h2X : (1 : ZMod (p ^ 3))
        + 2 * (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2)
      = 1 - ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * (5 * b ^ 2) := by
    linear_combination (-5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2 * hh)
  have h1X' : (1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2)) ^ 2
      = 1 - ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * (5 * b ^ 2) := by
    rw [h1X, h2X]
  have hy2' : (((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * (5 * b ^ 2)) ^ 2 = 0 := by
    linear_combination ((((((rho - 1 : ℕ))) : ZMod (p ^ 3))) ^ 2 * 25 * hb4)
  have hmul : (a ^ (rho - 1)
        * (1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2))) ^ 2
      = ((a ^ (rho - 1)) ^ 2)
        * ((1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2)) ^ 2) := by
    rw [mul_pow]
  rw [hmul, ha_sq, h1X']
  linear_combination (-hy2')

private theorem telescoping_prod_eq_c (p rho : ℕ) [Fact p.Prime]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho2 : 2 ≤ rho) :
    ∏ i ∈ Finset.range (rho - 2), qFun p (i + 1)
      = ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) := by
  have hm : rho - 2 + 1 < rho := by omega
  have htel := telescoping_Q p rho (rho - 2) hmin hm
  have heq : rho - 2 + 1 = rho - 1 := by omega
  rw [heq] at htel
  have hF1 : ((((Nat.fib 1 : ℕ)) : ZMod p)) = 1 := by
    have h1 : Nat.fib 1 = 1 := rfl
    rw [h1]
    simp
  rw [hF1, div_one] at htel
  exact htel

private theorem image_range_eq_Q_sdiff (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    Finset.image (fun i => qFun p (i + 1)) (Finset.range (rho - 2))
      = QSet p rho \ {0} := by
  have hEq : rho - 1 = (rho - 2) + 1 := by omega
  have hEq2 : rho - 2 + 1 = rho - 1 := by omega
  have hmem : rho - 2 ∈ Finset.range (rho - 1) :=
    Finset.mem_range.mpr (by omega)
  have hrange : Finset.range (rho - 1)
      = insert (rho - 2) (Finset.range (rho - 2)) := by
    rw [hEq, Finset.range_add_one]
  have hQ : QSet p rho
      = insert (qFun p (rho - 2 + 1))
        (Finset.image (fun i => qFun p (i + 1)) (Finset.range (rho - 2))) := by
    unfold QSet
    rw [hrange, Finset.image_insert]
  have hq0 : qFun p (rho - 2 + 1) = 0 := by
    have heq : rho - 2 + 1 = rho - 1 := by omega
    rw [heq]
    exact q_rho_sub_one_eq_zero p rho hfib0 hrho1
  rw [hq0] at hQ
  have hnotmem : (0 : ZMod p) ∉ Finset.image (fun i => qFun p (i + 1))
      (Finset.range (rho - 2)) := by
    rw [Finset.mem_image]
    rintro ⟨a, ha_range, ha_eq⟩
    rw [Finset.mem_range] at ha_range
    have hj0 : 0 < a + 1 := Nat.succ_pos a
    have hjR1 : a + 1 + 1 < rho := by omega
    have hne := q_ne_zero_of_lt p rho (a + 1) hmin hj0 hjR1
    exact hne ha_eq
  ext x
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro hx
    constructor
    · rw [hQ]
      exact Finset.mem_insert_of_mem hx
    · intro h0
      rw [h0] at hx
      exact hnotmem hx
  · intro hx
    obtain ⟨hxQ, hx0⟩ := hx
    rw [hQ] at hxQ
    rcases Finset.mem_insert.mp hxQ with h | h
    · exfalso
      exact hx0 h
    · exact h

private theorem prod_Q_sdiff_eq_c (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    ∏ q ∈ QSet p rho \ {0}, q = ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) := by
  have himage := image_range_eq_Q_sdiff p rho hmin hfib0 hrho1 hrho2
  have htel := telescoping_prod_eq_c p rho hmin hrho2
  have hinj : ∀ x ∈ Finset.range (rho - 2), ∀ y ∈ Finset.range (rho - 2),
      (fun i => qFun p (i + 1)) x = (fun i => qFun p (i + 1)) y → x = y := by
    intro a ha b hb hab
    simp only at hab
    rw [Finset.mem_range] at ha hb
    by_contra hne
    have hne' : a + 1 ≠ b + 1 := by omega
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact absurd hab
        (q_injective p rho (a + 1) (b + 1) hmin (Nat.succ_pos a) (by omega)
          (Nat.succ_pos b) (by omega) hlt)
    · exact absurd hab.symm
        (q_injective p rho (b + 1) (a + 1) hmin (Nat.succ_pos b) (by omega)
          (Nat.succ_pos a) (by omega) hgt)
  have hprod : ∏ q ∈ Finset.image (fun i => qFun p (i + 1))
      (Finset.range (rho - 2)), q
      = ∏ i ∈ Finset.range (rho - 2), qFun p (i + 1) :=
    Finset.prod_image hinj
  rw [himage] at hprod
  rw [hprod, htel]

private theorem prod_C_eq_neg_one_of_card_two (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (hC2 : Finset.card (CSet p rho) = 2) :
    ∏ c ∈ CSet p rho, c = -1 := by
  obtain ⟨x, y, hxy, hC⟩ := Finset.card_eq_two.mp hC2
  have hx_mem : x ∈ CSet p rho := by
    rw [hC]
    exact Finset.mem_insert_self x {y}
  have hy_mem : y ∈ CSet p rho := by
    rw [hC]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have hx0 := g_eq_zero_of_mem_C_two p rho hmin hfib0 hrho1 hrho2 hC2 x hx_mem
  have hy0 := g_eq_zero_of_mem_C_two p rho hmin hfib0 hrho1 hrho2 hC2 y hy_mem
  unfold gFun at hx0 hy0
  have hsum : x + y - 1 = 0 := by
    have hsub : (x ^ 2 - x - 1) - (y ^ 2 - y - 1) = 0 := by
      rw [hx0, hy0, sub_self]
    have hfactor : (x ^ 2 - x - 1) - (y ^ 2 - y - 1)
        = (x - y) * (x + y - 1) := by ring
    rw [hfactor] at hsub
    rcases mul_eq_zero.mp hsub with h | h
    · exfalso
      apply hxy
      have hxy0 : x - y = 0 := h
      have : x = y := sub_eq_zero.mp hxy0
      exact this
    · exact h
  have hprod : x * y + 1 = 0 := by
    linear_combination -hx0 + x * hsum
  have hxy_eq : x * y = -1 := eq_neg_of_add_eq_zero_left hprod
  have hprod_C : ∏ c ∈ CSet p rho, c = x * y := by
    rw [hC, Finset.prod_insert (by simp [hxy]), Finset.prod_singleton]
  rw [hprod_C, hxy_eq]

private theorem univ_sdiff_eq (p rho : ℕ) [Fact p.Prime] [NeZero p]
    (hfib0 : Nat.fib rho % p = 0) (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    ∏ x ∈ (Finset.univ \ ({0} : Finset (ZMod p))), x
      = (∏ q ∈ QSet p rho \ {0}, q) * ∏ c ∈ CSet p rho, c := by
  have h0Q : (0 : ZMod p) ∈ QSet p rho := zero_mem_Q p rho hfib0 hrho1 hrho2
  have hsub : QSet p rho \ {0} ⊆ Finset.univ \ {0} := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_univ x, hx.2⟩
  have hsdiff_eq : (Finset.univ \ ({0} : Finset (ZMod p))) \ (QSet p rho \ {0})
      = CSet p rho := by
    unfold CSet
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · rintro ⟨hx0, hxQ0⟩ hxQ
      exact hxQ0 ⟨hxQ, hx0⟩
    · intro hxQ
      have hx0 : ¬x = 0 := by
        intro h0
        rw [h0] at hxQ
        exact hxQ h0Q
      exact ⟨hx0, fun h => hxQ h.1⟩
  have hprod := Finset.prod_sdiff (s₁ := QSet p rho \ {0})
    (s₂ := Finset.univ \ ({0} : Finset (ZMod p))) (f := fun x : ZMod p => x) hsub
  rw [hsdiff_eq] at hprod
  rw [mul_comm] at hprod
  exact hprod.symm

private theorem c_eq_eps (p rho : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    (_hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (hfib0 : Nat.fib rho % p = 0)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) = ((ε : ℤ) : ZMod p) := by
  have hQc := prod_Q_sdiff_eq_c p rho hmin hfib0 hrho1 hrho2
  have hU := univ_sdiff_eq p rho hfib0 hrho1 hrho2
  have hN := prod_nonzero_eq_neg_one p
  have hC_card := C_card p rho hmin hrho1
  have hmain : (-1 : ZMod p)
      = ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) * ∏ c ∈ CSet p rho, c := by
    rw [← hN, hU, hQc]
  rcases hε with rfl | rfl
  · have hC2 : Finset.card (CSet p rho) = 2 := by
      rw [hC_card]
      omega
    have hCprod := prod_C_eq_neg_one_of_card_two p rho hmin hfib0 hrho1 hrho2 hC2
    rw [hCprod] at hmain
    have hneg_ne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have h1 : (1 : ZMod p) * (-1) = ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) * (-1) := by
      rw [one_mul]
      exact hmain
    have hc : (1 : ZMod p) = ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) :=
      mul_right_cancel₀ hneg_ne h1
    have heps : (((1 : ℤ)) : ZMod p) = 1 := by simp
    rw [heps]
    exact hc.symm
  · have hC0 : Finset.card (CSet p rho) = 0 := by
      rw [hC_card]
      omega
    have hCempty : CSet p rho = ∅ := Finset.card_eq_zero.mp hC0
    have hCprod : ∏ c ∈ CSet p rho, c = 1 := by
      rw [hCempty, Finset.prod_empty]
    rw [hCprod, mul_one] at hmain
    have heps : (((-1 : ℤ)) : ZMod p) = -1 := by simp
    rw [heps]
    exact hmain.symm

private theorem fib_rho_add_one_eq_eps (p rho : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    (_hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (hfib0 : Nat.fib rho % p = 0)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) :
    ((((Nat.fib (rho + 1) : ℕ)) : ZMod p)) = ((ε : ℤ) : ZMod p) := by
  have hNat : Nat.fib (rho + 1) = Nat.fib (rho - 1) + Nat.fib rho := by
    have h1 : rho - 1 + 2 = rho + 1 := by omega
    have h2 := Nat.fib_add_two (n := rho - 1)
    rw [h1] at h2
    have h3 : rho - 1 + 1 = rho := Nat.sub_add_cancel hrho1
    rw [h3] at h2
    exact h2
  have hR : ((((Nat.fib (rho + 1) : ℕ)) : ZMod p))
      = ((((Nat.fib (rho - 1) : ℕ)) : ZMod p)) + ((((Nat.fib rho : ℕ)) : ZMod p)) := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) hNat
    push_cast at hcast
    exact hcast
  have h0 : ((((Nat.fib rho : ℕ)) : ZMod p)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero hfib0
  have hc := c_eq_eps p rho ε _hp hp7 hε hrho hfib0 hmin hrho1 hrho2
  rw [hR, h0, add_zero]
  exact hc

private theorem fib_k_rho_add_one_eq_pow (p rho : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (hfib0 : Nat.fib rho % p = 0)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho) (k : ℕ) :
    ((((Nat.fib (k * rho + 1) : ℕ)) : ZMod p)) = (((ε : ℤ) : ZMod p)) ^ k := by
  induction k with
  | zero =>
    have hfib1 : Nat.fib (0 * rho + 1) = 1 := by
      have h01 : 0 * rho + 1 = 1 := by omega
      rw [h01]
      rfl
    rw [hfib1]
    simp
  | succ j ih =>
    have hNat := Nat.fib_add (j * rho) rho
    have heq : j * rho + rho + 1 = (j + 1) * rho + 1 := by ring
    rw [heq] at hNat
    have hR : ((((Nat.fib ((j + 1) * rho + 1) : ℕ)) : ZMod p))
        = ((((Nat.fib (j * rho) : ℕ)) : ZMod p)) * ((((Nat.fib rho : ℕ)) : ZMod p))
          + ((((Nat.fib (j * rho + 1) : ℕ)) : ZMod p))
            * ((((Nat.fib (rho + 1) : ℕ)) : ZMod p)) := by
      have hcast := congrArg (Nat.cast : ℕ → ZMod p) hNat
      push_cast at hcast
      exact hcast
    have h0j : ((((Nat.fib (j * rho) : ℕ)) : ZMod p)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact fib_k_rho_dvd p rho j hfib0
    have h1 := fib_rho_add_one_eq_eps p rho ε hp hp7 hε hrho hfib0 hmin hrho1 hrho2
    rw [hR, h0j, zero_mul, zero_add, h1, ih, pow_succ]

private theorem pi_a_eq_eps_pow (p rho n k : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    [NeZero (p ^ 3)] (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (hfib0 : Nat.fib rho % p = 0)
    (hmin : ∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m)
    (hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (hn : n = k * rho) (hn1 : 1 ≤ n) (half : ZMod (p ^ 3)) :
    piHom p ((Nat.fib (n - 1) : ZMod (p ^ 3)) + half * (Nat.fib n : ZMod (p ^ 3)))
      = (((ε : ℤ) : ZMod p)) ^ k := by
  have hFib1 := fib_k_rho_add_one_eq_pow p rho ε hp hp7 hε hrho hfib0 hmin hrho1 hrho2 k
  have hn_eq : n + 1 = k * rho + 1 := by rw [hn]
  have hFib_n1 : ((((Nat.fib (n + 1) : ℕ)) : ZMod p)) = (((ε : ℤ) : ZMod p)) ^ k := by
    rw [hn_eq]
    exact hFib1
  have hdvd : p ∣ Nat.fib (k * rho) := fib_k_rho_dvd p rho k hfib0
  have hfib_eq : Nat.fib n = Nat.fib (k * rho) := congrArg Nat.fib hn
  have hdvd_n : p ∣ Nat.fib n := by
    rw [hfib_eq]
    exact hdvd
  have h0n : ((((Nat.fib n : ℕ)) : ZMod p)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdvd_n
  have hNat : Nat.fib (n + 1) = Nat.fib (n - 1) + Nat.fib n := by
    have h1 : n - 1 + 2 = n + 1 := by omega
    have h2 := Nat.fib_add_two (n := n - 1)
    rw [h1] at h2
    have h3 : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    rw [h3] at h2
    exact h2
  have hR : ((((Nat.fib (n + 1) : ℕ)) : ZMod p))
      = ((((Nat.fib (n - 1) : ℕ)) : ZMod p)) + ((((Nat.fib n : ℕ)) : ZMod p)) := by
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) hNat
    push_cast at hcast
    exact hcast
  have hFn1 : ((((Nat.fib (n - 1) : ℕ)) : ZMod p)) = (((ε : ℤ) : ZMod p)) ^ k := by
    rw [hR, h0n, add_zero] at hFib_n1
    exact hFib_n1
  have hpiFn1 : piHom p ((Nat.fib (n - 1) : ZMod (p ^ 3)))
      = ((Nat.fib (n - 1) : ZMod p)) := piHom_natCast p _
  have hpiFn : piHom p ((Nat.fib n : ZMod (p ^ 3))) = 0 :=
    piHom_eq_zero_of_dvd p _ hdvd_n
  have hpi : piHom p ((Nat.fib (n - 1) : ZMod (p ^ 3)) + half * (Nat.fib n : ZMod (p ^ 3)))
      = piHom p ((Nat.fib (n - 1) : ZMod (p ^ 3)))
        + piHom p half * piHom p ((Nat.fib n : ZMod (p ^ 3))) := by
    rw [map_add, map_mul]
  have hFn1' : ((Nat.fib (n - 1) : ZMod p)) = (((ε : ℤ) : ZMod p)) ^ k := hFn1
  rw [hpi, hpiFn1, hpiFn, mul_zero, add_zero, hFn1']

private theorem pi_B_eq_eps_pow (p rho _n k : ℕ) (ε : ℤ) [Fact p.Prime] [NeZero p]
    [NeZero (p ^ 3)] (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hε : ε = 1 ∨ ε = -1) (hrho : (rho : ℤ) = (p : ℤ) - ε)
    (_hrho1 : 1 ≤ rho) (hrho2 : 2 ≤ rho)
    (a b : ZMod (p ^ 3)) (hb0 : piHom p b = 0)
    (hpa : piHom p a = (((ε : ℤ) : ZMod p)) ^ k) :
    piHom p (∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)))
      = (((ε : ℤ) : ZMod p)) ^ k := by
  have hpiB : piHom p (∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)))
      = (piHom p a) ^ (rho - 1) := by
    rw [map_prod]
    have hterm : ∀ i ∈ Finset.range (rho - 1),
        piHom p (a + b * rFun p (i + 1)) = piHom p a := by
      intro i _
      rw [map_add, map_mul, hb0, zero_mul, add_zero]
    rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]
  rw [hpiB, hpa]
  have heps_sq : ((((ε : ℤ)) : ZMod p)) ^ 2 = 1 := by
    rcases hε with rfl | rfl
    · have h1 : ((((1 : ℤ))) : ZMod p) = 1 := by simp
      rw [h1, one_pow]
    · have h1 : ((((-1 : ℤ))) : ZMod p) = -1 := by simp
      rw [h1]
      exact neg_one_sq
  have heven_rho : Even rho := (rho_facts p rho ε hp hp7 hε hrho).2.1
  obtain ⟨t, ht⟩ := heven_rho
  have ht1 : 1 ≤ t := by omega
  have heven_rho2 : Even (rho - 2) := ⟨t - 1, by omega⟩
  have heven_exp : Even (k * (rho - 2)) := heven_rho2.mul_left k
  obtain ⟨s, hs⟩ := heven_exp
  have hs2 : k * (rho - 2) = 2 * s := by
    rw [hs, two_mul]
  have hpow_even : ((((ε : ℤ)) : ZMod p)) ^ (k * (rho - 2)) = 1 := by
    rw [hs2, pow_mul, heps_sq, one_pow]
  have hrho_eq : rho - 1 = 1 + (rho - 2) := by omega
  have hexp_eq : k * (rho - 1) = k + k * (rho - 2) := by
    rw [hrho_eq, Nat.mul_add, Nat.mul_one]
  have hpow_mul : ((((ε : ℤ) : ZMod p)) ^ k) ^ (rho - 1)
      = ((((ε : ℤ)) : ZMod p)) ^ (k * (rho - 1)) := by
    rw [← pow_mul]
  rw [hpow_mul, hexp_eq, pow_add, hpow_even, mul_one]

/-- **Kimball–Webb congruence for Fibonomial coefficients modulo $p^3$.** Let $F_n$ be the
Fibonacci numbers, with $F_1 = F_2 = 1$, and write $F_n! = F_1 F_2 \cdots F_n$, with $F_0! = 1$.
Let $p \ge 7$ be a prime and $\varepsilon \in \{1, -1\}$, and suppose that $\rho = p - \varepsilon$
is the rank of appearance of $p$, that is, $p \mid F_\rho$ and $p \nmid F_m$ for $0 < m < \rho$.
Then for every natural number $k$ the Fibonomial coefficient
$$\binom{(k+1)\rho - 1}{\rho - 1}_F = \frac{F_{(k+1)\rho - 1}!}{F_{\rho - 1}!\, F_{k\rho}!}$$
is congruent to $\varepsilon^k$ modulo $p^3$.

The quotient is taken in the natural numbers; it is exact because Fibonomial coefficients are
integers. This is the Fibonacci case only, not Ballot's general theorem for Lucasnomial
coefficients.

Proves `Wanted` entry `fibonomial_prime_cube_congr`.

Source: Christian Ballot, *The Congruence of Wolstenholme for Generalized
Binomial Coefficients Related to Lucas Sequences*, Journal of Integer
Sequences 18 (2015), Article 15.5.4,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Ballot/ballot14.tex>,
Theorem `thm:KW` (rewriting Lemma 3 of Kimball and Webb), equation `eq:Fib`,
lines 144-150.
-/
theorem fibonomial_prime_cube_congr :
    ∀ (p rho : ℕ) (ε : ℤ) (k : ℕ), Nat.Prime p → 7 ≤ p →
      (ε = 1 ∨ ε = -1) → (rho : ℤ) = (p : ℤ) - ε → Nat.fib rho % p = 0 →
      (∀ m : ℕ, 0 < m → m < rho → ¬ p ∣ Nat.fib m) →
      Int.ModEq ((p : ℤ) ^ 3)
        (((Finset.prod (Finset.range ((k + 1) * rho - 1)) (fun i => Nat.fib (i + 1)) /
          (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) *
            Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1)))) : ℕ) : ℤ)
        (ε ^ k) := by
  intro p rho ε k hp hp7 hε hrho hfib0 hmin
  rcases Nat.eq_zero_or_pos k with rfl | _hpos
  · exact fibonomial_zero_case p rho ε 0 rfl hp hp7 hε hrho hfib0 hmin
  · -- Step 1 (hint): split the numerator and cancel the common factor,
    -- reducing the quotient to X / Y.
    have hrho1 : 1 ≤ rho := (rho_facts p rho ε hp hp7 hε hrho).2.2.2
    have hexpand : (k + 1) * rho = k * rho + rho := by ring
    have hsplit : (k + 1) * rho - 1 = k * rho + (rho - 1) := by omega
    have hN1pos : 0 < Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1)) :=
      Finset.prod_pos (fun i _ => Nat.fib_pos.mpr (Nat.succ_pos i))
    have hnum : Finset.prod (Finset.range ((k + 1) * rho - 1)) (fun i => Nat.fib (i + 1))
        = (Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1))) *
          (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (k * rho + i + 1))) := by
      rw [hsplit]
      exact Finset.prod_range_add _ _ _
    have hQ : (Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1))) *
          (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (k * rho + i + 1))) /
          ((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1))) *
            (Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1))))
        = (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (k * rho + i + 1))) /
          (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1))) := by
      rw [mul_comm (Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)))
        (Finset.prod (Finset.range (k * rho)) (fun i => Nat.fib (i + 1)))]
      exact Nat.mul_div_mul_left _ _ hN1pos
    rw [hnum, hQ]
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
    obtain ⟨hodd, heven_rho, h6, _h1⟩ := rho_facts p rho ε hp hp7 hε hrho
    have hrho2 : 2 ≤ rho := by omega
    set n := k * rho with hn_def
    have hn_pos : 0 < n := Nat.mul_pos _hpos (by omega)
    have hn1 : 1 ≤ n := hn_pos
    have heven_n : Even n := heven_rho.mul_left k
    have hdvd_n : p ∣ Nat.fib n := by
      have h1 : p ∣ Nat.fib rho := Nat.dvd_of_mod_eq_zero hfib0
      have h2 : Nat.fib rho ∣ Nat.fib n := by
        rw [hn_def]
        exact Nat.fib_dvd rho (k * rho) (Nat.dvd_mul_left rho k)
      exact h1.trans h2
    have hF_rho_small : piHom p ((((Nat.fib rho : ℕ)) : ZMod (p ^ 3))) = 0 :=
      piHom_eq_zero_of_dvd p _ (Nat.dvd_of_mod_eq_zero hfib0)
    have hF_n_small : piHom p ((((Nat.fib n : ℕ)) : ZMod (p ^ 3))) = 0 :=
      piHom_eq_zero_of_dvd p _ hdvd_n
    set half : ZMod (p ^ 3) := (2 : ZMod (p ^ 3))⁻¹ with hhalf_def
    have hh : 2 * half = 1 := half_spec p hodd
    set a : ZMod (p ^ 3) := ((((Nat.fib (n - 1) : ℕ)) : ZMod (p ^ 3))
      + half * ((((Nat.fib n : ℕ)) : ZMod (p ^ 3)))) with ha_def
    set b : ZMod (p ^ 3) := half * ((((Nat.fib n : ℕ)) : ZMod (p ^ 3))) with hb_def
    have hb_small : piHom p b = 0 := by
      rw [hb_def, map_mul]
      rw [hF_n_small, mul_zero]
    have hb3 : b ^ 3 = 0 := pow_three_eq_zero_of_small p b hb_small
    have hb4 : b ^ 4 = 0 := cube_zero_pow_four _ b hb3
    have hsq : a ^ 2 = 1 + 5 * b ^ 2 := by
      rw [ha_def, hb_def]
      exact a_sq_eq p n half hh heven_n hn1
    have hu_a : IsUnit a := a_isUnit_of_sq p a b hb4 hsq
    set t : ZMod (p ^ 3) := b * a⁻¹ with ht_def
    have ht_small : piHom p t = 0 := by
      rw [ht_def, map_mul]
      rw [hb_small, zero_mul]
    have ht3 : t ^ 3 = 0 := t_cube_eq_zero _ b (a⁻¹) hb3
    have ht2_eq : t ^ 2 = b ^ 2 := by
      rw [ht_def]
      exact t_sq_eq_b_sq p a b hb4 hsq hu_a
    have he1 : e1Def p rho
        = ((((Nat.fib rho : ℕ)) : ZMod (p ^ 3))) * WDef p rho :=
      e1_eq_fib_rho_mul_W p rho hp hmin hrho1 hodd
    have hW0 : piHom p (WDef p rho) = 0 :=
      pi_W_eq_zero p rho ε hp hp7 hε hrho hfib0 hmin hrho1 hrho2
    have hS0 : SDef p rho = 0 := S_eq_zero p rho ε hp hp7 hε hrho hfib0 hmin
    have hSR_eq : piHom p (SRDef p rho) = SDef p rho :=
      pi_SR_eq_S p rho hp hmin
    have hSR0 : piHom p (SRDef p rho) = 0 := by
      rw [hSR_eq, hS0]
    have hp2 : p2Def p rho
        = 5 * ((((rho - 1 : ℕ)) : ZMod (p ^ 3))) + 4 * SRDef p rho :=
      p2_eq p rho hp hmin
    have ht0 : t * e1Def p rho = 0 :=
      t_mul_e1_eq_zero p rho t ht_small hF_rho_small hW0 he1
    have ht0' : (b * a⁻¹) * e1Def p rho = 0 := by
      rw [← ht_def]
      exact ht0
    have hb0 : b * e1Def p rho = 0 :=
      b_mul_e1_eq_zero p a b _ hu_a ht0'
    have hb_e1_sq : b ^ 2 * (e1Def p rho) ^ 2 = 0 :=
      b_sq_mul_e1_sq_eq_zero p b _ hb0
    have hb_SR : b ^ 2 * SRDef p rho = 0 :=
      b_sq_mul_SR_eq_zero p rho b hb_small hSR0
    have hB1 : ((Finset.prod (Finset.range (rho - 1))
        (fun i => Nat.fib (n + i + 1)) /
        Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ZMod (p ^ 3)))
        = ∏ i ∈ Finset.range (rho - 1),
          ((Nat.fib (n + i + 1) : ZMod (p ^ 3)) * ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹) :=
      nat_div_eq_prod_ratios p rho n hp hmin hrho1
    have hB2 : (∏ i ∈ Finset.range (rho - 1),
          ((Nat.fib (n + i + 1) : ZMod (p ^ 3)) * ((Nat.fib (i + 1) : ZMod (p ^ 3)))⁻¹))
        = ∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)) := by
      have h := B_eq_prod_linear p rho n hp hmin hn1 half hh
      rw [← ha_def, ← hb_def] at h
      exact h
    have hB3 : (∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)))
        = a ^ (rho - 1)
          * (1 + t * e1Def p rho
            + t ^ 2 * half * ((e1Def p rho) ^ 2 - p2Def p rho)) :=
      prod_linear_eq_expansion p rho a b t half ht_def hu_a ht3 hh
    have hE : (1 + t * e1Def p rho
          + t ^ 2 * half * ((e1Def p rho) ^ 2 - p2Def p rho) : ZMod (p ^ 3))
        = 1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2) := by
      have h1 : t * e1Def p rho = 0 := ht0
      have h2 : t ^ 2 = b ^ 2 := ht2_eq
      have h3 : b ^ 2 * half * ((e1Def p rho) ^ 2
          - (5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) + 4 * SRDef p rho))
          = -half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2 := by
        linear_combination half * hb_e1_sq - half * 4 * hb_SR
      rw [h1, add_zero, h2, hp2, h3]
    have hB : ((Finset.prod (Finset.range (rho - 1))
          (fun i => Nat.fib (n + i + 1)) /
          Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ZMod (p ^ 3)))
        = a ^ (rho - 1)
          * (1 + (-half * 5 * ((((rho - 1 : ℕ))) : ZMod (p ^ 3)) * b ^ 2)) := by
      rw [hB1, hB2, hB3, hE]
    have hB_sq : ((Finset.prod (Finset.range (rho - 1))
          (fun i => Nat.fib (n + i + 1)) /
          Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ZMod (p ^ 3))) ^ 2
        = 1 := by
      rw [hB]
      exact pow_mul_one_add_sq_eq_one p rho a b half hb4 hsq hh
    have hpa : piHom p a = (((ε : ℤ) : ZMod p)) ^ k := by
      rw [ha_def]
      have hn_eq : n = k * rho := hn_def
      exact pi_a_eq_eps_pow p rho n k ε hp hp7 hε hrho hfib0 hmin hrho1 hrho2
        hn_eq hn1 half
    have hpiB_prod : piHom p (∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)))
        = (((ε : ℤ) : ZMod p)) ^ k :=
      pi_B_eq_eps_pow p rho n k ε hp hp7 hε hrho hrho1 hrho2 a b hb_small hpa
    have hpiB : piHom p ((Finset.prod (Finset.range (rho - 1))
          (fun i => Nat.fib (n + i + 1)) /
          Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ZMod (p ^ 3)))
        = (((ε : ℤ) : ZMod p)) ^ k := by
      have hBB : ((Finset.prod (Finset.range (rho - 1))
            (fun i => Nat.fib (n + i + 1)) /
            Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ZMod (p ^ 3)))
          = ∏ i ∈ Finset.range (rho - 1), (a + b * rFun p (i + 1)) := by
        rw [hB1, hB2]
      rw [hBB]
      exact hpiB_prod
    set B : ZMod (p ^ 3) := ((Finset.prod (Finset.range (rho - 1))
      (fun i => Nat.fib (n + i + 1)) /
      Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ZMod (p ^ 3)))
      with hB_def
    set eR : ZMod (p ^ 3) := ((((ε ^ k : ℤ))) : ZMod (p ^ 3)) with heR_def
    have hB_sq' : B ^ 2 = 1 := hB_sq
    have hpiB' : piHom p B = (((ε : ℤ) : ZMod p)) ^ k := hpiB
    have heps_sq_int : ε ^ 2 = 1 := by
      rcases hε with rfl | rfl
      · exact one_pow 2
      · exact neg_one_sq
    have hpow_int : (ε ^ k) ^ 2 = 1 := by
      have h1 : (ε ^ k) ^ 2 = ε ^ (k * 2) := (pow_mul ε k 2).symm
      have h2 : ε ^ (k * 2) = ε ^ (2 * k) := by rw [mul_comm]
      have h3 : ε ^ (2 * k) = (ε ^ 2) ^ k := pow_mul ε 2 k
      rw [h1, h2, h3, heps_sq_int, one_pow]
    have heR2 : eR ^ 2 = 1 := by
      rw [heR_def]
      have hR := congrArg (Int.cast : ℤ → ZMod (p ^ 3)) hpow_int
      push_cast at hR ⊢
      exact hR
    have hmul : (B - eR) * (B + eR) = 0 := by
      linear_combination hB_sq' - heR2
    have hpi_e : piHom p eR = (((ε : ℤ) : ZMod p)) ^ k := by
      rw [heR_def, piHom_intCast]
      norm_cast
    have hpi_add : piHom p (B + eR) = 2 * ((((ε : ℤ) : ZMod p)) ^ k) := by
      rw [map_add, hpiB', hpi_e]
      ring
    have h2ne : (2 : ZMod p) ≠ 0 := by
      have hndvd : ¬p ∣ 2 := by
        intro hdvd
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      intro h0
      rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff] at h0
      exact hndvd h0
    have heps_ne : ((((ε : ℤ)) : ZMod p)) ≠ 0 := by
      rcases hε with rfl | rfl
      · have h1 : ((((1 : ℤ))) : ZMod p) = 1 := by simp
        rw [h1]
        exact one_ne_zero
      · have h1 : ((((-1 : ℤ))) : ZMod p) = -1 := by simp
        rw [h1]
        exact neg_ne_zero.mpr one_ne_zero
    have hpow_ne : ((((ε : ℤ) : ZMod p)) ^ k) ≠ 0 := pow_ne_zero k heps_ne
    have hpi_ne : piHom p (B + eR) ≠ 0 := by
      rw [hpi_add]
      exact mul_ne_zero h2ne hpow_ne
    have hu_add : IsUnit (B + eR) := isUnit_of_pi_ne_zero p hp _ hpi_ne
    have hBeq0 : B - eR = 0 := by
      obtain ⟨v, hv1, _hv2⟩ := isUnit_iff_exists.mp hu_add
      calc B - eR = (B - eR) * 1 := by ring
        _ = (B - eR) * ((B + eR) * v) := by rw [hv1]
        _ = ((B - eR) * (B + eR)) * v := by ring
        _ = 0 * v := by rw [hmul]
        _ = 0 := zero_mul v
    have hB_eq : B = eR := sub_eq_zero.mp hBeq0
    have hmod : ((((p ^ 3 : ℕ))) : ℤ) = (p : ℤ) ^ 3 := by norm_cast
    have hR_eq : ((((Finset.prod (Finset.range (rho - 1))
        (fun i => Nat.fib (n + i + 1)) /
        Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)) : ℤ) : ZMod (p ^ 3))
        = ((((ε ^ k : ℤ))) : ZMod (p ^ 3)) := by
      have hcast : ((((Finset.prod (Finset.range (rho - 1))
          (fun i => Nat.fib (n + i + 1)) /
          Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)) : ℤ) : ZMod (p ^ 3))
          = B := by
        rw [hB_def]
        norm_cast
      rw [hcast, hB_eq, heR_def]
    have hmodEq := (ZMod.intCast_eq_intCast_iff
      (((Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (n + i + 1)) /
        Finset.prod (Finset.range (rho - 1)) (fun i => Nat.fib (i + 1)) : ℕ)) : ℤ)
      (ε ^ k) (p ^ 3)).mp hR_eq
    rw [hmod] at hmodEq
    exact hmodEq

end
end MetaMathlibExt

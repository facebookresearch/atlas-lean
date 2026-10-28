/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Variants of Wilson's theorem modulo prime powers

This file proves Gauss's generalisation of Wilson's theorem to prime powers, and describes the
square roots of `1` modulo a power of `2`.

## Main statements

* `Int.sq_modEq_one_two_pow_iff`: for `s ≥ 2`, `x ^ 2 ≡ 1 [ZMOD 2 ^ s]` iff `x` is congruent to
  `1`, `-1`, `2 ^ (s - 1) - 1` or `2 ^ (s - 1) + 1` modulo `2 ^ s`.
* `prod_univ_eq_prod_filter_sq_eq_one`: in a finite abelian group, the product of all elements is
  the product of the elements of order dividing `2`.
* `ZMod.units_eq_one_or_eq_neg_one_of_sq_eq_one`: modulo an odd prime power, the only square
  roots of `1` are `±1`.
* `ZMod.prod_units_prime_pow_eq_neg_one`: modulo an odd prime power, the product of all units is
  `-1`.
* `ZMod.prod_units_two_pow_eq_one`: modulo `2 ^ s` with `s ≥ 3`, the product of all units is `1`.
* `ZMod.prod_range_filter_not_dvd_add_eq_prod_units`: the integers prime to `p` in any block of
  `p ^ s` consecutive integers multiply to the product of all units modulo `p ^ s`.
* `ZMod.factorial_sub_mul_factorial_pred`: `(p - k)! (k - 1)! ≡ (-1) ^ k (mod p)` for a prime
  `p` and `1 ≤ k ≤ p - 1`.
-/

@[expose] public section

namespace Int

private lemma modEq_or_modEq_add_of_two_pow_dvd_sub (n : ℕ) (x c : ℤ)
    (h : (2 : ℤ) ^ (n + 1) ∣ x - c) :
    x ≡ c [ZMOD 2 ^ (n + 2)] ∨ x ≡ 2 ^ (n + 1) + c [ZMOD 2 ^ (n + 2)] := by
  obtain ⟨t, ht⟩ := h
  rcases Int.even_or_odd' t with ⟨r, rfl | rfl⟩
  · left
    exact (Int.modEq_iff_dvd.mpr ⟨-r, by rw [pow_succ _ (n + 1)]; linear_combination -ht⟩)
  · right
    exact (Int.modEq_iff_dvd.mpr ⟨-r, by rw [pow_succ _ (n + 1)]; linear_combination -ht⟩)

private lemma two_pow_dvd_of_two_pow_dvd_mul_odd (n : ℕ) (a b : ℤ) (hb : Odd b)
    (h : (2 : ℤ) ^ (n + 2) ∣ 2 * a * (2 * b)) : (2 : ℤ) ^ (n + 1) ∣ 2 * a := by
  have h2 : (2 : ℤ) ^ (n + 1) ∣ 2 * a * b := by
    rw [pow_succ] at h
    have : 2 * a * (2 * b) = 2 * a * b * 2 := by ring
    rw [this] at h
    exact (mul_dvd_mul_iff_right two_ne_zero).mp h
  have hc : IsCoprime ((2 : ℤ) ^ (n + 1)) b := (Int.isCoprime_two_left.mpr hb).pow_left
  exact hc.dvd_of_dvd_mul_right h2

/-- For `s ≥ 2`, the square roots of `1` modulo `2 ^ s` are the classes of `1`, `-1`,
`2 ^ (s - 1) - 1` and `2 ^ (s - 1) + 1`. -/
theorem sq_modEq_one_two_pow_iff {s : ℕ} (hs : 2 ≤ s) (x : ℤ) :
    x ^ 2 ≡ 1 [ZMOD 2 ^ s] ↔
      x ≡ 1 [ZMOD 2 ^ s] ∨ x ≡ -1 [ZMOD 2 ^ s] ∨
        x ≡ 2 ^ (s - 1) - 1 [ZMOD 2 ^ s] ∨ x ≡ 2 ^ (s - 1) + 1 [ZMOD 2 ^ s] := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
  have hn : n + 2 - 1 = n + 1 := by omega
  rw [hn]
  constructor
  · intro h
    have hd : (2 : ℤ) ^ (n + 2) ∣ (x - 1) * (x + 1) := by
      have := (Int.modEq_iff_dvd.mp h.symm)
      have e : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
      rwa [e] at this
    have hx : Odd x := by
      by_contra hx
      rw [Int.not_odd_iff_even] at hx
      obtain ⟨k, rfl⟩ := hx
      have h2 : (2 : ℤ) ∣ (k + k - 1) * (k + k + 1) :=
        (dvd_pow_self 2 (by omega)).trans hd
      have : (k + k - 1) * (k + k + 1) = 2 * (2 * k * k) - 1 := by ring
      rw [this] at h2
      omega
    obtain ⟨y, rfl⟩ := hx
    rcases Int.even_or_odd y with hy | hy
    · have e : (2 * y + 1 - 1) * (2 * y + 1 + 1) = 2 * y * (2 * (y + 1)) := by ring
      rw [e] at hd
      have := two_pow_dvd_of_two_pow_dvd_mul_odd n y (y + 1) hy.add_one hd
      have h' : (2 : ℤ) ^ (n + 1) ∣ 2 * y + 1 - 1 := by simpa using this
      rcases modEq_or_modEq_add_of_two_pow_dvd_sub n _ 1 h' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inr h1))
    · have e : (2 * y + 1 - 1) * (2 * y + 1 + 1) = 2 * (y + 1) * (2 * y) := by ring
      rw [e] at hd
      have := two_pow_dvd_of_two_pow_dvd_mul_odd n (y + 1) y hy hd
      have h' : (2 : ℤ) ^ (n + 1) ∣ 2 * y + 1 - (-1) := by
        have e2 : 2 * y + 1 - (-1) = 2 * (y + 1) := by ring
        rw [e2]; exact this
      rcases modEq_or_modEq_add_of_two_pow_dvd_sub n _ (-1) h' with h1 | h1
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr (Or.inl ?_))
        rwa [← sub_eq_add_neg] at h1
  · have key : ∀ c : ℤ, x ≡ c [ZMOD 2 ^ (n + 2)] → (2 : ℤ) ^ (n + 2) ∣ 1 - c ^ 2 →
        x ^ 2 ≡ 1 [ZMOD 2 ^ (n + 2)] := fun c hc hc2 =>
      (hc.pow 2).trans (Int.modEq_iff_dvd.mpr hc2)
    rintro (h | h | h | h)
    · exact key _ h (by simp)
    · exact key _ h (by simp)
    · refine key _ h ⟨-(2 ^ n - 1), ?_⟩
      rw [pow_succ, pow_succ, pow_succ]; ring
    · refine key _ h ⟨-(2 ^ n + 1), ?_⟩
      rw [pow_succ, pow_succ, pow_succ]; ring

end Int

/-- In a finite abelian group, the product of all elements equals the product of the elements
`g` with `g ^ 2 = 1`: the other elements cancel in pairs `g, g⁻¹`. -/
theorem prod_univ_eq_prod_filter_sq_eq_one (G : Type*) [CommGroup G] [Fintype G]
    [DecidableEq G] :
    ∏ g : G, g = ∏ g ∈ Finset.univ.filter (fun g : G => g ^ 2 = 1), g := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun g : G => g ^ 2 = 1)]
  have hrest : ∏ g ∈ Finset.univ.filter (fun g : G => ¬ g ^ 2 = 1), g = 1 := by
    refine Finset.prod_involution (fun g _ => g⁻¹) (fun g _ => mul_inv_cancel g) ?_ ?_ ?_
    · intro g hg _ h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      apply hg
      rw [sq]
      nth_rewrite 2 [← h]
      exact mul_inv_cancel g
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rwa [inv_pow, inv_eq_one]
    · intro g _
      exact inv_inv g
  rw [hrest, mul_one]

namespace ZMod

/-- The element `-1` of the unit group modulo an odd prime power has order two. -/
theorem orderOf_neg_one_units_prime_pow (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    orderOf (-1 : (ZMod (p ^ (s + 1)))ˣ) = 2 := by
  have h1 : (-1 : (ZMod (p ^ (s + 1)))ˣ) ≠ 1 := by
    rw [Ne, Units.ext_iff]
    simp only [Units.val_neg, Units.val_one]
    have h23 : 2 < p ^ (s + 1) := by
      have h2le := (Fact.out : p.Prime).two_le
      have h3 : 3 ≤ p := by omega
      calc 2 < 3 := by norm_num
        _ ≤ p := h3
        _ ≤ p ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) p
    have : Fact (2 < p ^ (s + 1)) := ⟨h23⟩
    exact ZMod.neg_one_ne_one
  have h2 : (-1 : (ZMod (p ^ (s + 1)))ˣ) ^ 2 = 1 := by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, neg_one_sq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 h1

/-- Modulo an odd prime power, a unit whose square is `1` is `1` or `-1`. -/
theorem units_eq_one_or_eq_neg_one_of_sq_eq_one (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (x : (ZMod (p ^ (s + 1)))ˣ) (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : IsCyclic (ZMod (p ^ (s + 1)))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 (s + 1)
  have hneg : orderOf (-1 : (ZMod (p ^ (s + 1)))ˣ) = 2 :=
    orderOf_neg_one_units_prime_pow p s hp2
  have h2dvd : 2 ∣ Fintype.card (ZMod (p ^ (s + 1)))ˣ := hneg ▸ orderOf_dvd_card
  have hcount : (Finset.univ.filter
      (fun a : (ZMod (p ^ (s + 1)))ˣ => orderOf a = 2)).card = 1 :=
    (IsCyclic.card_orderOf_eq_totient (α := (ZMod (p ^ (s + 1)))ˣ) (d := 2) h2dvd).trans
      Nat.totient_two
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcount
  have hx2 : orderOf x = 1 ∨ orderOf x = 2 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hx2 with h | h
  · exact Or.inl (orderOf_eq_one_iff.mp h)
  · have hxm : x ∈ ({a} : Finset (ZMod (p ^ (s + 1)))ˣ) := by
      rw [← ha]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩
    have hnm : (-1 : (ZMod (p ^ (s + 1)))ˣ) ∈ ({a} : Finset (ZMod (p ^ (s + 1)))ˣ) := by
      rw [← ha]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg⟩
    rw [Finset.mem_singleton] at hxm hnm
    exact Or.inr (hxm.trans hnm.symm)

/-- **Gauss's generalisation of Wilson's theorem** for odd prime powers: the product of all units
of `ZMod (p ^ (s + 1))` is `-1`. -/
theorem prod_units_prime_pow_eq_neg_one (p s : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∏ u : (ZMod (p ^ (s + 1)))ˣ, (u : ZMod (p ^ (s + 1))) = -1 := by
  classical
  have h1lt : 1 < p ^ (s + 1) := by
    have h2le := (Fact.out : p.Prime).two_le
    calc 1 < 2 := by norm_num
      _ ≤ p := h2le
      _ ≤ p ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) p
  have : Fact (1 < p ^ (s + 1)) := ⟨h1lt⟩
  have key := units_eq_one_or_eq_neg_one_of_sq_eq_one p s hp2
  have hg1 : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
      (_ : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
      ((a : ZMod (p ^ (s + 1))) * (((a⁻¹ : (ZMod (p ^ (s + 1)))ˣ)) : ZMod (p ^ (s + 1))) = 1) := by
    intro a _
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg3 : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
      (ha : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
      ((a : ZMod (p ^ (s + 1))) ≠ 1 → a⁻¹ ≠ a) := by
    intro a ha hne hcon
    apply hne
    have hmem : a ≠ (-1 : (ZMod (p ^ (s + 1)))ˣ) := (Finset.mem_erase.mp ha).1
    have hmul : a * a = a * a⁻¹ := by rw [hcon]
    have hsq : a ^ 2 = 1 := by
      rw [sq, hmul]
      exact mul_inv_cancel a
    rcases key a hsq with h | h
    · rw [h]
      rfl
    · exact absurd h hmem
  have hgmem : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
      (ha : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
      a⁻¹ ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ) := by
    intro a ha
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hcon
    have hmem : a ≠ (-1 : (ZMod (p ^ (s + 1)))ˣ) := (Finset.mem_erase.mp ha).1
    apply hmem
    have h1 : a = a⁻¹⁻¹ := (inv_inv a).symm
    rw [h1, hcon]
    apply Units.ext
    simp
  have hg4 : ∀ (a : (ZMod (p ^ (s + 1)))ˣ)
      (ha : a ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ)),
      (a⁻¹⁻¹ : (ZMod (p ^ (s + 1)))ˣ) = a := by
    intro a _
    exact inv_inv a
  have hrest : ∏ x ∈ Finset.univ.erase (-1 : (ZMod (p ^ (s + 1)))ˣ),
      (x : ZMod (p ^ (s + 1))) = 1 :=
    Finset.prod_involution (fun x _ => x⁻¹) hg1 hg3 hgmem hg4
  have hmem : (-1 : (ZMod (p ^ (s + 1)))ˣ) ∈ Finset.univ := Finset.mem_univ _
  conv_lhs => rw [← Finset.insert_erase hmem,
    Finset.prod_insert (Finset.notMem_erase _ _), hrest, mul_one]
  simp [Units.val_neg, Units.val_one]

/-- A unit of `ZMod (2 ^ (t + 3))` is the class of an integer `k` iff its least nonnegative
representative is congruent to `k`. -/
private lemma unit_val_eq_intCast_iff (t : ℕ) (u : (ZMod (2 ^ (t + 3)))ˣ) (k : ℤ) :
    (u : ZMod (2 ^ (t + 3))) = (k : ZMod (2 ^ (t + 3))) ↔
      (((u : ZMod (2 ^ (t + 3))).val : ℤ) ≡ k [ZMOD 2 ^ (t + 3)]) := by
  have hxu : ((((u : ZMod (2 ^ (t + 3))).val : ℤ)) : ZMod (2 ^ (t + 3))) =
      (u : ZMod (2 ^ (t + 3))) := by simp
  conv_lhs => rw [← hxu]
  rw [ZMod.intCast_eq_intCast_iff]
  push_cast
  rfl

private lemma coprime_two_pow_add_one (t : ℕ) :
    Nat.Coprime (2 ^ (t + 2) + 1) (2 ^ (t + 3)) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_two_right]
  exact (even_two.pow_of_ne_zero (by omega)).add_one

/-- The square roots of `1` among the units of `ZMod (2 ^ (t + 3))`. -/
private lemma units_two_pow_sq_eq_one_iff (t : ℕ) (u : (ZMod (2 ^ (t + 3)))ˣ) :
    u ^ 2 = 1 ↔ u = 1 ∨ u = -1 ∨ u = -ZMod.unitOfCoprime _ (coprime_two_pow_add_one t) ∨
      u = ZMod.unitOfCoprime _ (coprime_two_pow_add_one t) := by
  have e1 : ∀ v : (ZMod (2 ^ (t + 3)))ˣ, ∀ k : ℤ, (v : ZMod (2 ^ (t + 3))) = (k : ZMod _) →
      (u = v ↔ ((u : ZMod (2 ^ (t + 3))).val : ℤ) ≡ k [ZMOD 2 ^ (t + 3)]) := by
    intro v k hv
    rw [← unit_val_eq_intCast_iff, ← hv, Units.ext_iff]
  have hsq : u ^ 2 = 1 ↔ (((u : ZMod (2 ^ (t + 3))).val : ℤ) ^ 2 ≡ 1 [ZMOD 2 ^ (t + 3)]) := by
    have hxu : ((((u : ZMod (2 ^ (t + 3))).val : ℤ)) : ZMod (2 ^ (t + 3))) =
        (u : ZMod (2 ^ (t + 3))) := by simp
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
    conv_lhs => rw [← hxu, ← Int.cast_pow, ← Int.cast_one]
    rw [ZMod.intCast_eq_intCast_iff]
    push_cast
    rfl
  have h0 : (2 : ZMod (2 ^ (t + 3))) ^ (t + 3) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ (t + 3))
  rw [hsq, Int.sq_modEq_one_two_pow_iff (s := t + 3) (by omega), show t + 3 - 1 = t + 2 by omega,
    e1 1 1 (by simp), e1 (-1) (-1) (by simp),
    e1 _ (2 ^ (t + 2) - 1) (by
      simp only [Units.val_neg, ZMod.coe_unitOfCoprime]
      push_cast
      linear_combination (-1 : ZMod (2 ^ (t + 3))) * h0),
    e1 _ (2 ^ (t + 2) + 1) (by simp)]

/-- **Gauss's generalisation of Wilson's theorem** for `2 ^ s` with `s ≥ 3`: the product of all
units of `ZMod (2 ^ (t + 3))` is `1`. -/
theorem prod_units_two_pow_eq_one (t : ℕ) :
    ∏ u : (ZMod (2 ^ (t + 3)))ˣ, u = 1 := by
  classical
  set c := ZMod.unitOfCoprime _ (coprime_two_pow_add_one t)
  have hne : ∀ v w : (ZMod (2 ^ (t + 3)))ˣ, ∀ a b : ℤ, (v : ZMod (2 ^ (t + 3))) = a →
      (w : ZMod (2 ^ (t + 3))) = b → ¬ (8 * 2 ^ t : ℤ) ∣ b - a → v ≠ w := by
    intro v w a b hv hw hd h
    apply hd
    have : (a : ZMod (2 ^ (t + 3))) = b := by rw [← hv, ← hw, h]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
    push_cast at this
    rw [show (8 * 2 ^ t : ℤ) = 2 ^ (t + 3) by ring]
    exact this
  have hY : (0 : ℤ) < 2 ^ t := by positivity
  have h4 : ∀ d : ℤ, (8 * 2 ^ t : ℤ) ∣ d → (4 : ℤ) ∣ d := fun d hd =>
    (Dvd.intro (2 * 2 ^ t) (by ring)).trans hd
  have hc : (c : ZMod (2 ^ (t + 3))) = ((4 * 2 ^ t + 1 : ℤ) : ZMod _) := by
    simp only [c, ZMod.coe_unitOfCoprime]
    push_cast
    ring
  have hnc : ((-c : (ZMod (2 ^ (t + 3)))ˣ) : ZMod (2 ^ (t + 3))) =
      ((-(4 * 2 ^ t + 1) : ℤ) : ZMod _) := by
    rw [Units.val_neg, hc]
    push_cast
    ring
  have h1 : ((1 : (ZMod (2 ^ (t + 3)))ˣ) : ZMod (2 ^ (t + 3))) = ((1 : ℤ) : ZMod _) := by simp
  have hm1 : ((-1 : (ZMod (2 ^ (t + 3)))ˣ) : ZMod (2 ^ (t + 3))) = ((-1 : ℤ) : ZMod _) := by
    simp
  have hfilter : Finset.univ.filter (fun g : (ZMod (2 ^ (t + 3)))ˣ => g ^ 2 = 1) =
      {1, -1, -c, c} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact units_two_pow_sq_eq_one_iff t u
  have hc2 : c ^ 2 = 1 := (units_two_pow_sq_eq_one_iff t c).mpr (Or.inr (Or.inr (Or.inr rfl)))
  rw [prod_univ_eq_prod_filter_sq_eq_one, hfilter]
  rw [Finset.prod_insert, Finset.prod_insert, Finset.prod_pair]
  · rw [show (1 : (ZMod (2 ^ (t + 3)))ˣ) * (-1 * (-c * c)) = c ^ 2 by simp [sq], hc2]
  · refine hne _ _ _ _ hnc hc ?_
    intro hd; have := h4 _ hd; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hne _ _ _ _ hm1 hnc ?_, hne _ _ _ _ hm1 hc ?_⟩
    · intro hd
      have := Int.le_of_dvd (by positivity) (show (8 * 2 ^ t : ℤ) ∣ 4 * 2 ^ t by
        rw [← dvd_neg, show -(4 * 2 ^ t : ℤ) = -(4 * 2 ^ t + 1) - -1 by ring]; exact hd)
      linarith
    · intro hd; have := h4 _ hd; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hne _ _ _ _ h1 hm1 ?_, hne _ _ _ _ h1 hnc ?_, hne _ _ _ _ h1 hc ?_⟩
    · intro hd; have := h4 _ hd; omega
    · intro hd; have := h4 _ hd; omega
    · intro hd
      have := Int.le_of_dvd (by positivity) (show (8 * 2 ^ t : ℤ) ∣ 4 * 2 ^ t by
        convert hd using 1; ring)
      linarith

/-- As `j` runs over `range (p ^ s)`, the integers `n + j` prime to `p` run once over the units
of `ZMod (p ^ s)`. -/
theorem prod_range_filter_not_dvd_add_eq_prod_units (p : ℕ) [Fact p.Prime] (n s : ℕ)
    (hs : 0 < s) :
    ∏ j ∈ (Finset.range (p ^ s)).filter (fun j => ¬ p ∣ n + j),
      ((n + j : ℕ) : ZMod (p ^ s)) = ∏ u : (ZMod (p ^ s))ˣ, (u : ZMod (p ^ s)) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : ∀ j, ¬ p ∣ n + j → Nat.Coprime (n + j) (p ^ s) := fun j hj =>
    Nat.Coprime.pow_right s ((Nat.Prime.coprime_iff_not_dvd hp).mpr hj).symm
  refine Finset.prod_bij (fun j hj => ZMod.unitOfCoprime (n + j)
    (hcop j (Finset.mem_filter.mp hj).2)) ?_ ?_ ?_ ?_
  · simp
  · intro a ha b hb h
    have h' := congrArg Units.val h
    simp only [ZMod.coe_unitOfCoprime] at h'
    rw [ZMod.natCast_eq_natCast_iff] at h'
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have := Nat.ModEq.add_left_cancel' n h'
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at this
  · intro u _
    have hc : ((n + ((u : ZMod (p ^ s)) - n).val : ℕ) : ZMod (p ^ s)) = u := by
      push_cast
      simp
    refine ⟨((u : ZMod (p ^ s)) - n).val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt _, ?_⟩
      have hu : IsUnit ((n + ((u : ZMod (p ^ s)) - n).val : ℕ) : ZMod (p ^ s)) := by
        rw [hc]; exact u.isUnit
      exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hs).mp hu
    · apply Units.ext
      rw [ZMod.coe_unitOfCoprime, hc]
  · intro j hj
    simp

/-- A form of **Wilson's theorem**: for a prime `p` and `1 ≤ k ≤ p - 1`,
`(p - k)! (k - 1)! ≡ (-1) ^ k (mod p)`. -/
theorem factorial_sub_mul_factorial_pred (p : ℕ) [Fact p.Prime] {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ p - 1) :
    (((p - k).factorial * (k - 1).factorial : ℕ) : ZMod p) = (-1) ^ k := by
  have hdesc : ∀ j, j ≤ p - 1 →
      (((p - 1).descFactorial j : ℕ) : ZMod p) = (-1) ^ j * (j.factorial : ℕ) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Nat.descFactorial_succ, Nat.cast_mul, ih (by omega), Nat.cast_sub (by omega),
        Nat.cast_sub (by omega), ZMod.natCast_self, Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hw := ZMod.wilsons_lemma (p := p)
  rw [← Nat.factorial_mul_descFactorial (show m ≤ p - 1 by omega), Nat.cast_mul,
    hdesc m (by omega)] at hw
  have h1 : (p - 1 - m) = p - (m + 1) := by omega
  rw [h1] at hw
  push_cast
  have h2 : ((-1 : ZMod p)) ^ m * (-1) ^ m = 1 := by rw [← mul_pow]; simp
  rw [pow_succ]
  linear_combination ((-1 : ZMod p) ^ m) * hw -
    (((p - (m + 1)).factorial : ℕ) * ((m).factorial : ℕ) : ZMod p) * h2

end ZMod

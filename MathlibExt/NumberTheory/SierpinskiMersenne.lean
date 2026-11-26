/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LucasLehmer
public import MathlibExt.NumberTheory.Composite
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.BangZsigmondy

/-!
# Arbitrarily long sequences of Sierpiński numbers

We follow Finch-Smith and Groth, *Journal of Integer Sequences* 28 (2025), Article 25.2.4,
[Theorem 1](https://cs.uwaterloo.ca/journals/JIS/VOL28/Finch/finchs1.html).
The dyadic part of the covering classifies `n + j` by its first nonzero binary digit. It uses
primes at which the base integer is `1`, so the same congruences work for every Mersenne shift.
For each shift, a distinct odd prime splits the remaining class into smaller classes, which use
new covering primes supplied by Bang–Zsigmondy. The Chinese remainder theorem combines all of
these conditions; starting the progression beyond the covering primes ensures proper divisors.
-/

namespace MathlibExt.NumberTheory.SierpinskiMersenneWanted

open Nat

private theorem exists_prime_orderOf_two {m : ℕ} (hm : 2 ≤ m) (hm₆ : m ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = m := by
  have hne : ¬ MetaMathlibExt.IsBangZsigmondyExceptional 2 1 m := by
    rintro (⟨_, _, h⟩ | ⟨_, k, h⟩)
    · exact hm₆ h
    · cases k with
      | zero => simp at h
      | succ k =>
        exact (by decide : ¬ (2 : ℕ) ∣ 2 + 1) ⟨2 ^ k, by simpa [pow_succ, mul_comm] using h⟩
  obtain ⟨p, hp⟩ := MetaMathlibExt.bangZsigmondy_exists_primitivePrimeDivisor
    (a := 2) (b := 1) (by decide) (by decide) (by decide) hm hne
  refine ⟨p, hp.prime, ?_⟩
  have hpow (u : ℕ) :
      (2 : ZMod p) ^ u = 1 ↔ (p : ℤ) ∣ ((2 : ℕ) : ℤ) ^ u - ((1 : ℕ) : ℤ) ^ u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [sub_eq_zero]
  have hd : orderOf (2 : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one ((hpow m).2 hp.dvd)
  refine le_antisymm (Nat.le_of_dvd (by omega) hd) (le_of_not_gt ?_)
  intro hlt
  exact hp.not_dvd_of_lt (Nat.pos_of_dvd_of_pos hd (by omega)) hlt
    ((hpow _).1 (pow_orderOf_eq_one (2 : ZMod p)))

private theorem odd_mul_two_pow_inj {a b u v : ℕ} (ha : Odd a) (hb : Odd b)
    (h : a * 2 ^ u = b * 2 ^ v) : a = b ∧ u = v := by
  have hfac (c e : ℕ) (hc : Odd c) : (c * 2 ^ e).factorization 2 = e := by
    have hc₀ : c ≠ 0 := by obtain ⟨k, hk⟩ := hc; omega
    rw [Nat.factorization_mul hc₀ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hc.not_two_dvd_nat,
      Nat.factorization_pow_self Nat.prime_two, zero_add]
  have huv : u = v := by rw [← hfac a u ha, h, hfac b v hb]
  subst v
  exact ⟨Nat.mul_right_cancel (pow_pos (by decide) _) h, rfl⟩

-- The `Fin s` indices are shared across shifts. The other indices belong to a single shift `j`.
private abbrev CoverIndex {t : ℕ} (s : ℕ) (q : Fin (t + 1) → ℕ) :=
  Fin s ⊕ (Σ j : Fin (t + 1), Fin (q j))

private def coverPeriod {t s : ℕ} (q : Fin (t + 1) → ℕ) : CoverIndex s q → ℕ
  | .inl i => 2 ^ (i.val + 1)
  | .inr ⟨j, i⟩ => q j * 2 ^ (i.val + 1)

private theorem coverPeriod_injective {t s : ℕ} {q : Fin (t + 1) → ℕ}
    (hq : Function.Injective q) (hodd : ∀ j, Odd (q j)) (hgt : ∀ j, 3 < q j) :
    Function.Injective (coverPeriod (s := s) q) := by
  rintro (i | ⟨j, i⟩) (i' | ⟨j', i'⟩) h
  · exact congrArg Sum.inl (Fin.ext (Nat.succ.inj ((Nat.pow_right_injective (by decide)) h)))
  · have he := (odd_mul_two_pow_inj odd_one (hodd j') (by simpa [coverPeriod] using h)).1
    have := hgt j'
    omega
  · have he := (odd_mul_two_pow_inj odd_one (hodd j) (by simpa [coverPeriod] using h.symm)).1
    have := hgt j
    omega
  · have he := odd_mul_two_pow_inj (hodd j) (hodd j') h
    obtain rfl := hq he.1
    obtain rfl : i = i' := Fin.ext (Nat.succ.inj he.2)
    rfl

private theorem coverPeriod_bounds {t s : ℕ} {q : Fin (t + 1) → ℕ} (hgt : ∀ j, 3 < q j)
    (x : CoverIndex s q) : 2 ≤ coverPeriod q x ∧ coverPeriod q x ≠ 6 := by
  rcases x with i | ⟨j, i⟩
  · change 2 ≤ 2 ^ (i.val + 1) ∧ 2 ^ (i.val + 1) ≠ 6
    refine ⟨Nat.le_of_dvd (pow_pos (by decide) _) (pow_dvd_pow 2 (by omega : 1 ≤ i.val + 1)), ?_⟩
    intro he
    have hd : 3 ∣ 2 ^ (i.val + 1) := he ▸ (by decide : 3 ∣ 6)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  · change 2 ≤ q j * 2 ^ (i.val + 1) ∧ q j * 2 ^ (i.val + 1) ≠ 6
    have hm : 2 ≤ 2 ^ (i.val + 1) :=
      Nat.le_of_dvd (pow_pos (by decide) _) (pow_dvd_pow 2 (by omega : 1 ≤ i.val + 1))
    have hb := Nat.mul_le_mul (show 4 ≤ q j from hgt j) hm
    omega

-- Each exponent lies in a dyadic class or in the one class that the dyadic classes miss.
private theorem dyadic_cover (N s : ℕ) :
    2 ^ s ∣ N ∨ ∃ i : Fin s, N ≡ 2 ^ i.val [MOD 2 ^ (i.val + 1)] := by
  induction s with
  | zero => exact Or.inl (by simp)
  | succ s ih =>
    rcases ih with h | ⟨i, hi⟩
    · by_cases hs : 2 ^ (s + 1) ∣ N
      · exact Or.inl hs
      · obtain ⟨u, rfl⟩ := h
        have hu : u ≡ 1 [MOD 2] := by
          change u % 2 = 1
          apply Nat.two_dvd_ne_zero.mp
          intro h₂
          apply hs
          rw [pow_succ]
          exact Nat.mul_dvd_mul (dvd_refl _) h₂
        exact Or.inr ⟨⟨s, Nat.lt_succ_self s⟩, by
          simpa only [mul_one, pow_succ] using hu.mul_left' (2 ^ s)⟩
    · exact Or.inr ⟨i.castSucc, hi⟩

private theorem pow_eq_neg_one_of_orderOf {p u : ℕ} [Fact (Nat.Prime p)]
    (hord : orderOf (2 : ZMod p) = 2 ^ (u + 1)) : (2 : ZMod p) ^ (2 ^ u) = -1 := by
  have hsq : ((2 : ZMod p) ^ (2 ^ u)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, ← hord, pow_orderOf_eq_one]
  refine (sq_eq_one_iff.mp hsq).resolve_left fun he => ?_
  have hd := orderOf_dvd_of_pow_eq_one he
  rw [hord] at hd
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self u)))
    (Nat.le_of_dvd (pow_pos (by decide) _) hd)

-- Use the product as step, and add it once to the CRT representative to bound every prime.
private theorem exists_progression_zmod {ι : Type} [Finite ι] {p : ι → ℕ}
    (hp : ∀ x, (p x).Prime) (hinj : Function.Injective p) (b : ∀ x, ZMod (p x)) :
    ∃ a d : ℕ, 0 < d ∧ ∀ r x, p x ≤ a + r * d ∧ ((a + r * d : ℕ) : ZMod (p x)) = b x := by
  classical
  let _ := Fintype.ofFinite ι
  let d := ∏ x, p x
  have hd : 0 < d := Finset.prod_pos fun x _ => (hp x).pos
  have hcop : (↑(Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime p) := by
    intro x _ y _ hxy
    exact (Nat.coprime_primes (hp x) (hp y)).2 (fun he => hxy (hinj he))
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun x => (b x).val) p Finset.univ
    (fun x _ => (hp x).ne_zero) hcop
  refine ⟨a + d, d, hd, fun r x => ?_⟩
  have hdiv : p x ∣ d := Finset.dvd_prod_of_mem p (Finset.mem_univ x)
  have hx : p x ≤ d := Nat.le_of_dvd hd hdiv
  let _ : NeZero (p x) := ⟨(hp x).ne_zero⟩
  have ha' : (a : ZMod (p x)) = b x :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).2 (ha x (Finset.mem_univ x))).trans
      (ZMod.natCast_zmod_val (b x))
  refine ⟨by omega, ?_⟩
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, ha', (ZMod.natCast_eq_zero_iff _ _).2 hdiv]
  simp

private theorem cast_mersenne (p j : ℕ) : (mersenne j : ZMod p) = 2 ^ j - 1 := by
  rw [mersenne, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_two, Nat.cast_one]

private theorem composite_of_cover {p k j n : ℕ} (hp : p.Prime) (hk : p ≤ k)
    (hzero : ((k : ZMod p) + (mersenne j : ZMod p)) * 2 ^ n + 1 = 0) :
    Nat.IsComposite ((k + mersenne j) * 2 ^ n + 1) := by
  have hdiv : p ∣ (k + mersenne j) * 2 ^ n + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_two, Nat.cast_one] using hzero
  have hle : k + mersenne j ≤ (k + mersenne j) * 2 ^ n := by
    simpa only [mul_one] using Nat.mul_le_mul_left (k + mersenne j) (Nat.one_le_two_pow (n := n))
  have hlt : p < (k + mersenne j) * 2 ^ n + 1 := by omega
  refine ⟨hp.one_lt.trans hlt, fun hprime => ?_⟩
  rcases hprime.eq_one_or_self_of_dvd p hdiv with h | h
  · exact hp.ne_one h
  · exact hlt.ne h

/-- **Composite numbers from Mersenne shifts of an arithmetic progression.** For a natural
number $j$ let $M_j = 2^j - 1$ be the $j$-th Mersenne number (so $M_0 = 0$). For every natural
number $t$ there are natural numbers $a$ and $d > 0$ such that, for every natural number $r$,
every natural number $j \le t$ and every natural number $n$, the number
$(a + rd + M_j) \cdot 2^n + 1$ is composite.

Source: Carrie E. Finch-Smith and R. Scottfield Groth,
"Arbitrarily Long Sequences of Sierpiński Numbers that
are the Sum of a Sierpiński Number and a Mersenne
Number", Theorem 1. -/
public theorem exists_arithProg_sierpinski_add_mersenne
    (t : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ r : ℕ, ∀ j ≤ t, ∀ n : ℕ,
      Nat.IsComposite ((a + r * d + mersenne j) * 2 ^ n + 1) := by
  classical
  let q (j : Fin (t + 1)) := Nat.nth Nat.Prime (j.val + 2)
  have hqprime (j) : (q j).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have hqgt (j) : 3 < q j := by
    rw [← Nat.nth_prime_one_eq_three]
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime) (by omega : 1 < j.val + 2)
  have hqinj : Function.Injective q := fun j j' h =>
    Fin.ext (Nat.add_right_cancel (Nat.nth_injective Nat.infinite_setOfPred_prime h))
  let s := Finset.univ.sup q
  have hqs (j) : q j ≤ s := Finset.le_sup (Finset.mem_univ j)
  choose p hp hord using fun x : CoverIndex s q =>
    exists_prime_orderOf_two (coverPeriod_bounds hqgt x).1 (coverPeriod_bounds hqgt x).2
  have hqodd (j) : Odd (q j) :=
    (hqprime j).odd_of_ne_two (ne_of_gt ((by decide : 2 < 3).trans (hqgt j)))
  have hpinj : Function.Injective p := by
    intro x y he
    apply coverPeriod_injective hqinj hqodd hqgt
    rw [← hord x, ← hord y, he]
  -- On the extra class `n + j ≡ i * 2^s`, the complement `(q j - i) * 2^s` makes the
  -- exponent a multiple of the covering period. This writes the inverse power without division.
  let b (x : CoverIndex s q) : ZMod (p x) := match x with
    | .inl _ => 1
    | .inr ⟨j, i⟩ => 1 - 2 ^ j.val - 2 ^ (j.val + (q j - i.val) * 2 ^ s)
  obtain ⟨a, d, hd, hcrt⟩ := exists_progression_zmod hp hpinj b
  refine ⟨a, d, hd, fun r j hj n => ?_⟩
  rcases dyadic_cover (n + j) s with hmiss | ⟨i, hi⟩
  · obtain ⟨u, hu⟩ := hmiss
    let J : Fin (t + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    let i : Fin (q J) := ⟨u % q J, Nat.mod_lt _ (hqprime J).pos⟩
    let x : CoverIndex s q := .inr ⟨J, i⟩
    obtain ⟨hlt, hk⟩ := hcrt r x
    apply composite_of_cover (hp x) hlt
    have hsum : q J ∣ u + (q J - i.val) := by
      refine ⟨u / q J + 1, ?_⟩
      rw [Nat.mul_add, mul_one]
      have hmod := Nat.mod_add_div u (q J)
      have hi := i.isLt
      change u % q J < q J at hi
      change u + (q J - u % q J) = _
      omega
    have hperiod : coverPeriod q x ∣ (j + (q J - i.val) * 2 ^ s) + n := by
      rw [show (j + (q J - i.val) * 2 ^ s) + n = (u + (q J - i.val)) * 2 ^ s by
        rw [mul_comm (u + _) _, Nat.mul_add, ← hu]; ac_rfl]
      exact Nat.mul_dvd_mul hsum (pow_dvd_pow 2 ((Nat.succ_le_of_lt i.isLt).trans (hqs J)))
    have hpow : (2 : ZMod (p x)) ^ ((j + (q J - i.val) * 2 ^ s) + n) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by simpa only [hord x] using hperiod)
    rw [hk, cast_mersenne]
    change (1 - 2 ^ j - 2 ^ (j + (q J - i.val) * 2 ^ s) + (2 ^ j - 1)) * 2 ^ n + 1 = 0
    calc
      _ = 1 - (2 : ZMod (p x)) ^ ((j + (q J - i.val) * 2 ^ s) + n) := by rw [pow_add]; ring
      _ = 0 := by rw [hpow, sub_self]
  · let x : CoverIndex s q := .inl i
    let _ : Fact (Nat.Prime (p x)) := ⟨hp x⟩
    obtain ⟨hlt, hk⟩ := hcrt r x
    apply composite_of_cover (hp x) hlt
    have hord' : orderOf (2 : ZMod (p x)) = 2 ^ (i.val + 1) := hord x
    have hpow : (2 : ZMod (p x)) ^ (n + j) = (2 : ZMod (p x)) ^ (2 ^ i.val) := by
      rw [← pow_mod_orderOf _ (n + j), ← pow_mod_orderOf _ (2 ^ i.val), hord']
      exact congrArg (fun m : ℕ => (2 : ZMod (p x)) ^ m) hi
    rw [hk, cast_mersenne]
    change (1 + (2 ^ j - 1)) * 2 ^ n + 1 = 0
    calc
      _ = (2 : ZMod (p x)) ^ (n + j) + 1 := by rw [pow_add]; ring
      _ = 0 := by rw [hpow, pow_eq_neg_one_of_orderOf hord', neg_add_cancel]

end MathlibExt.NumberTheory.SierpinskiMersenneWanted

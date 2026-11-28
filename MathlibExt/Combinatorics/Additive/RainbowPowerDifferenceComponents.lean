/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import all MathlibExt.Combinatorics.Additive.RainbowPowerDifference
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.IntegralDomain
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Two- and three-component criteria for power digraphs

Let `p` be prime. Zero is isolated for every positive exponent. For positive even `k`, if all
prime divisors of `p - 1` divide `k`, a common iterate sends all units to one. Otherwise a unit
of prime order not dividing `k` has an orbit disjoint from the orbits of zero and one.

For prime `p` and odd `k ≥ 3`, there are exactly three weak components if and only if
`p - 1 = 2 * m` for some `m` whose prime divisors all divide `k`. For odd `p`, the classes of
`0`, `1`, and `-1` are distinct. If they exhaust the components, a generator of the unit group
eventually reaches `1` or `-1`, so `m` divides a power of `k`. Conversely, such an iterate sends
every nonzero vertex to a square root of one. The criterion also covers `p = 2`, where neither
side holds: there are only two vertices, and `p - 1` is odd.

## References

* Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and
  Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 1.
* Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and
  Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, pp. 1–16, Proposition 2.
* Caroline Lucheta, Eli Miller and Clifford Reiter, *Digraphs from Powers Modulo p*, Fibonacci
  Quarterly 34 (1996), 226–239, Corollary 16 (the cycle-vertex count cited in Propositions 1 and 2).
* The three-component proof adapts the quotient and common-iterate arguments of
  `card_powMap_components_eq_two_iff_of_even` in this module
  (`MathlibExt.Combinatorics.Additive.RainbowPowerDifferenceComponents`).
-/

namespace MetaMathlibExt

private def powOrbitSetoid (p k : ℕ) : Setoid (ZMod p) where
  r a b := ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n
  iseqv := by
    refine ⟨fun a => ⟨0, 0, rfl⟩, ?_, ?_⟩
    · rintro a b ⟨m, n, h⟩
      exact ⟨n, m, h.symm⟩
    · rintro a b c ⟨m, n, hab⟩ ⟨i, j, hbc⟩
      refine ⟨m + i, j + n, ?_⟩
      calc
        a ^ k ^ (m + i) = (a ^ k ^ m) ^ k ^ i := by rw [pow_add k, pow_mul]
        _ = (b ^ k ^ n) ^ k ^ i := congrArg (· ^ k ^ i) hab
        _ = (b ^ k ^ i) ^ k ^ n := by rw [← pow_mul, ← pow_mul, mul_comm (k ^ n)]
        _ = (c ^ k ^ j) ^ k ^ n := congrArg (· ^ k ^ n) hbc
        _ = c ^ k ^ (j + n) := by rw [pow_add k, pow_mul]

-- The statement retains the parity hypothesis of Proposition 1; positivity suffices.
set_option linter.unusedVariables false in
open isCycleVertex_powMap_iff_orderOf_dvd in
/-- **Power digraphs modulo a prime with two components.** Let $p$ be a prime and $k > 0$ an even
natural number, and let $G^k_p$ be the directed graph on $\mathbb{Z}/p\mathbb{Z}$ with an edge
$a \to a^k$ from every vertex $a$. Its (weak) components are the classes of the equivalence
relation "$a^{k^m} = b^{k^n}$ for some natural numbers $m, n$". Then $G^k_p$ has exactly two
components if and only if every prime factor of $p - 1$ divides $k$.

In the source, writing the prime factorization of $k$ as
$k = 2^{\alpha_0} q_1^{\alpha_1} \cdots q_\ell^{\alpha_\ell}$ with distinct odd primes
$q_1, \dots, q_\ell$, the condition reads
$p - 1 = 2^{\beta_0} q_1^{\beta_1} \cdots q_\ell^{\beta_\ell}$ with all $\beta_i \ge 0$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 1
(`integers-2024-A105-prop-1`). -/
public theorem card_powMap_components_eq_two_iff_of_even
    (p k : ℕ) [Fact p.Prime] (hk : Even k) (hk0 : 0 < k) :
    Nat.card (Quot fun a b : ZMod p => ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) = 2 ↔
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k := by
  classical
  let R := powOrbitSetoid p k
  let cls : ZMod p → Quotient R := Quotient.mk R
  change Nat.card (Quotient R) = 2 ↔ _
  have hzero {a : ZMod p} (ha : a ≠ 0) : cls a ≠ cls 0 := by
    intro h
    obtain ⟨m, n, heq⟩ := Quotient.exact h
    exact pow_ne_zero (k ^ m) ha (heq.trans (zero_pow (pow_ne_zero n hk0.ne')))
  rw [Nat.card_eq_two_iff' (cls 0)]
  constructor
  · rintro ⟨C, _, hC⟩ q hq hqdiv
    have hdiv : q ∣ Fintype.card (ZMod p)ˣ := by
      rwa [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
    -- In the cyclic group of units, a prime divisor of the group order occurs as an order.
    let S := Finset.univ.filter fun u : (ZMod p)ˣ => orderOf u = q
    have hS : S.card = q.totient := IsCyclic.card_orderOf_eq_totient hdiv
    have hSpos : 0 < S.card := by
      rw [hS, Nat.totient_prime hq]
      exact Nat.sub_pos_of_lt hq.one_lt
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hSpos
    have huorder : orderOf u = q := (Finset.mem_filter.mp hu).2
    have heq : cls (u : ZMod p) = cls 1 :=
      (hC _ (hzero (Units.ne_zero u))).trans (hC _ (hzero one_ne_zero)).symm
    obtain ⟨m, n, hmn⟩ := Quotient.exact heq
    have hm : (u : ZMod p) ^ k ^ m = 1 := hmn.trans (one_pow _)
    have hdivpow := orderOf_dvd_of_pow_eq_one hm
    rw [orderOf_units, huorder] at hdivpow
    exact hq.dvd_of_dvd_pow hdivpow
  · intro h
    have hp : p - 1 ≠ 0 := (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'
    have hpow : p - 1 ∣ k ^ (p - 1) := (Nat.dvd_pow_self_iff hp hk0.ne').mpr (by
      intro q hq
      rw [Nat.mem_primeFactors_of_ne_zero hp] at hq
      exact (Nat.mem_primeFactors_of_ne_zero hk0.ne').mpr ⟨hq.1, h q hq.1 hq.2⟩)
    refine ⟨cls 1, hzero one_ne_zero, fun C hC => ?_⟩
    obtain ⟨a, rfl⟩ := Quotient.exists_rep C
    have ha : a ≠ 0 := fun h => hC (congrArg cls h)
    obtain ⟨u, rfl⟩ := isUnit_of_ne_zero ha
    have hunit : u ^ k ^ (p - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_sub_one u).trans hpow)
    have hau : (u : ZMod p) ^ k ^ (p - 1) = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hunit
    exact Quotient.sound ⟨p - 1, 0, hau.trans (one_pow _).symm⟩

open isCycleVertex_powMap_iff_orderOf_dvd in
/-- **Power digraphs modulo a prime with three components.** Let $p$ be a prime and $k \ge 3$ an
odd natural number, and let $G^k_p$ be the directed graph on $\mathbb{Z}/p\mathbb{Z}$ with an edge
$a \to a^k$ from every vertex $a$. Its (weak) components are the classes of the equivalence
relation "$a^{k^m} = b^{k^n}$ for some natural numbers $m, n$". Then $G^k_p$ has exactly three
components if and only if $p - 1 = 2m$ for some natural number $m$ every prime factor of which
divides $k$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 2
(`integers-2024-A105-prop-2`). -/
public theorem card_powMap_components_eq_three_iff_of_odd
    (p k : ℕ) [Fact p.Prime] (hk : Odd k) (hk3 : 3 ≤ k) :
    Nat.card (Quot fun a b : ZMod p => ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) = 3 ↔
      ∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k := by
  classical
  let R := powOrbitSetoid p k
  let cls : ZMod p → Quotient R := Quotient.mk R
  have hsurj : Function.Surjective cls := Quotient.exists_rep
  change Nat.card (Quotient R) = 3 ↔ _
  by_cases hp2 : p = 2
  · subst p
    have hle := Nat.card_le_card_of_surjective cls hsurj
    rw [Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at hle
    exact iff_of_false (by omega) (by rintro ⟨m, hm, _⟩; omega)
  have hp : p.Prime := Fact.out
  have hp1 := hp.one_lt
  have hk0 : k ≠ 0 := by omega
  obtain ⟨m, hm⟩ := hp.even_sub_one hp2
  have hpm : p - 1 = 2 * m := hm.trans (two_mul m).symm
  have hm0 : m ≠ 0 := by omega
  have hzero {a : ZMod p} (ha : a ≠ 0) : cls a ≠ cls 0 := by
    intro h
    obtain ⟨i, j, e⟩ := Quotient.exact h
    exact pow_ne_zero (k ^ i) ha (e.trans (zero_pow (pow_ne_zero j hk0)))
  have hneg (i : ℕ) : (-1 : ZMod p) ^ k ^ i = -1 := (hk.pow (n := i)).neg_one_pow
  have hneg_ne : (-1 : ZMod p) ≠ 1 :=
    fun h => (ZMod.neg_one_eq_one_iff.mp h).elim hp.ne_one hp2
  have h1neg : cls 1 ≠ cls (-1) := by
    intro h
    obtain ⟨i, j, e⟩ := Quotient.exact h
    exact hneg_ne ((hneg j).symm.trans (e.symm.trans (one_pow _)))
  have h01 : cls 0 ≠ cls 1 := (hzero one_ne_zero).symm
  have h0neg : cls 0 ≠ cls (-1) := (hzero (neg_ne_zero.mpr one_ne_zero)).symm
  let reps : Finset (Quotient R) := {cls 0, cls 1, cls (-1)}
  have hreps : reps.card = 3 := by
    change ({cls 0, cls 1, cls (-1)} : Finset (Quotient R)).card = 3
    rw [Finset.card_insert_of_notMem (by simp [h01, h0neg]),
      Finset.card_insert_of_notMem (by simpa using h1neg), Finset.card_singleton]
  have hcard : Nat.card (Quotient R) = 3 ↔ ∀ a : ZMod p, cls a ∈ reps := by
    let _ : Fintype (Quotient R) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← hreps, eq_comm, Finset.card_eq_iff_eq_univ]
    constructor
    · intro h a
      rw [h]
      exact Finset.mem_univ _
    · intro h
      exact Finset.eq_univ_of_forall fun C => by
        obtain ⟨a, rfl⟩ := hsurj C
        exact h a
  rw [hcard]
  constructor
  · intro h
    -- A generator has full order, so reaching either sign forces `m` to divide an iterate exponent.
    obtain ⟨u, hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
      (inferInstance : IsCyclic (ZMod p)ˣ)
    have huorder : orderOf (u : ZMod p) = p - 1 := by
      rw [orderOf_units, hu, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime hp]
    have hcls := h (u : ZMod p)
    simp only [reps, Finset.mem_insert, Finset.mem_singleton] at hcls
    obtain ⟨i, hsq⟩ : ∃ i : ℕ, ((u : ZMod p) ^ k ^ i) ^ 2 = 1 := by
      rcases hcls.resolve_left (hzero (Units.ne_zero u)) with hOne | hNeg
      · obtain ⟨i, j, e⟩ := Quotient.exact hOne
        exact ⟨i, by rw [e, one_pow, one_pow]⟩
      · obtain ⟨i, j, e⟩ := Quotient.exact hNeg
        exact ⟨i, by rw [e, hneg]; simp⟩
    rw [← pow_mul, mul_comm (k ^ i) 2] at hsq
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [huorder, hpm] at hd
    have hdiv := Nat.dvd_of_mul_dvd_mul_left Nat.two_pos hd
    exact ⟨m, hpm, fun q hq hqm => hq.dvd_of_dvd_pow (hqm.trans hdiv)⟩
  · rintro ⟨n, hn, hall⟩
    have heq : n = m := by omega
    subst n
    have hpow : m ∣ k ^ m := (Nat.dvd_pow_self_iff hm0 hk0).mpr (by
      intro q hq
      rw [Nat.mem_primeFactors_of_ne_zero hm0] at hq
      exact (Nat.mem_primeFactors_of_ne_zero hk0).mpr ⟨hq.1, hall q hq.1 hq.2⟩)
    intro a
    by_cases ha : a = 0
    · simp [ha, reps]
    have haorder : orderOf a ∣ p - 1 := by
      obtain ⟨u, rfl⟩ := isUnit_of_ne_zero ha
      rw [orderOf_units]
      exact orderOf_dvd_sub_one u
    have hsq : (a ^ k ^ m) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm (k ^ m) 2, ← orderOf_dvd_iff_pow_eq_one]
      exact haorder.trans (hpm.symm ▸ Nat.mul_dvd_mul_left 2 hpow)
    rcases sq_eq_one_iff.mp hsq with h | h
    · have e : cls a = cls 1 := Quotient.sound ⟨m, 0, h.trans (one_pow _).symm⟩
      simp [e, reps]
    · have e : cls a = cls (-1) := Quotient.sound ⟨m, 0, h.trans (hneg 0).symm⟩
      simp [e, reps]

end MetaMathlibExt

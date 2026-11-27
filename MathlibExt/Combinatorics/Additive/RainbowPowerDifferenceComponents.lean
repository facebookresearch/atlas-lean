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
# The two-component criterion for power digraphs

Zero is isolated for every positive exponent. If all prime divisors of `p - 1` divide `k`,
a common iterate sends all units to one. Otherwise a unit of prime order not dividing `k`
has an orbit disjoint from the orbits of zero and one.

## References

* Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free Colorings and
  Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 1.
* Caroline Lucheta, Eli Miller and Clifford Reiter, *Digraphs from Powers Modulo p*, Fibonacci
  Quarterly 34 (1996), 226–239, Corollary 16 (the cycle-vertex count cited in Proposition 1).
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

end MetaMathlibExt

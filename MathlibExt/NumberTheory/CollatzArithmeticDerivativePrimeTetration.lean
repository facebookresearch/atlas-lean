/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CollatzArithmeticDerivative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-!
# The arithmetic derivative and the Collatz map on prime tetrations

A prime tetration `p ^ p` is a fixed point of the arithmetic derivative. The commutation
condition on `p ^ p` therefore asks whether its accelerated Collatz image is also fixed.

## References

* Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations Involving
  the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, pp. 1–21,
  Proposition 4 (p. 7).
* Victor Ufnarovski and Bo Åhlander, *How to Differentiate a Number*, Journal of Integer
  Sequences 6 (2003), Article 03.3.4, pp. 1–24, Theorems 1 and 6 (the prime factorization
  formula and the classification of positive fixed points).
-/

namespace MetaMathlibExt

private theorem derivative_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    arithmeticDerivative (p ^ (k + 1)) = (k + 1) * p ^ k := by
  induction k with
  | zero => simpa using arithmeticDerivative_prime hp
  | succ k ih =>
    rw [pow_succ p (k + 1), arithmeticDerivative_mul, arithmeticDerivative_prime hp, ih, mul_one,
      pow_succ p k]
    ring

private theorem derivative_prime_tetration {p : ℕ} (hp : p.Prime) :
    arithmeticDerivative (p ^ p) = p ^ p := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  change p = k + 1 at hk
  calc
    arithmeticDerivative (p ^ p) = arithmeticDerivative (p ^ (k + 1)) :=
      congrArg (fun e => arithmeticDerivative (p ^ e)) hk
    _ = (k + 1) * p ^ k := derivative_prime_pow_succ hp k
    _ = p ^ k * p := by rw [← hk, mul_comm]
    _ = p ^ p := by rw [← pow_succ, ← hk]

-- If every factor is prime and different from `p`, then `p` does not divide their product.
private theorem prime_not_dvd_prod {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime ∧ q ≠ p) : ¬ p ∣ ∏ q ∈ s, q := by
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert q s hqs ih =>
    have hq := hs q (Finset.mem_insert_self q s)
    rw [Finset.prod_insert hqs, hp.dvd_mul]
    exact not_or.mpr ⟨fun h => hq.2 ((Nat.prime_dvd_prime_iff_eq hp hq.1).mp h).symm,
      ih fun r hr => hs r (Finset.mem_insert_of_mem hr)⟩

private theorem exists_prime_tetration_of_derivative_eq {n : ℕ} (hn : 2 ≤ n)
    (h : arithmeticDerivative n = n) : ∃ p : ℕ, p.Prime ∧ n = p ^ p := by
  let s := n.primeFactors
  let M := ∏ q ∈ s, q
  let omitted (p : ℕ) := ∏ q ∈ s.erase p, q
  have hprime {p : ℕ} (hp : p ∈ s) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hs (p : ℕ) (hp : p ∈ s) : p * omitted p = M := Finset.mul_prod_erase s id hp
  have homitted (p : ℕ) : 0 < omitted p :=
    Finset.prod_pos fun _ hq => (hprime (Finset.mem_of_mem_erase hq)).pos
  have hM : 0 < M := Finset.prod_pos fun _ hq => (hprime hq).pos
  -- Clear the denominators in ∑ p, vₚ(n) / p = 1. Multiplying by M before
  -- cancelling n keeps this calculation in ℕ, where every p in the sum divides n.
  have hsum : ∑ p ∈ s, n.factorization p * omitted p = M := by
    have hmul : n * (∑ p ∈ s, n.factorization p * omitted p) = M * arithmeticDerivative n := by
      rw [arithmeticDerivative, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      calc
        n * (n.factorization p * omitted p) =
            (n / p * p) * (n.factorization p * omitted p) := by rw [Nat.div_mul_cancel hpd]
        _ = (p * omitted p) * (n.factorization p * (n / p)) := by ring
        _ = M * (n.factorization p * (n / p)) := by rw [hs p hp]
    rw [h, mul_comm M n] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  -- Modulo p, the term at p is the only one whose omitted product lacks p.
  have hvaluation (p : ℕ) (hp : p ∈ s) : n.factorization p = p := by
    have hoff : p ∣ ∑ q ∈ s.erase p, n.factorization q * omitted q := by
      apply Finset.dvd_sum
      intro q hq
      have hne := (Finset.mem_erase.mp hq).1
      have hpq : p ∈ s.erase q := Finset.mem_erase.mpr ⟨hne.symm, hp⟩
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hpq) _
    have hsplit := hsum
    rw [← Finset.sum_erase_add s (fun q => n.factorization q * omitted q) hp] at hsplit
    have hMdiv : p ∣ M := Finset.dvd_prod_of_mem id hp
    have hvd : p ∣ n.factorization p * omitted p := by
      apply (Nat.dvd_add_iff_right hoff).mpr
      rw [hsplit]
      exact hMdiv
    have hcop : ¬ p ∣ omitted p := prime_not_dvd_prod (hprime hp) (s.erase p) fun q hq =>
      ⟨hprime (Finset.mem_of_mem_erase hq), (Finset.mem_erase.mp hq).1⟩
    have hv : p ∣ n.factorization p := ((hprime hp).dvd_mul.mp hvd).resolve_right hcop
    have hvpos : 0 < n.factorization p :=
      (hprime hp).factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    have hle : n.factorization p * omitted p ≤ p * omitted p := calc
      _ ≤ ∑ q ∈ s, n.factorization q * omitted q :=
        Finset.single_le_sum (fun q _ => Nat.zero_le (n.factorization q * omitted q)) hp
      _ = _ := hsum.trans (hs p hp).symm
    exact le_antisymm (Nat.le_of_mul_le_mul_right hle (homitted p)) (Nat.le_of_dvd hvpos hv)
  -- All multiplicities are positive, so each term is now M and there is just one term.
  have hcount : s.card * M = M := by
    calc
      s.card * M = ∑ _q ∈ s, M := by simp
      _ = ∑ p ∈ s, n.factorization p * omitted p :=
        Finset.sum_congr rfl fun p hp => by rw [hvaluation p hp, hs p hp]
      _ = M := hsum
  have hcard : s.card = 1 := Nat.eq_of_mul_eq_mul_right hM (hcount.trans (one_mul M).symm)
  obtain ⟨p, hsing⟩ := Finset.card_eq_one.mp hcard
  have hp : p ∈ s := by simp [hsing]
  refine ⟨p, hprime hp, ?_⟩
  have hnfac := Nat.prod_primeFactors_pow_factorization (n := n) (by omega)
  change n = ∏ q ∈ s, q ^ n.factorization q at hnfac
  simpa [hsing, hvaluation p hp] using hnfac

private theorem two_le_collatzAccelerated {n : ℕ} (hn : 4 ≤ n) : 2 ≤ collatzAccelerated n := by
  by_cases h : n % 2 = 0
  · rw [collatzAccelerated_of_even h]
    simp only [Nat.collatzStep, h, ite_true]
    omega
  · have ho : n % 2 = 1 := by omega
    have he : (3 * n + 1) % 2 = 0 := by omega
    rw [collatzAccelerated_of_odd ho]
    simp only [Nat.collatzStep, h, ite_false, he, ite_true]
    omega

/-- **Prime tetrations where the arithmetic derivative and the Collatz map commute.** Let $D$ be
the arithmetic derivative and $C$ the accelerated Collatz map. For a prime $p$,
$D(C(p^p)) = C(D(p^p))$ if and only if $C(p^p) = q^q$ for some prime $q$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 4 (`jis-2025-25.1.8-prop-4`). -/
public theorem arithmeticDerivative_collatz_comm_prime_tetration_iff (p : ℕ)
    (hp : p.Prime) :
    arithmeticDerivative (collatzAccelerated (p ^ p)) =
        collatzAccelerated (arithmeticDerivative (p ^ p)) ↔
      ∃ q : ℕ, q.Prime ∧ collatzAccelerated (p ^ p) = q ^ q := by
  rw [derivative_prime_tetration hp]
  have hpow : 4 ≤ p ^ p := calc
    4 = (2 : ℕ) ^ 2 := rfl
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    _ ≤ p ^ p := Nat.pow_le_pow_right hp.pos hp.two_le
  constructor
  · exact exists_prime_tetration_of_derivative_eq (two_le_collatzAccelerated hpow)
  · rintro ⟨q, hq, he⟩
    rw [he, derivative_prime_tetration hq]

end MetaMathlibExt

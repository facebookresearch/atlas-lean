/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.FermatPsp
import MathlibExt.NumberTheory.FermatPseudoprimeBaseCount

/-!
# Fermat pseudoprime bases of a product of distinct primes

For distinct primes $p$ and $q$, the number of integers $1 \le b < pq$ satisfying
$b^{pq-1} \equiv 1 \pmod{pq}$ is a square. The two factors in the Fermat pseudoprime
base count are both $\gcd(p-1,q-1)$, by reducing $pq-1$ modulo $p-1$ and $q-1$.
Neither prime is required to be odd.

## References

* Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024), Article A23,
  pp. 1–10, Corollary 1 and Theorem 2. The proof uses the existing formalization of Theorem 2,
  `MetaMathlibExt.card_fermatPsp_bases_eq_prod_gcd` in
  `MathlibExt.NumberTheory.FermatPseudoprimeBaseCount`.
* Robert Baillie and Samuel S. Wagstaff, Jr., *Lucas pseudoprimes*, Mathematics of Computation 35
  (1980), pp. 1391–1417, Theorem 1; and Louis Monier, *Evaluation and comparison of two efficient
  probabilistic primality testing algorithms*, Theoretical Computer Science 12 (1980), pp. 97–108.
  These are the original sources for the base-count formula cited in Wagstaff's Theorem 2.
-/

namespace MetaMathlibExt

/-- **Products of two distinct primes have a square number of Fermat pseudoprime bases.** Let
$p$ and $q$ be distinct primes. Then the number of integers $b$ with $1 \le b < pq$ such that
$pq$ is a Fermat pseudoprime to the base $b$, that is, $b^{pq-1} \equiv 1 \pmod{pq}$, is a perfect
square.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 1 (`integers-2024-A23-cor-1`). -/
public theorem isSquare_card_fermatPsp_bases_mul_of_prime {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) :
    IsSquare {b : ℕ | 1 ≤ b ∧ b < p * q ∧ Nat.FermatPsp (p * q) b}.ncard := by
  have hn : 1 < p * q := hq.one_lt.trans_le (Nat.le_mul_of_pos_left q hp.pos)
  have gcd_sub_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
      Nat.gcd (a * b - 1) (a - 1) = Nat.gcd (b - 1) (a - 1) := by
    have h : a * b - 1 = (a - 1) * b + (b - 1) := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_sub_cancel (Nat.le_mul_of_pos_left b ha) hb]
    rw [h, Nat.gcd_mul_left_add_left]
  have hqg := gcd_sub_one q p hq.pos hp.pos
  rw [mul_comm q p] at hqg
  rw [card_fermatPsp_bases_eq_prod_gcd hn (Nat.not_prime_mul hp.ne_one hq.ne_one),
    Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
    Finset.singleton_union, Finset.prod_insert (by simpa using hpq), Finset.prod_singleton,
    gcd_sub_one p q hp.pos hq.pos, hqg, Nat.gcd_comm (q - 1) (p - 1)]
  exact ⟨Nat.gcd (p - 1) (q - 1), rfl⟩

end MetaMathlibExt

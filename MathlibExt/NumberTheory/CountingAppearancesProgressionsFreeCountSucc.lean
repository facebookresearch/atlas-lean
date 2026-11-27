/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableRecurrence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.PrimeFin
import all MathlibExt.NumberTheory.CountingAppearancesProgressionsFirstPrimes

/-!
# Recurrence for free integers modulo the first primes

The Chinese remainder theorem expresses the count as a product of the numbers of allowed
remainders. Adding a prime contributes one new factor, regardless of the new residue class.

## References

* Florian Pausinger, *Counting Appearances of Integers in Sets of Arithmetic Progressions*,
  INTEGERS 26 (2026), Article A50, pp. 1–10, Section 3, Lemma 3 (free recurrence).
* Leonard Eugene Dickson, *History of the Theory of Numbers*, Vol. I: *Divisibility and
  Primality*, Dover Publications (2005 reprint), p. 439. Pausinger's Remark 1 credits
  the zero-residue case to earlier work of de Polignac, Deschamps, and H. J. S. Smith
  reported by Dickson.
* Dennis R. Martin, *Proofs Regarding Primorial Patterns*, preprint (2006), Section 5,
  pp. 10–11, Equation (4), proves the corresponding recurrence for zero residues.
-/

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- **Lemma 3, free recurrence.** Let $k \ge 1$, let $p_1 < p_2 < \cdots$ be the primes in
increasing order, and let $r_1, \dots, r_{k+1}$ be natural numbers. For $m \in \{k, k + 1\}$
write $\mathrm{free}(m)$ for the number of integers $n$ with $1 \le n \le p_1 \cdots p_m$ such
that $n \not\equiv r_i \pmod{p_i}$ for every $i \le m$. Then
$\mathrm{free}(k+1) = (p_{k+1} - 1) \cdot \mathrm{free}(k)$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 3. -/
public theorem freeCount_firstPrimes_succ (k : ℕ) (hk : 1 ≤ k)
    (r : Fin (k + 1) → ℕ) :
    freeCount (firstPrimes (k + 1)) r =
      (Nat.nth Nat.Prime k - 1) *
        freeCount (firstPrimes k) (r ∘ Fin.castSucc) := by
  have _ := hk -- The product argument also covers the empty product.
  have hprod (m : ℕ) (s : Fin m → ℕ) : freeCount (firstPrimes m) s =
      ∏ i, (firstPrimes m i - 1) := by
    have hp (i : Fin m) : (firstPrimes m i).Prime :=
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i.val
    apply freeCount_firstPrimes.freeCount_eq_prod _ _ (fun i => (hp i).pos)
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.ne (fun h => hij (Fin.ext h)))
  rw [hprod, hprod, Fin.prod_univ_castSucc]
  exact Nat.mul_comm _ _

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

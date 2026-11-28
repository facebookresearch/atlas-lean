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

/-!
# Recurrence for occupied integers modulo the first primes

Available and occupied integers partition the period. The available-count recurrence then gives
an addition-only form of the occupied-count recurrence.

## References

* Florian Pausinger, *Counting Appearances of Integers in Sets of Arithmetic Progressions*,
  INTEGERS 26 (2026), Article A50, pp. 1–10, Section 3, Lemmas 3 and 4.
  <https://math.colgate.edu/~integers/aa50/aa50.pdf>
* For historical background on the all-zero-residue free count, Pausinger's Remark 1 credits
  A. de Polignac, J. Deschamps and H. J. S. Smith, as recorded by L. E. Dickson,
  *History of the Theory of Numbers*, Vol. I: *Divisibility and Primality*, Dover Publications
  (2005), p. 439, with proofs in D. R. Martin, *Proofs regarding primorial patterns*, preprint.
  <https://oeis.org/A005867/a005867.pdf>
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- **Occupied count.** For natural numbers $p_1, \dots, p_k$ and $r_1, \dots, r_k$, let
$\gamma(n)$ be the number of indices $i$ with $n \equiv r_i \pmod{p_i}$. The occupied count is
the number of integers $n$ with $1 \le n \le p_1 \cdots p_k$ and $\gamma(n) > 1$.

When $p_1, \dots, p_k$ are the first $k$ primes, this is the count $\mathrm{occ}(k)$ of
Pausinger's paper. -/
def occupiedCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => 1 < residueHitCount p r n)).card

private theorem availableCount_add_occupiedCount {k : ℕ} (p r : Fin k → ℕ) :
    availableCount p r + occupiedCount p r = ∏ i, p i := by
  simpa only [availableCount, occupiedCount, not_le, Nat.card_Icc, Nat.add_sub_cancel] using
    Finset.card_filter_add_card_filter_not
      (s := Finset.Icc 1 (∏ i, p i)) (p := fun n => residueHitCount p r n ≤ 1)

/-- **Lemma 3, occupied recurrence.** Let $k \ge 1$, let $p_1 < p_2 < \cdots$ be the primes in
increasing order, and let $r_1, \dots, r_{k+1}$ be natural numbers. For $m \in \{k, k + 1\}$
write $P_m = p_1 \cdots p_m$, let $\gamma_m(n)$ be the number of $i \le m$ with
$n \equiv r_i \pmod{p_i}$, let $\mathrm{occ}(m)$ be the number of integers $n$ with
$1 \le n \le P_m$ and $\gamma_m(n) > 1$, and let $\mathrm{free}(m)$ be the number of those with
$\gamma_m(n) = 0$. Then
$\mathrm{occ}(k+1) + \mathrm{free}(k) = P_k + (p_{k+1} - 1) \cdot \mathrm{occ}(k)$.

In the paper's form this reads
$\mathrm{occ}(k+1) = P_k + (p_{k+1} - 1) \cdot \mathrm{occ}(k) - \mathrm{free}(k)$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 3. -/
theorem occupiedCount_firstPrimes_succ_add_free (k : ℕ)
    (hk : 1 ≤ k) (r : Fin (k + 1) → ℕ) :
    occupiedCount (firstPrimes (k + 1)) r +
        freeCount (firstPrimes k) (r ∘ Fin.castSucc) =
      (∏ i : Fin k, Nat.nth Nat.Prime i.val) +
        (Nat.nth Nat.Prime k - 1) *
          occupiedCount (firstPrimes k) (r ∘ Fin.castSucc) := by
  let P := ∏ i, firstPrimes k i
  let q := Nat.nth Nat.Prime k
  let rs := r ∘ Fin.castSucc
  have hq : 1 ≤ q := (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k).pos
  have hprod : ∏ i, firstPrimes (k + 1) i = P * q := Fin.prod_univ_castSucc _
  have hshort := availableCount_add_occupiedCount (firstPrimes k) rs
  have hlong := availableCount_add_occupiedCount (firstPrimes (k + 1)) r
  rw [hprod, availableCount_firstPrimes_succ k hk r] at hlong
  change (q - 1) * availableCount (firstPrimes k) rs + freeCount (firstPrimes k) rs +
    occupiedCount (firstPrimes (k + 1)) r = P * q at hlong
  change occupiedCount (firstPrimes (k + 1)) r + freeCount (firstPrimes k) rs =
    P + (q - 1) * occupiedCount (firstPrimes k) rs
  have hmul : P * q = P + ((q - 1) * availableCount (firstPrimes k) rs +
      (q - 1) * occupiedCount (firstPrimes k) rs) := by
    calc
      P * q = (q - 1 + 1) * P := by rw [Nat.sub_add_cancel hq, Nat.mul_comm]
      _ = P + ((q - 1) * availableCount (firstPrimes k) rs +
          (q - 1) * occupiedCount (firstPrimes k) rs) := by
        rw [← Nat.mul_add, hshort, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  omega

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

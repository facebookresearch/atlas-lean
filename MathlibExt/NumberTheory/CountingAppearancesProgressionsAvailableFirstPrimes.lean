/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableRecurrence
import MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableCountDistinctPrimes

/-!
# Available integers modulo the first primes

For any natural number `k` and any residues modulo the first `k` primes, the number of
integers from `1` to the product of the primes that lie in at most one chosen residue class
is the determinant with those primes on its diagonal and ones off the diagonal. For `k ≥ 2`
this is the distinct-primes formula; for `k = 1` both sides are `2`. The empty case `k = 0`
extends the published available-count clause: the interval is `{1}`, and the empty determinant
is `1`. Residue representatives need not be reduced because the congruences depend only on
their residue classes. The free-count clause is separate.

## References

* Florian Pausinger, *Counting Appearances of Integers in Sets of Arithmetic Progressions*,
  INTEGERS **26** (2026), Article A50, pp. 1–10, Theorems 1 and 2.
  <https://math.colgate.edu/~integers/aa50/aa50.pdf>
* `availableCount_distinct_primes` in
  `MathlibExt.NumberTheory.CountingAppearancesProgressionsAvailableCountDistinctPrimes`
  supplies the available-count clause of Theorem 2.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- **Available integers for the first primes.** Let $k$ be a natural number, let
$p_1, \dots, p_k$ be the first $k$ primes, and let $r_1, \dots, r_k$ be any natural numbers. Call an
integer $n$ available if $n \equiv r_i \pmod{p_i}$ holds for at most one index $i$. Then the number
of available integers $n$ with $1 \le n \le p_1 p_2 \cdots p_k$ equals
$a_k = A_k(p_1, \dots, p_k)$, the determinant of the $k \times k$ matrix with diagonal entries
$p_1, \dots, p_k$ and all other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 1. -/
theorem availableCount_firstPrimes (k : ℕ)
    (r : Fin k → ℕ) :
    (availableCount (firstPrimes k) r : ℤ) =
      onesDiagDet (firstPrimes k) := by
  rcases k with _ | _ | k
  · rw [availableCount_eq_card_filter, onesDiagDet_eq_det_diagonal_add, Matrix.det_isEmpty]
    simp
  · rw [availableCount_eq_card_filter, onesDiagDet_eq_det_diagonal_add, Matrix.det_fin_one]
    simp
  · refine availableCount_distinct_primes (k + 2) (Nat.le_add_left 2 k) (firstPrimes (k + 2))
      (fun i => (firstPrimes_eq_iff.mp (rfl : firstPrimes (k + 2) i = _)).1) ?_ r
    intro i j hij
    have hi := (firstPrimes_eq_iff.mp hij).2
    have hj := (firstPrimes_eq_iff.mp (rfl : firstPrimes (k + 2) j = _)).2
    exact Fin.ext (hi.symm.trans hj)

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

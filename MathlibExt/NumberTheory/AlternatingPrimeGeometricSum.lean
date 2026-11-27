/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeometricSumsTwoSquaresAltBigeomPythagorean

/-!
# Alternating prime geometric sums as sums of two coprime squares

The alternating sum with an odd prime number of terms and an even exponent is a
special case of the alternating sum in two coprime integers.

## References

* Lorenz Halbeisen, Norbert Hungerbühler, and Franz Lemmermeyer,
  *Geometric Sums as Sums of Two Squares*, INTEGERS 26 (2026), Article A30,
  pp. 1–19, Theorems 5 and 6. The proof below specializes Theorem 6.
  <https://math.colgate.edu/~integers/aa30/aa30.pdf>
* For the characterization by primitive sums of two squares, see the sources
  cited in §1: B. Frénicle de Bessy, *Mémoires de l’Académie Royale des Sciences*,
  vol. V (Paris, 1729), pp. 22–34 and 156–163; E. Grosswald,
  *Representations of Integers as Sums of Squares* (Springer, 1985), Chapter 2;
  and C. Busenhart, L. Halbeisen, N. Hungerbühler, and O. Riesen,
  *On primitive solutions of the diophantine equation x² + y² = M*,
  Open Mathematics 19 (2021), pp. 863–868.
* Koopa Tak-Lun Koo, *Problem 12295*, American Mathematical Monthly 129 (2022),
  no. 1, pp. 86–95, posed the motivating nonalternating problems.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

/-- **Alternating geometric sums for odd primes $p$ and even $n$ are sums of two coprime squares.**
Let $p$ be an odd prime, let $n$ be a positive even integer, and let
$S = \sum_{j=0}^{p-1} (-1)^j p^{nj} = 1 - p^n + p^{2n} - \cdots + p^{(p-1)n}$. Then every prime
divisor of $S$ is $2$ or congruent to $1$ modulo $4$, and there are coprime natural numbers
$a, b$ with $S = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 5. -/
public theorem altGeomSum_pythagorean (p n : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : Even n) (hn0 : 0 < n) :
    (∀ q : ℕ, q.Prime →
      (q : ℤ) ∣ ∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j) →
        q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ, (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  obtain ⟨t, ht⟩ := hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact (Nat.ne_of_gt hn0) (by simpa using ht)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hm0 : 0 < m := by
    have := hp.two_le
    omega
  have hsum :
      (∑ j ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ j * (1 : ℤ) ^ (4 * m - 2 * j) * ((p : ℤ) ^ t.succ) ^ (2 * j)) =
      ∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j) := by
    apply Finset.sum_congr (congrArg Finset.range hm.symm)
    intro j _
    rw [one_pow, mul_one, ← pow_mul, show t.succ * (2 * j) = n * j by
      rw [← Nat.mul_assoc, Nat.mul_two, ← ht]]
  simpa only [hsum] using
    altBigeom_pythagorean 1 ((p : ℤ) ^ t.succ) m isCoprime_one_left hm0

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

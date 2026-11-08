/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The arithmetic derivative commuting with the Collatz map

Statements from Zachary P. Bradshaw, "On a Family of Solutions to Arithmetic Differential
Equations Involving the Collatz Map", *Journal of Integer Sequences* 28 (2025), Article 25.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.html>).

The arithmetic derivative `D` is `arithmeticDerivative`
(`MathlibExt/NumberTheory/ArithmeticDerivative.lean`), given by the paper's explicit formula
`D(n) = ∑_{p ∣ n} ν_p(n) · n / p` (so `D(0) = D(1) = 0`, `D(p) = 1` for primes `p`, and the
Leibniz rule holds). The paper's Collatz map is the accelerated map
`C(n) = (3n + 1)/2` for odd `n`, `C(n) = n/2` for even `n` (`collatzAccelerated`). The paper's
sequence `(aₙ)` lists the positive integers `n` with `D(C(n)) = C(D(n))`; statements about
`aₙ` are stated for every positive `n` with this property. Semiprimes `pq` and `rs` are
*compatible* (`IsCompatibleSemiprimePair p q r s`) when `p, q, r, s` are primes and `r, s` are
the roots of `2x² - (p + q)x + 3pq + 1 = 0`, that is, `2(r + s) = p + q` and
`2rs = 3pq + 1`.
-/
module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.ArithmeticDerivative
public import MathlibExt.NumberTheory.Collatz

namespace MetaMathlibExt

@[expose] public section

/-- The accelerated Collatz map: `(3n + 1)/2` for odd `n` and `n/2` for even `n`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
def collatzAccelerated (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- On odd inputs the accelerated map is two steps of `Nat.collatzStep`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem collatzAccelerated_of_odd {n : ℕ} (hn : n % 2 = 1) :
    collatzAccelerated n = Nat.collatzStep (Nat.collatzStep n) := by
  have h : (3 * n + 1) % 2 = 0 := by omega
  simp [collatzAccelerated, Nat.collatzStep, hn, h]

/-- On even inputs the accelerated map is one step of `Nat.collatzStep`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem collatzAccelerated_of_even {n : ℕ} (hn : n % 2 = 0) :
    collatzAccelerated n = Nat.collatzStep n := by
  simp [collatzAccelerated, Nat.collatzStep, hn]

/-- Semiprimes `pq` and `rs` are compatible: `p, q, r, s` are primes and `r, s` are the roots of
`2x² - (p + q)x + 3pq + 1 = 0`, i.e. `2(r + s) = p + q` and `2rs = 3pq + 1`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 3,
definition after Proposition 7. -/
def IsCompatibleSemiprimePair (p q r s : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ 2 * (r + s) = p + q ∧ 2 * (r * s) = 3 * (p * q) + 1

/-- The first entry of the paper's Table 1: `71 · 1609 = 114239` is compatible with
`349 · 491`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Table 1. -/
theorem isCompatibleSemiprimePair_71_1609 : IsCompatibleSemiprimePair 71 1609 349 491 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- For `n ≥ 2` with least prime factor `p` and `Ω(n)` prime factors counted with multiplicity,
`Ω(n) n^{(Ω(n) - 1)/Ω(n)} ≤ D(n) ≤ n log_p(n) / p`, and each bound is an equality exactly when
`n` is a prime power.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 1
(`jis-2025-25.1.8-lem-1`). -/
public theorem_wanted arithmeticDerivative_bounds (n : ℕ) (hn : 2 ≤ n) :
    let om : ℝ := n.primeFactorsList.length
    let p : ℝ := n.minFac
    let lower : ℝ := om * (n : ℝ) ^ ((om - 1) / om)
    let upper : ℝ := n * Real.logb p n / p
    lower ≤ arithmeticDerivative n ∧ (arithmeticDerivative n : ℝ) ≤ upper ∧
      (lower = arithmeticDerivative n ↔ IsPrimePow n) ∧
      ((arithmeticDerivative n : ℝ) = upper ↔ IsPrimePow n)

/-- Every positive solution of `D(C(n)) = C(D(n))` is odd.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 2 (`jis-2025-25.1.8-prop-2`). -/
public theorem_wanted odd_of_arithmeticDerivative_collatz_comm (n : ℕ) (hn : 0 < n)
    (h : arithmeticDerivative (collatzAccelerated n) =
      collatzAccelerated (arithmeticDerivative n)) :
    Odd n

/-- Every positive solution of `D(C(n)) = C(D(n))` is composite.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 3 (`jis-2025-25.1.8-prop-3`). -/
public theorem_wanted composite_of_arithmeticDerivative_collatz_comm (n : ℕ) (hn : 0 < n)
    (h : arithmeticDerivative (collatzAccelerated n) =
      collatzAccelerated (arithmeticDerivative n)) :
    1 < n ∧ ¬ n.Prime

/-- For a prime `p`, the tetration `p^p` solves `D(C(n)) = C(D(n))` if and only if
`C(p^p) = q^q` for some prime `q`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 4 (`jis-2025-25.1.8-prop-4`). -/
public theorem_wanted arithmeticDerivative_collatz_comm_prime_tetration_iff (p : ℕ)
    (hp : p.Prime) :
    arithmeticDerivative (collatzAccelerated (p ^ p)) =
        collatzAccelerated (arithmeticDerivative (p ^ p)) ↔
      ∃ q : ℕ, q.Prime ∧ collatzAccelerated (p ^ p) = q ^ q

/-- If `pq` with primes `q < p` solves `D(C(n)) = C(D(n))`, then
`p - q ≥ 2√(30p² + 2) - 10p`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 5 (`jis-2025-25.1.8-prop-5`). -/
public theorem_wanted prime_gap_bound_of_arithmeticDerivative_collatz_comm (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (h : arithmeticDerivative (collatzAccelerated (p * q)) =
      collatzAccelerated (arithmeticDerivative (p * q))) :
    2 * Real.sqrt (30 * (p : ℝ) ^ 2 + 2) - 10 * p ≤ (p : ℝ) - q

/-- No positive solution of `D(C(n)) = C(D(n))` is the square of a prime, a product of twin
primes, a product of cousin primes, or a product `p(2p + 1)` of a Sophie Germain prime and its
safe prime.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Corollary 6 (`jis-2025-25.1.8-cor-6`). -/
public theorem_wanted not_special_semiprime_of_arithmeticDerivative_collatz_comm (n : ℕ)
    (hn : 0 < n)
    (h : arithmeticDerivative (collatzAccelerated n) =
      collatzAccelerated (arithmeticDerivative n))
    (p : ℕ) (hp : p.Prime) :
    n ≠ p ^ 2 ∧ ((p + 2).Prime → n ≠ p * (p + 2)) ∧ ((p + 4).Prime → n ≠ p * (p + 4)) ∧
      ((2 * p + 1).Prime → n ≠ p * (2 * p + 1))

/-- If `p, q` are primes and both `r± = (p + q ± √(p² - 22pq + q² - 8))/4` are primes, then
`C(pq) = r₊ r₋` and `pq` solves `D(C(n)) = C(D(n))`. The square root is an integer `t ≥ 0`
with `t² = p² - 22pq + q² - 8`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 7 (`jis-2025-25.1.8-prop-7`). -/
public theorem_wanted collatzAccelerated_mul_eq_and_comm_of_roots_prime (p q r s t : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (ht : (t : ℤ) ^ 2 = (p : ℤ) ^ 2 - 22 * p * q + (q : ℤ) ^ 2 - 8)
    (hr' : 4 * (r : ℤ) = p + q + t) (hs' : 4 * (s : ℤ) = p + q - t) :
    collatzAccelerated (p * q) = r * s ∧
      arithmeticDerivative (collatzAccelerated (p * q)) =
        collatzAccelerated (arithmeticDerivative (p * q))

/-- For compatible semiprimes `pq` and `rs`, `pq ≡ 2 ≡ rs (mod 3)`; hence one of `p, q` is
`≡ 1` and the other `≡ 2 (mod 3)`, and likewise for `r, s`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 8 (`jis-2025-25.1.8-prop-8`). -/
public theorem_wanted IsCompatibleSemiprimePair.mod_three {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    p * q % 3 = 2 ∧ r * s % 3 = 2 ∧
      ((p % 3 = 1 ∧ q % 3 = 2) ∨ (p % 3 = 2 ∧ q % 3 = 1)) ∧
      ((r % 3 = 1 ∧ s % 3 = 2) ∨ (r % 3 = 2 ∧ s % 3 = 1))

/-- For compatible semiprimes `pq` and `rs`, all of `p, q, r, s` are odd.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 9
(`jis-2025-25.1.8-lem-9`). -/
public theorem_wanted IsCompatibleSemiprimePair.odd {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    Odd p ∧ Odd q ∧ Odd r ∧ Odd s

/-- If `pq` is compatible with another semiprime, then `pq ≡ 3 (mod 4)`; hence one of `p, q` is
`≡ 1` and the other `≡ 3 (mod 4)`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 10 (`jis-2025-25.1.8-prop-10`). -/
public theorem_wanted IsCompatibleSemiprimePair.mod_four {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    p * q % 4 = 3 ∧ ((p % 4 = 1 ∧ q % 4 = 3) ∨ (p % 4 = 3 ∧ q % 4 = 1))

/-- For compatible semiprimes `pq` and `rs` with `p > q`, both `r, s ≥ 241` and
`3q < r, s < 3p`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 11
(`jis-2025-25.1.8-lem-11`). -/
public theorem_wanted IsCompatibleSemiprimePair.bounds {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) (hqp : q < p) :
    241 ≤ r ∧ 241 ≤ s ∧ 3 * q < r ∧ 3 * q < s ∧ r < 3 * p ∧ s < 3 * p

/-- For compatible semiprimes `pq` and `rs`, one of `p, q` is `≡ 1` and the other `≡ 4 (mod 5)`,
and likewise for `r, s`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 12 (`jis-2025-25.1.8-prop-12`). -/
public theorem_wanted IsCompatibleSemiprimePair.mod_five {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    ((p % 5 = 1 ∧ q % 5 = 4) ∨ (q % 5 = 1 ∧ p % 5 = 4)) ∧
      ((r % 5 = 1 ∧ s % 5 = 4) ∨ (s % 5 = 1 ∧ r % 5 = 4))

/-- For compatible semiprimes `pq` and `rs`, one of `p, q` is `≡ 1` and the other
`≡ 9 (mod 10)`, and likewise for `r, s`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 13 (`jis-2025-25.1.8-prop-13`). -/
public theorem_wanted IsCompatibleSemiprimePair.mod_ten {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    ((p % 10 = 1 ∧ q % 10 = 9) ∨ (p % 10 = 9 ∧ q % 10 = 1)) ∧
      ((r % 10 = 1 ∧ s % 10 = 9) ∨ (r % 10 = 9 ∧ s % 10 = 1))

/-- The sum of the reciprocals of the semiprimes compatible with another semiprime converges.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Theorem 14 (`jis-2025-25.1.8-thm-14`). -/
public theorem_wanted summable_inv_compatibleSemiprimes :
    Summable (Set.indicator {n : ℕ | ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ n = p * q}
      fun n => (1 : ℝ) / n)

end

end MetaMathlibExt

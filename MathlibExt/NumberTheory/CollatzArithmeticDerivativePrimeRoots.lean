/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CollatzArithmeticDerivative
import Mathlib.Tactic.Linarith

/-!
# Prime roots and the derivative–Collatz equation

When the quadratic roots are prime, their product is the accelerated Collatz value of
`p * q`, and their sum is the common value of the two compositions.

## References

* Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
  Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
  pp. 1–21, Section 3, Proposition 7.
  <https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.html>
-/

namespace MetaMathlibExt

/-- **Prime roots give semiprime solutions.** Let $D$ be the arithmetic derivative and $C$ the
accelerated Collatz map. Let $p$ and $q$ be primes and let $t \ge 0$ be an integer with
$t^2 = p^2 - 22pq + q^2 - 8$. If $r = (p + q + t)/4$ and $s = (p + q - t)/4$ are both primes,
then $C(pq) = rs$ and $D(C(pq)) = C(D(pq))$.

The numbers $r$ and $s$ are the roots $(p + q \pm \sqrt{p^2 - 22pq + q^2 - 8})/4$ of
$2x^2 - (p + q)x + 3pq + 1 = 0$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 7 (`jis-2025-25.1.8-prop-7`). -/
public theorem collatzAccelerated_mul_eq_and_comm_of_roots_prime (p q r s t : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (ht : (t : ℤ) ^ 2 = (p : ℤ) ^ 2 - 22 * p * q + (q : ℤ) ^ 2 - 8)
    (hr' : 4 * (r : ℤ) = p + q + t) (hs' : 4 * (s : ℤ) = p + q - t) :
    collatzAccelerated (p * q) = r * s ∧
      arithmeticDerivative (collatzAccelerated (p * q)) =
        collatzAccelerated (arithmeticDerivative (p * q)) := by
  have hsum : 2 * (r + s) = p + q := by
    have h : 2 * ((r : ℤ) + s) = p + q := by omega
    exact_mod_cast h
  have hprod : 2 * (r * s) = 3 * (p * q) + 1 := by
    have hmul : (4 * (r : ℤ)) * (4 * (s : ℤ)) = (p + q + t) * (p + q - t) :=
      congrArg₂ (· * ·) hr' hs'
    have h : 2 * ((r : ℤ) * s) = 3 * ((p : ℤ) * q) + 1 := by
      nlinarith only [hmul, ht]
    exact_mod_cast h
  have hC : collatzAccelerated (p * q) = r * s := by
    have hodd : p * q % 2 ≠ 0 := by omega
    rw [collatzAccelerated, ite_eq_right hodd]
    omega
  have hD (a b : ℕ) (ha : a.Prime) (hb : b.Prime) :
      arithmeticDerivative (a * b) = a + b := by
    rw [arithmeticDerivative_mul, arithmeticDerivative_prime ha, arithmeticDerivative_prime hb,
      one_mul, mul_one, add_comm]
  have heven : (p + q) % 2 = 0 := by omega
  refine ⟨hC, ?_⟩
  rw [hC, hD r s hr hs, hD p q hp hq, collatzAccelerated, ite_eq_left heven]
  omega

end MetaMathlibExt

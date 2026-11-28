/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CollatzArithmeticDerivativeModFive

/-!
# Compatible semiprimes modulo ten

If `p`, `q`, `r`, and `s` are primes satisfying `2 * (r + s) = p + q` and
`2 * (r * s) = 3 * (p * q) + 1`, the two prime factors of each semiprime are congruent to
`1` and `9` modulo `10`, in either order. The proof lifts the factor residues modulo `5` from
`MetaMathlibExt.IsCompatibleSemiprimePair.mod_five` by observing that neither residue allows
a factor to be the prime `2`.

## References

* Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
  Involving the Collatz Map*, *Journal of Integer Sequences* 28 (2025), Article 25.1.8,
  pp. 1–21, Propositions 12 and 13 (p. 11), and Table 1 (p. 6).
  <https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.html>
* The proof uses `IsCompatibleSemiprimePair.mod_five` from
  `MathlibExt.NumberTheory.CollatzArithmeticDerivativeModFive`. The concrete test follows
  the corresponding example in `MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeModFive`,
  using `isCompatibleSemiprimePair_71_1609` from
  `MathlibExt.NumberTheory.CollatzArithmeticDerivative`.
-/

namespace MetaMathlibExt

/-- **Compatible semiprimes modulo 10.** Let $p, q, r, s$ be primes with $2(r + s) = p + q$ and
$2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible. Then one of $p, q$ is
congruent to $1$ and the other to $9$ modulo $10$, and likewise one of $r, s$ is congruent to $1$
and the other to $9$ modulo $10$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 13 (`jis-2025-25.1.8-prop-13`). -/
public theorem IsCompatibleSemiprimePair.mod_ten {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    ((p % 10 = 1 ∧ q % 10 = 9) ∨ (p % 10 = 9 ∧ q % 10 = 1)) ∧
      ((r % 10 = 1 ∧ s % 10 = 9) ∨ (r % 10 = 9 ∧ s % 10 = 1)) := by
  have liftPair {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
      (hmod : (a % 5 = 1 ∧ b % 5 = 4) ∨ (b % 5 = 1 ∧ a % 5 = 4)) :
      (a % 10 = 1 ∧ b % 10 = 9) ∨ (a % 10 = 9 ∧ b % 10 = 1) := by
    have ha₂ := ha.eq_two_or_odd.resolve_left (by omega)
    have hb₂ := hb.eq_two_or_odd.resolve_left (by omega)
    rcases hmod with hmod | hmod
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  obtain ⟨hpq, hrs⟩ := h.mod_five
  obtain ⟨hp, hq, hr, hs, -, -⟩ := h
  exact ⟨liftPair hp hq hpq, liftPair hr hs hrs⟩

end MetaMathlibExt

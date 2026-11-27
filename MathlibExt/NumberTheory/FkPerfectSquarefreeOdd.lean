/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FkPerfect
import all MathlibExt.NumberTheory.FkPerfect

/-!
# Odd squarefree numbers are not near Fₖ-perfect

For a nonempty product of distinct odd primes, the divisor power sum is even.
The near-perfect equation would make it odd instead.

## References

* Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
  *On Near Fₖ-Perfect and Deficient Fₖ-Perfect Numbers*, INTEGERS 25 (2025),
  Article A86, pp. 1–22, Theorem 22. The proof uses the divisor-sum product
  formula from Theorem 21, equation (36), on p. 21.
  <https://math.colgate.edu/~integers/z86/z86.pdf>
* T. Cai, D. Chen, and Y. Zhang, *Perfect numbers and Fibonacci primes (I)*,
  International Journal of Number Theory 11 (2015), pp. 159–169, introduced
  F-perfect numbers, as cited in §1 of the source.
* P. Pollack and V. Shevelev, *On perfect and near-perfect numbers*, Journal of
  Number Theory 132 (2012), pp. 3037–3046, introduced near-perfect numbers.
* M. Tang, X.-Z. Ren, and M. Li, *On near-perfect and deficient-perfect numbers*,
  Colloquium Mathematicum 133 (2013), pp. 221–226, studied the corresponding
  ordinary near-perfect and deficient-perfect problems, as cited in §1.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **No product of distinct odd primes is near $F_k$-perfect.** Let $k > 1$ and let $s$ be a
finite set of odd primes. Then $\prod_{p \in s} p$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 22. -/
public theorem not_isNearFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsNearFkPerfect k (∏ p ∈ s, p) := by
  -- Parity of powers does not require the source's restriction on the exponent.
  have _hk := hk
  rintro ⟨d, hdvd, hlt, hsum⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp only [Finset.prod_empty] at hdvd hlt
    exact (Nat.ne_of_lt hlt) (Nat.dvd_one.mp hdvd)
  · have hn := odd_prod_of_odd s (fun p hp => (hs p hp).2)
    have hd := odd_of_dvd_of_odd d _ hn hdvd
    have hσ : Even (∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k) := by
      rw [sigma_prod_eq k s (fun p hp => (hs p hp).1),
        ← Finset.mul_prod_erase s (fun p => 1 + p ^ k) hq]
      exact ((hs q hq).2.pow.one_add).mul_right _
    have h3n : Odd (3 * (∏ p ∈ s, p)) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).mul hn
    rw [hsum] at hσ
    exact (Nat.not_even_iff_odd.mpr ((hn.pow.add_odd hd.pow).add_odd h3n)) hσ

end MathlibExt.NumberTheory.FkPerfectWanted

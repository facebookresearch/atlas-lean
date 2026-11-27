/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors

/-!
# Top Kassel–Reutenauer coefficients

For indices in the top range, `n` is the only divisor counted by `kasselReutenauerCoeff`.

## References

* Christian Kassel and Christophe Reutenauer, *Pairs of Intertwined Integer Sequences*,
  Journal of Integer Sequences 29 (2026), Article 26.4.4, pp. 1–25, Lemma 14.
  The divisor interval, cited as display (2.3) in the definition, is given in the published
  proof of Lemma 14 on p. 13.
* Christian Kassel and Christophe Reutenauer, *Complete determination of the zeta function of the
  Hilbert scheme of n points on a two-dimensional torus*, The Ramanujan Journal 46 (2018),
  pp. 633–655, Theorem 1.3 (the divisor-count formula).
-/

namespace MetaMathlibExt

/-- **The Kassel–Reutenauer coefficients $a_{n,i}$.** For natural numbers $n$ and $i$, $a_{n,i}$ is
the number of positive divisors $d$ of $n$ with
$$\frac{i + \sqrt{2n + i^2}}{2} < d \le i + \sqrt{2n + i^2},$$
equivalently with $d(d - 2i) \le 2n$ and $n < 2d(d - i)$. For $n = 0$ the set of divisors is
taken to be empty, so $a_{0,i} = 0$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, display (2.3), quoting
their earlier Theorem 1.3 of *Complete determination of the zeta function of the
Hilbert scheme of n points on a two-dimensional torus*. -/
@[expose] public def kasselReutenauerCoeff (n i : ℕ) : ℕ :=
  ((Nat.divisors n).filter fun d => d * (d - 2 * i) ≤ 2 * n ∧ n < 2 * d * (d - i)).card

/-- **The top coefficients $a_{n,i}$ equal $1$.** Let $n \ge 1$ and let $i$ be a natural number
with $n \le 2i + 2$ and $i \le n - 1$; equivalently $n/2 - 1 \le i \le n - 1$, where $n/2$ is
the rational number, not the integer quotient. Then the Kassel–Reutenauer coefficient $a_{n,i}$
equals $1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 14
(`jis-2026-26.4.4-lem-14`). -/
public theorem kasselReutenauerCoeff_eq_one (n i : ℕ) (hn : 1 ≤ n) (hi : n ≤ 2 * i + 2)
    (hi' : i ≤ n - 1) : kasselReutenauerCoeff n i = 1 := by
  unfold kasselReutenauerCoeff
  suffices h : (n.divisors.filter fun d => d * (d - 2 * i) ≤ 2 * n ∧ n < 2 * d * (d - i)) =
      {n} by rw [h, Finset.card_singleton]
  ext d
  rw [Finset.mem_singleton]
  constructor
  · intro hd
    obtain ⟨hdiv, _, hlarge⟩ := Finset.mem_filter.mp hd
    by_contra hne
    obtain ⟨k, hk⟩ := (Nat.mem_divisors.mp hdiv).1
    have hk₂ : 2 ≤ k := by
      by_contra! h
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp at hk
        omega
      · exact hne (by simpa using hk.symm)
    have hd₂ : d * 2 ≤ n := hk ▸ Nat.mul_le_mul_left d hk₂
    by_cases hdi : d ≤ i
    · simp [Nat.sub_eq_zero_of_le hdi] at hlarge
    · have hgap : d - i ≤ 1 := by omega
      have hbound : 2 * d * (d - i) ≤ n := by
        calc
          2 * d * (d - i) ≤ 2 * d * 1 := Nat.mul_le_mul_left _ hgap
          _ = d * 2 := by simp [Nat.mul_comm]
          _ ≤ n := hd₂
      exact (not_lt_of_ge hbound) hlarge
  · intro hd
    subst d
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, ?_, ?_⟩
    · have hgap : n - 2 * i ≤ 2 := by omega
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hgap
    · have hgap : 1 ≤ n - i := by omega
      exact lt_of_lt_of_le (by omega : n < 2 * n) (by simpa using Nat.mul_le_mul_left (2 * n) hgap)

end MetaMathlibExt

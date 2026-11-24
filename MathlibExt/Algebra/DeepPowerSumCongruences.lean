/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Defs

/-!
# `p`-adic valuations of factorials and multinomial coefficients

Two results of Anni, Ghitza and Medvedovsky on the `p`-adic valuation `v_p`, which is
`padicValNat p`, for a prime `p`.

## Powers in an ideal and the `p`-adic valuation of factorials

Let `I` be an ideal of a commutative ring `B`. Write `x ∈ m I` for `∃ c ∈ I, x = m * c`.
`MetaMathlibExt.pow_mem_prime_pow_padicValNat_factorial_iff` states that `a ^ n ∈ p ^ v_p(n!) I`
for every `n ≥ 1` and every `a ∈ I` if and only if `a ^ p ∈ p I` for every `a ∈ I`. In a ring
where every natural number prime to `p` is a unit, `n!` is `p ^ v_p(n!)` times a unit, so the
first condition says that `a ^ n ∈ n! I` for all `n ≥ 1` and `a ∈ I`: the theorem is the paper's
step towards its criterion for divided-power ideals.

## A valuation bound for multinomial coefficients

Let `r_i` (`i ∈ s`) be natural numbers with sum `m`, and let `(m; r) = m! / ∏ r_i!` be their
multinomial coefficient `Nat.multinomial s r`.
`MetaMathlibExt.padicValNat_sum_le_add_padicValNat_multinomial` states that
`v_p(m) ≤ v_p(r_j) + v_p((m; r))` for every `j ∈ s` with `r_j ≠ 0`. The hypothesis `r_j ≠ 0` is
needed, as `v_p(0) = 0` in Mathlib: for `(r_1, r_2) = (0, p)` and `j = 1` the left side is `1`
and the right side is `0`.

## Proofs

For the first theorem, `v_p(p!) = 1` gives the forward implication. For the converse, write
`n = p q + r` with `r < p`; Legendre's formula gives `v_p(n!) = v_p((p q)!) = q + v_p(q!)`. If
`q = 0`, then `v_p(n!) = 0` and `a ^ n ∈ I` because `n ≥ 1`. Otherwise `a ^ p = p c` with
`c ∈ I`, so `a ^ (p q) = p ^ q c ^ q`, and strong induction on `n`, applied to `c` and `q < n`,
gives `c ^ q = p ^ v_p(q!) d` with `d ∈ I`; hence `a ^ n = p ^ (q + v_p(q!)) (d a ^ r)`. The
paper's proof instead treats `n = p ^ k` by induction on `k` and then expands `n` in base `p`.

For the second, splitting off `j` gives `(m; r) = C(m, r_j) (m - r_j; r)`, the last coefficient
taken over `s` without `j`, and `r_j C(m, r_j) = m C(m - 1, r_j - 1)`. So `m` divides the nonzero
number `r_j (m; r)`, and `v_p(m) ≤ v_p(r_j (m; r)) = v_p(r_j) + v_p((m; r))`. The paper deduces
the bound from Kummer's theorem instead: each trailing zero of `m` in base `p` that is not a
trailing zero of `r_j` gives a carry in the base-`p` addition `Σ_i r_i = m`.

## References

* S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
  Congruences*, INTEGERS 24 (2024), Article A46, the source of both statements (Proposition 3
  and Corollary 24). In version 2 of the arXiv preprint, arXiv:2207.07108v2 (titled *Deep
  congruences + the Brauer-Nesbitt theorem*), they are Proposition 2 of Section 2.2 and
  Corollary 20 of Section 3.5.
-/

namespace MetaMathlibExt

/-- **A prime-exponent criterion for powers in an ideal.** Let $p$ be a prime, $v_p$ the $p$-adic
valuation, and $\mathfrak{b}$ an ideal of a commutative ring $B$.
The following are equivalent: for every $n \ge 1$ and every $a \in \mathfrak{b}$ there is
$c \in \mathfrak{b}$ with $a^n = p^{v_p(n!)} c$; and for every $a \in \mathfrak{b}$ there is
$c \in \mathfrak{b}$ with $a^p = p c$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 3 (`integers-2024-A46-prop-3`). -/
public theorem pow_mem_prime_pow_padicValNat_factorial_iff {p : ℕ} [Fact p.Prime]
    {B : Type*} [CommRing B] (I : Ideal B) :
    (∀ n : ℕ, 1 ≤ n → ∀ a ∈ I, ∃ c ∈ I, a ^ n = (p : B) ^ padicValNat p n.factorial * c) ↔
      ∀ a ∈ I, ∃ c ∈ I, a ^ p = (p : B) * c := by
  have hp : p.Prime := Fact.out
  refine ⟨fun h a ha => ?_, fun h n hn => ?_⟩
  · -- The case `n = p`, as `v_p(p!) = 1`.
    obtain ⟨c, hc, hac⟩ := h p hp.one_lt.le a ha
    have hv : padicValNat p p.factorial = 1 := by
      simpa [Nat.padicValNat_def] using multiplicity_factorial_mul (p := p) 1
    exact ⟨c, hc, by rwa [hv, pow_one] at hac⟩
  · -- Strong induction on `n = p * q + r` with `r < p`, for all `a ∈ I` at once.
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < p ∧ n = p * q + r :=
        ⟨n / p, n % p, Nat.mod_lt _ hp.pos, (Nat.div_add_mod n p).symm⟩
      rw [Nat.padicValNat_def, multiplicity_factorial_mul_add q hr]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · exact ⟨a ^ r, I.pow_mem_of_mem ha r (by omega), by simp⟩
      · obtain ⟨c, hc, hac⟩ := h a ha
        obtain ⟨d, hd, hcd⟩ := ih q (by nlinarith [hp.two_le]) hq c hc
        rw [Nat.padicValNat_def] at hcd
        refine ⟨d * a ^ r, I.mul_mem_right _ hd, ?_⟩
        rw [multiplicity_factorial_mul, pow_add, pow_mul, hac, mul_pow, hcd]
        ring

/-- **A valuation bound from Kummer's theorem.** Let $p$ be a prime, let $r_1, \dots, r_k$ be
natural numbers with sum $m$, and let $j$ be an index with $r_j \ne 0$. Then

$$v_p(m) \le v_p(r_j) + v_p\binom{m}{r_1, \dots, r_k},$$

that is, $v_p(r_j) \ge v_p(m) - v_p\binom{m}{r_1, \dots, r_k}$.

The hypothesis $r_j \ne 0$ is needed because $v_p(0)$ is taken to be $0$: for $(r_1, r_2) = (0, p)$
the inequality fails at $j = 1$. With the paper's convention $v_p(0) = \infty$ that case is trivial.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 24 (`integers-2024-A46-cor-24`). -/
public theorem padicValNat_sum_le_add_padicValNat_multinomial {p : ℕ} [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (r : ι → ℕ) {j : ι} (hj : j ∈ s) (hr : r j ≠ 0) :
    padicValNat p (∑ i ∈ s, r i) ≤ padicValNat p (r j) + padicValNat p (Nat.multinomial s r) := by
  classical
  have hM : Nat.multinomial s r ≠ 0 := (Nat.multinomial_pos s r).ne'
  -- Splitting off `j`: `(m; r) = C(m, r_j) (m - r_j; r)`, the last coefficient over `s \ {j}`.
  have hsplit : Nat.multinomial s r =
      (∑ i ∈ s, r i).choose (r j) * Nat.multinomial (s.erase j) r := by
    conv_lhs => rw [← Finset.insert_erase hj]
    rw [Nat.multinomial_insert (Finset.notMem_erase j s), Finset.add_sum_erase s r hj]
  -- `m` divides `r_j (m; r)`, as `r_j C(m, r_j) = m C(m - 1, r_j - 1)`.
  have hdvd : (∑ i ∈ s, r i) ∣ r j * Nat.multinomial s r := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hr
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero
      fun h => hr (Finset.sum_eq_zero_iff.mp h j hj)
    rw [hsplit, hn, hk, ← mul_assoc, mul_comm (k + 1), ← Nat.add_one_mul_choose_eq, mul_assoc]
    exact dvd_mul_right _ _
  simp only [Nat.padicValNat_def]
  rw [← Nat.multiplicity_mul hr hM, ← multiplicity_dvd_iff_le (mul_ne_zero hr hM)]
  exact (pow_multiplicity_dvd _ _).trans hdvd

end MetaMathlibExt

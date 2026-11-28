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

Three results of Anni, Ghitza and Medvedovsky on the `p`-adic valuation `v_p`, which is
`padicValNat p`, for a prime `p`.

## Powers in an ideal and the `p`-adic valuation of factorials

Let `I` be an ideal of a commutative ring `B`. Write `x ∈ m I` for `∃ c ∈ I, x = m * c`.
`MetaMathlibExt.pow_mem_prime_pow_padicValNat_factorial_iff` states that `a ^ n ∈ p ^ v_p(n!) I`
for every `n ≥ 1` and every `a ∈ I` if and only if `a ^ p ∈ p I` for every `a ∈ I`. In a ring
where every natural number prime to `p` is a unit, `n!` is `p ^ v_p(n!)` times a unit, so the
first condition says that `a ^ n ∈ n! I` for all `n ≥ 1` and `a ∈ I`: the theorem is the paper's
step towards its criterion for divided-power ideals.

## Kummer's theorem for multinomial coefficients

Let `r_j` (`j ∈ s`) be natural numbers with sum `m`, and let `(m; r) = m! / ∏ r_j!` be their
multinomial coefficient `Nat.multinomial s r`. For `i ≥ 1`, the carry into digit position `i`
when the `r_j` are added in base `p` is `c_i = ⌊(Σ_j (r_j mod p ^ i)) / p ^ i⌋`.
`MetaMathlibExt.padicValNat_multinomial_eq_sum_carries` states that `v_p((m; r))` is the sum of
the carries `c_i` over `1 ≤ i ≤ m`; the later carries vanish, as `p ^ i > m` for `i > m`. For two
numbers this is Kummer's theorem for binomial coefficients, Mathlib's `multiplicity_choose'`,
where every carry is `0` or `1`; with more numbers a carry can be larger.

## A valuation bound for multinomial coefficients

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

For Kummer's theorem, `m = p ^ i Σ_j ⌊r_j / p ^ i⌋ + Σ_j (r_j mod p ^ i)` gives
`⌊m / p ^ i⌋ = Σ_j ⌊r_j / p ^ i⌋ + c_i`. Legendre's formula `v_p(n!) = Σ_{i ≥ 1} ⌊n / p ^ i⌋`
(Mathlib's `multiplicity_factorial`), applied over `1 ≤ i ≤ m` to `m!` and to every `r_j!`, and
`m! = (m; r) ∏_j r_j!` then give `v_p((m; r)) = Σ_i c_i`. The arXiv preprint attributes the case
of two numbers to Kummer and obtains the general case by writing the multinomial coefficient as a
product of binomial coefficients.

For the bound, splitting off `j` gives `(m; r) = C(m, r_j) (m - r_j; r)`, the last coefficient
taken over `s` without `j`, and `r_j C(m, r_j) = m C(m - 1, r_j - 1)`. So `m` divides the nonzero
number `r_j (m; r)`, and `v_p(m) ≤ v_p(r_j (m; r)) = v_p(r_j) + v_p((m; r))`. The paper deduces
the bound from Kummer's theorem instead: each trailing zero of `m` in base `p` that is not a
trailing zero of `r_j` gives a carry in the base-`p` addition `Σ_i r_i = m`.

## References

* S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
  Congruences*, INTEGERS 24 (2024), Article A46, the source of the three statements
  (Proposition 3, Kummer's theorem for multinomial coefficients and Corollary 24). In version 2
  of the arXiv preprint, arXiv:2207.07108v2 (titled *Deep congruences + the Brauer-Nesbitt
  theorem*), they are Proposition 2 of Section 2.2, and Theorem 19 (attributed to Kummer, 1852)
  and Corollary 20 of Section 3.5.
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

/-- **Kummer's theorem for multinomial coefficients.** Let $p$ be a prime and let
$r_1, \dots, r_k$ be natural numbers with sum $m$. For $i \ge 1$ let
$c_i = \lfloor ((r_1 \bmod p^i) + \dots + (r_k \bmod p^i)) / p^i \rfloor$. Then

$$v_p\binom{m}{r_1, \dots, r_k} = \sum_{i=1}^{m} c_i.$$

Here $c_i$ is the carry into digit position $i$ when $r_1 + \dots + r_k$ is added in base $p$, and
$c_i = 0$ for $i > m$, so the right side is the sum of all the carries.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Theorem 23 (`integers-2024-A46-thm-23`). -/
public theorem padicValNat_multinomial_eq_sum_carries {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (r : ι → ℕ) :
    padicValNat p (Nat.multinomial s r) =
      ∑ i ∈ Finset.Icc 1 (∑ j ∈ s, r j), (∑ j ∈ s, r j % p ^ i) / p ^ i := by
  have hp : p.Prime := Fact.out
  -- `v_p(∏_j r_j!) = Σ_j v_p(r_j!)`.
  have hprod : ∀ t : Finset ι,
      multiplicity p (∏ j ∈ t, (r j).factorial) = ∑ j ∈ t, multiplicity p (r j).factorial := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.multiplicity_mul
        (Nat.factorial_ne_zero _) (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _),
        ih]
  -- Legendre's formula for every `n ≤ m = Σ_j r_j`, summed over `1 ≤ i ≤ m`.
  have hleg : ∀ n ≤ ∑ j ∈ s, r j,
      multiplicity p n.factorial = ∑ i ∈ Finset.Icc 1 (∑ j ∈ s, r j), n / p ^ i := fun n hn => by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    exact multiplicity_factorial
      (((Nat.log_mono_right hn).trans (Nat.log_le_self p _)).trans_lt (Nat.lt_add_one _))
  -- The carry at position `i`: `⌊m / p ^ i⌋ = Σ_j ⌊r_j / p ^ i⌋ + c_i`.
  have hdiv : ∀ i, (∑ j ∈ s, r j) / p ^ i =
      ∑ j ∈ s, r j / p ^ i + (∑ j ∈ s, r j % p ^ i) / p ^ i := fun i => by
    have hsplit : ∑ j ∈ s, r j = ∑ j ∈ s, r j % p ^ i + p ^ i * ∑ j ∈ s, r j / p ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => (Nat.mod_add_div (r j) (p ^ i)).symm
    rw [hsplit, Nat.add_mul_div_left _ _ (pow_pos hp.pos i), add_comm]
  -- Compare the valuations of both sides of `(∏_j r_j!) (m; r) = m!`.
  have hr : ∀ j ∈ s, r j ≤ ∑ j ∈ s, r j := fun j hj =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  have hspec := congrArg (multiplicity p) (Nat.multinomial_spec s r)
  rw [Nat.multiplicity_mul (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _)
      (Nat.multinomial_pos s r).ne', hprod, hleg _ le_rfl,
    Finset.sum_congr rfl fun j hj => hleg (r j) (hr j hj),
    Finset.sum_congr rfl fun i _ => hdiv i, Finset.sum_add_distrib, Finset.sum_comm] at hspec
  rw [Nat.padicValNat_def]
  exact Nat.add_left_cancel hspec

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

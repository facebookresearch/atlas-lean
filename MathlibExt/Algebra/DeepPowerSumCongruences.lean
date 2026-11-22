/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Powers in an ideal and the `p`-adic valuation of factorials

Let `p` be a prime and `I` an ideal of a commutative ring `B`. Write `x ∈ m I` for
`∃ c ∈ I, x = m * c`. `MetaMathlibExt.pow_mem_prime_pow_padicValNat_factorial_iff` states that
`a ^ n ∈ p ^ v_p(n!) I` for every `n ≥ 1` and every `a ∈ I` if and only if `a ^ p ∈ p I` for every
`a ∈ I`, where `v_p` is `padicValNat p`. In a ring where every natural number prime to `p` is a
unit, `n!` is `p ^ v_p(n!)` times a unit, so the first condition says that `a ^ n ∈ n! I` for all
`n ≥ 1` and `a ∈ I`: the theorem is the paper's step towards its criterion for divided-power
ideals.

## Proof

`v_p(p!) = 1` gives the forward implication. For the converse, write `n = p q + r` with `r < p`;
Legendre's formula gives `v_p(n!) = v_p((p q)!) = q + v_p(q!)`. If `q = 0`, then `v_p(n!) = 0` and
`a ^ n ∈ I` because `n ≥ 1`. Otherwise `a ^ p = p c` with `c ∈ I`, so `a ^ (p q) = p ^ q c ^ q`,
and strong induction on `n`, applied to `c` and `q < n`, gives `c ^ q = p ^ v_p(q!) d` with
`d ∈ I`; hence `a ^ n = p ^ (q + v_p(q!)) (d a ^ r)`. The paper's proof instead treats
`n = p ^ k` by induction on `k` and then expands `n` in base `p`.

## References

* S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
  Congruences*, INTEGERS 24 (2024), Article A46, the source of the statement. In version 2 of the
  arXiv preprint, arXiv:2207.07108v2 (titled *Deep congruences + the Brauer-Nesbitt theorem*), the
  result is Proposition 2 of Section 2.2.
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

end MetaMathlibExt

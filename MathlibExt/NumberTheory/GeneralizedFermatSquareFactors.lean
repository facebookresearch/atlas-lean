/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import MathlibExt.NumberTheory.GeneralizedFermatWieferich

/-!
# Squared prime factors of generalized Fermat numbers

If an odd prime `p` coprime to `a * b` has `p ^ 2 ∣ a ^ b ^ n + 1`, then `p` is Wieferich
to base `a` and the order of `a` modulo `p` divides `2 * b ^ n`. The Wieferich congruence
and equality of the order with `2 * b ^ n` suffice for this divisibility.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Squared prime factors of generalized Fermat numbers.** For natural numbers $a$, $b$ and $n$
write $F_n(a, b) = a^{b^n} + 1$. Let $a, b \ge 2$, let $n$ be a natural number, let $p$ be an odd
prime coprime to $ab$, and write $\operatorname{ord}_p(a)$ for the multiplicative order of $a$
modulo $p$. If $p^2$ divides $F_n(a, b)$, then $a^{p-1} \equiv 1 \pmod{p^2}$ (that is, $p$ is a
Wieferich prime to base $a$) and $\operatorname{ord}_p(a)$ divides $2b^n$. Conversely, if
$a^{p-1} \equiv 1 \pmod{p^2}$ and $\operatorname{ord}_p(a) = 2b^n$, then $p^2$ divides $F_n(a, b)$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 4 (`integers-2026-A77-thm-4`). -/
public theorem sq_dvd_pow_pow_add_one_wieferich {a b n p : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime (a * b) p) :
    (p ^ 2 ∣ a ^ b ^ n + 1 →
        a ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ orderOf (a : ZMod p) ∣ 2 * b ^ n) ∧
      (a ^ (p - 1) ≡ 1 [MOD p ^ 2] → orderOf (a : ZMod p) = 2 * b ^ n →
        p ^ 2 ∣ a ^ b ^ n + 1) := by
  obtain ⟨hap, hbp⟩ := Nat.coprime_mul_iff_left.mp hcop
  constructor
  · intro h
    have hneg : (a : ZMod (p ^ 2)) ^ b ^ n = -1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa using (ZMod.natCast_eq_zero_iff _ _).mpr h
    have horder : orderOf (a : ZMod (p ^ 2)) ∣ 2 * b ^ n := by
      rw [orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, hneg]
      simp
    -- Euler’s theorem gives divisibility into p(p - 1). The order is coprime to p.
    have heuler := Nat.ModEq.pow_totient (hap.pow_right 2)
    have hphi : orderOf (a : ZMod (p ^ 2)) ∣ p * (p - 1) := by
      apply orderOf_dvd_of_pow_eq_one
      simpa [Nat.totient_prime_pow hp two_pos] using
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr heuler
    have hcop' : Nat.Coprime (2 * b ^ n) p :=
      Nat.coprime_mul_iff_left.mpr ⟨(hp.odd_of_ne_two hp2).coprime_two_left, hbp.pow_left n⟩
    have hfermat := (hcop'.coprime_dvd_left horder).dvd_of_dvd_mul_left hphi
    constructor
    · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      simpa using orderOf_dvd_iff_pow_eq_one.mp hfermat
    · refine dvd_trans ?_ horder
      simpa using orderOf_map_dvd
        (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)).toMonoidHom (a : ZMod (p ^ 2))
  · intro hw ho
    have hk : 0 < b ^ n := pow_pos (by omega) _
    -- Apply the criterion for p² ∣ x + 1 to x = a^(b^n), whose order modulo p is two.
    have hpx := hp.coprime_iff_not_dvd.mp (hap.pow_left (b ^ n)).symm
    have hcrit := sq_dvd_pow_two_pow_add_one_iff_wieferich (n := 0) hp hp2 hpx
    simp only [pow_zero, pow_one, Nat.cast_pow, Nat.zero_add] at hcrit
    refine hcrit.mpr ⟨?_, ?_⟩
    · simpa only [pow_right_comm a (p - 1), one_pow] using hw.pow (b ^ n)
    · rw [orderOf_pow_of_dvd hk.ne' (ho ▸ dvd_mul_left _ _), ho, Nat.mul_div_cancel _ hk]

end MetaMathlibExt

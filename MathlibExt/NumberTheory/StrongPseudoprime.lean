/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum.Prime

/-!
# Strong pseudoprimes

`IsStrongPseudoprime n b`: `n` is an odd composite number and, writing `n - 1 = 2 ^ k * d`
with `d` odd, the base `b ∈ ZMod n` satisfies `b ^ d = 1` or `b ^ (2 ^ i * d) = -1` for some
`i < k` (the Miller–Rabin strong probable-prime test passes although `n` is composite).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Strong pseudoprime.** Let $n$ be a natural number and $b$ a residue class modulo $n$. Then
$n$ is a strong pseudoprime to the base $b$ if $n$ is an odd composite number (that is, $n > 1$,
$n$ is odd and $n$ is not prime) and there are natural numbers $k$ and $d$ with $d$ odd and
$n - 1 = 2^k d$ such that either $b^d = 1$ or $b^{2^i d} = -1$ for some $i < k$, where the
powers are computed in $\mathbb{Z}/n\mathbb{Z}$.

For odd composite $n$ the decomposition $n - 1 = 2^k d$ with $d$ odd is unique, so the
existential agrees with the usual definition for the fixed $k$ and $d$. An integer base is used
through its residue class modulo $n$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Section 1, Congruences (2) and (3). -/
def IsStrongPseudoprime (n : ℕ) (b : ZMod n) : Prop :=
  1 < n ∧ ¬n.Prime ∧ Odd n ∧
    ∃ k d : ℕ, n - 1 = 2 ^ k * d ∧ Odd d ∧ (b ^ d = 1 ∨ ∃ i < k, b ^ (2 ^ i * d) = -1)

/-- **2047 is a strong pseudoprime to base 2.** The number $2047 = 23 \cdot 89$ is a strong
pseudoprime to the base $2$.

Indeed $2046 = 2 \cdot 1023$ with $1023$ odd, and $2^{1023} = (2^{11})^{93} = 1$ modulo $2047$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Section 1 (first strong pseudoprime to base 2 in the list given there). -/
theorem isStrongPseudoprime_2047_two : IsStrongPseudoprime 2047 2 := by
  refine ⟨by norm_num, ?_, by decide, 1, 1023, by norm_num, by decide, Or.inl ?_⟩
  · rw [show (2047 : ℕ) = 23 * 89 from rfl]
    exact Nat.not_prime_mul (by norm_num) (by norm_num)
  have h : (2 : ZMod 2047) ^ 11 = 1 := by decide
  calc (2 : ZMod 2047) ^ 1023 = ((2 : ZMod 2047) ^ 11) ^ 93 := by rw [← pow_mul]
    _ = 1 := by rw [h, one_pow]

/-- **Every odd composite is a strong pseudoprime to base 1.** Every odd composite number $n$
is a strong pseudoprime to the base $1$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, proof of Theorem 6 ("every composite `n` is spsp(1)"). -/
theorem isStrongPseudoprime_one {n : ℕ} (hn : 1 < n) (hcomp : ¬n.Prime) (hodd : Odd n) :
    IsStrongPseudoprime n 1 := by
  obtain ⟨k, d, hd, hnd⟩ := Nat.exists_eq_two_pow_mul_odd (n := n - 1) (by omega)
  exact ⟨hn, hcomp, hodd, k, d, hnd, hd, Or.inl (one_pow d)⟩

/-- **Unfolded definition of strong pseudoprimes.** Let $n$ be a natural number and $b$ a residue
class modulo $n$. Then $n$ is a strong pseudoprime to the base $b$ if and only if $n > 1$, $n$ is
not prime, $n$ is odd, and there are natural numbers $k$ and $d$ with $n - 1 = 2^k d$ and $d$ odd
such that $b^d = 1$ or $b^{2^i d} = -1$ in $\mathbb{Z}/n\mathbb{Z}$ for some $i < k$. -/
theorem isStrongPseudoprime_iff {n : ℕ} {b : ZMod n} :
    IsStrongPseudoprime n b ↔ 1 < n ∧ ¬n.Prime ∧ Odd n ∧
      ∃ k d : ℕ, n - 1 = 2 ^ k * d ∧ Odd d ∧ (b ^ d = 1 ∨ ∃ i < k, b ^ (2 ^ i * d) = -1) :=
  Iff.rfl

/-- **Strong pseudoprimes exceed one.** If $n$ is a strong pseudoprime to some base $b$ modulo
$n$, then $n > 1$. -/
theorem IsStrongPseudoprime.one_lt {n : ℕ} {b : ZMod n} (h : IsStrongPseudoprime n b) :
    1 < n :=
  h.1

/-- **Strong pseudoprimes are not prime.** If $n$ is a strong pseudoprime to some base $b$
modulo $n$, then $n$ is not prime. -/
theorem IsStrongPseudoprime.not_prime {n : ℕ} {b : ZMod n} (h : IsStrongPseudoprime n b) :
    ¬n.Prime :=
  h.2.1

/-- **Strong pseudoprimes are odd.** If $n$ is a strong pseudoprime to some base $b$ modulo $n$,
then $n$ is odd. -/
theorem IsStrongPseudoprime.odd {n : ℕ} {b : ZMod n} (h : IsStrongPseudoprime n b) : Odd n :=
  h.2.2.1

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LucasLehmer
public import MathlibExt.NumberTheory.MersenneOmega
public import MathlibExt.NumberTheory.OrderOfTwoMulCoprime
public import MathlibExt.NumberTheory.PellEulerSolutions

/-!
# The Lucas–Lehmer test with the rational seed `6/5`

Statement from E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer
Primality Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5.

The sequence is `s_{i+1} = s_i² - 2` computed modulo `M_n = 2ⁿ - 1`, so `s_{k}` is the
`(k - 1)`-fold iterate of `x ↦ x² - 2` from the seed `s_1`. The rational seed `6/5` is read in
`ZMod M_n` as `6 · 5⁻¹`; `5` is a unit modulo `M_n` for odd `n`, since `5 ∣ 2ⁿ - 1` only when
`4 ∣ n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Lucas–Lehmer test with the rational seed $6/5$.** Let $n \ge 3$, let $M_n = 2^n - 1$, and
define $s_1 = 6 \cdot 5^{-1}$ and $s_{k+1} = s_k^2 - 2$ in $\mathbb{Z}/M_n\mathbb{Z}$. If
$n \equiv 3 \pmod 4$, then $M_n$ is prime if and only if $s_{n-1} = 0$. If $n \equiv 1 \pmod 4$,
then $M_n$ is prime if and only if $s_{n-2} = 0$.

In both cases $n$ is odd, so $5$ does not divide $M_n$ and $5^{-1}$ is the inverse of $5$
modulo $M_n$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 17. -/
theorem_wanted mersenne_prime_iff_lucasLehmer_six_div_five {n : ℕ} (h3 : 3 ≤ n) :
    (n % 4 = 3 → ((mersenne n).Prime ↔
      (fun x : ZMod (mersenne n) => x ^ 2 - 2)^[n - 2] (6 * 5⁻¹) = 0)) ∧
    (n % 4 = 1 → ((mersenne n).Prime ↔
      (fun x : ZMod (mersenne n) => x ^ 2 - 2)^[n - 3] (6 * 5⁻¹) = 0))

/-! ### Lehmer sequences and the general test -/

/-- **Lehmer's companion sequence.** For integers $R$ and $Q$, Lehmer's companion sequence
$\bar V_k(R, Q)$, $k = 0, 1, 2, \ldots$, is the integer sequence with $\bar V_0 = 2$,
$\bar V_1 = 1$, $\bar V_2 = R - 2Q$, $\bar V_3 = R - 3Q$ and
$\bar V_{k+4} = (R - 2Q)\,\bar V_{k+2} - Q^2\,\bar V_k$ for every $k \ge 0$.

With $P = \sqrt R$ and the Lucas sequence $V_k(P, Q)$ given by $V_0 = 2$, $V_1 = P$ and
$V_{k+2} = P V_{k+1} - Q V_k$, for $R \ne 0$ the term $\bar V_k(R, Q)$ equals $V_k(\sqrt R, Q)$
for even $k$ and $V_k(\sqrt R, Q)/\sqrt R$ for odd $k$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2 (definition of `V̄_n` and
recurrence (4thLehmer)). -/
def lehmerV (R Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | 2 => R - 2 * Q
  | 3 => R - 3 * Q
  | k + 4 => (R - 2 * Q) * lehmerV R Q (k + 2) - Q ^ 2 * lehmerV R Q k

/-- **Fourth-order recurrence of Lehmer's companion sequence.** For all integers $R$ and $Q$ and
every natural number $k$, Lehmer's companion sequence satisfies
$\bar V_{k+4}(R, Q) = (R - 2Q)\,\bar V_{k+2}(R, Q) - Q^2\,\bar V_k(R, Q)$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2, recurrence (4thLehmer). -/
theorem lehmerV_add_four (R Q : ℤ) (k : ℕ) :
    lehmerV R Q (k + 4) = (R - 2 * Q) * lehmerV R Q (k + 2) - Q ^ 2 * lehmerV R Q k :=
  rfl

/-- **Lehmer's companion sequence for $R = 2$ and $Q = -1$.** For $R = 2$ and $Q = -1$, Lehmer's
companion sequence has $\bar V_2(2, -1) = 4$, $\bar V_4(2, -1) = 14$ and
$\bar V_8(2, -1) = 194$.

These are the parameters giving the seed $4$, and $14 = 4^2 - 2$ and $194 = 14^2 - 2$, as the
doubling formula (LehmerV2n) predicts.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 2 (formula (LehmerV2n) and
the case `R = 2`, `Q = -1` after Theorem 6). -/
theorem lehmerV_two_neg_one :
    lehmerV 2 (-1) 2 = 4 ∧ lehmerV 2 (-1) 4 = 14 ∧ lehmerV 2 (-1) 8 = 194 := by
  decide

/-- **Lehmer-sequence primality criterion for Mersenne numbers.** Let $n \ge 3$ be odd, let
$M_n = 2^n - 1$, and let $R$ and $Q$ be integers with $\gcd(M_n, Q) = 1$. If $M_n$ divides
Lehmer's companion term $\bar V_{2^{n-1}}(R, Q)$, then $M_n$ is prime.

Here $2^{n-1} = (M_n + 1)/2$. No coprimality of $R$ and $Q$ and no condition on $D = R - 4Q$
is assumed.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 4. -/
public theorem_wanted mersenne_prime_of_dvd_lehmerV {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (R Q : ℤ) (hQ : Int.gcd (mersenne n) Q = 1)
    (hV : (mersenne n : ℤ) ∣ lehmerV R Q (2 ^ (n - 1))) :
    (mersenne n).Prime

/-- **Divisibility of Lehmer's companion sequence by a Mersenne prime.** Let $n \ge 3$ be an odd
natural number such that $M_n = 2^n - 1$ is prime, let $R$ and $Q$ be integers, let
$\bar V_k(R, Q)$ denote Lehmer's companion sequence, and put $D = R - 4Q$. If the Jacobi symbols
$\left(\frac{DR}{M_n}\right)$ and $\left(\frac{QR}{M_n}\right)$ are both $-1$, then $M_n$
divides $\bar V_{(M_n+1)/2}(R, Q) = \bar V_{2^{n-1}}(R, Q)$.

Since $M_n$ is prime, these Jacobi symbols are Legendre symbols.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 5. -/
public theorem_wanted mersenne_dvd_lehmerV_of_jacobi {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hp : (mersenne n).Prime) (R Q : ℤ)
    (hDR : jacobiSym ((R - 4 * Q) * R) (mersenne n) = -1)
    (hQR : jacobiSym (Q * R) (mersenne n) = -1) :
    (mersenne n : ℤ) ∣ lehmerV R Q (2 ^ (n - 1))

/-- **Divisibility of Lehmer's companion sequence by a Mersenne prime, Diophantine form.** Let
$n \ge 3$ be an odd natural number such that $M_n = 2^n - 1$ is prime, and let $r$, $d$, $q$,
$X$, $Y$, $Z$ be integers with $\gcd(M_n, Y) = 1$ and $4qY^2 = rX^2 - dZ^2$. Put $R = rX^2$ and
$Q = qY^2$, and let $\bar V_k(R, Q)$ denote Lehmer's companion sequence. If the Jacobi symbols
$\left(\frac{rd}{M_n}\right)$ and $\left(\frac{qr}{M_n}\right)$ are both $-1$, then $M_n$ divides
$\bar V_{(M_n+1)/2}(R, Q) = \bar V_{2^{n-1}}(R, Q)$.

Here $D = R - 4Q = dZ^2$, and since $M_n$ is prime the Jacobi symbols are Legendre symbols.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 7. -/
public theorem_wanted mersenne_dvd_lehmerV_of_diophantine {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (hp : (mersenne n).Prime) (r d q X Y Z : ℤ) (hY : Int.gcd (mersenne n) Y = 1)
    (hdio : 4 * q * Y ^ 2 = r * X ^ 2 - d * Z ^ 2)
    (hrd : jacobiSym (r * d) (mersenne n) = -1) (hqr : jacobiSym (q * r) (mersenne n) = -1) :
    (mersenne n : ℤ) ∣ lehmerV (r * X ^ 2) (q * Y ^ 2) (2 ^ (n - 1))

/-! ### Squarefree parts, the order of `2`, and condition (etar) -/

/-- **Condition (etar) on Jacobi symbols of $M_n$.** Let $s^-$, $s^+$ and $n$ be natural
numbers and let $M_n = 2^n - 1$. For a natural number $s$ write $\left(\frac{M_n}{s}\right)$ for
the Jacobi symbol, the product of the Legendre symbols $\left(\frac{M_n}{p}\right)$ over the
prime factors $p$ of $s$ counted with multiplicity (so it is $1$ for $s = 0$ and $s = 1$).
Condition (etar) holds for $s^-$, $s^+$ and $n$ when $s^- = 1$ or
$\left(\frac{M_n}{s^-}\right) = (-1)^{(s^- - 1)/2}$, and moreover
$\left(\frac{M_n}{s^+}\right) = (-1)^{(s^+ + 1)/2}$. Here the exponents are rounded down, and
$s^- - 1$ is read as $0$ when $s^- = 0$.

In the source, $s^-$ and $s^+$ are the odd squarefree parts $s_1^-$ and $s_1^+$ of $s_1 - 2$
and $s_1 + 2$ for a seed $s_1$. For squarefree $s$ the Jacobi symbol $\left(\frac{M_n}{s}\right)$
is the product of $\eta_n(p) = \left(\frac{M_n}{p}\right)$ over the primes $p$ dividing $s$,
which is how the source states the condition.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7, condition (etar). -/
def MersenneEtaCondition (sm sp n : ℕ) : Prop :=
  (sm = 1 ∨ jacobiSym (mersenne n) sm = (-1) ^ ((sm - 1) / 2)) ∧
    jacobiSym (mersenne n) sp = (-1) ^ ((sp + 1) / 2)

/-- **Condition (etar) for the seed $37$.** For the seed $s_1 = 37$, the odd squarefree parts of
$s_1 - 2 = 35$ and $s_1 + 2 = 39$ are $s_1^- = 35$ and $s_1^+ = 39$. Condition (etar) for
$s_1^- = 35$ and $s_1^+ = 39$ holds for $n = 7$ and fails for $n = 1$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Section 7 (example `s_1 = 37`,
`𝒜(37) = {7}`). -/
theorem mersenneEtaCondition_37 :
    MersenneEtaCondition 35 39 7 ∧ ¬ MersenneEtaCondition 35 39 1 := by
  norm_num [MersenneEtaCondition, mersenne]

/-- **Infinitely many acceptable seeds with the same odd squarefree parts.** Let $n \ge 3$ be a
natural number and $M_n = 2^n - 1$. For an integer $S$ put $S_1 = S$ and $S_{k+1} = S_k^2 - 2$,
and call $S$ an acceptable seed for $M_n$ if $M_n$ is prime exactly when $M_n$ divides
$S_{n-1}$. Let $s_1 \ge 3$ be an integer that is an acceptable seed for $M_n$, and let $s_1^-$
and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$. Then there are infinitely
many integers $S \ge 3$ that are acceptable seeds for $M_n$ and for which $s_1^-$ and $s_1^+$
are the odd squarefree parts of $S - 2$ and $S + 2$.

Seeds are taken $\ge 3$ (the paper's seeds are nonnegative, and the odd squarefree part of
$S - 2$ needs $S - 2 > 0$).

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 10. -/
public theorem_wanted infinite_acceptableSeeds_same_parts {n : ℕ} (h3 : 3 ≤ n) (s₁ : ℤ)
    (hs₁ : 3 ≤ s₁) (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm)
    (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (hacc : (mersenne n).Prime ↔
      (mersenne n : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[n - 2] s₁) :
    {S : ℤ | 3 ≤ S ∧ IsOddSquarefreePart (S - 2) sm ∧ IsOddSquarefreePart (S + 2) sp ∧
      ((mersenne n).Prime ↔ (mersenne n : ℤ) ∣ (fun x : ℤ => x ^ 2 - 2)^[n - 2] S)}.Infinite

/-- **Condition (etar) fails for some reduced residue when $s_1^- \equiv 3 \pmod 4$.** Let
$s_1 \ge 3$ be an integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and
$s_1 + 2$, and let $\Omega = \Omega(s_1^- s_1^+)$ be the order of $2$ modulo $s_1^- s_1^+$,
doubled when it is odd. If $s_1^- \equiv 3 \pmod 4$, then there is a natural number $n$ with
$1 \le n < \Omega$ and $\gcd(n, \Omega) = 1$ for which condition (etar) for $s_1^-$, $s_1^+$
and $n$ fails.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 13. -/
public theorem_wanted exists_not_mersenneEtaCondition_of_minus (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (h4 : sm % 4 = 3) :
    ∃ n, 1 ≤ n ∧ n < mersenneOmega (sm * sp) ∧ n.Coprime (mersenneOmega (sm * sp)) ∧
      ¬ MersenneEtaCondition sm sp n

/-- **Condition (etar) fails for some reduced residue when $s_1^+ \equiv 1 \pmod 4$.** Let
$s_1 \ge 3$ be an integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and
$s_1 + 2$, and let $\Omega = \Omega(s_1^- s_1^+)$ be the order of $2$ modulo $s_1^- s_1^+$,
doubled when it is odd. If $s_1^+ \equiv 1 \pmod 4$, then there is a natural number $n$ with
$1 \le n < \Omega$ and $\gcd(n, \Omega) = 1$ for which condition (etar) for $s_1^-$, $s_1^+$
and $n$ fails.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 14. -/
public theorem_wanted exists_not_mersenneEtaCondition_of_plus (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (h4 : sp % 4 = 1) :
    ∃ n, 1 ≤ n ∧ n < mersenneOmega (sm * sp) ∧ n.Coprime (mersenneOmega (sm * sp)) ∧
      ¬ MersenneEtaCondition sm sp n

/-- **Residues mod $4$ of $s_1^-$ and $s_1^+$ when (etar) always holds.** Let $s_1 \ge 3$ be an
integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$, and let
$\Omega = \Omega(s_1^- s_1^+)$. If the number of integers $n$ with $1 \le n < \Omega$ and
$\gcd(n, \Omega) = 1$ for which condition (etar) holds for $s_1^-$, $s_1^+$ and $n$ equals
$\varphi(\Omega)$, then $s_1^- \equiv 1 \pmod 4$ and $s_1^+ \equiv 3 \pmod 4$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 15. -/
public theorem_wanted minus_mod_four_of_mersenneEtaCondition_all (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (hq : {n | n ∈ Finset.Ico 1 (mersenneOmega (sm * sp)) ∧
        n.Coprime (mersenneOmega (sm * sp)) ∧ MersenneEtaCondition sm sp n}.ncard =
      Nat.totient (mersenneOmega (sm * sp))) :
    sm % 4 = 1 ∧ sp % 4 = 3

/-- **Condition (etar) fails for some reduced residue when the seed is odd.** Let $s_1 \ge 3$ be
an odd integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$,
and let $\Omega = \Omega(s_1^- s_1^+)$. Then the number of integers $n$ with $1 \le n < \Omega$
and $\gcd(n, \Omega) = 1$ for which condition (etar) holds for $s_1^-$, $s_1^+$ and $n$ is not
equal to $\varphi(\Omega)$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Corollary 16. -/
public theorem_wanted mersenneEtaCondition_not_all_of_odd (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (hodd : Odd s₁) (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm)
    (hsp : IsOddSquarefreePart (s₁ + 2) sp) :
    {n | n ∈ Finset.Ico 1 (mersenneOmega (sm * sp)) ∧
        n.Coprime (mersenneOmega (sm * sp)) ∧ MersenneEtaCondition sm sp n}.ncard ≠
      Nat.totient (mersenneOmega (sm * sp))

end

end MetaMathlibExt

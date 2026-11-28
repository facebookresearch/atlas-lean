/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LucasLehmer
public import MathlibExt.NumberTheory.LehmerCompanionMersenneDivisibility
public import MathlibExt.NumberTheory.LehmerCompanionMersennePrimality
public import MathlibExt.NumberTheory.LucasLehmerInfiniteSeeds
public import MathlibExt.NumberTheory.MersenneEtaCondition
public import MathlibExt.NumberTheory.MersenneEtaConditionResidues
public import MathlibExt.NumberTheory.OrderOfTwoMulCoprime
public import MathlibExt.NumberTheory.PellEulerSolutions
public import MathlibExt.NumberTheory.LucasLehmerRationalSeedExistsNotMersenneEtaConditionOfMinus

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

/-! ### Squarefree parts, the order of `2`, and condition (etar) -/

end

end MetaMathlibExt

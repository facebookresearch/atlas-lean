/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.MersenneOmega

/-!
# The Jacobi symbol condition for Lucas–Lehmer seeds

When the odd squarefree part of the seed plus two is one modulo four, the reduced
residue one fails condition (etar).
-/

namespace MetaMathlibExt

@[expose] public section

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

set_option linter.unusedVariables false in
/-- **Condition (etar) fails for some reduced residue when $s_1^+ \equiv 1 \pmod 4$.** Let
$s_1 \ge 3$ be an integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and
$s_1 + 2$, and let $\Omega = \Omega(s_1^- s_1^+)$ be the order of $2$ modulo $s_1^- s_1^+$,
doubled when it is odd. If $s_1^+ \equiv 1 \pmod 4$, then there is a natural number $n$ with
$1 \le n < \Omega$ and $\gcd(n, \Omega) = 1$ for which condition (etar) for $s_1^-$, $s_1^+$
and $n$ fails.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 14. -/
theorem exists_not_mersenneEtaCondition_of_plus (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (h4 : sp % 4 = 1) :
    ∃ n, 1 ≤ n ∧ n < mersenneOmega (sm * sp) ∧ n.Coprime (mersenneOmega (sm * sp)) ∧
      ¬ MersenneEtaCondition sm sp n := by
  have hodd := hsm.1.mul hsp.1
  have : NeZero (sm * sp) := ⟨hodd.pos.ne'⟩
  have hu : IsUnit (2 : ZMod (sm * sp)) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr hodd.coprime_two_left
  have hpos := hu.isOfFinOrder.orderOf_pos
  have hΩ : 1 < mersenneOmega (sm * sp) := by
    unfold mersenneOmega
    split_ifs with h
    · omega
    · rw [Nat.odd_iff] at h
      omega
  refine ⟨1, le_rfl, hΩ, Nat.coprime_one_left _, fun h => ?_⟩
  have hsign : Odd ((sp + 1) / 2) := Nat.odd_iff.mpr (by omega)
  have hplus := h.2
  rw [hsign.neg_one_pow] at hplus
  norm_num [mersenne, jacobiSym.one_left] at hplus

end

end MetaMathlibExt

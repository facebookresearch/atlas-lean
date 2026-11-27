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

/-- A reduced residue failing condition (etar) makes the qualifying count less than the totient. -/
private theorem mersenneEtaCondition_ncard_lt_totient_of_missing {sm sp Ω n : ℕ}
    (hn : n < Ω) (hcop : n.Coprime Ω) (hfail : ¬ MersenneEtaCondition sm sp n) :
    {m | m ∈ Finset.Ico 1 Ω ∧ m.Coprime Ω ∧ MersenneEtaCondition sm sp m}.ncard <
      Nat.totient Ω := by
  let A : Set ℕ := {m | m ∈ Finset.Ico 1 Ω ∧ m.Coprime Ω ∧ MersenneEtaCondition sm sp m}
  let R : Set ℕ := {m | m < Ω ∧ Ω.Coprime m}
  have hAR : A ⊂ R := by
    refine ⟨?_, fun hRA ↦ hfail (hRA ⟨hn, hcop.symm⟩).2.2⟩
    intro m hm
    exact ⟨(Finset.mem_Ico.mp hm.1).2, hm.2.1.symm⟩
  have hRfin : R.Finite := (Set.finite_Iio Ω).subset fun _ hm ↦ hm.1
  have hRcard : R.ncard = Nat.totient Ω := by
    rw [Nat.totient_eq_card_lt_and_coprime]
    rfl
  exact hRcard ▸ Set.ncard_lt_ncard hAR hRfin

set_option linter.unusedVariables false in
/-- **Condition (etar) fails for some reduced residue when the seed is odd.** Let $s_1 \ge 3$ be
an odd integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$,
and let $\Omega = \Omega(s_1^- s_1^+)$. Then the number of integers $n$ with $1 \le n < \Omega$
and $\gcd(n, \Omega) = 1$ for which condition (etar) holds for $s_1^-$, $s_1^+$ and $n$ is not
equal to $\varphi(\Omega)$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Corollary 16. -/
theorem mersenneEtaCondition_not_all_of_odd (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (hodd : Odd s₁) (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm)
    (hsp : IsOddSquarefreePart (s₁ + 2) sp) :
    {n | n ∈ Finset.Ico 1 (mersenneOmega (sm * sp)) ∧
        n.Coprime (mersenneOmega (sm * sp)) ∧ MersenneEtaCondition sm sp n}.ncard ≠
      Nat.totient (mersenneOmega (sm * sp)) := by
  have hres : ∀ (N : ℤ) (k : ℕ), IsOddSquarefreePart N k → Odd N →
      (k : ZMod 4) = ((N : ℤ) : ZMod 4) := by
    intro N k hk hN
    obtain ⟨hkodd, -, a, m, hm⟩ := hk
    have ha : a = 0 := by
      by_contra ha
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have h2 : (2 : ℤ) ∣ N := by
        rw [hm]
        exact ((dvd_pow_self (2 : ℤ) (show b + 1 ≠ 0 by omega)).mul_right _).mul_right _
      obtain ⟨u, hu⟩ := h2
      obtain ⟨t, ht⟩ := hN
      omega
    subst ha
    have hm0 : N = (m : ℤ) ^ 2 * (k : ℤ) := by simpa using hm
    have hm_odd : Odd m := by
      have hoddprod : Odd ((m : ℤ) ^ 2 * (k : ℤ)) := hm0 ▸ hN
      have h1 : Odd ((m : ℤ) ^ 2) := Int.Odd.of_mul_left hoddprod
      rcases (Int.odd_pow (n := 2)).mp h1 with h | h
      · exact h
      · omega
    have hsq : ((m : ℤ) : ZMod 4) ^ 2 = 1 := by
      have hsq_int : (m : ℤ) ^ 2 % 4 = 1 := Int.sq_emod_four_eq_one_of_odd hm_odd
      have hme : (m : ℤ) ^ 2 ≡ (1 : ℤ) [ZMOD 4] := by
        rw [Int.ModEq]
        simpa using hsq_int
      have hcast := (ZMod.intCast_eq_intCast_iff ((m : ℤ) ^ 2) (1 : ℤ) 4).mpr hme
      push_cast at hcast
      exact hcast
    have hcast : ((N : ℤ) : ZMod 4) = ((m : ℤ) : ZMod 4) ^ 2 * (k : ZMod 4) := by
      rw [hm0]
      push_cast
      ring
    rw [hcast, hsq, one_mul]
  have hNminus : Odd (s₁ - 2) := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t - 1, by omega⟩
  have hNplus : Odd (s₁ + 2) := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t + 1, by omega⟩
  have hcast_eq : (sm : ZMod 4) = (sp : ZMod 4) := by
    have h1 := hres (s₁ - 2) sm hsm hNminus
    have h2 := hres (s₁ + 2) sp hsp hNplus
    have h3 : ((s₁ - 2 : ℤ) : ZMod 4) = ((s₁ + 2 : ℤ) : ZMod 4) := by
      apply (ZMod.intCast_eq_intCast_iff _ _ 4).mpr
      rw [Int.ModEq]
      omega
    rw [h1, h2, h3]
  have hmod4 : sm % 4 = sp % 4 := (ZMod.natCast_eq_natCast_iff sm sp 4).mp hcast_eq
  have hsm4 : sm % 4 = 1 ∨ sm % 4 = 3 := by
    obtain ⟨t, ht⟩ := hsm.1
    omega
  have hfail : ¬ MersenneEtaCondition sm sp 1 := by
    intro h
    rcases hsm4 with h4 | h4
    · have hsp4 : sp % 4 = 1 := by omega
      have hsign : Odd ((sp + 1) / 2) := Nat.odd_iff.mpr (by omega)
      have hplus := h.2
      rw [hsign.neg_one_pow] at hplus
      norm_num [mersenne, jacobiSym.one_left] at hplus
    · have hsign : Odd ((sm - 1) / 2) := Nat.odd_iff.mpr (by omega)
      rcases h.1 with hsm1 | hminus
      · omega
      · rw [hsign.neg_one_pow] at hminus
        norm_num [mersenne, jacobiSym.one_left] at hminus
  have hoddprod : Odd (sm * sp) := hsm.1.mul hsp.1
  have hΩ : 1 < mersenneOmega (sm * sp) := by
    have hne : NeZero (sm * sp) := ⟨hoddprod.pos.ne'⟩
    have hu : IsUnit (2 : ZMod (sm * sp)) :=
      (ZMod.isUnit_iff_coprime 2 _).mpr hoddprod.coprime_two_left
    have hpos := hu.isOfFinOrder.orderOf_pos
    unfold mersenneOmega
    split_ifs with h
    · omega
    · rw [Nat.odd_iff] at h
      omega
  exact ne_of_lt (mersenneEtaCondition_ncard_lt_totient_of_missing hΩ
    (Nat.coprime_one_left _) hfail)

end

end MetaMathlibExt

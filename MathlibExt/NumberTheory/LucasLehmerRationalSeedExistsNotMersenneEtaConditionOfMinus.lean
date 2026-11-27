/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
public import MathlibExt.NumberTheory.MersenneEtaCondition

/-!
# Condition (etar) fails for a reduced residue when `s₁⁻ ≡ 3 [MOD 4]`

For an integer seed `s₁ ≥ 3` with odd squarefree parts `s₁⁻` of `s₁ - 2` and `s₁⁺` of
`s₁ + 2`, when `s₁⁻` is three modulo four, some reduced residue `n` with `1 ≤ n < Ω(s₁⁻ s₁⁺)`
fails condition (etar).

Statement from E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer
Primality Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5.
-/

namespace MetaMathlibExt

@[expose] public section

set_option linter.unusedVariables false in
/-- **Condition (etar) fails for some reduced residue when $s_1^- \equiv 3 \pmod 4$.** Let
$s_1 \ge 3$ be an integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and
$s_1 + 2$, and let $\Omega = \Omega(s_1^- s_1^+)$ be the order of $2$ modulo $s_1^- s_1^+$,
doubled when it is odd. If $s_1^- \equiv 3 \pmod 4$, then there is a natural number $n$ with
$1 \le n < \Omega$ and $\gcd(n, \Omega) = 1$ for which condition (etar) for $s_1^-$, $s_1^+$
and $n$ fails.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Lemma 13. -/
theorem exists_not_mersenneEtaCondition_of_minus (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (h4 : sm % 4 = 3) :
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
  have hsm1 : sm ≠ 1 := by omega
  refine ⟨1, le_rfl, hΩ, Nat.coprime_one_left _, fun h => ?_⟩
  have hsign : Odd ((sm - 1) / 2) := Nat.odd_iff.mpr (by omega)
  have hminus := h.1.resolve_left hsm1
  rw [hsign.neg_one_pow] at hminus
  norm_num [mersenne, jacobiSym.one_left] at hminus

end

end MetaMathlibExt

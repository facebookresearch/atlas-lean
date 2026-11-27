/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MersenneEtaCondition
import MathlibExt.NumberTheory.LucasLehmerRationalSeedExistsNotMersenneEtaConditionOfMinus

/-!
# Residues of the odd squarefree parts of a Lucas–Lehmer seed

If condition (etar) holds for every reduced residue modulo the adjusted order of two,
the odd squarefree parts of the seed minus and plus two are respectively `1` and `3` modulo four.

## References

* E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality Test*,
  Journal of Integer Sequences 28 (2025), Article 25.2.5, pp. 1–26, Theorem 15 and Lemmas 13–14.
* D. H. Lehmer, *An extended theory of Lucas' functions*, Annals of Mathematics 31 (1930),
  pp. 419–448, §5, for the integral seeds discussed in §8 of Roettger and Williams.
-/

namespace MetaMathlibExt

public section

/-- **Residues mod $4$ of $s_1^-$ and $s_1^+$ when (etar) always holds.** Let $s_1 \ge 3$ be an
integer, let $s_1^-$ and $s_1^+$ be the odd squarefree parts of $s_1 - 2$ and $s_1 + 2$, and let
$\Omega = \Omega(s_1^- s_1^+)$. If the number of integers $n$ with $1 \le n < \Omega$ and
$\gcd(n, \Omega) = 1$ for which condition (etar) holds for $s_1^-$, $s_1^+$ and $n$ equals
$\varphi(\Omega)$, then $s_1^- \equiv 1 \pmod 4$ and $s_1^+ \equiv 3 \pmod 4$.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 15. -/
theorem minus_mod_four_of_mersenneEtaCondition_all (s₁ : ℤ) (hs₁ : 3 ≤ s₁)
    (sm sp : ℕ) (hsm : IsOddSquarefreePart (s₁ - 2) sm) (hsp : IsOddSquarefreePart (s₁ + 2) sp)
    (hq : {n | n ∈ Finset.Ico 1 (mersenneOmega (sm * sp)) ∧
        n.Coprime (mersenneOmega (sm * sp)) ∧ MersenneEtaCondition sm sp n}.ncard =
      Nat.totient (mersenneOmega (sm * sp))) :
    sm % 4 = 1 ∧ sp % 4 = 3 := by
  let Ω := mersenneOmega (sm * sp)
  let A : Set ℕ := {n | n ∈ Finset.Ico 1 Ω ∧ n.Coprime Ω ∧ MersenneEtaCondition sm sp n}
  let R : Set ℕ := {n | n < Ω ∧ Ω.Coprime n}
  change A.ncard = Nat.totient Ω at hq
  have hRcard : R.ncard = Nat.totient Ω := by
    rw [Nat.totient_eq_card_lt_and_coprime]
    rfl
  have hRfin : R.Finite := (Set.finite_Iio Ω).subset fun _ hn ↦ hn.1
  -- Any missing reduced residue would make `A` a strict subset of `R`.
  have hno : ¬ ∃ n, 1 ≤ n ∧ n < Ω ∧ n.Coprime Ω ∧ ¬ MersenneEtaCondition sm sp n := by
    rintro ⟨n, -, hlt, hcop, hfail⟩
    have hAR : A ⊂ R := by
      refine ⟨?_, fun hRA ↦ hfail (hRA ⟨hlt, hcop.symm⟩).2.2⟩
      intro m hm
      exact ⟨(Finset.mem_Ico.mp hm.1).2, hm.2.1.symm⟩
    exact (ne_of_lt (Set.ncard_lt_ncard hAR hRfin)) (hq.trans hRcard.symm)
  have hsmOdd : sm % 2 = 1 := Nat.odd_iff.mp hsm.1
  have hspOdd : sp % 2 = 1 := Nat.odd_iff.mp hsp.1
  constructor
  · by_contra h
    exact hno (exists_not_mersenneEtaCondition_of_minus s₁ hs₁ sm sp hsm hsp (by omega))
  · by_contra h
    exact hno (exists_not_mersenneEtaCondition_of_plus s₁ hs₁ sm sp hsm hsp (by omega))

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HigherANumbersTowerTauAdjacentDigits

import Mathlib.Tactic.NormNum

/-!
# A digit criterion for the higher `a`-number rounding indicator

For a prime `p`, a natural number `d` dividing `p - 1`, and `τ = (p + 1)/d`, suppose the
natural number `i` is not divisible by `p`. The rounding indicator `δ(i)` is `1` exactly when
the first fractional base-`p` digit of `τ i` exceeds its units digit. Those digits differ by
Lemma 3, so the first index decides the lexicographic comparison in the definition of `δ`.
The same argument covers `p = 2`, when `d = 1`.

## References

* Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
  *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026),
  Article A78, pp. 1–28, Equation (1), Definition 7, Lemmas 3 and 4, and Example 5 (Table 2).
  The proof uses Lemma 3 as `basePDigit_towerTau_neg_one_eq_zero_iff` from
  `MathlibExt.NumberTheory.HigherANumbersTowerTauAdjacentDigits`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Lexicographic order on integer sequences.** For sequences
$a, b \colon \mathbb{N} \to \mathbb{Z}$, $a$ is lexicographically larger than $b$ when there is
an index $m$ with $a_j = b_j$ for all $j < m$ and $a_m > b_m$. This is the order used in
Definition 1.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Equation (1). -/
def SeqLexGt (a b : ℕ → ℤ) : Prop := ∃ m, (∀ j < m, a j = b j) ∧ b m < a m

/-- **The rounding indicator $\delta$.** Let $p$, $d$ and $i$ be natural numbers and let
$\tau = (p + 1)/d$. For a rational $x$ and an integer $k$, write $[p^k](x)$ for the residue of
$\lfloor x / p^k \rfloor$ modulo $p$, the $k$-th base-$p$ digit of $x$. Then $\delta(i) = 0$ if
the integer-part digits $([p^n](\tau i))_{n \ge 0}$ are lexicographically larger than the
fractional digits $([p^{-1-n}](\tau i))_{n \ge 0}$, that is, the two sequences agree at every
index below some $m$ and the first is larger at $m$; otherwise $\delta(i) = 1$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `δ`. -/
noncomputable def higherANumberDelta (p d i : ℕ) : ℕ :=
  open Classical in
  if SeqLexGt (fun n => basePDigit p (towerTau p d * i) n)
      (fun n => basePDigit p (towerTau p d * i) (-1 - n)) then 0 else 1

/-- **Two values of $\delta$ for $p = 5$ and $d = 4$.** For $p = 5$ and $d = 4$, so that
$\tau = (p + 1)/d = 3/2$, the rounding indicator satisfies $\delta(1) = 1$ and $\delta(2) = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Table 1 (`δ(1) = 1`, `δ(2) = 0` for
`p = 5`, `d = 4`). -/
theorem higherANumberDelta_five_four :
    higherANumberDelta 5 4 1 = 1 ∧ higherANumberDelta 5 4 2 = 0 := by
  constructor
  · unfold higherANumberDelta
    split_ifs with h
    · obtain ⟨m, hm, hlt⟩ := h
      rcases m with _ | m
      · norm_num [basePDigit, towerTau, zpow_neg] at hlt
      · have := hm 0 (by omega)
        norm_num [basePDigit, towerTau, zpow_neg] at this
    · rfl
  · unfold higherANumberDelta
    split_ifs with h
    · rfl
    · exact absurd ⟨0, by simp, by norm_num [basePDigit, towerTau, zpow_neg]⟩ h

/-- **A digit criterion for $\delta(i) = 1$.** Let $p$ be a prime, $d$ a divisor of $p - 1$ and
$\tau = (p + 1)/d$. For a rational $t$ and an integer $k$ write $[p^k](t)$ for the $k$-th base-$p$
digit of $t$, the residue of $\lfloor t / p^k \rfloor$ modulo $p$ in
$\lbrace 0, \dots, p - 1 \rbrace$, and let $\delta$ be the rounding indicator. If $i$ is a natural
number not divisible by $p$, then $[p^0](\tau i) < [p^{-1}](\tau i)$ if and only if $\delta(i) = 1$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 4 (`integers-2026-A78-lem-4`). -/
public theorem higherANumberDelta_eq_one_iff (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {i : ℕ} (hi : ¬ p ∣ i) :
    basePDigit p (towerTau p d * i) 0 < basePDigit p (towerTau p d * i) (-1) ↔
      higherANumberDelta p d i = 1 := by
  have hne := mt (basePDigit_towerTau_neg_one_eq_zero_iff p d hd i).mp hi
  classical
  unfold higherANumberDelta
  split
  next h =>
    obtain ⟨m, hm, hlt⟩ := h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos fun hmpos =>
      hne (by simpa using (hm 0 hmpos).symm)
    subst m
    have hgt : basePDigit p (towerTau p d * i) (-1) < basePDigit p (towerTau p d * i) 0 := by
      simpa using hlt
    exact iff_of_false hgt.not_gt Nat.zero_ne_one
  next h =>
    have hnot : ¬ basePDigit p (towerTau p d * i) (-1) < basePDigit p (towerTau p d * i) 0 :=
      fun hgt => h ⟨0, by simp, by simpa using hgt⟩
    exact iff_of_true (lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)) rfl

end

end MetaMathlibExt

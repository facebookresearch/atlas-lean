/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import MathlibExt.NumberTheory.GobelBSequence
public import MathlibExt.NumberTheory.OddMultiplePrimeHalfSets

/-!
# The diagonal is zigzag-below every odd Göbel residue walk

For an odd prime `p` and an odd `l < p`, the diagonal `n ↦ n` is zigzag-below the residue walk
`gobelResidueWalk p l` up to `p`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Proposition 9.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem gobelResidueWalk_le (p l : ℕ) (hlp : l < p) (n : ℕ) :
    gobelResidueWalk p l n ≤ p := by
  have h0 : 0 ≤ n := Nat.zero_le n
  induction n, h0 using Nat.le_induction with
  | base => exact Nat.zero_le p
  | succ n _ ih =>
    by_cases hn0 : n = 0
    · subst hn0
      change gobelResidueWalk p l 1 ≤ p
      rw [gobelResidueWalk_one]
      exact hlp.le
    · have hn1 : 1 ≤ n := by omega
      by_cases hx0 : 0 < gobelResidueWalk p l n
      · by_cases hxp : gobelResidueWalk p l n < p
        · rw [gobelResidueWalk_succ_of_between p l n hn1 ⟨hx0, hxp⟩]
          have ht1 := jacobiSym.trichotomy (n : ℤ) p
          have ht2 := jacobiSym.trichotomy (gobelResidueWalk p l n : ℤ) p
          rcases ht1 with h1|h1|h1 <;> rcases ht2 with h2|h2|h2 <;> rw [h1, h2] <;> omega
        · have hpx : p ≤ gobelResidueWalk p l n := by omega
          have hx : gobelResidueWalk p l n = p := le_antisymm ih hpx
          rw [gobelResidueWalk_succ_of_eq_prime p l n hn1 hx]
      · have hx0' : gobelResidueWalk p l n = 0 := by omega
        rw [gobelResidueWalk_succ_of_eq_zero p l n hn1 hx0']
        exact Nat.zero_le p

private theorem gobelResidueWalk_ge_and_parity (p l : ℕ) (hp : p.Prime) (hlodd : Odd l)
    (hlp : l < p) (n : ℕ) (hn1 : 1 ≤ n) :
    n ≤ p → n ≤ gobelResidueWalk p l n ∧
      (gobelResidueWalk p l n = p ∨ gobelResidueWalk p l n % 2 = n % 2) := by
  induction n, hn1 using Nat.le_induction with
  | base =>
    intro _
    rw [gobelResidueWalk_one]
    obtain ⟨k, hk⟩ := hlodd
    refine ⟨by omega, Or.inr (by omega)⟩
  | succ n hn1 ih =>
    intro hnp
    have hnp' : n ≤ p := by omega
    obtain ⟨ih_ge, ih_par⟩ := ih hnp'
    by_cases hx0 : 0 < gobelResidueWalk p l n
    · by_cases hxp : gobelResidueWalk p l n < p
      · have hlt : n < p := by omega
        have hcop_n : (n : ℤ).gcd p = 1 :=
          (Nat.coprime_of_lt_prime (by omega : n ≠ 0) hlt hp).symm
        have hcop_x : (gobelResidueWalk p l n : ℤ).gcd p = 1 :=
          (Nat.coprime_of_lt_prime (by omega : gobelResidueWalk p l n ≠ 0) hxp hp).symm
        by_cases heq : gobelResidueWalk p l n = n
        · have hsq : jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p = 1 := by
            rw [heq, ← pow_two, jacobiSym.sq_one hcop_n]
          have hstep := gobelResidueWalk_succ_of_between p l n hn1 ⟨hx0, hxp⟩
          rw [hsq] at hstep
          have hton : Int.toNat ((gobelResidueWalk p l n : ℤ) + 1) =
              gobelResidueWalk p l n + 1 := by omega
          rw [hton, heq] at hstep
          rw [hstep]
          exact ⟨le_rfl, Or.inr rfl⟩
        · have hgt : n < gobelResidueWalk p l n := by omega
          have hpar : gobelResidueWalk p l n % 2 = n % 2 := by
            rcases ih_par with hx_p|hpar
            · omega
            · exact hpar
          have hx2 : n + 2 ≤ gobelResidueWalk p l n := by omega
          have h1 := jacobiSym.eq_one_or_neg_one hcop_n
          have h2 := jacobiSym.eq_one_or_neg_one hcop_x
          have hprod : jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p = 1 ∨
              jacobiSym (n : ℤ) p * jacobiSym (gobelResidueWalk p l n : ℤ) p = -1 := by
            rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> simp [h1, h2]
          have hstep := gobelResidueWalk_succ_of_between p l n hn1 ⟨hx0, hxp⟩
          rcases hprod with hs|hs
          · rw [hs] at hstep
            have hton : Int.toNat ((gobelResidueWalk p l n : ℤ) + 1) =
                gobelResidueWalk p l n + 1 := by omega
            rw [hton] at hstep
            by_cases hx1p : gobelResidueWalk p l n + 1 = p
            · rw [hstep]
              exact ⟨by omega, Or.inl hx1p⟩
            · rw [hstep]
              refine ⟨by omega, Or.inr (by omega)⟩
          · rw [hs] at hstep
            have hton : Int.toNat ((gobelResidueWalk p l n : ℤ) + -1) =
                gobelResidueWalk p l n - 1 := by omega
            rw [hton] at hstep
            rw [hstep]
            refine ⟨by omega, Or.inr (by omega)⟩
      · have hpx : p ≤ gobelResidueWalk p l n := by omega
        have hle := gobelResidueWalk_le p l hlp n
        have hx : gobelResidueWalk p l n = p := le_antisymm hle hpx
        have hstep := gobelResidueWalk_succ_of_eq_prime p l n hn1 hx
        rw [hstep]
        exact ⟨by omega, Or.inl rfl⟩
    · have hx0' : gobelResidueWalk p l n = 0 := by omega
      have hfalse : False := by omega
      exact hfalse.elim

/-- **The diagonal is zigzag-below every odd residue walk.** Let $p$ be an odd prime, let $l$ be
an odd natural number with $l < p$, and let $\tilde g_l$ be the residue walk of $l$ for $p$. Then
the diagonal $n \mapsto n$ is zigzag-below $\tilde g_l$ up to $p$: there is $m \le p$ such that
$n < \tilde g_l(n)$ for all $1 \le n \le m$ and $\tilde g_l(n) = n$ for all $m < n \le p$.

Source: Yuh Kobayashi and
Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer
Sequences 29 (2026), Article 26.3.8, Proposition 9. -/
public theorem diagonal_isZigzagBelow_gobelResidueWalk_of_odd
    (p l : ℕ) (hp : p.Prime) (hpodd : Odd p) (hlodd : Odd l) (hlp : l < p) :
    IsZigzagBelow p (fun n => (n : ℤ)) (fun n => gobelResidueWalk p l n)
    := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p := by omega
  have hl : l ≤ p - 1 := by omega
  have hge_p := (gobelResidueWalk_ge_and_parity p l hp hlodd hlp p hp1 le_rfl).1
  have hle_p := gobelResidueWalk_le p l hlp p
  have hgp : gobelResidueWalk p l p = p := le_antisymm hle_p hge_p
  have hex : ∃ n, 1 ≤ n ∧ gobelResidueWalk p l n = n := ⟨p, hp1, hgp⟩
  have ht1 : 1 ≤ Nat.find hex := (Nat.find_spec hex).1
  have hteq : gobelResidueWalk p l (Nat.find hex) = Nat.find hex := (Nat.find_spec hex).2
  have htp : Nat.find hex ≤ p := Nat.find_min' hex ⟨hp1, hgp⟩
  have htail := gobelResidueWalk_eq_index_of_eq_index p l (Nat.find hex) hp hpodd hl ht1 htp hteq
  refine ⟨Nat.find hex - 1, by omega, ⟨?_, ?_⟩⟩
  · intro n hn1 hnm
    have hnt : n < Nat.find hex := by omega
    have hne : gobelResidueWalk p l n ≠ n := by
      intro heq
      have hle := Nat.find_min' hex ⟨hn1, heq⟩
      omega
    have hnp' : n ≤ p := by omega
    have hge := (gobelResidueWalk_ge_and_parity p l hp hlodd hlp n hn1 hnp').1
    have hlt : n < gobelResidueWalk p l n := by omega
    change (n : ℤ) < ((gobelResidueWalk p l n : ℕ) : ℤ)
    exact_mod_cast hlt
  · intro n hmn hnp
    have htn : Nat.find hex ≤ n := by omega
    have heq := htail n htn hnp
    change (n : ℤ) = ((gobelResidueWalk p l n : ℕ) : ℤ)
    exact_mod_cast heq.symm

end

end MetaMathlibExt

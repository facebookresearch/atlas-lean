/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CollatzArithmeticDerivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# Compatible semiprimes modulo five

The prime factors of each of two compatible semiprimes are congruent to `1` and `4` modulo
`5`, up to order (`IsCompatibleSemiprimePair.mod_five`).

Statements from Zachary P. Bradshaw, "On a Family of Solutions to Arithmetic Differential
Equations Involving the Collatz Map", *Journal of Integer Sequences* 28 (2025), Article 25.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.html>).
-/

namespace MetaMathlibExt

@[expose] public section

namespace IsCompatibleSemiprimePair

-- If `p = 5`, the compatibility equations give `(r - 15) * (s - 15) = 188` over `ℤ`.
-- Both factors negative forces `r, s < 15` and a product below `188`; opposite signs
-- force a nonpositive product. Above `15`, `r` and `s` are odd, so halving the factors
-- gives a factorization of `47`, forcing `{r, s} = {17, 109}` and `q = 247 = 13 * 19`,
-- against the primality of `q`.
private theorem left_ne_five {p q r s : ℕ} (h : IsCompatibleSemiprimePair p q r s) :
    p ≠ 5 := by
  obtain ⟨_hp, hq, hr, hs, hsum, hprod⟩ := h
  intro hp5
  subst hp5
  have hsumZ : 2 * ((r : ℤ) + s) = 5 + q := by exact_mod_cast hsum
  have hprodZ : 2 * ((r : ℤ) * s) = 3 * (5 * (q : ℤ)) + 1 := by exact_mod_cast hprod
  have hfac2 : 2 * (((r : ℤ) - 15) * ((s : ℤ) - 15)) = 376 := by
    linear_combination hprodZ - 15 * hsumZ
  have hfac : ((r : ℤ) - 15) * ((s : ℤ) - 15) = 188 := by linarith
  have hr2 : (2 : ℤ) ≤ r := by exact_mod_cast hr.two_le
  have hs2 : (2 : ℤ) ≤ s := by exact_mod_cast hs.two_le
  by_cases hrl : (r : ℤ) < 15
  · by_cases hsl : (s : ℤ) < 15
    · have hneg : (15 - (r : ℤ)) * (15 - (s : ℤ)) = 188 := by
        linear_combination hfac
      have hle : (15 - (r : ℤ)) * (15 - (s : ℤ)) ≤ 13 * 13 :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      norm_num at hle
      linarith
    · push Not at hsl
      have hnonpos : ((r : ℤ) - 15) * ((s : ℤ) - 15) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      linarith
  · by_cases hsl : (s : ℤ) < 15
    · push Not at hrl
      have hnonpos : ((r : ℤ) - 15) * ((s : ℤ) - 15) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
    · push Not at hrl hsl
      have hrne : (15 : ℤ) ≠ r := by
        intro heq
        rw [← heq] at hfac
        norm_num at hfac
      have hr15 : (15 : ℤ) < r := lt_of_le_of_ne hrl hrne
      have hsne : (15 : ℤ) ≠ s := by
        intro heq
        rw [← heq] at hfac
        norm_num at hfac
      have hs15 : (15 : ℤ) < s := lt_of_le_of_ne hsl hsne
      have hr15N : 15 < r := by exact_mod_cast hr15
      have hs15N : 15 < s := by exact_mod_cast hs15
      obtain ⟨rk, hrk⟩ := hr.odd_of_ne_two (by omega)
      obtain ⟨sk, hsk⟩ := hs.odd_of_ne_two (by omega)
      have hreven : (r : ℤ) - 15 = 2 * ((rk : ℤ) - 7) := by
        have hrZ : (r : ℤ) = 2 * rk + 1 := by exact_mod_cast hrk
        linarith
      have hseven : (s : ℤ) - 15 = 2 * ((sk : ℤ) - 7) := by
        have hsZ : (s : ℤ) = 2 * sk + 1 := by exact_mod_cast hsk
        linarith
      rw [hreven, hseven] at hfac
      have hab : ((rk : ℤ) - 7) * ((sk : ℤ) - 7) = 47 := by
        have h4 : 4 * (((rk : ℤ) - 7) * ((sk : ℤ) - 7)) = 188 := by
          linear_combination hfac
        linarith
      have hrk8 : 8 ≤ rk := by omega
      have hsk8 : 8 ≤ sk := by omega
      have e1 : ((rk - 7 : ℕ) : ℤ) = (rk : ℤ) - 7 := by omega
      have e2 : ((sk - 7 : ℕ) : ℤ) = (sk : ℤ) - 7 := by omega
      have habN : (rk - 7) * (sk - 7) = 47 := by
        have hcast : (((rk - 7) * (sk - 7) : ℕ) : ℤ) = 47 := by
          rw [Nat.cast_mul, e1, e2]
          exact hab
        exact_mod_cast hcast
      have hdvd : (rk - 7) ∣ 47 := ⟨sk - 7, habN.symm⟩
      have h47 : Nat.Prime 47 := by norm_num
      rw [Nat.dvd_prime h47] at hdvd
      have hqeq : q = 2 * (r + s) - 5 := by omega
      have hnprime : ¬ Nat.Prime 247 := by norm_num
      rcases hdvd with h | h
      · rw [h, one_mul] at habN
        have hr17 : r = 17 := by omega
        have hs109 : s = 109 := by omega
        have hq247 : q = 247 := by omega
        rw [hq247] at hq
        exact hnprime hq
      · rw [h] at habN
        have hs17 : s = 17 := by omega
        have hr109 : r = 109 := by omega
        have hq247 : q = 247 := by omega
        rw [hq247] at hq
        exact hnprime hq

-- If `r = 5`, eliminating `s` from the compatibility equations gives
-- `(3p - 5) * (3q - 5) = -128` over `ℤ`, whereas both factors are positive.
private theorem right_ne_five {p q r s : ℕ} (h : IsCompatibleSemiprimePair p q r s) :
    r ≠ 5 := by
  obtain ⟨hp, hq, _hr, _hs, hsum, hprod⟩ := h
  intro hr5
  subst hr5
  have hsumZ : 2 * (5 + (s : ℤ)) = (p : ℤ) + q := by exact_mod_cast hsum
  have hprodZ : 2 * (5 * (s : ℤ)) = 3 * ((p : ℤ) * q) + 1 := by exact_mod_cast hprod
  have hfac : (3 * (p : ℤ) - 5) * (3 * (q : ℤ) - 5) = -128 := by
    linear_combination -3 * hprodZ + 15 * hsumZ
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have hpos : (0 : ℤ) < (3 * (p : ℤ) - 5) * (3 * (q : ℤ) - 5) :=
    mul_pos (by linarith) (by linarith)
  linarith

/-- **Compatible semiprimes modulo 5.** Let $p, q, r, s$ be primes with $2(r + s) = p + q$ and
$2rs = 3pq + 1$, so that the semiprimes $pq$ and $rs$ are compatible. Then one of $p, q$ is
congruent to $1$ and the other to $4$ modulo $5$, and likewise one of $r, s$ is congruent to $1$
and the other to $4$ modulo $5$.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Proposition 12 (`jis-2025-25.1.8-prop-12`). -/
theorem mod_five {p q r s : ℕ}
    (h : IsCompatibleSemiprimePair p q r s) :
    ((p % 5 = 1 ∧ q % 5 = 4) ∨ (q % 5 = 1 ∧ p % 5 = 4)) ∧
      ((r % 5 = 1 ∧ s % 5 = 4) ∨ (s % 5 = 1 ∧ r % 5 = 4)) := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
  have hp5 : p ≠ 5 := left_ne_five ⟨hp, hq, hr, hs, hsum, hprod⟩
  have hq5 : q ≠ 5 := left_ne_five ⟨hq, hp, hr, hs, by omega, by linear_combination hprod⟩
  have hr5 : r ≠ 5 := right_ne_five ⟨hp, hq, hr, hs, hsum, hprod⟩
  have hs5 : s ≠ 5 := right_ne_five ⟨hp, hq, hs, hr, by omega, by linear_combination hprod⟩
  have hp0 : p % 5 ≠ 0 := fun hz =>
    hp5 ((hp.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero hz))
  have hq0 : q % 5 ≠ 0 := fun hz =>
    hq5 ((hq.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero hz))
  have hr0 : r % 5 ≠ 0 := fun hz =>
    hr5 ((hr.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero hz))
  have hs0 : s % 5 ≠ 0 := fun hz =>
    hs5 ((hs.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero hz))
  have hpres : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  have hqres : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
  have hrres : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by omega
  have hsres : s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4 := by omega
  have hsum5 : (p + q) % 5 = (2 * (r + s)) % 5 := by rw [← hsum]
  have hprod5 : (2 * (r * s)) % 5 = (3 * (p * q) + 1) % 5 := by rw [hprod]
  rw [Nat.add_mod p q 5, Nat.mul_mod 2 (r + s) 5, Nat.add_mod r s 5] at hsum5
  rw [Nat.mul_mod 2 (r * s) 5, Nat.mul_mod r s 5, Nat.add_mod (3 * (p * q)) 1 5,
    Nat.mul_mod 3 (p * q) 5, Nat.mul_mod p q 5] at hprod5
  rcases hpres with h1 | h1 | h1 | h1 <;> rcases hqres with h2 | h2 | h2 | h2 <;>
    rcases hrres with h3 | h3 | h3 | h3 <;> rcases hsres with h4 | h4 | h4 | h4 <;>
    simp [h1, h2, h3, h4] at hsum5 hprod5 ⊢

end IsCompatibleSemiprimePair

end

end MetaMathlibExt

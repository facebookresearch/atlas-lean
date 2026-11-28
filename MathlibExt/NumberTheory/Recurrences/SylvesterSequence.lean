/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import MathlibExt.NumberTheory.GeneralizedSylvester
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Insert
import Mathlib.Tactic.Ring

/-!
# Sylvester number congruences

The recurrence preserves the residue of `Sₖ` modulo `(Sₖ - 1)²` for every term
from index `k` onward. In particular, the terms from `S₂ = 7` onward have
residue `7` modulo `36`.

Starting from `S₃ = 43`, the recurrence preserves the residue `43` modulo `1764`
because `43² - 43 + 1 = 1807 = 1764 + 43` (congruence (7) in the reference below).
Starting from `S₁ = 3`, the residue modulo `4` gives a prime divisor congruent to
`3` modulo `4` in every subsequent term, including `S₁` itself.

Among the terms $S_n$ with $n \ge 0$, only $S_1 = 3$ has $2S_n = m(m+1)$ for a
natural number $m \ge 1$. The products $m(m+1)$ have residues $0, 2, 3, 6$ modulo
$9$, excluding $2S_0 \equiv 4 \pmod{9}$ and $2S_n \equiv 5 \pmod{9}$ for $n \ge 2$.

## References

* Abderrahim Makki Naciri, *A Note on Sylvester's Sequence*, INTEGERS 24
  (2024), Article A117, pp. 1–7, Proposition 1, divisibility (4) and congruences
  (5)–(7), and Corollary 1(b) and (d).
  <https://math.colgate.edu/~integers/y117/y117.pdf>
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- **Sylvester numbers.** The Sylvester numbers $S_0, S_1, S_2, \dots$ are the natural numbers
given by $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$ for $n \ge 0$, so the sequence begins
$2, 3, 7, 43, 1807, \dots$. It is the generalized Sylvester sequence with parameter $1$. -/
abbrev sylvesterNumber (n : ℕ) : ℕ :=
  Nat.generalizedSylvester 1 n

/-- **Sylvester numbers modulo 36.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 2$, $S_n \equiv 7 \pmod{36}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (6). -/
theorem sylvester_modEq_seven_mod_thirty_six
    (n : ℕ) (hn : 2 ≤ n) :
    sylvesterNumber n % 36 = 7 := by
  change sylvesterNumber n ≡ 7 [MOD 36]
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
    calc
      sylvesterNumber (n + 1) = sylvesterNumber n ^ 2 - sylvesterNumber n + 1 :=
        Nat.generalizedSylvester_succ 1 n
      _ ≡ 7 ^ 2 - 7 + 1 [MOD 36] :=
        (Nat.ModEq.sub (Nat.le_self_pow two_ne_zero _) (by decide)
          (ih.pow 2) ih).add_right 1
      _ ≡ 7 [MOD 36] := by decide

/-- **Divisibility of differences of Sylvester numbers.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For all natural numbers $k$, $m$ and $n$
with $k \ge 1$, $m \ge k$ and $n \ge k$, the integer $(S_k - 1)^2$ divides $S_n - S_m$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, divisibility
(4). -/
theorem sylvester_sub_dvd
    (k m n : ℕ) (hk : 1 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    ((sylvesterNumber k : ℤ) - 1) ^ 2 ∣
      (sylvesterNumber n : ℤ) - (sylvesterNumber m : ℤ) := by
  -- Keep the paper's named hypothesis; the residue argument also works at `k = 0`.
  have _ := hk
  have hres (j : ℕ) (hj : k ≤ j) :
      (sylvesterNumber j : ℤ) ≡ (sylvesterNumber k : ℤ)
        [ZMOD ((sylvesterNumber k : ℤ) - 1) ^ 2] := by
    induction j, hj using Nat.le_induction with
    | base => exact Int.ModEq.rfl
    | succ i _ ih =>
      have hstep : (sylvesterNumber (i + 1) : ℤ) =
          (sylvesterNumber i : ℤ) + ((sylvesterNumber i : ℤ) - 1) ^ 2 := by
        rw [show sylvesterNumber (i + 1) = sylvesterNumber i ^ 2 - sylvesterNumber i + 1 from
          Nat.generalizedSylvester_succ 1 i, Nat.cast_add,
          Int.ofNat_sub (Nat.le_self_pow two_ne_zero _), Nat.cast_pow, Nat.cast_one]
        ring
      rw [hstep]
      exact (ih.add ((ih.sub_right 1).pow 2)).trans
        (Int.add_modEq_left_iff.mpr (dvd_refl _))
  exact ((hres m hm).trans (hres n hn).symm).dvd

/-- **Sylvester numbers modulo 1764.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 3$, $S_n \equiv 43 \pmod{1764}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (7). -/
theorem sylvester_modEq_forty_three_mod_1764
    (n : ℕ) (hn : 3 ≤ n) :
    sylvesterNumber n % 1764 = 43 := by
  have hmod : (43 : ℤ) ≡ (sylvesterNumber n : ℤ) [ZMOD 1764] :=
    Int.modEq_iff_dvd.mpr (sylvester_sub_dvd 3 3 n (by decide) (by decide) hn)
  have hnat : 43 ≡ sylvesterNumber n [MOD 1764] := Int.natCast_modEq_iff.mp hmod
  exact hnat.symm

private theorem exists_prime_dvd_mod_four_eq_three (m : ℕ) (hm : m % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  induction m using induction_on_primes with
  | zero => simp at hm
  | one => simp at hm
  | prime_mul p a hp ih =>
    have hresidue : ∀ i j : Fin 4, (i.val * j.val) % 4 = 3 → i.val = 3 ∨ j.val = 3 := by
      decide
    rw [Nat.mul_mod] at hm
    rcases hresidue ⟨p % 4, Nat.mod_lt _ (by decide)⟩ ⟨a % 4, Nat.mod_lt _ (by decide)⟩ hm with
      h | h
    · exact ⟨p, hp, dvd_mul_right p a, h⟩
    · obtain ⟨q, hq, hqa, hqmod⟩ := ih h
      exact ⟨q, hq, hqa.trans (dvd_mul_left a p), hqmod⟩

/-- **Prime divisors congruent to 3 modulo 4 of Sylvester numbers.** Let $(S_n)_{n \ge 0}$ be the
Sylvester sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 1$, $S_n$ has a
prime divisor $p$ with $p \equiv 3 \pmod 4$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(d). -/
theorem sylvester_exists_prime_divisor_mod_four_eq_three
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ sylvesterNumber n ∧ p % 4 = 3 := by
  have hmod : (3 : ℤ) ≡ (sylvesterNumber n : ℤ) [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr (sylvester_sub_dvd 1 1 n (by decide) (by decide) hn)
  have hnat : 3 ≡ sylvesterNumber n [MOD 4] := Int.natCast_modEq_iff.mp hmod
  exact exists_prime_dvd_mod_four_eq_three _ hnat.symm

/-- **The only triangular Sylvester number is $3$.** Let $S_n$ denote the $n$-th Sylvester
number. A natural number $x$ equals $S_n$ for some $n$ and satisfies $2x = m(m + 1)$ for some
natural number $m \ge 1$ if and only if $x = 3$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(b). -/
theorem triangular_sylvester_values_eq :
    {x : ℕ | ∃ n m : ℕ, 1 ≤ m ∧ x = sylvesterNumber n ∧
      2 * x = m * (m + 1)} = {3} := by
  have havoid (m : ℕ) : ¬ m * (m + 1) ≡ 4 [MOD 9] ∧ ¬ m * (m + 1) ≡ 5 [MOD 9] := by
    have hfin : ∀ r : Fin 9,
        ¬ r.val * (r.val + 1) ≡ 4 [MOD 9] ∧ ¬ r.val * (r.val + 1) ≡ 5 [MOD 9] := by decide
    have hr := Nat.mod_modEq m 9
    have hp := hr.mul (hr.add_right 1)
    obtain ⟨h4, h5⟩ := hfin ⟨m % 9, Nat.mod_lt _ (by decide)⟩
    exact ⟨fun h => h4 (hp.trans h), fun h => h5 (hp.trans h)⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, m, -, rfl, hm⟩
    rcases n with _ | _ | n
    · have h4 : m * (m + 1) ≡ 4 [MOD 9] := by
        rw [← hm]
        decide
      exact ((havoid m).1 h4).elim
    · decide
    · have h36 : sylvesterNumber (n + 2) ≡ 7 [MOD 36] :=
        sylvester_modEq_seven_mod_thirty_six (n + 2) (by omega)
      have h5 : m * (m + 1) ≡ 5 [MOD 9] := by
        rw [← hm]
        exact ((h36.of_dvd (by decide : 9 ∣ 36)).mul_left 2).trans (by decide)
      exact ((havoid m).2 h5).elim
  · rintro rfl
    exact ⟨1, 2, by decide, by decide, by decide⟩

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

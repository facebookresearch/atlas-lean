/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeInterval.Breusch

@[expose] public section

namespace MathlibExt.NumberTheory.BreuschWanted

/-- **Ramanujan's two-primes refinement of Bertrand's postulate.** For every natural number
$n \ge 6$ there are primes $p$ and $q$ with $n < p < q < 2n$; that is, the open interval
$(n, 2n)$ contains two distinct primes.

For $n \ge 48$ this follows from Breusch's theorem applied at $n$ and at $9n/8$; the remaining
finitely many cases are checked by direct computation.

Source: Nathaniel Benjamin, Grant Fickes, Eugene Fiorini,
Edgar Jaramillo Rodriguez, Eric Jovinelly, and Tony W. H. Wong, "Primes
and Perfect Powers in the Catalan Triangle", Journal of Integer Sequences
22 (2019), Article 19.7.6, proof sentence at line 153 (inside the proof of
the theorem labeled `c_nn not power`), attributed there to Ramanujan,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Fiorini/fiorini3.tex>. -/
theorem ramanujan_two_primes_between (n : ℕ) (hn : 6 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q < 2 * n := by
  by_cases h48 : 48 ≤ n
  · obtain ⟨p, hp_prime, hn_p, hp_upper⟩ :=
      breusch_prime_interval (n : ℝ) (by exact_mod_cast h48)
    have hscaled : (48 : ℝ) ≤ (9 / 8 : ℝ) * n := by
      have hn_real : (48 : ℝ) ≤ n := by exact_mod_cast h48
      nlinarith
    obtain ⟨q, hq_prime, hscaled_q, hq_upper⟩ :=
      breusch_prime_interval ((9 / 8 : ℝ) * n) hscaled
    refine ⟨p, q, hp_prime, hq_prime, ?_, ?_, ?_⟩
    · exact_mod_cast hn_p
    · exact_mod_cast hp_upper.trans hscaled_q
    · have hn_pos : (0 : ℝ) < n := by positivity
      have hq_two : (q : ℝ) < 2 * n := by
        calc
          (q : ℝ) < (9 / 8 : ℝ) * ((9 / 8 : ℝ) * n) := hq_upper
          _ < 2 * n := by nlinarith
      exact_mod_cast hq_two
  · have hn_lt : n < 48 := Nat.lt_of_not_ge h48
    by_cases h7 : n < 7
    · exact ⟨7, 11, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h11 : n < 11
    · exact ⟨11, 13, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h13 : n < 13
    · exact ⟨13, 17, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h17 : n < 17
    · exact ⟨17, 19, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h23 : n < 23
    · exact ⟨23, 29, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h29 : n < 29
    · exact ⟨29, 31, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h37 : n < 37
    · exact ⟨37, 41, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h43 : n < 43
    · exact ⟨43, 47, by decide, by decide, by omega, by omega, by omega⟩
    exact ⟨53, 59, by decide, by decide, by omega, by omega, by omega⟩

end MathlibExt.NumberTheory.BreuschWanted

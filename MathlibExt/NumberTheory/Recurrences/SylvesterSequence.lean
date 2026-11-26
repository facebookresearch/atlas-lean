/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedSylvester
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Sylvester number congruences

The recurrence preserves the residue of `Sₖ` modulo `(Sₖ - 1)²` for every term
from index `k` onward. In particular, the terms from `S₂ = 7` onward have
residue `7` modulo `36`.

Starting from `S₃ = 43`, the recurrence preserves the residue `43` modulo `1764`
because `43² - 43 + 1 = 1807 = 1764 + 43` (congruence (7) in the reference below).

## References

* Abderrahim Makki Naciri, *A Note on Sylvester's Sequence*, INTEGERS 24
  (2024), Article A117, Proposition 1, divisibility (4) and congruence (6).
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

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

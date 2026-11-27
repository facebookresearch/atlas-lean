/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/-! # Integrality of Fuss-Catalan numbers
-/

/--
**Integrality of the Fuss–Catalan numbers.** For natural numbers $a \ge 2$ and $n \ge 1$, the
integer $(a-1)n + 1$ divides the binomial coefficient $\binom{an}{n}$. Hence the Fuss–Catalan
number $\frac{1}{(a-1)n+1}\binom{an}{n}$ is an integer.

Proves `Wanted` entry `fuss_catalan_dvd_choose`.

Source: Christian Ballot,
"Lucasnomial Fuss-Catalan Numbers and Related Divisibility Questions,"
Journal of Integer Sequences 21 (2018), Article 18.6.5,
equation (label eq:FC), lines 115–117 (classical definition),
line 127 (classical integrality recorded as known),
Theorem (label thm:1), lines 516–521 (Lucasnomial generalization),
https://cs.uwaterloo.ca/journals/JIS/VOL21/Ballot/ballot30.tex
-/
theorem fuss_catalan_dvd_choose
    (a n : ℕ) (ha : 2 ≤ a) (hn : 1 ≤ n) :
    (a - 1) * n + 1 ∣ Nat.choose (a * n) n := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : 2 + c - 1 = c + 1 := by omega
  have hdivisor : (2 + c - 1) * (1 + k) + 1 = (c + 1) * (k + 1) + 1 := by
    rw [hsub]; ring
  have hprod : (2 + c) * (1 + k) = ((c + 1) * (k + 1) + 1) + k := by ring
  rw [hdivisor, hprod]
  have hident : Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) * (k + 1)
      = Nat.choose ((c + 1) * (k + 1) + 1 + k) k * ((c + 1) * (k + 1) + 1) := by
    have h := Nat.choose_succ_right_eq ((c + 1) * (k + 1) + 1 + k) k
    rwa [Nat.add_sub_cancel] at h
  have hgoal_eq : Nat.choose (((c + 1) * (k + 1) + 1) + k) (1 + k)
      = Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) := by
    rw [Nat.add_comm 1 k]
  rw [hgoal_eq]
  have hdiv : (c + 1) * (k + 1) + 1 ∣ (k + 1) * Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) := by
    refine ⟨Nat.choose ((c + 1) * (k + 1) + 1 + k) k, ?_⟩
    calc (k + 1) * Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1)
        = Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) * (k + 1) := by ring
      _ = Nat.choose ((c + 1) * (k + 1) + 1 + k) k * ((c + 1) * (k + 1) + 1) := hident
      _ = ((c + 1) * (k + 1) + 1) * Nat.choose ((c + 1) * (k + 1) + 1 + k) k := by ring
  have hcop : Nat.Coprime ((c + 1) * (k + 1) + 1) (k + 1) := by
    have h1 : Nat.Coprime (k + 1) (1 + (c + 1) * (k + 1)) :=
      (Nat.coprime_add_mul_right_right (k + 1) 1 (c + 1)).mpr
        (Nat.coprime_one_right (k + 1))
    have h2 : (c + 1) * (k + 1) + 1 = 1 + (c + 1) * (k + 1) := by ring
    rw [h2]
    exact h1.symm
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdiv

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KFull
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/-- **Arithmetic progressions of 2-full numbers of every length.** For every natural number
$k$ there are positive integers $a$ and $d$ such that $a + id$ is $2$-full (powerful) for every
natural number $i < k$. -/
theorem arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general (k : ℕ) :
    ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
      ∀ i : ℕ, i < k → Nat.IsKFull 2 (a + i * d) := by
  -- Let L be a common multiple of 1, 2, ..., k; use N_i = 1 + i and M_i = L^2 * N_i.
  set L : ℕ := ∏ j ∈ Finset.range k, (1 + j) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Finset.prod_pos
    intro j _
    omega
  have ha : 0 < L ^ 2 := pow_pos hLpos 2
  refine ⟨L ^ 2, L ^ 2, ha, ha, fun i hi => ⟨(Nat.add_pos_left ha _).ne', fun p hp hdvd => ?_⟩⟩
  have hmem : (1 + i) ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)
  have heq : L ^ 2 + i * L ^ 2 = L ^ 2 * (1 + i) := by ring
  rw [heq] at hdvd ⊢
  have hpL : p ∣ L := by
    rcases (hp.dvd_mul.mp hdvd) with h | h
    · exact hp.dvd_of_dvd_pow h
    · exact h.trans hmem
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpL 2) _

set_option linter.unusedVariables false in
/--
**Arbitrarily long arithmetic progressions of powerful numbers.** For every integer $k \ge 3$
there are positive integers $a$ and $d$ such that each of the $k$ numbers $a + id$ with
$0 \le i < k$ is powerful: every prime that divides $a + id$ has its square dividing $a + id$.

Source: Tsz Ho Chan, "Arithmetic Progressions Among Powerful Numbers",
Journal of Integer Sequences 26 (2023), Article 23.1.1, Theorem `thm-longAP`,
source lines 97–99,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Chan/chan33.tex>.
The paper notes the result is not new (see remark 2 in [H] there) and includes a
proof for completeness. Powerful (squarefull) means every prime divisor appears
with exponent at least two; nonconstant is `0 < d`.
It follows from `arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general`, which
states powerfulness as `Nat.IsKFull 2`; the hypothesis `hk` is unused and keeps the source's
shape.
Proves `Wanted` entry `arbitrarily_long_arithmetic_progressions_of_powerful_numbers`.
-/
theorem arbitrarily_long_arithmetic_progressions_of_powerful_numbers
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
      ∀ i : ℕ, i < k →
        ∀ p : ℕ, p.Prime → p ∣ a + i * d → p ^ 2 ∣ a + i * d := by
  obtain ⟨a, d, ha, hd, h⟩ := arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general k
  exact ⟨a, d, ha, hd, fun i hi => (h i hi).2⟩

end MetaMathlibExt

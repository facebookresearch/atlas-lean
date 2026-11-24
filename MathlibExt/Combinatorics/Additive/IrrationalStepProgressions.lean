/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.Irrational

/-!
# Rational starts and irrational steps in arithmetic progressions
-/

namespace MetaMathlibExt

/-- **Nonnegative integer points for a rational start and an irrational difference.** Let $x$ be
a rational number that is not a nonnegative integer, and let $d$ be an irrational real number.
Then $x + id$ is not a nonnegative integer for any natural number $i$, and $2x + jd$ is not a
nonnegative integer for any natural number $j \ge 1$.

As printed, the paper's Lemma 18 (ii) also claims $2x + 0 \cdot d \notin \mathbb{N}$, which fails
at $x = 1/2$ (where $2x = 1$); the paper's proof ("then $d \in \mathbb{Q}$") covers only $j \ge 1$,
and the condition that the denominator of $x$ be at least $3$ is attached only to part (iii).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem add_mul_not_mem_nat_of_rat_of_irrational (x d : ℝ)
    (hx : x ∈ Set.range ((↑) : ℚ → ℝ)) (hxn : x ∉ Set.range ((↑) : ℕ → ℝ)) (hd : Irrational d)
    (i j : ℕ) (hj : 1 ≤ j) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ) := by
  obtain ⟨q, rfl⟩ := hx
  have not_mem (a : ℚ) {k : ℕ} (hk : k ≠ 0) :
      (a : ℝ) + k * d ∉ Set.range ((↑) : ℕ → ℝ) := by
    rintro ⟨n, hn⟩
    exact ((hd.natCast_mul hk).ratCast_add a).ne_nat n hn.symm
  constructor
  · by_cases hi : i = 0
    · simpa [hi] using hxn
    · exact not_mem q hi
  · simpa using not_mem (2 * q) (Nat.ne_of_gt hj)

end MetaMathlibExt

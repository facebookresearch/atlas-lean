/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.Irrational

/-!
# Irrational starts and rational steps in arithmetic progressions

No natural number occurs in a rational-step progression starting at an irrational number or at its
double.
-/

namespace MetaMathlibExt

/-- **No nonnegative integer points for an irrational start and a rational difference.** Let
$x$ be an irrational real number and $d$ a rational number. Then for all natural numbers $i$ and
$j$, neither $x + id$ nor $2x + jd$ is a nonnegative integer.

The paper assumes $d \in \mathbb{Q} \setminus \mathbb{N}$; the claim holds for every rational $d$,
so that restriction is not stated.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem add_mul_not_mem_nat_of_irrational_of_rat (x d : ℝ) (hx : Irrational x)
    (hd : d ∈ Set.range ((↑) : ℚ → ℝ)) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ) := by
  obtain ⟨q, rfl⟩ := hd
  have not_mem {y : ℝ} (hy : Irrational y) (k : ℕ) :
      y + k * (q : ℝ) ∉ Set.range ((↑) : ℕ → ℝ) := by
    rintro ⟨n, hn⟩
    exact (hy.add_ratCast (k * q)).ne_nat n (by simpa using hn.symm)
  exact ⟨not_mem hx i, not_mem (hx.natCast_mul (m := 2) (by decide)) j⟩

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import MathlibExt.NumberTheory.GenLeonardo

import Mathlib.Tactic.NormNum

/-!
# Log-balance of the Leonardo numbers at index three

The Leonardo numbers are log-convex at index three, and their factorial normalization is
log-concave there.
-/

namespace MetaMathlibExt

/-- **Leonardo numbers are log-balanced at index three.** Let $Le_n$ be the Leonardo numbers
($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$). Then $Le_3^2 \le Le_2 Le_4$ and
$\frac{Le_2}{2!} \cdot \frac{Le_4}{4!} \le \left(\frac{Le_3}{3!}\right)^2$, the second
inequality in the real numbers. That is, $(Le_n)$ satisfies the log-convexity inequality at
$n = 3$ and $(Le_n / n!)$ satisfies the log-concavity inequality at $n = 3$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 11, with the
definition of log-balanced displayed before Proposition 10 (`integers-2026-A48-prop-11`). -/
public theorem leonardo_logBalanced_three :
    genLeonardo 1 3 ^ 2 ≤ genLeonardo 1 2 * genLeonardo 1 4 ∧
      ((genLeonardo 1 2 : ℝ) / Nat.factorial 2) * ((genLeonardo 1 4 : ℝ) / Nat.factorial 4) ≤
        ((genLeonardo 1 3 : ℝ) / Nat.factorial 3) ^ 2 := by
  have h₂ : genLeonardo 1 2 = 3 := rfl
  have h₃ : genLeonardo 1 3 = 5 := rfl
  have h₄ : genLeonardo 1 4 = 9 := rfl
  rw [h₂, h₃, h₄]
  constructor
  · norm_num
  · norm_num [Nat.factorial]

end MetaMathlibExt

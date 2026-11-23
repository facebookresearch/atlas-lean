/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

variable {K : Type*} [Field K]

/-- **Binet formula for second-order linear recurrences.** Let $K$ be a field, let
$P, Q, \alpha, \beta \in K$ with $\alpha \ne \beta$, and suppose that $\alpha$ and $\beta$ are
both roots of $z^2 - Pz + Q$. If a sequence $u : \mathbb{N} \to K$ satisfies
$u_{n+2} = P u_{n+1} - Q u_n$ for all $n$, then for every natural number $n$,
$$u_n = \frac{(u_1 - \beta u_0)\alpha^n - (u_1 - \alpha u_0)\beta^n}{\alpha - \beta}.$$

Source: Hongshen Chua, "A Study of Second-Order Linear Recurrence
Sequences via Continuants," Journal of Integer Sequences 26 (2023),
Article 23.8.8, Theorem [Binet's formula] (label Th:Binet_Formula),
lines 270–274,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Chua2/chua13.tex>.
Proves `Wanted` entry `binet_closed_form_second_order`. -/
theorem binet_closed_form_second_order
    (u : ℕ → K) (P Q α β : K)
    (hα : α ^ 2 - P * α + Q = 0) (hβ : β ^ 2 - P * β + Q = 0)
    (hne : α ≠ β)
    (hrec : ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n)
    (n : ℕ) :
    u n = ((u 1 - β * u 0) * α ^ n - (u 1 - α * u 0) * β ^ n) / (α - β) := by
  have hne' : α - β ≠ 0 := sub_ne_zero.mpr hne
  have key : ∀ m : ℕ, u m * (α - β) =
      (u 1 - β * u 0) * α ^ m - (u 1 - α * u 0) * β ^ m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => ring
    | one => ring
    | more m ih0 ih1 =>
      have r := hrec m
      linear_combination (α - β) * r + P * ih1 - Q * ih0 -
        ((u 1 - β * u 0) * α ^ m) * hα + ((u 1 - α * u 0) * β ^ m) * hβ
  rw [eq_div_iff hne']
  exact key n

end MetaMathlibExt

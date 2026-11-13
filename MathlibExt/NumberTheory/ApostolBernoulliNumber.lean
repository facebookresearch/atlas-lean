/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Apostol-Bernoulli numbers
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Apostol–Bernoulli numbers.** Let $\alpha$ be a complex number and let $\log$ denote the
principal branch of the complex logarithm. A sequence $(\beta_k)_{k \ge 0}$ of complex numbers
is the sequence of Apostol–Bernoulli numbers $\beta_k(\alpha)$ when $\alpha \ne 0$,
$\alpha \ne 1$, and for every complex number $t$ with $|t| < |\log \alpha|$ the series
$\sum_{k \ge 0} \beta_k t^k / k!$ converges unconditionally to $t / (\alpha e^t - 1)$.

Source: concept `jis_sem_b4b0e1e624b9b6eac0d29207`, source statement
`jis_5ab17288071712819e845b9a`, equation `eq21111`. -/
public def IsApostolBernoulliSequence (α : ℂ) (β : ℕ → ℂ) : Prop :=
  α ≠ 0 ∧ α ≠ 1 ∧
    ∀ t : ℂ, ‖t‖ < ‖Complex.log α‖ →
      HasSum (fun k : ℕ => β k * t ^ k / (Nat.factorial k : ℂ))
        (t / (α * Complex.exp t - 1))

end

end MetaMathlibExt

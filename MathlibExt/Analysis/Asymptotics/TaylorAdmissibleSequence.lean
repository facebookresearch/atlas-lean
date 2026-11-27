/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Admissible sequences for Taylor's law.** A sequence $a : \mathbb{N} \to \mathbb{N}$, indexed
from $1$ (its value at $0$ is ignored), is admissible when $a(n) > 0$ for every $n \ge 1$ and
there is $n_0 \ge 1$ such that $a(n) < a(n + 1)$ for every $n \ge n_0$.

Source: Joel E. Cohen, *Variance Functions of Asymptotically Exponentially
Increasing Integer Sequences Go Beyond Taylor's Law*, Journal of Integer
Sequences 25 (2022), Article 22.9.3, the collection `𝒜` of infinite
eventually strictly increasing sequences of natural numbers, lines 113–125,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Cohen/cohen13.tex>. -/
public def IsTaylorAdmissibleSequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < a n) ∧ ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → a n < a (n + 1)

end

end MetaMathlibExt

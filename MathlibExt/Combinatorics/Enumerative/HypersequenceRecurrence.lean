/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Recurrence between hypersequence generations -/

namespace MetaMathlibExt

@[expose] public section

/-- **Recurrence between consecutive hypersequence generations.** Let $(a_n)$ be a sequence of
complex numbers and let $a^{(r)}_n$ denote its hypersequence of generation $r$. For all natural
numbers $r$ and $n$, $a^{(r+1)}_{n+1} = a^{(r+1)}_n + a^{(r)}_{n+1}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 2, Equation (2.2) (`integers-2024-A70-thm-2`). -/
public theorem hypersequence_succ_succ (a : ℕ → ℂ) (r n : ℕ) :
    hypersequence a (r + 1) (n + 1) = hypersequence a (r + 1) n + hypersequence a r (n + 1) := by
  rw [hypersequence_succ a r (n + 1), hypersequence_succ a r n, Finset.sum_range_succ]

end

end MetaMathlibExt

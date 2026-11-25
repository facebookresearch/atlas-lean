/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackRecurrence
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Interval.Finset.Basic

/-!
# Recurrence for the positive even integers with the first two entries swapped

In the sequence starting with `4, 2, 6, 8, …`, the value two leads at times one and four
and recurs beyond every cutoff.
-/

namespace MetaMathlibExt.throwbackSequence_infinite_eq

private def swappedEvens (i : ℕ) := 2 * Equiv.swap 0 1 i + 2

example : ((Finset.range 5).filter fun k => throwbackSequence swappedEvens k = 2) = {1, 4} := by
  decide

example (N : ℕ) : ∃ k > N, throwbackSequence swappedEvens k = 2 := by
  have hinj : Function.Injective swappedEvens := by
    intro i j heq
    apply (Equiv.swap 0 1).injective
    unfold swappedEvens at heq
    omega
  have hits := throwbackSequence_infinite_eq swappedEvens (fun _ => by unfold swappedEvens; omega)
    hinj 1
  obtain ⟨k, hk, hNk⟩ := hits.exists_gt N
  exact ⟨k, hNk, hk⟩

end MetaMathlibExt.throwbackSequence_infinite_eq

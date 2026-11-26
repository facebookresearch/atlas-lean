/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MathlibExt.Combinatorics.MisereCubeFaceNim

/-! # Tests for misère face Nim on a cube -/

open MetaMathlibExt

namespace MetaMathlibExt.cubeFaceNim_misere_pPositions

-- The total number of tokens decreases on each move, so the misère recursion defines a set.
private def losing (p : Fin 6 → ℕ) : Prop :=
  (∃ q, CubeFaceMove p q) ∧ ∀ q, (hm : CubeFaceMove p q) → ¬ losing q
termination_by ∑ i, p i
decreasing_by
  obtain ⟨i, hle, hne, hfixed⟩ := hm
  apply Finset.sum_lt_sum (fun j _ => hle j)
  exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hle i) fun he =>
    hne (funext fun j => if hj : j = i then hj ▸ he else hfixed j hj)⟩

example : ∃ P : Set (Fin 6 → ℕ),
    ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P :=
  ⟨{p | losing p}, fun p => by
    change losing p ↔ _
    conv_lhs => rw [losing]
    rfl⟩

end MetaMathlibExt.cubeFaceNim_misere_pPositions

variable (P : Set (Fin 6 → ℕ))
  (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)

-- No player is forced to take the last token on an already empty cube.
example : ![0, 0, 0, 0, 0, 0] ∉ P := fun hp => (by decide : ¬ _) <|
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- A single token loses, while two tokens on the same face allow a winning move.
example : ![0, 0, 0, 0, 0, 1] ∈ P :=
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

example : ![0, 0, 0, 0, 0, 2] ∉ P := fun hp => (by decide : ¬ _) <|
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- The three nonempty heaps have distinct sizes and zero nim-sum.
example : ![0, 0, 0, 1, 2, 3] ∈ P :=
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.SlowANim

namespace MetaMathlibExt.slowANim_n_sub_one_option_of_reduced

private abbrev start : Fin 3 → ℕ := ![1, 1, 2]
private abbrev middle : Fin 3 → ℕ := ![1, 0, 1]

private theorem middle_reaches_zero :
    Relation.ReflTransGen (fun p q => q ∈ slowANimMoves {2} p) middle (fun _ => 0) :=
  .single (by decide)

private theorem reduced_of_reaches_zero {p : Fin 3 → ℕ}
    (h : Relation.ReflTransGen (fun x y => y ∈ slowANimMoves {2} x) p (fun _ => 0)) :
    SlowANimReduced {2} p :=
  fun _ => ⟨_, h, slowANimMoves_zero _, rfl⟩

-- Omitting an odd stack sends residue 0 to 2 and leaves two odd stacks.
example :
    (∑ i, slowANimAfter start {1, 2} i) % 4 = 2 ∧
      (Finset.univ.filter fun i => Odd (slowANimAfter start {1, 2} i)).card = 2 := by
  have hp := reduced_of_reaches_zero (middle_reaches_zero.head
    (show middle ∈ slowANimMoves {2} start by decide))
  have hmove : slowANimAfter start {1, 2} = middle := by decide
  exact slowANim_n_sub_one_option_of_reduced 3 (by decide) start hp {1, 2} (by decide)
    (by decide) (hmove ▸ reduced_of_reaches_zero middle_reaches_zero) 0 (by decide)

-- The only move omits the empty stack, sends residue 2 to 0, and leaves no odd stacks.
example : slowANimMoves {2} middle = {fun _ => 0} := by decide

example :
    (∑ i, slowANimAfter middle {0, 2} i) % 4 = 0 ∧
      (Finset.univ.filter fun i => Odd (slowANimAfter middle {0, 2} i)).card = 0 := by
  have hmove : slowANimAfter middle {0, 2} = fun _ => 0 := by decide
  exact slowANim_n_sub_one_option_of_reduced 3 (by decide) middle
    (reduced_of_reaches_zero middle_reaches_zero) {0, 2} (by decide) (by decide)
    (hmove ▸ slowANimReduced_zero _) 1 (by decide)

end MetaMathlibExt.slowANim_n_sub_one_option_of_reduced

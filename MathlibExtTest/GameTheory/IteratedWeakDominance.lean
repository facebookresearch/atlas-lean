/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.IteratedWeakDominance

/-! # Tests for iterated weak dominance on surviving pure strategies -/

namespace MathlibExtTest.GameTheory.IteratedWeakDominance

open Finset MathlibExt.GameTheory

private abbrev State := Finset (Fin 3) × Finset (Fin 2)
private abbrev full : State := (univ, univ)
private abbrev right : State := ({1, 2}, {1})
private abbrev left : State := ({0, 1}, {0})

-- Read both players' payoffs, including the two middle-row entries where the column player ties.
example : orderDependencePayoff (0, 0) = (1, 1) ∧ orderDependencePayoff (0, 1) = (0, 0) ∧
    orderDependencePayoff (1, 0) = (1, 1) ∧ orderDependencePayoff (1, 1) = (2, 1) ∧
    orderDependencePayoff (2, 0) = (0, 0) ∧ orderDependencePayoff (2, 1) = (2, 1) := by decide

-- Neither column may be deleted first: the column player prefers L at T and R at B.
example {next : State} (h : WeakDominanceStep orderDependencePayoff full next) :
    next.2 = univ := by
  cases h with
  | row => rfl
  | col _ _ better =>
    have cross : ∀ c d : Fin 2, ¬ ((fun r : (univ : Finset (Fin 3)) ↦
        (orderDependencePayoff (r, c)).2) <
          fun r : (univ : Finset (Fin 3)) ↦ (orderDependencePayoff (r, d)).2) := by
      simp_rw [Pi.lt_def]
      decide
    exact (cross _ _ better).elim

-- Against {M,B}, R ties L at M and wins at B; against {T,M}, the reverse comparison holds.
example : WeakDominanceStep orderDependencePayoff ({1, 2}, univ) right ∧
    WeakDominanceStep orderDependencePayoff ({0, 1}, univ) left := by
  constructor
  · change WeakDominanceStep _ ({1, 2}, univ) ({1, 2}, {1})
    rw [show ({1} : Finset (Fin 2)) = univ.erase 0 by decide]
    exact .col (mem_univ 0) (mem_univ 1) (Pi.lt_def.mpr (by decide))
  · change WeakDominanceStep _ ({0, 1}, univ) ({0, 1}, {0})
    rw [show ({0} : Finset (Fin 2)) = univ.erase 1 by decide]
    exact .col (mem_univ 1) (mem_univ 0) (Pi.lt_def.mpr (by decide))

-- Both maximal runs retain two distinct profiles, even though their remaining rows tie.
example : Relation.ReflTransGen (WeakDominanceStep orderDependencePayoff) full right ∧
    Relation.ReflTransGen (WeakDominanceStep orderDependencePayoff) full left ∧
    (∀ next, ¬ WeakDominanceStep orderDependencePayoff right next) ∧
    (∀ next, ¬ WeakDominanceStep orderDependencePayoff left next) ∧
    right.1.product right.2 = {(1, 1), (2, 1)} ∧ left.1.product left.2 = {(0, 0), (1, 0)} := by
  obtain ⟨hr, hl, sr, sl, _⟩ := iteratedWeakDominance_depends_on_order
  exact ⟨hr, hl, sr, sl, by decide, by decide⟩

-- In a different game even distinct row labels cannot witness a deletion if all payoffs tie.
example (next : Finset Bool × Finset Bool) :
    ¬ WeakDominanceStep (fun _ ↦ ((0, 0) : ℤ × ℤ)) (univ, univ) next :=
  not_weakDominanceStep_of_constant (v := (0, 0)) (fun _ _ _ _ ↦ rfl) next

end MathlibExtTest.GameTheory.IteratedWeakDominance

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Epistemic.CommonKnowledge
import Mathlib.Data.Set.Basic

namespace Cslib.Epistemic.CommonKnowledgeTests

open Cslib.Epistemic

/-- Empty group: common knowledge collapses to the formula itself, which
holds at the heads world of the coin model. -/
example : Sat muddy (.common ∅ (.atom ())) true := by
  apply common_induction muddy (show Sat muddy (.atom ()) true from rfl)
  intro u _ i hi
  exact absurd hi (Set.notMem_empty i)

/-- One agent who sees the coin: `p` is common knowledge of `{0}` at heads. -/
example : Sat muddy (.common {0} (.atom ())) true := by
  apply common_induction muddy (show Sat muddy (.atom ()) true from rfl)
  intro u hu i hi v hiv
  have hi0 : i = 0 := hi
  subst hi0
  have hu' : u = true := hu
  subst hu'
  have hv : v = true := hiv.symm
  exact hv ▸ rfl

/-- Both agents: agent `1` reaches the tails world in one step, so `p` is
not common knowledge at heads, even though agent `0` knows it. -/
example : ¬ Sat muddy (.common Set.univ (.atom ())) true := by
  intro h
  have hstep : Relation.ReflTransGen (groupRel muddy Set.univ) true false :=
    Relation.ReflTransGen.single ⟨1, Set.mem_univ 1, trivial⟩
  have hfalse : (false : Bool) = true := h false hstep
  exact Bool.false_ne_true hfalse

/-- A three-world chain: agent `0` steps `0 → 1 → 2`; the atom holds at
`0` and `1` only. -/
def chainModel : Model (Fin 3) Unit (Fin 1) where
  rel := fun _ a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
  valuation := fun w _ => w = 0 ∨ w = 1
  nonempty_world := ⟨0⟩

/-- Everyone in `{0}` knows the atom at `0` (its only successor is `1`). -/
example : Sat chainModel (.know 0 (.atom ())) 0 := by
  intro v hv
  rcases hv with ⟨-, rfl⟩ | ⟨h, -⟩
  · exact Or.inr rfl
  · exact absurd h (by decide)

/-- But the atom is not common knowledge at `0`: two steps reach `2`. -/
example : ¬ Sat chainModel (.common {0} (.atom ())) 0 := by
  intro h
  have h01 : Relation.ReflTransGen (groupRel chainModel {0}) 0 1 :=
    Relation.ReflTransGen.single ⟨0, rfl, Or.inl ⟨rfl, rfl⟩⟩
  have h12 : Relation.ReflTransGen (groupRel chainModel {0}) 1 2 :=
    Relation.ReflTransGen.single ⟨0, rfl, Or.inr ⟨rfl, rfl⟩⟩
  have hfalse := h 2 (h01.trans h12)
  rcases hfalse with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Empty group at tails: common knowledge collapses to the atom itself,
which is false there (the positive-length convention would make it true). -/
example : ¬ Sat muddy (.common ∅ (.atom ())) false := by
  intro h
  have hfalse : (false : Bool) = true := h false Relation.ReflTransGen.refl
  exact Bool.false_ne_true hfalse

end Cslib.Epistemic.CommonKnowledgeTests

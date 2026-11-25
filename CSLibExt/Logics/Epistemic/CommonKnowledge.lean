/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Common knowledge
-/
module

public import CSLibExt.Logics.Epistemic.Basic

/-!
# Common knowledge

Common knowledge `C_G φ` for a group `G` holds at a world when `φ` holds at
every world reachable by a finite chain of `G`-steps, zero steps included
(the reflexive-transitive convention). This file proves the fixed-point
unfolding `C_G φ ↔ φ ∧ E_G (C_G φ)`, that common knowledge gives each group
member's knowledge, and the induction principles: a formula holding at a
world and preserved along every single `G`-step is common knowledge there,
and so is any formula certified by an arbitrary step-preserved invariant.

Background: R. Fagin, J. Y. Halpern, Y. Moses and M. Y. Vardi, *Reasoning
About Knowledge*, MIT Press, 1995, Chapter 2 defines common knowledge by
positive-length iteration; the two conventions agree when the group is
nonempty and every member relation is reflexive. Under the zero-step
convention used here, `C_G φ` implies `φ` on every frame, `C_∅ φ` is
equivalent to `φ`, and `C_G ⊥` is false everywhere; in non-reflexive models
this operator is therefore not the positive-length notion.
-/

@[expose] public section

namespace Cslib
namespace Epistemic

variable {World Atom Agent : Type*} (M : Model World Atom Agent)
  {G : Set Agent} {φ : Formula Atom Agent} {w : World}

/-- Fixed point: common knowledge is the formula itself together with every
group member knowing the common knowledge (one unfolding of reachability). -/
theorem sat_common_iff :
    Sat M (.common G φ) w ↔
      Sat M φ w ∧ ∀ i ∈ G, ∀ v, M.rel i w v → Sat M (.common G φ) v := by
  constructor
  · intro h
    constructor
    · exact h w Relation.ReflTransGen.refl
    · intro i hi v hrel u huv
      exact h u ((Relation.ReflTransGen.single ⟨i, hi, hrel⟩).trans huv)
  · rintro ⟨h0, hE⟩ v h
    rcases Relation.ReflTransGen.cases_head h with rfl | ⟨u, hstep, huv⟩
    · exact h0
    · obtain ⟨i, hi, hrel⟩ := hstep
      exact hE i hi u hrel v huv

/-- Common knowledge implies each group member's knowledge of the formula. -/
theorem sat_know_of_common_of_mem {i : Agent} (hi : i ∈ G) :
    Sat M (.common G φ) w → Sat M (.know i φ) w := by
  intro h v hrel
  exact h v (Relation.ReflTransGen.single ⟨i, hi, hrel⟩)

/-- Induction: a formula that holds at `w` and is preserved along every
single group step is common knowledge at `w`. -/
theorem common_induction
    (h0 : Sat M φ w)
    (hstep : ∀ u, Sat M φ u → ∀ i ∈ G, ∀ v, M.rel i u v → Sat M φ v) :
    Sat M (.common G φ) w := by
  intro v h
  induction h with
  | refl => exact h0
  | tail _ h2 ih =>
      obtain ⟨i, hi, hrel⟩ := h2
      exact hstep _ ih i hi _ hrel

/-- Induction, general invariant form: any predicate `P` that holds at `w`,
implies `φ` wherever it holds, and is preserved along every single group
step, certifies common knowledge of `φ` at `w`. -/
theorem sat_common_induction {P : World → Prop}
    (hw : P w)
    (himp : ∀ u, P u → Sat M φ u)
    (hstep : ∀ u, P u → ∀ i ∈ G, ∀ v, M.rel i u v → P v) :
    Sat M (.common G φ) w := by
  have hP : ∀ v, Relation.ReflTransGen (groupRel M G) w v → P v := by
    intro v h
    induction h with
    | refl => exact hw
    | tail _ h2 ih =>
        obtain ⟨i, hi, hrel⟩ := h2
        exact hstep _ ih i hi _ hrel
  intro v h
  exact himp v (hP v h)

end Epistemic
end Cslib

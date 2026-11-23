/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Languages.IMP.Denotational
public import CSLibExt.Languages.IMP.HoareTotal

/-!
# Total preconditions as least fixed points

The existing total-correctness `wp` of an IMP while loop is the least fixed point
of its guarded predicate transformer. Leastness is transported from the existing
relational denotation through `Denote.while_ind`; no new execution semantics or
loop induction principle is assumed. Unlike liberal preconditions, these
preconditions require a terminating execution.

For deterministic IMP, total correctness is exactly termination together with
liberal correctness. This characterization does not assert must-termination for
arbitrary nondeterministic relations.

The total-correctness setting follows Nipkow and Klein, *Concrete Semantics*,
Section 12.5, https://concrete-semantics.cs.tum.edu/concrete-semantics.pdf.
The predicate fixed-point characterization is derived using the existing IMP
relational least-fixed-point semantics and Mathlib's Knaster–Tarski API.
-/

@[expose] public section
namespace Cslib.IMP.wp

/-- One total-correctness step: exit with the postcondition, or terminate the body safely. -/
def whileStep (b : BExp) (c : Cmd) (Q : Assertion) : Set State →o Set State where
  toFun I := {s | (b.eval s = false ∧ Q s) ∨ (b.eval s = true ∧ wp c I s)}
  monotone' := by
    intro I J h s hs
    rcases hs with h | ⟨hb, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨hb, wp.monotone h hc⟩

/-- The existing while unfolding equation makes its total precondition a fixed point. -/
theorem whileStep_wp (b : BExp) (c : Cmd) (Q : Assertion) :
    whileStep b c Q {s | wp (.while b c) Q s} = {s | wp (.while b c) Q s} := by
  ext s
  exact wp.while_iff.symm

/-- Least-fixed-point induction: every pre-fixed assertion bounds the total precondition. -/
theorem while_le_of_prefixed (b : BExp) (c : Cmd) (Q : Assertion) (I : Set State)
    (hI : whileStep b c Q I ⊆ I) : {s | wp (.while b c) Q s} ⊆ I := by
  rintro s ⟨t, hrun, hQ⟩
  have hdenote := Denote.iff_bigStep.mpr hrun
  apply Denote.while_ind (P := fun s t => Q t → s ∈ I) ?_ hdenote hQ
  intro s t hstep hpost
  rcases hstep with ⟨hb, rfl⟩ | ⟨hb, m, hc, hm⟩
  · exact hI (Or.inl ⟨hb, hpost⟩)
  · exact hI (Or.inr ⟨hb, m, Denote.iff_bigStep.mp hc, hm hpost⟩)

/-- Total while preconditions are the least fixed points of the guarded transformer. -/
theorem while_eq_lfp (b : BExp) (c : Cmd) (Q : Assertion) :
    {s | wp (.while b c) Q s} = (whileStep b c Q).lfp := by
  apply le_antisymm
  · exact while_le_of_prefixed b c Q _ (whileStep b c Q).map_lfp.le
  · exact (whileStep b c Q).lfp_le (whileStep_wp b c Q).le

/-- For deterministic IMP, total correctness is termination plus liberal correctness. -/
theorem iff_terminates_and_wlp {c : Cmd} {Q : Assertion} {s : State} :
    wp c Q s ↔ (∃ t, BigStep c s t) ∧ wlp c Q s := by
  constructor
  · intro h
    exact ⟨⟨h.choose, h.choose_spec.1⟩, wp.le_wlp h⟩
  · rintro ⟨⟨t, ht⟩, hQ⟩
    exact ⟨t, ht, hQ ht⟩

end Cslib.IMP.wp

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Languages.IMP.TotalPrecondition

namespace Cslib.IMP.TotalPreconditionTests
example (b : BExp) (c : Cmd) (Q : Assertion) :
    {s | wp (.while b c) Q s} = (wp.whileStep b c Q).lfp := wp.while_eq_lfp b c Q

example (c : Cmd) (Q : Assertion) (s : State) :
    wp c Q s ↔ (∃ t, BigStep c s t) ∧ wlp c Q s := wp.iff_terminates_and_wlp

-- Immediate exit has precisely the requested postcondition.
example (Q : Assertion) : (wp.whileStep (.truth false) .skip Q).lfp = {s | Q s} := by
  rw [← wp.while_eq_lfp]
  ext s
  change wp (.while (.truth false) .skip) Q s ↔ Q s
  rw [wp.while_iff]
  simp [BExp.eval]

private def spin : Cmd := .while (.truth true) .skip

private theorem spin_step (Q : Assertion) : wp.whileStep (.truth true) .skip Q = OrderHom.id := by
  ext I s
  simp [wp.whileStep, wp, BigStep.skip_iff, BExp.eval]
  rfl

-- Greatest versus least matters: this loop has every assertion as a fixed point.
example (Q : Assertion) : (wp.whileStep (.truth true) .skip Q).lfp = ∅ := by
  apply le_antisymm ?_ (Set.empty_subset _)
  apply OrderHom.lfp_le
  rw [spin_step]
  exact le_rfl

private theorem spin_no_wp (Q : Assertion) (s : State) : ¬ wp spin Q s := by
  have h := wp.while_le_of_prefixed (.truth true) .skip Q ∅ (by
    rw [spin_step]
    exact le_rfl)
  exact fun hs => h hs

example (s : State) : ¬ ∃ t, BigStep spin s t := by
  rintro ⟨t, ht⟩
  exact spin_no_wp (fun _ => True) s ⟨t, ht, trivial⟩

example (Q : Assertion) (s : State) : wlp spin Q s := by
  intro t ht
  exact False.elim (spin_no_wp (fun _ => True) s ⟨t, ht, trivial⟩)

-- A selected diverging body must not be treated using liberal correctness.
example (Q : Assertion) : (wp.whileStep (.truth true) spin Q).lfp = ∅ := by
  apply le_antisymm ?_ (Set.empty_subset _)
  apply OrderHom.lfp_le
  intro s h
  rcases h with h | ⟨_, hc⟩
  · simp [BExp.eval] at h
  · exact False.elim (spin_no_wp (fun _ => False) s hc)

-- Direct use of leastness bounds terminating executions by a pre-fixed assertion.
example (b : BExp) : {s | wp (.while b .skip) (fun t => t 0 = 7) s} ⊆ {s | s 0 = 7} := by
  apply wp.while_le_of_prefixed
  intro s h
  rcases h with ⟨_, hQ⟩ | ⟨_, hI⟩
  · exact hQ
  · obtain ⟨t, ht, hQ⟩ := hI
    rw [BigStep.skip_iff] at ht
    subst t
    exact hQ

private def countdown : Cmd :=
  .while (.le (.const 1) (.var 0)) (.assign 0 (.sub (.var 0) (.const 1)))

private theorem countdown_total : TValid (fun _ => True) countdown (fun s => s 0 = 0) := by
  apply TValid.consequence (Assertion.entails_refl _) (TValid.whileVariant
    (invariant := fun _ => True) (variant := fun s => s 0) ?_) ?_
  · intro s _ hb
    have hpos : 1 ≤ s 0 := BExp.eval_le_eq_true.mp hb
    refine ⟨Function.update s 0 (s 0 - 1), .assign s 0 _, trivial, ?_⟩
    simp only [Function.update_self]
    omega
  · intro s h
    have hn : ¬ 1 ≤ s 0 := by
      intro hp
      have ht : (BExp.le (.const 1) (.var 0)).eval s = true := BExp.eval_le_eq_true.mpr hp
      rw [h.2] at ht
      contradiction
    omega

example : (wp.whileStep (.le (.const 1) (.var 0))
    (.assign 0 (.sub (.var 0) (.const 1))) (fun s => s 0 = 0)).lfp = Set.univ := by
  rw [← wp.while_eq_lfp]
  ext s
  exact ⟨fun _ => trivial, fun _ => countdown_total (s := s) trivial⟩

-- A concrete multi-iteration run is obtained from the total specification.
example : ∃ t, BigStep countdown (fun _ => 3) t ∧ t 0 = 0 := countdown_total trivial

example : ¬ wp countdown (fun s => s 0 = 1) (fun _ => 3) := by
  intro h
  obtain ⟨t, ht, hz⟩ := countdown_total (s := fun _ => 3) trivial
  have bad := wp.le_wlp h ht
  omega

-- An actual nested-loop run, with both inner and outer feedback exercised.
private def nested : Cmd := .while (.le (.const 1) (.var 0))
  (.seq (.while (.le (.const 1) (.var 1)) (.assign 1 (.const 0))) (.assign 0 (.const 0)))

example : wp nested (fun t => t 0 = 0 ∧ t 1 = 0) (fun _ => 1) := by
  let s : State := fun _ => 1
  let m := Function.update s 1 0
  let t := Function.update m 0 0
  refine ⟨t, ?_, by decide, by decide⟩
  exact .whileTrue (by decide)
    (.seq (.whileTrue (by decide) (.assign s 1 _) (.whileFalse (by decide)))
      (.assign m 0 _)) (.whileFalse (by decide))

example (s : State) : wp .skip (fun t => t = s) s := ⟨s, .skip s, rfl⟩

-- Liberal correctness alone does not establish total correctness.
example (s : State) : ¬ wp spin (fun _ => True) s := spin_no_wp _ _

#print axioms wp.while_eq_lfp
#print axioms wp.while_le_of_prefixed
#print axioms wp.iff_terminates_and_wlp
end Cslib.IMP.TotalPreconditionTests

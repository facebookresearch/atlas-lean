/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.PiCalculus.Contextual

/-!
# Observable π-calculus client regressions

Normal-import tests of free/bound subject visibility, name-passing observers,
scope extrusion, binder capture, guarded choice, and the outputless
obstruction to reduction. None adds a second process semantics.
-/

namespace Cslib.PiCalculus.BehaviouralTests

/-- Waiting input has a barb but cannot reduce and is not inert-equivalent. -/
theorem waiting_input (a : ℕ) (p q : Proc) :
    Barb (.inp (.const a) p) (.input a) ∧
      ¬ Step (.inp (.const a) p) q ∧
      ¬ BarbedBisimilar (.inp (.const a) p) .nil := by
  refine ⟨Barb.of_offer (.input (.refl _)), ?_,
    input_not_barbedBisimilar_nil a p⟩
  exact not_step_of_no_output (by simp [HasUnguardedOutput]) q

/-- A restricted subject is invisible; a restricted object on a free
subject is visible. This distinguishes subject hiding from name passing. -/
theorem bound_vs_free (a : ℕ) (o : Observable) :
    ¬ Barb (.nu (.out (.var 0) (.const a) .nil)) o ∧
      Barb (.nu (.out (.const a) (.var 0) .nil)) (.output a) := by
  simp

/-- The canonical reduction-only LTS misses the waiting-input distinction. -/
theorem reduction_only_misses_input (a : ℕ) :
    LTS.HomBisimilarity
      (⟨fun p (_ : Unit) q => Step p q⟩ : LTS Proc Unit)
      (.inp (.const a) .nil) .nil := by
  refine ⟨fun p q => ¬ HasUnguardedOutput p ∧ ¬ HasUnguardedOutput q,
    ⟨by simp [HasUnguardedOutput], by simp [HasUnguardedOutput]⟩, ?_⟩
  intro p q h _
  exact ⟨fun p' hp => False.elim (h.1 hp.hasUnguardedOutput),
    fun q' hq => False.elim (h.2 hq.hasUnguardedOutput)⟩

/-- A receiver becomes ready on the transmitted free name. -/
theorem free_name_observer (a b : ℕ) :
    MayBarb (.par (.out (.const a) (.const b) .nil)
      (.inp (.const a) (.out (.var 0) (.const 0) .nil))) (.output b) := by
  refine ⟨.par .nil (.out (.const b) (.const 0) .nil),
    Relation.ReflTransGen.single
      (Step.commSelect (Select.refl _) (Select.refl _)), ?_⟩
  exact Barb.of_offer (.parR (.output (.refl _)))

/-- A private name is delivered too, but its received subject remains
hidden by the enclosing restriction. -/
theorem bound_name_observer (a : ℕ) (o : Observable) :
    Step (.nu (.par (.out (.const a) (.var 0) .nil)
      (.inp (.const a) (.out (.var 0) (.const 0) .nil))))
      (.nu (.par .nil (.out (.var 0) (.const 0) .nil))) ∧
    ¬ Barb (.nu (.par .nil (.out (.var 0) (.const 0) .nil))) o := by
  refine ⟨Step.nu (Step.commSelect (Select.refl _) (Select.refl _)), ?_⟩
  have h : Cong (.nu (.par .nil (.out (.var 0) (.const 0) .nil)))
      (.nu (.out (.var 0) (.const 0) .nil)) :=
    Cong.nu_cong ((Cong.par_comm _ _).trans (Cong.par_nil _))
  rw [h.barb_iff]
  simp

/-- Scope extrusion remains equivalent under arbitrary lexical observers. -/
theorem scope_contextual (p q : Proc) :
    ContextualBarbedEquiv (.par (.nu p) q)
      (.nu (.par p (liftProc 0 q))) :=
  (Cong.scope p q).contextualBarbedEquiv

/-- A real outside receiver receives an extruded private name and exposes
a free output subject. The scope law is used by the actual reduction. -/
theorem extrusion_with_receiver (a success : ℕ) :
    MayBarb (.par (.nu (.out (.const a) (.var 0) .nil))
      (.inp (.const a) (.out (.const success) (.var 0) .nil)))
      (.output success) := by
  refine ⟨.nu (.par .nil (.out (.const success) (.var 0) .nil)),
    Relation.ReflTransGen.single ?_, ?_⟩
  · exact Step.cong (Cong.scope _ _)
      (Step.nu (Step.commSelect (Select.refl _) (Select.refl _)))
      (.refl _)
  · exact Barb.of_offer (.nu (.parR (.output (.refl _))))

/-- A parallel observer sees the same successful name-passing behaviour
after a structural rearrangement. This uses reduction-path transfer, not
just equality of immediate barb sets. -/
theorem parallel_observer_transfer (p q observer : Proc)
    (h : Cong p q) (o : Observable)
    (hp : MayBarb (.par p observer) o) :
    MayBarb (.par q observer) o :=
  ((h.contextualBarbedEquiv (.parL .hole observer)).mayBarb_iff o).mp hp

/-- Different transmitted free names give distinguishable received
subjects, even when parallel `nil` is hidden by structural congruence. -/
theorem received_subject_separation :
    ¬ BarbedBisimilar (.par .nil (.out (.const 1) (.const 0) .nil))
      (.par .nil (.out (.const 2) (.const 0) .nil)) := by
  intro h
  have hb := (h.barb_iff (.output 1)).mp
    (Barb.of_offer (.parR (.output (.refl _))))
  have hc : Cong (.par .nil (.out (.const 2) (.const 0) .nil))
      (.out (.const 2) (.const 0) .nil) :=
    (Cong.par_comm _ _).trans (Cong.par_nil _)
  have := (hc.barb_iff _).mp hb
  simp at this

/-- Substitution crosses input and restriction binders without capturing
the transmitted outer name or changing the new innermost bound name. -/
theorem substitution_two_binders :
    subst (.inp (.const 0) (.nu (.out (.var 2) (.var 0) .nil))) (.var 0) =
      .inp (.const 0) (.nu (.out (.var 2) (.var 0) .nil)) := rfl

/-- Capture-avoiding filling shifts dangling hole names through two
context binders. Lexical filling intentionally does not. -/
theorem avoiding_two_binders :
    (Context.nu (.inp (.const 0) .hole)).fillAvoiding
      (.out (.var 0) (.var 1) .nil) =
        .nu (.inp (.const 0) (.out (.var 2) (.var 3) .nil)) := rfl

/-- The raw lexical filler would capture an open hole; its distinction
from the capture-avoiding operation is not an undocumented convention. -/
theorem open_hole_capture_counterexample :
    (Context.nu .hole).fill (.out (.var 0) (.const 0) .nil) ≠
      (Context.nu .hole).fillAvoiding (.out (.var 0) (.const 0) .nil) := by
  decide

/-- A nontrivial closed hole, with its own private binder, remains
structurally sound under capture-avoiding input/restriction contexts. -/
theorem closed_hole_sound :
    BarbedBisimilar
      ((Context.nu (.inp (.const 7) .hole)).fillAvoiding
        (.par (.nu (.out (.var 0) (.const 0) .nil)) .nil))
      ((Context.nu (.inp (.const 7) .hole)).fillAvoiding
        (.nu (.out (.var 0) (.const 0) .nil))) := by
  apply (Cong.par_nil _).fillAvoiding_barbedBisimilar
  · simp [Proc.ClosedAt, Name.ClosedAt]
  · simp [Proc.ClosedAt, Name.ClosedAt]

/-- Replicated input readiness is visible, but replication cannot
manufacture a reduction from a guarded output in its continuation. -/
theorem replicated_input (a : ℕ) (p q : Proc) :
    Barb (.repl (.inp (.const a) p)) (.input a) ∧
      ¬ Step (.repl (.inp (.const a) p)) q := by
  refine ⟨⟨_, Cong.repl_unfold _, .parL (.input (.refl _))⟩, ?_⟩
  exact not_step_of_no_output (by simp [HasUnguardedOutput]) q

/-- A private cyclic pair of waiting inputs cannot reduce, even though
its guarded continuations contain outputs. Structural rearrangement
cannot turn those continuations into active outputs. -/
theorem cyclic_wait_stuck (q : Proc) :
    ¬ Step (.nu (.nu (.par
      (.inp (.var 0) (.out (.var 2) (.const 0) .nil))
      (.inp (.var 1) (.out (.var 1) (.const 0) .nil))))) q :=
  not_step_of_no_output (by simp [HasUnguardedOutput]) q

/-- Restriction swapping is contextually sound, with the de Bruijn swap
specified by the existing Basic semantics. -/
theorem swap_contextual (p : Proc) :
    ContextualBarbedEquiv (.nu (.nu p)) (.nu (.nu (swapProc 0 p))) :=
  (Cong.nu_swap p).contextualBarbedEquiv

/-- A two-communication name-passing run reaches an observer's success
barb. The observer uses the name received by the first input. -/
theorem two_communication_observer :
    MayBarb (.par
      (.par (.out (.const 0) (.const 1) .nil)
        (.inp (.const 0) (.out (.var 0) (.const 2) .nil)))
      (.inp (.const 1) (.out (.const 3) (.const 0) .nil))) (.output 3) := by
  refine ⟨.par .nil (.out (.const 3) (.const 0) .nil),
    (Relation.ReflTransGen.single
      (Step.parL (Step.commSelect (Select.refl _) (Select.refl _)))).tail ?_,
    Barb.of_offer (.parR (.output (.refl _)))⟩
  exact Step.cong
    (Cong.par_cong ((Cong.par_comm _ _).trans (Cong.par_nil _)) (.refl _))
    (Step.commSelect (Select.refl _) (Select.refl _)) (.refl _)

/-- Swapping the communicating pair in that concrete observer run
preserves the eventual free success subject. -/
theorem swapped_communication_observer :
    MayBarb (.par
      (.par (.inp (.const 0) (.out (.var 0) (.const 2) .nil))
        (.out (.const 0) (.const 1) .nil))
      (.inp (.const 1) (.out (.const 3) (.const 0) .nil))) (.output 3) :=
  parallel_observer_transfer _ _ _ (Cong.par_comm _ _) _
    two_communication_observer

/-- Nested guarded choice exposes the selected output and communicates
with a free input, without prematurely reducing either sum alone. -/
theorem guarded_choice_observer (a success : ℕ) :
    MayBarb (.par
      (.sum (.sum (.out (.const a) (.const 0) .nil) .nil) .nil)
      (.inp (.const a) (.out (.const success) (.const 0) .nil)))
      (.output success) := by
  refine ⟨.par .nil (.out (.const success) (.const 0) .nil),
    Relation.ReflTransGen.single ?_,
    Barb.of_offer (.parR (.output (.refl _)))⟩
  exact Step.commSelect
    (Select.trans (Select.left _ _) (Select.left _ _)) (Select.refl _)

/-- Standalone waiting inputs cannot inspect their continuations. This
positive non-structural bisimulation probe is deliberately not advertised
as a context law: an external sender can activate the continuations. -/
theorem waiting_continuations (a : ℕ) (p q : Proc) :
    BarbedBisimilar (.inp (.const a) p) (.inp (.const a) q) := by
  refine ⟨fun s t => s = .inp (.const a) p ∧ t = .inp (.const a) q,
    ⟨rfl, rfl⟩, (isBisimulation_observedLTS_iff _).mpr ?_⟩
  rintro s t ⟨rfl, rfl⟩
  refine ⟨fun s' hs => ?_, fun t' ht => ?_, ?_⟩
  · exact False.elim
      (not_step_of_no_output (by simp [HasUnguardedOutput]) s' hs)
  · exact False.elim
      (not_step_of_no_output (by simp [HasUnguardedOutput]) t' ht)
  · intro o
    simp

end Cslib.PiCalculus.BehaviouralTests

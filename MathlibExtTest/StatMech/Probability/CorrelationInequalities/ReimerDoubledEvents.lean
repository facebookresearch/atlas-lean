/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDoubledEvents

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerEndpointProve`

* `leftCfg`, `rightCfg` computed on `ConfigSpace (Fin 1 ⊕ Fin 1)`; `doubleWeight` evaluated;
* `reimer_wprob_doubled_split` for the doubled uniform weight and the events "the left copy is
  open" and "the right copy is closed";
* `wprob_familyEvent_boxDoubled_eq_wdpairs` for `famA = {∅, {0}}`, `famB = {∅, {1}}` on `Fin 2`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerEndpointProve

open _root_.StatMech
open scoped FinsetFamily

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

/-- The uniform coordinate weight on `Fin 2`. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- `leftCfg` and `rightCfg` read the two copies.
example : leftCfg (Sum.elim (fun _ : Fin 1 => true) (fun _ => false)) = (fun _ => true) ∧
    rightCfg (Sum.elim (fun _ : Fin 1 => true) (fun _ => false)) = (fun _ => false) :=
  ⟨rfl, rfl⟩

-- `doubleWeight` uses `w` on both copies.
example : doubleWeight half (Sum.inr 1) true = 1 / 2 := rfl

-- Reimer with equality for a left event and a right event.
example : wprob (doubleWeight half)
      (disjointOccurrence (leftEvent {ω | ω 0 = true}) (rightEvent {ω | ω 1 = false}))
    = wprob (doubleWeight half) (leftEvent {ω | ω 0 = true})
      * wprob (doubleWeight half) (rightEvent {ω | ω 1 = false}) :=
  reimer_wprob_doubled_split _ (fun x => by cases x <;> norm_num [doubleWeight, half]) _ _

-- The weighted disjoint-pair count is the probability of the doubled family event.
example : wprob (doubleWeight half) (familyEvent (boxDoubled famA famB)) = wdpairs half famA famB :=
  wprob_familyEvent_boxDoubled_eq_wdpairs _ _ _

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerEndpointProve

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Classes

/-!
# Running two single-tape machines one after the other

CSLib's `SingleTapeTM.compComputer tm1 tm2` runs `tm1` and, when it halts, starts `tm2` on the
tape `tm1` left. Upstream proves its correctness only inside `TimeComputable.comp`, for total
functions with time bounds, through private lemmas. This file states the facts for single runs,
which is what a composition with a possibly non-halting second machine needs:

* `Outputs.compComputer`, `OutputsWithinTime.compComputer`: outputs compose (time bounds add).
* `haltsOn_compComputer_iff`: if `tm1` outputs `b` on `a`, the composite halts on `a` iff `tm2`
  halts on `b`.

The proofs embed the two machines' configurations into the composite (`compCfgLeft`,
`compCfgRight`, public versions of upstream's private `toCompCfg_left` / `toCompCfg_right`) and
use that machines are deterministic (`rightUnique_transitionRelation`).

## Main results

- `Cslib.Turing.SingleTapeTM.Outputs.compComputer`,
  `Cslib.Turing.SingleTapeTM.OutputsWithinTime.compComputer`,
  `Cslib.Turing.SingleTapeTM.haltsOn_compComputer_iff`.
-/

@[expose] public section

set_option autoImplicit false

open Relation

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm1 tm2 : SingleTapeTM Symbol)

/-- A configuration of the first machine as one of the composite: a halted first machine is the
second machine at its start state. (Upstream's private `toCompCfg_left`.) -/
def compCfgLeft (c : tm1.Cfg) : (compComputer tm1 tm2).Cfg :=
  ⟨some (c.state.elim (.inr tm2.q₀) .inl), c.BiTape⟩

/-- A configuration of the second machine as one of the composite. (Upstream's private
`toCompCfg_right`.) -/
def compCfgRight (c : tm2.Cfg) : (compComputer tm1 tm2).Cfg :=
  ⟨c.state.map .inr, c.BiTape⟩

variable {tm1 tm2}

/-- A step of the first machine is a step of the composite (upstream's private
`map_toCompCfg_left_step`, as a relation). -/
theorem transitionRelation_compCfgLeft {c c' : tm1.Cfg} (h : tm1.TransitionRelation c c') :
    (compComputer tm1 tm2).TransitionRelation (compCfgLeft tm1 tm2 c) (compCfgLeft tm1 tm2 c') := by
  obtain ⟨s, t⟩ := c
  cases s with
  | none => simp [TransitionRelation, step] at h
  | some q =>
    simp only [TransitionRelation, step] at h
    generalize hM : tm1.tr q t.head = r at h
    obtain ⟨⟨wr, dir⟩, q'⟩ := r
    obtain rfl := Option.some_injective _ h
    simp only [TransitionRelation, step, compCfgLeft, Option.elim_some, compComputer, hM]
    cases q' <;> rfl

/-- The composite steps from a configuration of the second machine as the second machine does
(upstream's private `map_toCompCfg_right_step`). -/
theorem step_compCfgRight (c : tm2.Cfg) :
    (compComputer tm1 tm2).step (compCfgRight tm1 tm2 c) =
      (tm2.step c).map (compCfgRight tm1 tm2) := by
  obtain ⟨s, t⟩ := c
  cases s with
  | none => rfl
  | some q =>
    rcases hM : tm2.tr q t.head with ⟨stmt, q'⟩
    have e : compCfgRight tm1 tm2 ⟨some q, t⟩ = ⟨some (.inr q), t⟩ := rfl
    rw [e]
    cases q' <;> simp only [step, compComputer, hM, Option.map_some] <;> rfl

/-- A step of the second machine is a step of the composite. -/
theorem transitionRelation_compCfgRight {c c' : tm2.Cfg} (h : tm2.TransitionRelation c c') :
    (compComputer tm1 tm2).TransitionRelation (compCfgRight tm1 tm2 c)
      (compCfgRight tm1 tm2 c') := by
  simp only [TransitionRelation, step_compCfgRight] at h ⊢
  rw [h, Option.map_some]

/-- Runs of the composite from a configuration of the second machine are runs of the second
machine. -/
theorem exists_of_reflTransGen_compCfgRight {c : tm2.Cfg} {d : (compComputer tm1 tm2).Cfg}
    (h : ReflTransGen (compComputer tm1 tm2).TransitionRelation (compCfgRight tm1 tm2 c) d) :
    ∃ c', ReflTransGen tm2.TransitionRelation c c' ∧ d = compCfgRight tm1 tm2 c' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨c', hc', rfl⟩ := ih
    simp only [TransitionRelation, step_compCfgRight] at hstep
    obtain ⟨c'', hc'', rfl⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨c'', hc'.tail hc'', rfl⟩

/-- **Outputs compose**: if `tm1` outputs `b` on `a` and `tm2` outputs `c` on `b`, the composite
outputs `c` on `a`. -/
theorem Outputs.compComputer {a b c : List Symbol} (h₁ : tm1.Outputs a b)
    (h₂ : tm2.Outputs b c) : (compComputer tm1 tm2).Outputs a c :=
  (h₁.lift (compCfgLeft tm1 tm2) fun _ _ ↦ transitionRelation_compCfgLeft).trans
    (h₂.lift (compCfgRight tm1 tm2) fun _ _ ↦ transitionRelation_compCfgRight)

/-- **Timed outputs compose**, with the time bounds added. -/
theorem OutputsWithinTime.compComputer {a b c : List Symbol} {t₁ t₂ : ℕ}
    (h₁ : tm1.OutputsWithinTime a b t₁) (h₂ : tm2.OutputsWithinTime b c t₂) :
    (compComputer tm1 tm2).OutputsWithinTime a c (t₁ + t₂) :=
  (h₁.map (compCfgLeft tm1 tm2) fun _ _ ↦ transitionRelation_compCfgLeft).trans
    (h₂.map (compCfgRight tm1 tm2) fun _ _ ↦ transitionRelation_compCfgRight)

/-- **Halting of a composite**: if `tm1` outputs `b` on `a`, the composite halts on `a` exactly
when `tm2` halts on `b`. -/
theorem haltsOn_compComputer_iff {a b : List Symbol} (h₁ : tm1.Outputs a b) :
    (compComputer tm1 tm2).HaltsOn a ↔ tm2.HaltsOn b := by
  have hmid : ReflTransGen (compComputer tm1 tm2).TransitionRelation
      ((compComputer tm1 tm2).initCfg a) (compCfgRight tm1 tm2 (tm2.initCfg b)) :=
    h₁.lift (compCfgLeft tm1 tm2) fun _ _ ↦ transitionRelation_compCfgLeft
  constructor
  · rintro ⟨d, hd, hstate⟩
    rcases hmid.total_of_right_unique (rightUnique_transitionRelation _) hd with h | h
    · obtain ⟨c', hc', rfl⟩ := exists_of_reflTransGen_compCfgRight h
      refine ⟨c', hc', ?_⟩
      exact Option.map_eq_none_iff.mp hstate
    · -- a halted configuration has no successor, so it is the middle one, which is running
      rcases h.cases_head with h | ⟨e, he, -⟩
      · rw [h] at hstate
        have e : (compCfgRight tm1 tm2 (tm2.initCfg b)).state = some (.inr tm2.q₀) := rfl
        rw [e] at hstate
        cases hstate
      · obtain ⟨s, t⟩ := d
        simp only at hstate
        subst hstate
        simp [TransitionRelation, step] at he
  · rintro ⟨c', hc', hstate⟩
    refine ⟨compCfgRight tm1 tm2 c', hmid.trans (hc'.lift (compCfgRight tm1 tm2) fun _ _ ↦
      transitionRelation_compCfgRight), ?_⟩
    change Option.map _ c'.state = none
    rw [hstate]
    rfl

end Cslib.Turing.SingleTapeTM

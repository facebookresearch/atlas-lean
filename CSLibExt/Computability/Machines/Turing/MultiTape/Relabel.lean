/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeSpace

/-!
# State relabelling of multi-tape machines

A machine `tm'` simulates `tm` up to the state relabelling `f : State → State'`
(`IsRelabelling f tm tm'`) when it starts in `f tm.q₀` and, in every relabelled state `f q`, takes
the action `tm` takes in `q` with the successor state relabelled by `f`. Nothing is assumed about
the states of `tm'` outside the range of `f`, and `f` need not be injective.

Such a `tm'` runs in lockstep with `tm`: its run from a relabelled configuration is the relabelled
run of `tm` (`IsRelabelling.runFrom`). Relabelling keeps the input head, the work tapes, the work
heads, the output and whether the machine has halted, so the two machines compute the same outputs
within the same time and space bounds (`IsRelabelling.computes_iff`, `runsInTime_iff`,
`runsInSpace_iff`, `computesFunInTimeAndSpace_iff`, `decides_iff`).

Space is CSLib's path-based `MultiTapeNTM.RunsInSpace`; for a deterministic machine it is a bound
on `MultiTapeTM.spaceUsed` along the run (`runsInSpace_iff_forall_spaceUsed_le`).

## Main definitions

- `Cslib.Turing.MultiTapeTM.relabelAction`: an action with its successor state relabelled.
- `Cslib.Turing.MultiTapeTM.IsRelabelling`: simulation up to a state relabelling.

## Main results

- `runsInSpace_iff_forall_spaceUsed_le`: deterministic space bounds are bounds on `spaceUsed`.
- `IsRelabelling.runFrom`, `IsRelabelling.runFrom_initCfg`: lockstep runs.
- `IsRelabelling.computes_iff`, `runsInTime_iff`, `runsInSpace_iff`,
  `computesFunInTimeAndSpace_iff`, `decides_iff`, `timeBoundedBy_iff`, `spaceBoundedBy_iff`:
  relabelling preserves outputs and resource bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ} {Symbol State State' : Type*} {input : List Symbol}

/-! ### Space of deterministic runs -/

/-- The space of the canonical computation path of `t` steps is the space used by the run. -/
theorem space_ofDeterministic (tm : MultiTapeTM k Symbol State) (x : List Symbol) (t : ℕ) :
    (MultiTapeNTM.ComputationPath.ofDeterministic tm x t).space =
      tm.spaceUsed (tm.initCfg x) t :=
  rfl

/-- For a deterministic machine, running in space `s` on `x` means using at most `s` work-tape
cells within every number of steps. -/
theorem runsInSpace_iff_forall_spaceUsed_le {tm : MultiTapeTM k Symbol State} {x : List Symbol}
    {s : ℕ} : tm.RunsInSpace x s ↔ ∀ t, tm.spaceUsed (tm.initCfg x) t ≤ s := by
  refine ⟨fun h t ↦ ?_, fun h p ↦ ?_⟩
  · rw [← space_ofDeterministic]
    exact h _
  · rw [p.eq_ofDeterministic, space_ofDeterministic]
    exact h _

/-! ### Relabelling -/

/-- The action `a` with its successor state relabelled by `f`. -/
def relabelAction (f : State → State') (a : Action k Symbol State) : Action k Symbol State' :=
  ⟨a.inputTape, a.workTapes, a.output, a.state.map f⟩

@[simp]
theorem relabelAction_id (a : Action k Symbol State) : relabelAction id a = a := by
  cases a; simp [relabelAction]

/-- Applying a relabelled action to a relabelled configuration relabels the result. -/
theorem apply_relabelAction (f : State → State') (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (relabelAction f a).apply (cfg.mapState (Option.map f)) =
      (a.apply cfg).mapState (Option.map f) :=
  rfl

/-- `tm'` simulates `tm` up to the state relabelling `f`: it starts in the relabelled initial
state, and in a relabelled state `f q` it takes the action of `tm` in `q`, with the successor
state relabelled. -/
structure IsRelabelling (f : State → State') (tm : MultiTapeTM k Symbol State)
    (tm' : MultiTapeTM k Symbol State') : Prop where
  /-- The initial state is relabelled. -/
  q₀ : tm'.q₀ = f tm.q₀
  /-- Transitions commute with the relabelling. -/
  tr : ∀ q a w, tm'.tr (f q) a w = relabelAction f (tm.tr q a w)

/-- Relabelling a configuration keeps it halted or running. -/
@[simp]
theorem halted_mapState_iff (f : State → State') (cfg : Cfg k Symbol State input) :
    (cfg.mapState (Option.map f)).Halted ↔ cfg.Halted := by
  simp [Cfg.Halted]

namespace IsRelabelling

variable {f : State → State'} {tm : MultiTapeTM k Symbol State}
  {tm' : MultiTapeTM k Symbol State'}

/-- Every machine simulates itself under the identity. -/
theorem refl (tm : MultiTapeTM k Symbol State) : IsRelabelling id tm tm where
  q₀ := rfl
  tr _ _ _ := (relabelAction_id _).symm

/-- Relabellings compose. -/
theorem trans {State'' : Type*} {g : State' → State''} {tm'' : MultiTapeTM k Symbol State''}
    (h : IsRelabelling f tm tm') (h' : IsRelabelling g tm' tm'') :
    IsRelabelling (g ∘ f) tm tm'' where
  q₀ := by rw [h'.q₀, h.q₀]; rfl
  tr q a w := by
    rw [Function.comp_apply, h'.tr, h.tr]
    simp [relabelAction, Option.map_map]

/-- One step of `tm'` from a relabelled configuration is the relabelled step of `tm`. -/
theorem step (h : IsRelabelling f tm tm') (cfg : Cfg k Symbol State input) :
    tm'.step (cfg.mapState (Option.map f)) = (tm.step cfg).mapState (Option.map f) := by
  cases hq : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt (by simp [hq])]
  | some q =>
    rw [MultiTapeTM.step_of_state hq, MultiTapeTM.step_of_state (q := f q) (by simp [hq])]
    exact (congrArg (fun a ↦ Action.apply a _) (h.tr q _ _)).trans (apply_relabelAction f _ cfg)

/-- **Lockstep runs.** The run of `tm'` from a relabelled configuration is the relabelled run of
`tm`. -/
theorem runFrom (h : IsRelabelling f tm tm') (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm'.runFrom (cfg.mapState (Option.map f)) t = (tm.runFrom cfg t).mapState (Option.map f) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ, MultiTapeTM.runFrom_succ, ih, h.step]

/-- The initial configuration of `tm'` is the relabelled initial configuration of `tm`. -/
theorem initCfg (h : IsRelabelling f tm tm') (x : List Symbol) :
    tm'.initCfg x = (tm.initCfg x).mapState (Option.map f) := by
  simp [MultiTapeNTM.initCfg, Cfg.mapState, h.q₀]

/-- The run of `tm'` on `x` is the relabelled run of `tm`. -/
theorem runFrom_initCfg (h : IsRelabelling f tm tm') (x : List Symbol) (t : ℕ) :
    tm'.runFrom (tm'.initCfg x) t = (tm.runFrom (tm.initCfg x) t).mapState (Option.map f) := by
  rw [h.initCfg, h.runFrom]

theorem halted_runFrom_iff (h : IsRelabelling f tm tm') (x : List Symbol) (t : ℕ) :
    (tm'.runFrom (tm'.initCfg x) t).Halted ↔ (tm.runFrom (tm.initCfg x) t).Halted := by
  rw [h.runFrom_initCfg, halted_mapState_iff]

theorem output_runFrom (h : IsRelabelling f tm tm') (x : List Symbol) (t : ℕ) :
    (tm'.runFrom (tm'.initCfg x) t).output = (tm.runFrom (tm.initCfg x) t).output := by
  rw [h.runFrom_initCfg]
  rfl

theorem spaceUsed_initCfg (h : IsRelabelling f tm tm') (x : List Symbol) (t : ℕ) :
    tm'.spaceUsed (tm'.initCfg x) t = tm.spaceUsed (tm.initCfg x) t := by
  simp only [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead,
    h.runFrom_initCfg, Cfg.mapState_workTapePos]

/-- Relabelling preserves outputs. -/
theorem computes_iff (h : IsRelabelling f tm tm') {x o : List Symbol} :
    tm'.Computes x o ↔ tm.Computes x o := by
  simp only [MultiTapeTM.Computes, h.halted_runFrom_iff, h.output_runFrom]

/-- Relabelling preserves time bounds. -/
theorem runsInTime_iff (h : IsRelabelling f tm tm') {x : List Symbol} {t : ℕ} :
    tm'.RunsInTime x t ↔ tm.RunsInTime x t := by
  rw [runsInTime_iff_halted, runsInTime_iff_halted, h.halted_runFrom_iff]

/-- Relabelling preserves space bounds. -/
theorem runsInSpace_iff (h : IsRelabelling f tm tm') {x : List Symbol} {s : ℕ} :
    tm'.RunsInSpace x s ↔ tm.RunsInSpace x s := by
  simp only [runsInSpace_iff_forall_spaceUsed_le, h.spaceUsed_initCfg]

/-- Relabelling preserves function computation within time and space bounds. -/
theorem computesFunInTimeAndSpace_iff (h : IsRelabelling f tm tm') {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {g : α → β} {t s : α → ℕ} :
    tm'.ComputesFunInTimeAndSpace encIn encOut g t s ↔
      tm.ComputesFunInTimeAndSpace encIn encOut g t s := by
  simp only [MultiTapeTM.ComputesFunInTimeAndSpace, MultiTapeTM.ComputesInTimeAndSpace,
    h.computes_iff, h.runsInTime_iff, h.runsInSpace_iff]

theorem timeBoundedBy_iff (h : IsRelabelling f tm tm') {t : ℕ → ℕ} :
    TimeBoundedBy tm' t ↔ TimeBoundedBy tm t := by
  simp only [TimeBoundedBy, h.runsInTime_iff]

theorem spaceBoundedBy_iff (h : IsRelabelling f tm tm') {s : ℕ → ℕ} :
    SpaceBoundedBy tm' s ↔ SpaceBoundedBy tm s := by
  simp only [SpaceBoundedBy, h.runsInSpace_iff]

/-- Relabelling preserves deciding a language. -/
theorem decides_iff {tm : MultiTapeTM k Bool State} {tm' : MultiTapeTM k Bool State'}
    (h : IsRelabelling f tm tm') {L : Set (List Bool)} : Decides tm' L ↔ Decides tm L := by
  simp only [Decides, h.computes_iff]

end IsRelabelling

end Cslib.Turing.MultiTapeTM

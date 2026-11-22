/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Code
public import CSLibExt.Computability.Machines.Turing.MultiTape.Relabel
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Codes are complete for finite-state binary machines

Codes (`Code k`, MT1) and binary multi-tape machines with finitely many states describe the same
computations:

- **Codes give finite-state machines.** The machine of a code, `Code.toTM c`, has states in `ℕ`,
  but only the finitely many states `c.states` occur (`Code.state_runFrom_mem_states`). Restricting
  it to `Fin c.stateBound` gives `Code.toFinTM c`, a machine of CSLib's model with finitely many
  states, which `c.toTM` simulates up to the relabelling `Fin.val`
  (`Code.isRelabelling_toFinTM`). So every resource bound met by a code is met by a machine of the
  kind `MultiTapeTM.ComputableInTimeAndSpace` and `MultiTapeTM.DecidableInTimeAndSpace` quantify
  over (`Code.computableInTimeAndSpace`, `Code.decidableInTimeAndSpace`).
- **Every finite-state machine has a code.** For a machine `tm : MultiTapeTM k Bool State` with
  finitely many states and an injective numbering `e` of its states sending the initial state to
  `0`, the code `Code.ofTM tm e` tabulates the transition function of `tm`, and its machine
  simulates `tm` up to the relabelling `e` (`Code.isRelabelling_ofTM`); such a numbering always
  exists (`Code.exists_code_isRelabelling`).

Relabelling preserves outputs, time and space (`IsRelabelling.computes_iff` and its siblings), so
the classes of CSLib's model, and `DTIME`/`DSPACE`, can be stated equivalently over codes
(`computableInTimeAndSpace_iff_exists_code`, `decidableInTimeAndSpace_iff_exists_code`,
`mem_DTIME_iff_exists_code`, `mem_DSPACE_iff_exists_code`). This is what a diagonal argument
over codes needs; the universal machine that runs codes is a separate item
(`CSLibExt/BACKLOG.md`, MT3).

## Main definitions

- `Cslib.Turing.MultiTapeTM.Code.stateBound`, `Code.toFinTM`: the finite-state machine of a code.
- `Cslib.Turing.MultiTapeTM.encodeMove`, `encodeAction`: actions as coded actions.
- `Cslib.Turing.MultiTapeTM.Code.ofTM`: the code of a finite-state binary machine.

## Main results

- `Code.isRelabelling_toFinTM`: a code's machine simulates its finite-state machine.
- `Code.isRelabelling_ofTM`, `Code.exists_code_isRelabelling`: every finite-state binary machine is
  simulated by the machine of a code, up to an injective state relabelling.
- `Code.computableInTimeAndSpace`, `Code.decidableInTimeAndSpace`: codes land in CSLib's classes.
- `computableInTimeAndSpace_iff_exists_code`, `decidableInTimeAndSpace_iff_exists_code`,
  `mem_DTIME_iff_exists_code`, `mem_DSPACE_iff_exists_code`: the classes over codes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ}

/-! ### Coding actions -/

/-- Code a head move as a number, inverting `decodeMove`: left is `0`, stay is `1`, right is
`2`. -/
def encodeMove : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

@[simp]
theorem decodeMove_encodeMove (m : SignType) : decodeMove (encodeMove m) = m := by
  cases m <;> rfl

/-- Code an action of a binary machine, numbering its successor state by `e`. -/
def encodeAction {State : Type*} (e : State → ℕ) (a : Action k Bool State) : CodeAction k where
  inputMove := encodeMove a.inputTape
  work i := ((a.workTapes i).1, encodeMove (a.workTapes i).2)
  out := a.output
  next := a.state.map e

/-- A coded action stands for the action it codes, with its successor state numbered. -/
theorem toAction_encodeAction {State : Type*} (e : State → ℕ) (a : Action k Bool State) :
    (encodeAction e a).toAction = relabelAction e a := by
  cases a
  simp [encodeAction, CodeAction.toAction, relabelAction]

namespace Code

/-! ### The finite-state machine of a code -/

/-- A strict upper bound on the states of a code. -/
def stateBound (c : Code k) : ℕ := c.states.sup id + 1

theorem lt_stateBound (c : Code k) {q : ℕ} (h : q ∈ c.states) : q < c.stateBound :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) h)

theorem zero_lt_stateBound (c : Code k) : 0 < c.stateBound := Nat.succ_pos _

/-- A number as a state below `N`, if it is one. -/
def finState (N q : ℕ) : Option (Fin N) := if h : q < N then some ⟨q, h⟩ else none

/-- The transition function of a code on the states below `c.stateBound`. -/
def finTr (c : Code k) (q : Fin c.stateBound) (a : Option Bool) (w : Fin k → Option Bool) :
    Action k Bool (Fin c.stateBound) :=
  ⟨(c.tr q a w).inputTape, (c.tr q a w).workTapes, (c.tr q a w).output,
    (c.tr q a w).state.bind (finState c.stateBound)⟩

/-- **The finite-state machine of a code**: the machine of `c` with its states restricted to
`Fin c.stateBound`. -/
noncomputable def toFinTM (c : Code k) : MultiTapeTM k Bool (Fin c.stateBound) :=
  MultiTapeTM.ofTr ⟨0, c.zero_lt_stateBound⟩ c.finTr

/-- The machine of a code simulates its finite-state machine up to the relabelling `Fin.val`. -/
theorem isRelabelling_toFinTM (c : Code k) : IsRelabelling Fin.val c.toFinTM c.toTM where
  q₀ := rfl
  tr q a w := by
    rw [toTM, MultiTapeTM.tr_ofTr, toFinTM, MultiTapeTM.tr_ofTr]
    have hs : ((c.tr q a w).state.bind (finState c.stateBound)).map Fin.val =
        (c.tr q a w).state := by
      cases hq : (c.tr q a w).state with
      | none => rfl
      | some q' =>
        have hq' : q' ∈ c.states := c.next_act_mem_states hq
        simp [finState, c.lt_stateBound hq']
    simp only [finTr, relabelAction, hs]

/-- **Codes land in CSLib's classes.** A function computed by the machine of a code within some
time and space bounds is computable within them by a binary machine with finitely many states. -/
theorem computableInTimeAndSpace {α β : Type*} {g : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : α → ℕ} (c : Code k)
    (h : c.toTM.ComputesFunInTimeAndSpace encIn encOut g t s) :
    MultiTapeTM.ComputableInTimeAndSpace g encIn encOut t s :=
  ⟨k, Fin c.stateBound, inferInstance, c.toFinTM,
    c.isRelabelling_toFinTM.computesFunInTimeAndSpace_iff.mp h⟩

/-- **Codes land in `DecidableInTimeAndSpace`.** A language decided by the machine of a code
within some time and space bounds is decidable within them. -/
theorem decidableInTimeAndSpace {L : Set (List Bool)} {t s : List Bool → ℕ} (c : Code k)
    (hd : Decides c.toTM L) (ht : ∀ w, c.toTM.RunsInTime w (t w))
    (hs : ∀ w, c.toTM.RunsInSpace w (s w)) :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _) t s :=
  decidableInTimeAndSpace_iff.mpr ⟨k, Fin c.stateBound, inferInstance, c.toFinTM,
    c.isRelabelling_toFinTM.decides_iff.mp hd,
    fun w ↦ c.isRelabelling_toFinTM.runsInTime_iff.mp (ht w),
    fun w ↦ c.isRelabelling_toFinTM.runsInSpace_iff.mp (hs w)⟩

/-! ### The code of a finite-state machine -/

private theorem lookup_map_of_injective {ι κ β : Type*} [DecidableEq κ] {g : ι → κ}
    (hg : Function.Injective g) (v : ι → β) :
    ∀ {l : List ι} {x : ι}, x ∈ l →
      (l.map fun y ↦ (g y, v y)).lookup (g x) = some (v x)
  | [], _, hx => absurd hx List.not_mem_nil
  | y :: l, x, hx => by
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hne : (g x == g y) = false := by simpa using hg.ne hxy
      rw [List.map_cons, List.lookup, hne]
      exact lookup_map_of_injective hg v (List.mem_of_ne_of_mem hxy hx)

/-- **The code of a finite-state binary machine**: its transition table over all states and
symbols under the heads, with states numbered by `e`. It denotes `tm` when `e` is injective and
sends the initial state to `0` (`isRelabelling_ofTM`). -/
noncomputable def ofTM {State : Type*} [Fintype State] (tm : MultiTapeTM k Bool State)
    (e : State → ℕ) : Code k :=
  ⟨(Finset.univ : Finset (State × Option Bool × (Fin k → Option Bool))).toList.map
    fun x ↦ ((e x.1, x.2.1, x.2.2), encodeAction e (tm.tr x.1 x.2.1 x.2.2))⟩

/-- Under an injective numbering, the code of `tm` takes the coded action of `tm`. -/
theorem act_ofTM {State : Type*} [Fintype State] (tm : MultiTapeTM k Bool State) {e : State → ℕ}
    (he : Function.Injective e) (q : State) (a : Option Bool) (w : Fin k → Option Bool) :
    (ofTM tm e).act (e q) a w = encodeAction e (tm.tr q a w) := by
  have hg : Function.Injective fun x : State × Option Bool × (Fin k → Option Bool) ↦
      ((e x.1, x.2.1, x.2.2) : CodeKey k) := by
    rintro ⟨q₁, a₁, w₁⟩ ⟨q₂, a₂, w₂⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, rfl, rfl⟩ := h
    rw [he h₁]
  unfold act ofTM
  rw [lookup_map_of_injective hg (fun x ↦ encodeAction e (tm.tr x.1 x.2.1 x.2.2))
    (x := (q, a, w)) (Finset.mem_toList.mpr (Finset.mem_univ _))]
  rfl

/-- **The code of a machine simulates it.** For an injective numbering `e` of the states of `tm`
with `e tm.q₀ = 0`, the machine of `ofTM tm e` simulates `tm` up to the relabelling `e`. -/
theorem isRelabelling_ofTM {State : Type*} [Fintype State] (tm : MultiTapeTM k Bool State)
    {e : State → ℕ} (he : Function.Injective e) (h₀ : e tm.q₀ = 0) :
    IsRelabelling e tm (ofTM tm e).toTM where
  q₀ := h₀.symm
  tr q a w := by
    rw [toTM, MultiTapeTM.tr_ofTr, tr, act_ofTM tm he, toAction_encodeAction]

/-- A finite type has an injective numbering by `ℕ` sending a chosen element to `0`. -/
theorem exists_injective_nat_eq_zero {State : Type*} [Finite State] (q₀ : State) :
    ∃ e : State → ℕ, Function.Injective e ∧ e q₀ = 0 := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin State
  refine ⟨fun q ↦ Equiv.swap ((σ q₀ : Fin n) : ℕ) 0 (σ q), ?_, Equiv.swap_apply_left _ _⟩
  exact (Equiv.injective _).comp (Fin.val_injective.comp σ.injective)

/-- **Every finite-state machine has a code.** A binary machine with finitely many states is
simulated, up to an injective state relabelling, by the machine of some code. -/
theorem exists_code_isRelabelling {State : Type*} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ (c : Code k) (e : State → ℕ), Function.Injective e ∧ IsRelabelling e tm c.toTM := by
  have := Fintype.ofFinite State
  obtain ⟨e, he, h₀⟩ := exists_injective_nat_eq_zero tm.q₀
  exact ⟨ofTM tm e, e, he, isRelabelling_ofTM tm he h₀⟩

end Code

/-! ### The classes over codes -/

/-- **Computability over codes.** A function is computable within some time and space bounds by
a binary machine with finitely many states iff it is computed within them by the machine of a
code. -/
theorem computableInTimeAndSpace_iff_exists_code {α β : Type*} {g : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ} :
    MultiTapeTM.ComputableInTimeAndSpace g encIn encOut t s ↔
      ∃ (k : ℕ) (c : Code k), c.toTM.ComputesFunInTimeAndSpace encIn encOut g t s := by
  constructor
  · rintro ⟨k, State, _, tm, h⟩
    obtain ⟨c, e, -, he⟩ := Code.exists_code_isRelabelling tm
    exact ⟨k, c, he.computesFunInTimeAndSpace_iff.mpr h⟩
  · rintro ⟨k, c, h⟩
    exact c.computableInTimeAndSpace h

/-- **Decidability over codes.** A language over `Bool` is decidable within some time and space
bounds iff the machine of some code decides it within them. -/
theorem decidableInTimeAndSpace_iff_exists_code {L : Set (List Bool)} {t s : List Bool → ℕ} :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _) t s ↔
      ∃ (k : ℕ) (c : Code k), Decides c.toTM L ∧ (∀ w, c.toTM.RunsInTime w (t w)) ∧
        ∀ w, c.toTM.RunsInSpace w (s w) := by
  rw [decidableInTimeAndSpace_iff]
  constructor
  · rintro ⟨k, State, _, tm, hd, ht, hs⟩
    obtain ⟨c, e, -, he⟩ := Code.exists_code_isRelabelling tm
    exact ⟨k, c, he.decides_iff.mpr hd, fun w ↦ he.runsInTime_iff.mpr (ht w),
      fun w ↦ he.runsInSpace_iff.mpr (hs w)⟩
  · rintro ⟨k, c, hd, ht, hs⟩
    exact decidableInTimeAndSpace_iff.mp (c.decidableInTimeAndSpace hd ht hs)

/-- `DTIME` over codes. -/
theorem mem_DTIME_iff_exists_code {t : ℕ → ℕ} {L : Set (List Bool)} :
    L ∈ DTIME t ↔ ∃ (c₁ c₂ k : ℕ) (c : Code k), Decides c.toTM L ∧
      TimeBoundedBy c.toTM (fun n ↦ c₁ * t n + c₂) ∧ ∃ s, SpaceBoundedBy c.toTM s := by
  constructor
  · rintro ⟨c₁, c₂, s, h⟩
    obtain ⟨k, c, hd, ht, hs⟩ := decidableInTimeAndSpace_iff_exists_code.mp h
    exact ⟨c₁, c₂, k, c, hd, ht, _, hs⟩
  · rintro ⟨c₁, c₂, k, c, hd, ht, s, hs⟩
    exact ⟨c₁, c₂, s, c.decidableInTimeAndSpace hd ht hs⟩

/-- `DSPACE` over codes. -/
theorem mem_DSPACE_iff_exists_code {s : ℕ → ℕ} {L : Set (List Bool)} :
    L ∈ DSPACE s ↔ ∃ (c₁ c₂ k : ℕ) (c : Code k), Decides c.toTM L ∧
      SpaceBoundedBy c.toTM (fun n ↦ c₁ * s n + c₂) ∧ ∃ t, TimeBoundedBy c.toTM t := by
  constructor
  · rintro ⟨c₁, c₂, t, h⟩
    obtain ⟨k, c, hd, ht, hs⟩ := decidableInTimeAndSpace_iff_exists_code.mp h
    exact ⟨c₁, c₂, k, c, hd, hs, _, ht⟩
  · rintro ⟨c₁, c₂, k, c, hd, hs, t, ht⟩
    exact ⟨c₁, c₂, t, c.decidableInTimeAndSpace hd ht hs⟩

end Cslib.Turing.MultiTapeTM

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

/-- **Space of the deterministic computation path.** Let $M$ be a deterministic multi-tape
Turing machine, $x$ an input and $t \in \mathbb{N}$. The number of work-tape cells visited along
the computation path of $M$ on $x$ made of the first $t$ steps from the initial configuration
equals the space used by the run of $M$ from the initial configuration on $x$ up to step $t$.
Both count the visited cells on each work tape separately and sum over the work tapes. -/
theorem space_ofDeterministic (tm : MultiTapeTM k Symbol State) (x : List Symbol) (t : ℕ) :
    (MultiTapeNTM.ComputationPath.ofDeterministic tm x t).space =
      tm.spaceUsed (tm.initCfg x) t :=
  rfl

/-- **Space bounds of deterministic machines.** Let $M$ be a deterministic multi-tape Turing
machine, $x$ an input and $s \in \mathbb{N}$. Then $M$ runs in space $s$ on $x$, that is, every
computation path of $M$ on $x$ visits at most $s$ work-tape cells, if and only if for every
$t \in \mathbb{N}$ the run of $M$ from the initial configuration on $x$ visits at most $s$
work-tape cells within its first $t$ steps. Visited cells are counted on each work tape
separately and summed over the work tapes. -/
theorem runsInSpace_iff_forall_spaceUsed_le {tm : MultiTapeTM k Symbol State} {x : List Symbol}
    {s : ℕ} : tm.RunsInSpace x s ↔ ∀ t, tm.spaceUsed (tm.initCfg x) t ≤ s := by
  refine ⟨fun h t ↦ ?_, fun h p ↦ ?_⟩
  · rw [← space_ofDeterministic]
    exact h _
  · rw [p.eq_ofDeterministic, space_ofDeterministic]
    exact h _

/-! ### Relabelling -/

/-- **Relabelling the successor state of an action.** For a map $f : Q \to Q'$ of states and an
action $a$ of a machine with $k$ work tapes and states $Q$, the relabelled action is the action
with states $Q'$ that moves the input head, writes and moves on the work tapes and outputs exactly
as $a$ does, and whose successor state is $f(q)$ when $a$ goes to state $q$ and is halting when $a$
halts. -/
def relabelAction (f : State → State') (a : Action k Symbol State) : Action k Symbol State' :=
  ⟨a.inputTape, a.workTapes, a.output, a.state.map f⟩

@[simp]
theorem relabelAction_id (a : Action k Symbol State) : relabelAction id a = a := by
  cases a; simp [relabelAction]

/-- **Applying a relabelled action.** Let $f : Q \to Q'$ be a map of states; relabelling by $f$
replaces a state $q$ by $f(q)$ and keeps the halting state. For every action $a$ of a machine with
$k$ work tapes and states $Q$ and every configuration $c$ of such a machine, applying $a$ with its
successor state relabelled by $f$ to $c$ with its state relabelled by $f$ gives the configuration
obtained by applying $a$ to $c$ and then relabelling its state by $f$. -/
theorem apply_relabelAction (f : State → State') (a : Action k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (relabelAction f a).apply (cfg.mapState (Option.map f)) =
      (a.apply cfg).mapState (Option.map f) :=
  rfl

/-- **Simulation up to a state relabelling.** Let $M$ and $M'$ be deterministic machines with $k$
work tapes over the same alphabet, with state sets $Q$ and $Q'$, and let $f : Q \to Q'$. Then $M'$
simulates $M$ up to the relabelling $f$ when the initial state of $M'$ is $f(q_0)$, where $q_0$ is
the initial state of $M$, and for every state $q \in Q$, every possibly blank symbol $a$ under the
input head and every tuple $w$ of possibly blank symbols under the work heads, the action of $M'$
in state $f(q)$ reading $a$ and $w$ is the action of $M$ in state $q$ reading $a$ and $w$ with its
successor state relabelled by $f$ (a successor state $q'$ becomes $f(q')$, and halting stays
halting).

Nothing is required of $M'$ in states outside the range of $f$, and $f$ need not be injective. -/
structure IsRelabelling (f : State → State') (tm : MultiTapeTM k Symbol State)
    (tm' : MultiTapeTM k Symbol State') : Prop where
  /-- The initial state is relabelled. -/
  q₀ : tm'.q₀ = f tm.q₀
  /-- Transitions commute with the relabelling. -/
  tr : ∀ q a w, tm'.tr (f q) a w = relabelAction f (tm.tr q a w)

/-- **Relabelling preserves halting.** Let $f$ be a map of states. For every configuration $c$,
the configuration obtained from $c$ by replacing its state $q$ by $f(q)$, and keeping the halting
state, is halted if and only if $c$ is halted. -/
@[simp]
theorem halted_mapState_iff (f : State → State') (cfg : Cfg k Symbol State input) :
    (cfg.mapState (Option.map f)).Halted ↔ cfg.Halted := by
  simp [Cfg.Halted]

namespace IsRelabelling

variable {f : State → State'} {tm : MultiTapeTM k Symbol State}
  {tm' : MultiTapeTM k Symbol State'}

/-- **Every machine is a relabelling of itself.** Every deterministic machine with $k$ work tapes
simulates itself up to the identity relabelling of its states. -/
theorem refl (tm : MultiTapeTM k Symbol State) : IsRelabelling id tm tm where
  q₀ := rfl
  tr _ _ _ := (relabelAction_id _).symm

/-- **Relabellings compose.** Let $M$, $M'$ and $M''$ be multi-tape Turing machines with the same
number of work tapes and the same alphabet, with state sets $Q$, $Q'$ and $Q''$. If $M'$
simulates $M$ up to the state relabelling $f : Q \to Q'$ and $M''$ simulates $M'$ up to the
state relabelling $g : Q' \to Q''$, then $M''$ simulates $M$ up to the state relabelling
$g \circ f$. -/
theorem trans {State'' : Type*} {g : State' → State''} {tm'' : MultiTapeTM k Symbol State''}
    (h : IsRelabelling f tm tm') (h' : IsRelabelling g tm' tm'') :
    IsRelabelling (g ∘ f) tm tm'' where
  q₀ := by rw [h'.q₀, h.q₀]; rfl
  tr q a w := by
    rw [Function.comp_apply, h'.tr, h.tr]
    simp [relabelAction, Option.map_map]

/-- **Relabelled machines step in lockstep.** Let $M$ and $M'$ be multi-tape Turing machines
with the same number of work tapes and the same alphabet, with state sets $Q$ and $Q'$, such that
$M'$ simulates $M$ up to the state relabelling $f : Q \to Q'$. For a configuration $c$ of $M$,
write $f_*(c)$ for the configuration of $M'$ obtained by replacing the state $q$ of $c$ by
$f(q)$ and keeping the input head, the work tapes, the work heads and the output (a halted
configuration stays halted). Then for every configuration $c$ of $M$, one step of $M'$ from
$f_*(c)$ gives $f_*(c')$, where $c'$ is the result of one step of $M$ from $c$. -/
theorem step (h : IsRelabelling f tm tm') (cfg : Cfg k Symbol State input) :
    tm'.step (cfg.mapState (Option.map f)) = (tm.step cfg).mapState (Option.map f) := by
  cases hq : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt (by simp [hq])]
  | some q =>
    rw [MultiTapeTM.step_of_state hq, MultiTapeTM.step_of_state (q := f q) (by simp [hq])]
    exact (congrArg (fun a ↦ Action.apply a _) (h.tr q _ _)).trans (apply_relabelAction f _ cfg)

/-- **Lockstep runs.** Let $M$ and $M'$ be multi-tape Turing machines with the same number of
work tapes and the same alphabet, with state sets $Q$ and $Q'$, such that $M'$ simulates $M$ up
to the state relabelling $f : Q \to Q'$. For a configuration $c$ of $M$, write $f_*(c)$ for the
configuration of $M'$ obtained by replacing the state $q$ of $c$ by $f(q)$ and keeping the input
head, the work tapes, the work heads and the output (a halted configuration stays halted). Then
for every configuration $c$ of $M$ and every $t \in \mathbb{N}$, running $M'$ for $t$ steps from
$f_*(c)$ gives $f_*(c_t)$, where $c_t$ is the configuration reached by running $M$ for $t$ steps
from $c$. -/
theorem runFrom (h : IsRelabelling f tm tm') (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm'.runFrom (cfg.mapState (Option.map f)) t = (tm.runFrom cfg t).mapState (Option.map f) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ, MultiTapeTM.runFrom_succ, ih, h.step]

/-- **Initial configurations under relabelling.** Let $M$ and $M'$ be deterministic machines with
$k$ work tapes over the same alphabet such that $M'$ simulates $M$ up to a state relabelling $f$.
Then for every input word $x$, the initial configuration of $M'$ on $x$ is the initial
configuration of $M$ on $x$ with its state $q$ replaced by $f(q)$. -/
theorem initCfg (h : IsRelabelling f tm tm') (x : List Symbol) :
    tm'.initCfg x = (tm.initCfg x).mapState (Option.map f) := by
  simp [MultiTapeNTM.initCfg, Cfg.mapState, h.q₀]

/-- **Lockstep runs from the initial configuration.** Let $M$ and $M'$ be deterministic machines
with $k$ work tapes over the same alphabet such that $M'$ simulates $M$ up to a state relabelling
$f$. Then for every input word $x$ and every $t \in \mathbb{N}$, the configuration of $M'$ after
$t$ steps on input $x$ is the configuration of $M$ after $t$ steps on input $x$ with its state
relabelled by $f$: a state $q$ becomes $f(q)$ and the halting state stays halting. -/
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

/-- **Relabelling preserves what a machine computes.** Let $M$ and $M'$ be deterministic machines
with $k$ work tapes over the same alphabet such that $M'$ simulates $M$ up to a state relabelling
$f$. Then for all words $x$ and $o$ over the alphabet, $M'$ started on input $x$ eventually halts
with output $o$ if and only if $M$ does. -/
theorem computes_iff (h : IsRelabelling f tm tm') {x o : List Symbol} :
    tm'.Computes x o ↔ tm.Computes x o := by
  simp only [MultiTapeTM.Computes, h.halted_runFrom_iff, h.output_runFrom]

/-- **Relabelling preserves time bounds.** Let $M$ and $M'$ be multi-tape Turing machines with
the same number of work tapes and the same alphabet such that $M'$ simulates $M$ up to a state
relabelling $f$. Then for every input $x$ and every $t \in \mathbb{N}$, $M'$ runs in time $t$ on
$x$ if and only if $M$ runs in time $t$ on $x$. -/
theorem runsInTime_iff (h : IsRelabelling f tm tm') {x : List Symbol} {t : ℕ} :
    tm'.RunsInTime x t ↔ tm.RunsInTime x t := by
  rw [runsInTime_iff_halted, runsInTime_iff_halted, h.halted_runFrom_iff]

/-- **Relabelling preserves space bounds.** Let $M$ and $M'$ be multi-tape Turing machines with
the same number of work tapes and the same alphabet such that $M'$ simulates $M$ up to a state
relabelling $f$. Then for every input $x$ and every $s \in \mathbb{N}$, $M'$ runs in space $s$
on $x$ if and only if $M$ runs in space $s$ on $x$. -/
theorem runsInSpace_iff (h : IsRelabelling f tm tm') {x : List Symbol} {s : ℕ} :
    tm'.RunsInSpace x s ↔ tm.RunsInSpace x s := by
  simp only [runsInSpace_iff_forall_spaceUsed_le, h.spaceUsed_initCfg]

/-- **Relabelling preserves computing a function within time and space bounds.** Let $M$ and $M'$
be deterministic machines with $k$ work tapes over the same alphabet such that $M'$ simulates $M$
up to a state relabelling $f$. Let $e_{\mathrm{in}}$ and $e_{\mathrm{out}}$ be injective encodings
of types $\alpha$ and $\beta$ as words over the alphabet, $g : \alpha \to \beta$ a function and
$t, s : \alpha \to \mathbb{N}$ bounds. Then $M'$ computes $g$ with respect to these encodings in
time $t$ and space $s$ if and only if $M$ does. Here a machine does so when, for every
$a \in \alpha$, on input $e_{\mathrm{in}}(a)$ it eventually halts with output
$e_{\mathrm{out}}(g(a))$, every computation path of at least $t(a)$ steps ends halted, and every
computation path visits at most $s(a)$ work-tape cells. -/
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

/-- **Relabelling preserves deciding a language.** Let $M$ and $M'$ be deterministic machines with
$k$ work tapes over the alphabet $\{\mathrm{false}, \mathrm{true}\}$ such that $M'$ simulates $M$
up to a state relabelling $f$. Then for every set $L$ of binary words, $M'$ decides $L$ if and only
if $M$ decides $L$. -/
theorem decides_iff {tm : MultiTapeTM k Bool State} {tm' : MultiTapeTM k Bool State'}
    (h : IsRelabelling f tm tm') {L : Set (List Bool)} : Decides tm' L ↔ Decides tm L := by
  simp only [Decides, h.computes_iff]

end IsRelabelling

end Cslib.Turing.MultiTapeTM

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Basic API for CSLib's deterministic multi-tape Turing machines

CSLib defines the canonical multi-tape machine model: `Turing.MultiTapeTM k Symbol State` has a
read-only input tape, `k` two-way infinite work tapes and a write-only output tape
(`Cslib/Computability/Machines/Turing/MultiTape/`). Configurations (`Turing.Cfg`), the step
function (`MultiTapeTM.step`), runs (`MultiTapeTM.runFrom`), the exact halting step
(`MultiTapeTM.HaltsAt`), outputs (`MultiTapeTM.Computes`) and the time and space bounds of
computation paths (`MultiTapeNTM.RunsInTime`, `MultiTapeNTM.RunsInSpace`) all live upstream. This
file does not redefine any of them; it adds the lemmas the rest of
`CSLibExt/Computability/Machines/Turing/MultiTape/` needs and that the pinned CSLib lacks.

The upstream step of a machine built from a transition function (`MultiTapeTM.ofTr`) goes
through `Classical.choose`; `stepWith tr` is the same successor written directly in terms of
`tr` (`step_ofTr`), which is what a code-level evaluator unfolds to.

## Main definitions

- `Cslib.Turing.MultiTapeTM.stepWith`: the successor configuration under a transition function.

## Main results

- `Cslib.Turing.MultiTapeTM.step_ofTr`, `runFrom_ofTr`: steps and runs of `ofTr` machines are
  `stepWith` and its iterates.
- `Cslib.Turing.MultiTapeTM.step_deterministic`: a configuration has at most one successor.
- `Cslib.Turing.MultiTapeTM.runFrom_succ'`, `runFrom_of_halted`: run composition, front-loaded
  form, and halted configurations are fixed.
- `Cslib.Turing.MultiTapeTM.haltsAt_add`, `HaltsAt.runFrom`: the halting step composes with
  run prefixes.
- `Cslib.Turing.MultiTapeTM.halted_runFrom_of_runsInTime`, `runsInTime_iff_halted`: a time bound
  of a deterministic machine means it is halted after that many steps.
- `Cslib.Turing.MultiTapeTM.computes_unique`: a deterministic machine has at most one output on an
  input; `computes_iff_output_of_runsInTime` reads it off the configuration at the time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-! ### Machines from transition functions -/

/-- **Successor under a transition function.** Let $\delta$ be a transition function of a
multi-tape Turing machine with $k$ work tapes, assigning an action to each state, input symbol
and tuple of $k$ work tape symbols, where a symbol may be blank. The successor of a configuration
$c$ under $\delta$ is $c$ itself if $c$ is halted, and otherwise the configuration obtained by
applying to $c$ the action $\delta(q, a, b)$, where $q$ is the state of $c$, $a$ the symbol under
its input head and $b$ the symbols under its work tape heads. -/
def stepWith (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- **Step of a machine given by a transition function.** Let $M$ be the deterministic multi-tape
Turing machine with initial state $q_0$ and transition function $\delta$. For every configuration
$c$, the step of $M$ from $c$ is the successor of $c$ under $\delta$: $c$ itself if $c$ is halted,
and otherwise the result of applying to $c$ the action that $\delta$ selects for the state of $c$
and the symbols under its input and work tape heads. -/
theorem step_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) : (MultiTapeTM.ofTr q₀ tr).step cfg = stepWith tr cfg := by
  cases h : cfg.state with
  | none => rw [MultiTapeTM.step_of_halt h]; simp [stepWith, h]
  | some q => rw [MultiTapeTM.step_of_state h, MultiTapeTM.tr_ofTr]; simp [stepWith, h]

/-- **Runs of a machine given by a transition function.** Let $\delta$ be a transition function
that assigns an action to every state, symbol or blank read on the input tape, and tuple of
symbols or blanks read on the work tapes, and let $M$ be the deterministic multi-tape Turing
machine with initial state $q_0$ and transition function $\delta$. Let $S_\delta$ be the map on
configurations that fixes every halted configuration and sends a running configuration in state
$q$ to the result of applying to it the action that $\delta$ selects for $q$ and the symbols or
blanks under its heads. For every configuration $c$ and every $t \in \mathbb{N}$, the run of $M$
from $c$ is in configuration $S_\delta^t(c)$ after $t$ steps, where $S_\delta^t$ is the $t$-fold
iterate of $S_\delta$. -/
theorem runFrom_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (MultiTapeTM.ofTr q₀ tr).runFrom cfg t = (stepWith tr)^[t] cfg := by
  have h : (MultiTapeTM.ofTr q₀ tr).step (input := input) = stepWith tr :=
    funext (step_ofTr q₀ tr)
  simp only [MultiTapeTM.runFrom, h]

/-! ### Steps and runs -/

variable {tm : MultiTapeTM k Symbol State}

/-- **Step determinism.** Let $M$ be a deterministic multi-tape Turing machine, with the one-step
relation it inherits as a nondeterministic machine. If a configuration $c$ steps to both $c_1$
and $c_2$, then $c_1 = c_2$. -/
theorem step_deterministic {c c₁ c₂ : Cfg k Symbol State input} (h₁ : tm.Step c c₁)
    (h₂ : tm.Step c c₂) : c₁ = c₂ :=
  (MultiTapeTM.step_iff.mp h₁).symm.trans (MultiTapeTM.step_iff.mp h₂)

@[simp]
theorem runFrom_zero (cfg : Cfg k Symbol State input) : tm.runFrom cfg 0 = cfg := rfl

/-- **Peeling off the first step of a run.** For a configuration $c$ of a deterministic
multi-tape Turing machine and every $t \in \mathbb{N}$, the run from $c$ after $t + 1$ steps is in
the same configuration as the run from the successor of $c$ after $t$ steps. -/
theorem runFrom_succ' (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  rw [Nat.add_comm, MultiTapeTM.runFrom_add]
  rfl

/-- **Halted configurations are fixed.** If a configuration $c$ of a deterministic multi-tape
Turing machine is halted, then for every $t \in \mathbb{N}$ the run from $c$ is in configuration
$c$ after $t$ steps. -/
theorem runFrom_of_halted {cfg : Cfg k Symbol State input} (h : cfg.Halted) (t : ℕ) :
    tm.runFrom cfg t = cfg :=
  MultiTapeTM.runFrom_eq_of_halt tm cfg (Nat.zero_le t) h

/-- **Halting persists along a run.** For a configuration $c$ of a deterministic multi-tape Turing
machine and steps $s \le t$, if the run from $c$ is halted after $s$ steps, then it is halted after
$t$ steps. -/
theorem halted_runFrom_mono {cfg : Cfg k Symbol State input} {s t : ℕ} (hst : s ≤ t)
    (h : (tm.runFrom cfg s).Halted) : (tm.runFrom cfg t).Halted := by
  rwa [MultiTapeTM.runFrom_eq_of_halt tm cfg hst h]

/-! ### The halting step -/

/-- **Halting at step zero.** A deterministic multi-tape Turing machine started in a
configuration $c$ halts at step $0$ if and only if $c$ is halted. -/
@[simp]
theorem haltsAt_zero_iff {cfg : Cfg k Symbol State input} : tm.HaltsAt cfg 0 ↔ cfg.Halted :=
  ⟨fun h ↦ h.halted, fun h ↦ ⟨h, fun _ hs ↦ absurd hs (Nat.not_lt_zero _)⟩⟩

/-- **Run composition for halting.** Let $c$ be a configuration of a deterministic multi-tape
Turing machine and let $m, n \in \mathbb{N}$. If the run from $c$ is not halted after any $s < m$
steps, and the run from the configuration reached after $m$ steps halts at step $n$ (it is halted
after $n$ steps and not halted after fewer), then the run from $c$ halts at step $m + n$. -/
theorem haltsAt_add {cfg : Cfg k Symbol State input} {m n : ℕ}
    (hm : ∀ s < m, ¬(tm.runFrom cfg s).Halted) (hn : tm.HaltsAt (tm.runFrom cfg m) n) :
    tm.HaltsAt cfg (m + n) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add]; exact hn.halted, fun s hs ↦ ?_⟩
  rcases Nat.lt_or_ge s m with hsm | hsm
  · exact hm s hsm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hsm
    rw [MultiTapeTM.runFrom_add]
    exact hn.not_halted (by omega)

/-- **Halting step after a run prefix.** Let $M$ be a deterministic multi-tape Turing machine,
$c$ a configuration of $M$ and $m, n$ natural numbers. If $M$ started in $c$ halts at step
$m + n$, that is, it is halted after $m + n$ steps and not halted after any fewer, then $M$
started in the configuration reached from $c$ after $m$ steps halts at step $n$. -/
theorem HaltsAt.runFrom {cfg : Cfg k Symbol State input} {m n : ℕ}
    (h : tm.HaltsAt cfg (m + n)) : tm.HaltsAt (tm.runFrom cfg m) n := by
  refine ⟨by rw [← MultiTapeTM.runFrom_add]; exact h.halted, fun s hs ↦ ?_⟩
  rw [← MultiTapeTM.runFrom_add]
  exact h.not_halted (by omega)

/-! ### Time bounds and outputs -/

/-- **A time bound forces halting.** If a deterministic multi-tape Turing machine runs in time $t$
on input $w$, then the run from the initial configuration on $w$ is halted after $t$ steps. -/
theorem halted_runFrom_of_runsInTime {t : ℕ} (h : tm.RunsInTime input t) :
    (tm.runFrom (tm.initCfg input) t).Halted := by
  have hp := h (MultiTapeNTM.ComputationPath.ofDeterministic tm input t) le_rfl
  rwa [MultiTapeTM.computationPath_last_eq_runFrom] at hp

/-- **Time bounds of deterministic machines.** Let $M$ be a deterministic multi-tape Turing
machine, $w$ an input and $t$ a natural number. Then $M$ runs in time $t$ on $w$, that is, every
computation path of $M$ on $w$ with at least $t$ steps ends in a halted configuration, if and only
if $M$ started in its initial configuration on $w$ is halted after $t$ steps. -/
theorem runsInTime_iff_halted {t : ℕ} :
    tm.RunsInTime input t ↔ (tm.runFrom (tm.initCfg input) t).Halted :=
  ⟨halted_runFrom_of_runsInTime, MultiTapeTM.runsInTime_of_halted⟩

/-- **Output determinism.** A deterministic machine computes at most one output on an input. -/
theorem computes_unique {o₁ o₂ : List Symbol} (h₁ : tm.Computes input o₁)
    (h₂ : tm.Computes input o₂) : o₁ = o₂ := by
  obtain ⟨u₁, hh₁, ho₁⟩ := h₁
  obtain ⟨u₂, hh₂, ho₂⟩ := h₂
  rcases le_total u₁ u₂ with hu | hu
  · rw [← ho₁, ← ho₂, MultiTapeTM.runFrom_eq_of_halt tm _ hu hh₁]
  · rw [← ho₁, ← ho₂, MultiTapeTM.runFrom_eq_of_halt tm _ hu hh₂]

/-- **Computing an output means halting with it.** A deterministic multi-tape Turing machine
computes the output $o$ on input $w$ if and only if there is a step $t$ at which the run from the
initial configuration on $w$ halts (it is halted after $t$ steps and not halted after any $s < t$
steps) and the configuration it reaches after $t$ steps has output tape $o$. -/
theorem computes_iff_exists_haltsAt {o : List Symbol} :
    tm.Computes input o ↔
      ∃ t, tm.HaltsAt (tm.initCfg input) t ∧ (tm.runFrom (tm.initCfg input) t).output = o := by
  constructor
  · rintro ⟨u, hu, ho⟩
    obtain ⟨t, ht, hhalt⟩ := MultiTapeTM.exists_haltsAt hu
    exact ⟨t, hhalt, by rw [← hhalt.runFrom_eq ht, ho]⟩
  · rintro ⟨t, ht, ho⟩
    exact ⟨t, ht.halted, ho⟩

/-- **Output at a time bound.** If a deterministic multi-tape Turing machine runs in time $t$ on
input $w$, then for every word $o$ the machine computes $o$ on $w$ if and only if the
configuration reached from the initial configuration on $w$ after $t$ steps has output tape $o$. -/
theorem computes_iff_output_of_runsInTime {t : ℕ} (h : tm.RunsInTime input t)
    {o : List Symbol} :
    tm.Computes input o ↔ (tm.runFrom (tm.initCfg input) t).output = o :=
  ⟨fun hc ↦ computes_unique ⟨t, halted_runFrom_of_runsInTime h, rfl⟩ hc,
    fun ho ↦ ⟨t, halted_runFrom_of_runsInTime h, ho⟩⟩

end Cslib.Turing.MultiTapeTM

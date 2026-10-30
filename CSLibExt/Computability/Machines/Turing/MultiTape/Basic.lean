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

/-- The successor of `cfg` under the transition function `tr`: a halted configuration is fixed,
and a running one applies the action that `tr` selects for its state and the symbols under its
heads. -/
def stepWith (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The step of the machine `ofTr q₀ tr` is `stepWith tr`. -/
theorem step_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) : (MultiTapeTM.ofTr q₀ tr).step cfg = stepWith tr cfg := by
  cases h : cfg.state with
  | none => rw [MultiTapeTM.step_of_halt h]; simp [stepWith, h]
  | some q => rw [MultiTapeTM.step_of_state h, MultiTapeTM.tr_ofTr]; simp [stepWith, h]

/-- The runs of the machine `ofTr q₀ tr` iterate `stepWith tr`. -/
theorem runFrom_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (MultiTapeTM.ofTr q₀ tr).runFrom cfg t = (stepWith tr)^[t] cfg := by
  have h : (MultiTapeTM.ofTr q₀ tr).step (input := input) = stepWith tr :=
    funext (step_ofTr q₀ tr)
  simp only [MultiTapeTM.runFrom, h]

/-! ### Steps and runs -/

variable {tm : MultiTapeTM k Symbol State}

/-- **Step determinism.** A configuration of a deterministic machine has at most one successor
under the step relation inherited from `MultiTapeNTM`. -/
theorem step_deterministic {c c₁ c₂ : Cfg k Symbol State input} (h₁ : tm.Step c c₁)
    (h₂ : tm.Step c c₂) : c₁ = c₂ :=
  (MultiTapeTM.step_iff.mp h₁).symm.trans (MultiTapeTM.step_iff.mp h₂)

@[simp]
theorem runFrom_zero (cfg : Cfg k Symbol State input) : tm.runFrom cfg 0 = cfg := rfl

/-- One step, then the rest of the run. -/
theorem runFrom_succ' (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  rw [Nat.add_comm, MultiTapeTM.runFrom_add]
  rfl

/-- A halted configuration is fixed by every run. -/
theorem runFrom_of_halted {cfg : Cfg k Symbol State input} (h : cfg.Halted) (t : ℕ) :
    tm.runFrom cfg t = cfg :=
  MultiTapeTM.runFrom_eq_of_halt tm cfg (Nat.zero_le t) h

/-- Halting persists along a run. -/
theorem halted_runFrom_mono {cfg : Cfg k Symbol State input} {s t : ℕ} (hst : s ≤ t)
    (h : (tm.runFrom cfg s).Halted) : (tm.runFrom cfg t).Halted := by
  rwa [MultiTapeTM.runFrom_eq_of_halt tm cfg hst h]

/-! ### The halting step -/

/-- A machine halts at step `0` exactly from a halted configuration. -/
@[simp]
theorem haltsAt_zero_iff {cfg : Cfg k Symbol State input} : tm.HaltsAt cfg 0 ↔ cfg.Halted :=
  ⟨fun h ↦ h.halted, fun h ↦ ⟨h, fun _ hs ↦ absurd hs (Nat.not_lt_zero _)⟩⟩

/-- **Run composition for halting.** If the run from `cfg` is still running for the first `m`
steps and the run from the configuration reached after `m` steps halts at step `n`, then the run
from `cfg` halts at step `m + n`. -/
theorem haltsAt_add {cfg : Cfg k Symbol State input} {m n : ℕ}
    (hm : ∀ s < m, ¬(tm.runFrom cfg s).Halted) (hn : tm.HaltsAt (tm.runFrom cfg m) n) :
    tm.HaltsAt cfg (m + n) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add]; exact hn.halted, fun s hs ↦ ?_⟩
  rcases Nat.lt_or_ge s m with hsm | hsm
  · exact hm s hsm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hsm
    rw [MultiTapeTM.runFrom_add]
    exact hn.not_halted (by omega)

/-- If the run from `cfg` halts at step `m + n`, the run from the configuration reached after `m`
steps halts at step `n`. -/
theorem HaltsAt.runFrom {cfg : Cfg k Symbol State input} {m n : ℕ}
    (h : tm.HaltsAt cfg (m + n)) : tm.HaltsAt (tm.runFrom cfg m) n := by
  refine ⟨by rw [← MultiTapeTM.runFrom_add]; exact h.halted, fun s hs ↦ ?_⟩
  rw [← MultiTapeTM.runFrom_add]
  exact h.not_halted (by omega)

/-! ### Time bounds and outputs -/

/-- A deterministic machine that runs in time `t` on `input` is halted after `t` steps. -/
theorem halted_runFrom_of_runsInTime {t : ℕ} (h : tm.RunsInTime input t) :
    (tm.runFrom (tm.initCfg input) t).Halted := by
  have hp := h (MultiTapeNTM.ComputationPath.ofDeterministic tm input t) le_rfl
  rwa [MultiTapeTM.computationPath_last_eq_runFrom] at hp

/-- For a deterministic machine, running in time `t` on `input` means being halted after `t`
steps. -/
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

/-- A machine computes `o` on `input` iff it halts at some step with output `o`. -/
theorem computes_iff_exists_haltsAt {o : List Symbol} :
    tm.Computes input o ↔
      ∃ t, tm.HaltsAt (tm.initCfg input) t ∧ (tm.runFrom (tm.initCfg input) t).output = o := by
  constructor
  · rintro ⟨u, hu, ho⟩
    obtain ⟨t, ht, hhalt⟩ := MultiTapeTM.exists_haltsAt hu
    exact ⟨t, hhalt, by rw [← hhalt.runFrom_eq ht, ho]⟩
  · rintro ⟨t, ht, ho⟩
    exact ⟨t, ht.halted, ho⟩

/-- Under a time bound `t`, a deterministic machine computes exactly the output of its
configuration after `t` steps. -/
theorem computes_iff_output_of_runsInTime {t : ℕ} (h : tm.RunsInTime input t)
    {o : List Symbol} :
    tm.Computes input o ↔ (tm.runFrom (tm.initCfg input) t).output = o :=
  ⟨fun hc ↦ computes_unique ⟨t, halted_runFrom_of_runsInTime h, rfl⟩ hc,
    fun ho ↦ ⟨t, halted_runFrom_of_runsInTime h, ho⟩⟩

end Cslib.Turing.MultiTapeTM

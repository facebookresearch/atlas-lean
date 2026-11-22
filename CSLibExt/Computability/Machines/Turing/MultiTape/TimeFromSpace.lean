/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean` (CSLib v4.35.0, commit
`5b56df99362532c46e1175381fbbdd755bd56030`):
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan

`Cslib/Computability/Machines/Turing/MultiTape/ConfigBound.lean` (CSLib v4.35.0, commit
`5b56df99362532c46e1175381fbbdd755bd56030`):
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import CSLibExt.Computability.Machines.Turing.MultiTape.Basic

/-!
# Time bounds for halting space-bounded machines

Before a deterministic machine's first halt, its readable configuration cores
are distinct. The canonical visited-work-tape-cell bound therefore gives an
actual time bound, not just a bound on the number of possible configurations.
The write-only output tape is excluded from the core, as in CSLib's
`ConfigBound`; the input head contributes the factor `input.length + 2`.

`exists_exponential_time_bound` chooses its constants before every input and
space budget. Halting remains a hypothesis: bounded space alone permits loops.
These results use the existing multi-tape machine and resource predicates.

CSLib v4.36.0 (leanprover/cslib#1117) dropped the space of a deterministic run,
`MultiTapeTM.spaceUsed` with `MultiTapeTM.visitedByTapeHead` and `MultiTapeTM.spaceUsedByTape`,
in favour of the space of computation paths, and dropped `core_step_eq_of_core_eq`. Those of them
that ATLAS uses are restated below, unchanged and in their original namespace, from
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean` and `ConfigBound.lean` of
CSLib v4.35.0 (commit `5b56df99362532c46e1175381fbbdd755bd56030`), whose copyright and authors
are given at the top of this file; the others, such as `spaceUsedByTape_le_spaceUsed`, are not.
-/

@[expose] public section

set_option autoImplicit false

namespace Turing

section

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol} {tm : MultiTapeTM k Symbol State}

/-- `step` never reads the output tape, so the core of the next configuration is determined by the
core of the current one. -/
lemma core_step_eq_of_core_eq {c₁ c₂ : Cfg k Symbol State input} (h : c₁.core = c₂.core) :
    (tm.step c₁).core = (tm.step c₂).core := by
  rcases c₁ with ⟨q₁, i₁, w₁, p₁, out₁⟩
  rcases c₂ with ⟨q₂, i₂, w₂, p₂, out₂⟩
  simp only [Cfg.core, Cfg.storage, Prod.mk.injEq, Storage.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  cases q₁ with
  | none => rw [MultiTapeTM.step_of_halt rfl, MultiTapeTM.step_of_halt rfl]; rfl
  | some q => rw [MultiTapeTM.step_of_state rfl, MultiTapeTM.step_of_state rfl]; rfl

end

namespace MultiTapeTM

variable {k : ℕ} {State Symbol : Type*} {tm : MultiTapeTM k Symbol State} {input : List Symbol}

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
noncomputable def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    Finset ℤ :=
  Finset.univ.image fun n : Fin (t + 1) => (tm.runFrom cfg n).workTapePos i

/--
The number of work tape cells visited by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
noncomputable def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells visited by a computation starting from configuration
`cfg` up to step `t`.
-/
noncomputable def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ :=
  ∑ i, tm.spaceUsedByTape cfg t i

end MultiTapeTM

end Turing

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

private theorem core_run_congr {c₁ c₂ : Cfg k Symbol State input}
    (h : c₁.core = c₂.core) (t : ℕ) :
    (tm.runFrom c₁ t).core = (tm.runFrom c₂ t).core := by
  induction t with
  | zero => exact h
  | succ t ih =>
    simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply'] at ih ⊢
    exact core_step_eq_of_core_eq ih

private theorem core_injective_before_halt {T : ℕ}
    (hT : tm.HaltsAt (tm.initCfg input) T) :
    Function.Injective (fun i : Fin (T + 1) =>
      (tm.runFrom (tm.initCfg input) i).core) := by
  have hneq (i j : Fin (T + 1)) (hij : (i : ℕ) < j)
      (hc : (tm.runFrom (tm.initCfg input) i).core =
        (tm.runFrom (tm.initCfg input) j).core) : False := by
    have hh := core_run_congr (tm := tm) hc (T - j)
    rw [← MultiTapeTM.runFrom_add, ← MultiTapeTM.runFrom_add] at hh
    have hj : (j : ℕ) + (T - j) = T := by omega
    rw [hj] at hh
    have halted : (tm.runFrom (tm.initCfg input) (i + (T - j))).Halted := by
      change ((tm.runFrom (tm.initCfg input) (i + (T - j))).core).2.state = none
      rw [hh]
      exact hT.halted
    exact hT.not_halted (by omega) halted
  intro i j hc
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · exact (hneq i j hij hc).elim
  · exact Fin.ext hij
  · exact (hneq j i hij hc.symm).elim

/-- The first halting time is smaller than the canonical bound on reachable cores. -/
theorem haltTime_lt_coreBound [Fintype Symbol] [Fintype State] {s T : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hT : tm.HaltsAt (tm.initCfg input) T) :
    T < (input.length + 2) * storageBound Symbol State k s := by
  have hi := core_injective_before_halt hT
  have hcard : (T + 1 : ℕ∞) ≤
      (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard := by
    calc (T + 1 : ℕ∞) = (Set.univ : Set (Fin (T + 1))).encard := by
          simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]
      _ ≤ (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core).encard :=
        Set.encard_le_encard_of_injOn
          (fun i _ => ⟨i, rfl⟩) (fun i _ j _ h => hi h)
  have hspace : tm.RunsInSpace input s := fun p => by
    rw [p.eq_ofDeterministic]
    exact hs _
  have hsub : (Set.range fun t => (tm.runFrom (tm.initCfg input) t).core) ⊆
      Set.range fun p : tm.ComputationPath input => p.last.core := by
    rintro _ ⟨t, rfl⟩
    exact ⟨.ofDeterministic tm input t, rfl⟩
  have hb := hcard.trans ((Set.encard_le_encard hsub).trans (tm.encard_cores_le hspace))
  have hn : T + 1 ≤ (input.length + 2) * storageBound Symbol State k s := by
    exact_mod_cast hb
  omega

/-- A halting, space-bounded run has an actual step bound. -/
theorem runsInTime_coreBound [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hh : ∃ t, (tm.runFrom (tm.initCfg input) t).Halted) :
    tm.RunsInTime input ((input.length + 2) * storageBound Symbol State k s) := by
  obtain ⟨t, ht⟩ := hh
  obtain ⟨T, _, hT⟩ := MultiTapeTM.exists_haltsAt ht
  exact MultiTapeTM.runsInTime_of_halted
    (halted_runFrom_mono (haltTime_lt_coreBound hs hT).le hT.halted)

private theorem spaceUsed_le_of_runsInSpace {s : ℕ}
    (hs : tm.RunsInSpace input s) (t : ℕ) :
    tm.spaceUsed (tm.initCfg input) t ≤ s := by
  exact hs (MultiTapeNTM.ComputationPath.ofDeterministic tm input t)

/-- Exponential time from a visited-cell space bound and a halting run. -/
theorem runsInTime_exponential_of_space [Fintype Symbol] [Fintype State] {s : ℕ}
    (hs : tm.RunsInSpace input s)
    (hh : ∃ t, (tm.runFrom (tm.initCfg input) t).Halted) :
    tm.RunsInTime input ((input.length + 2) * storageBoundBase Symbol State k *
      2 ^ (storageBoundExp Symbol k * s)) := by
  apply (runsInTime_coreBound (spaceUsed_le_of_runsInSpace hs) hh).mono
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (input.length + 2)
    (storageBound_le_base_mul_pow (Symbol := Symbol) (State := State) (k := k) s)

/-- One pair of constants works for every input of the fixed machine. -/
theorem exists_exponential_time_bound [Finite Symbol] [Finite State]
    (tm : MultiTapeTM k Symbol State) :
    ∃ a c : ℕ, ∀ (input : List Symbol) (s : ℕ), tm.RunsInSpace input s →
      (∃ t, (tm.runFrom (tm.initCfg input) t).Halted) →
      tm.RunsInTime input ((input.length + 2) * a * 2 ^ (c * s)) := by
  let : Fintype Symbol := Fintype.ofFinite Symbol
  let : Fintype State := Fintype.ofFinite State
  exact ⟨storageBoundBase Symbol State k, storageBoundExp Symbol k,
    fun _ _ hs hh => runsInTime_exponential_of_space hs hh⟩

end Cslib.Turing.MultiTapeTM

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math,
CSLibExt/Logics/CTLStar/UpstreamBridge.lean,
commit cbe67c4f99b625a43c98959d53f88f7b137d7119 (PR 10058).
Original formalization by Adam Kiezun; proofs adapted only to Atlas's
canonical run helper names and light LTS foundations import.
-/
module

public import CSLibExt.Logics.CTLStar.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
import CSLibExt.Foundations.Semantics.LTS.OmegaExecution

/-!
# CTL* state-run semantics and canonical labeled executions

`CSLibExt.Logics.CTLStar.Basic` interprets CTL* on `Cslib.LTS` using the
CSLibExt `OmegaRun` extension: a state sequence `ℕ → State` with an existentially
witnessed label at each step. This file gives the equivalent presentation using
canonical `Cslib.LTS.OmegaExecution`, whose values pair ω-sequences of states and
labels, and proves the two presentations agree (`stateSat_iff_upstream`, `pathSat_iff_upstream`).

The proof is by induction on a joint size measure of state and path formulas:
the two statements are proved together, since state satisfaction depends on path
satisfaction (through `E`/`A`) and path satisfaction depends on state
satisfaction (through the `.state` embedding). The run/execution conversion
uses `CSLibExt.Foundations.Semantics.LTS.OmegaExecution`
(`omegaExecution_of_omegaRun`, `omegaRun_of_omegaExecution`,
`shiftSeq_eq_drop`). Selecting labels uses `Classical.choice`; the CTL
embedding still requires seriality.

Main results:

* `Cslib.CTLStar.UpstreamStateSat`, `Cslib.CTLStar.UpstreamPathSat`: CTL* state
  and path satisfaction over canonical labeled executions.
* `Cslib.CTLStar.stateSat_iff_upstream`: state-run and execution-based state
  satisfaction agree on `lts`.
* `Cslib.CTLStar.pathSat_iff_upstream`: the two path presentations agree on
  every infinite run.

## References

* E. A. Emerson, J. Y. Halpern, "Sometimes and Not Never Revisited: On Branching
  Versus Linear Time Temporal Logic", *Journal of the ACM* 33 (1986), 151-178
  (CTL* syntax and semantics).
* E. Grädel, W. Thomas, T. Wilke (eds.), *Automata, Logics, and Infinite Games*,
  LNCS 2500, Springer, 2002, Chapter 2 (branching-time logics over transition
  systems).
-/

@[expose] public section

namespace Cslib
namespace CTLStar

universe u

variable {State Label Atom : Type*} {lts : _root_.Cslib.LTS State Label}
  {valuation : State → Atom → Prop}

/-! ## Sizes of CTL* formulas -/

mutual

/-- The size of a CTL* state formula, counting both connectives and embedded
path formulas (used for the joint induction in `bridge_aux`). -/
private def StateFormula.size : StateFormula Atom → ℕ
  | .atom _ => 1
  | .top => 1
  | .not φ => StateFormula.size φ + 1
  | .and φ ψ => StateFormula.size φ + StateFormula.size ψ + 1
  | .exists π => PathFormula.pathSize π + 1
  | .forall π => PathFormula.pathSize π + 1

/-- The size of a CTL* path formula, counting both connectives and embedded
state formulas (used for the joint induction in `bridge_aux`). -/
private def PathFormula.pathSize : PathFormula Atom → ℕ
  | .state φ => StateFormula.size φ + 1
  | .not π => PathFormula.pathSize π + 1
  | .and π ρ => PathFormula.pathSize π + PathFormula.pathSize ρ + 1
  | .next π => PathFormula.pathSize π + 1
  | .until π ρ => PathFormula.pathSize π + PathFormula.pathSize ρ + 1

end

/-! ## Canonical labeled-execution semantics -/

mutual

/-- **CTL$^{\ast}$ state satisfaction over labeled executions.**
Satisfaction of a CTL* state formula at a state over canonical `Cslib.LTS`:
`E π` holds when some infinite labeled execution from the state satisfies `π`;
`A π` when every infinite labeled execution does. -/
def UpstreamStateSat (lts : _root_.Cslib.LTS State Label)
    (valuation : State → Atom → Prop) : StateFormula Atom → State → Prop
  | .atom a, s => valuation s a
  | .top, _ => True
  | .not φ, s => ¬ UpstreamStateSat lts valuation φ s
  | .and φ ψ, s => UpstreamStateSat lts valuation φ s ∧
      UpstreamStateSat lts valuation ψ s
  | .exists π, s => ∃ oss μs, oss 0 = s ∧ lts.OmegaExecution oss μs ∧
      UpstreamPathSat lts valuation π oss
  | .forall π, s => ∀ oss μs, oss 0 = s → lts.OmegaExecution oss μs →
      UpstreamPathSat lts valuation π oss

/-- **CTL$^{\ast}$ path satisfaction on labeled executions.**
Satisfaction of a CTL* path formula on a canonical infinite labeled execution:
`next` drops the first state, while `until` asks for a target position with the guard
before it. -/
def UpstreamPathSat (lts : _root_.Cslib.LTS State Label)
    (valuation : State → Atom → Prop) : PathFormula Atom → ωSequence State → Prop
  | .state φ, oss => UpstreamStateSat lts valuation φ (oss 0)
  | .not π, oss => ¬ UpstreamPathSat lts valuation π oss
  | .and π ρ, oss => UpstreamPathSat lts valuation π oss ∧
      UpstreamPathSat lts valuation ρ oss
  | .next π, oss => UpstreamPathSat lts valuation π (oss.drop 1)
  | .until π ρ, oss =>
      ∃ k, UpstreamPathSat lts valuation ρ (oss.drop k) ∧
        ∀ j, j < k → UpstreamPathSat lts valuation π (oss.drop j)

end

/-! ## The bridge -/

/-- Joint induction step for the bridge: state-run and labeled-execution
satisfaction agree for all state formulas of size at most `n` and all path
formulas of path size at most `n`. -/
private theorem bridge_aux (n : ℕ) :
    (∀ φ : StateFormula Atom, StateFormula.size φ ≤ n → ∀ {s : State},
      StateSat lts valuation φ s ↔
        UpstreamStateSat (lts) valuation φ s) ∧
    (∀ π : PathFormula Atom, PathFormula.pathSize π ≤ n → ∀ {run : ℕ → State},
      LTS.OmegaRun (lts := lts) run →
        (PathSat lts valuation π run ↔
          UpstreamPathSat (lts) valuation π ⟨run⟩)) := by
  induction n with
  | zero =>
    constructor
    · intro φ
      cases φ <;> intro hsize s <;>
        simp only [StateFormula.size] at hsize <;> omega
    · intro π
      cases π <;> intro hsize run hrun <;>
        simp only [PathFormula.pathSize] at hsize <;> omega
  | succ n ih =>
    obtain ⟨ihS, ihP⟩ := ih
    constructor
    · intro φ
      cases φ with
      | atom a =>
        intro _ s
        exact Iff.rfl
      | top =>
        intro _ s
        exact Iff.rfl
      | not φ =>
        intro hsize s
        change (¬ StateSat lts valuation φ s) ↔
          (¬ UpstreamStateSat (lts) valuation φ s)
        exact not_congr (ihS φ (by
          have h := hsize
          simp only [StateFormula.size] at h
          omega) (s := s))
      | and φ ψ =>
        intro hsize s
        change (StateSat lts valuation φ s ∧ StateSat lts valuation ψ s) ↔
          (UpstreamStateSat (lts) valuation φ s ∧
            UpstreamStateSat (lts) valuation ψ s)
        exact and_congr (ihS φ (by
          have h := hsize
          simp only [StateFormula.size] at h
          omega) (s := s))
          (ihS ψ (by
            have h := hsize
            simp only [StateFormula.size] at h
            omega) (s := s))
      | «exists» π =>
        intro hsize s
        change (∃ run, run 0 = s ∧ LTS.OmegaRun (lts := lts) run ∧ PathSat lts valuation π run) ↔
          (∃ oss μs, oss 0 = s ∧ (lts).OmegaExecution oss μs ∧
            UpstreamPathSat (lts) valuation π oss)
        constructor
        · rintro ⟨run, h0, hrun, hpath⟩
          obtain ⟨μs, hμs⟩ := LTS.omegaExecution_of_omegaRun hrun
          exact ⟨⟨run⟩, μs, h0, hμs,
            (ihP π (by
              have h := hsize
              simp only [StateFormula.size] at h
              omega) hrun).mp hpath⟩
        · rintro ⟨oss, μs, h0, hex, hpath⟩
          refine ⟨fun i => oss i, h0, LTS.omegaRun_of_omegaExecution hex, ?_⟩
          exact (ihP π (by
            have h := hsize
            simp only [StateFormula.size] at h
            omega) (LTS.omegaRun_of_omegaExecution hex)).mpr hpath
      | «forall» π =>
        intro hsize s
        change (∀ run, run 0 = s → LTS.OmegaRun (lts := lts) run → PathSat lts valuation π run) ↔
          (∀ oss μs, oss 0 = s → (lts).OmegaExecution oss μs →
            UpstreamPathSat (lts) valuation π oss)
        constructor
        · intro hall oss μs h0 hex
          exact (ihP π (by
            have h := hsize
            simp only [StateFormula.size] at h
            omega) (LTS.omegaRun_of_omegaExecution hex)).mp
            (hall _ h0 (LTS.omegaRun_of_omegaExecution hex))
        · intro hall run h0 hrun
          obtain ⟨μs, hμs⟩ := LTS.omegaExecution_of_omegaRun hrun
          exact (ihP π (by
            have h := hsize
            simp only [StateFormula.size] at h
            omega) hrun).mpr (hall ⟨run⟩ μs h0 hμs)
    · intro π
      cases π with
      | state φ =>
        intro hsize run hrun
        change StateSat lts valuation φ (run 0) ↔
          UpstreamStateSat (lts) valuation φ
            ((⟨run⟩ : ωSequence State) 0)
        exact ihS φ (by
          have h := hsize
          simp only [PathFormula.pathSize] at h
          omega)
      | not π =>
        intro hsize run hrun
        change (¬ PathSat lts valuation π run) ↔
          (¬ UpstreamPathSat (lts) valuation π ⟨run⟩)
        exact not_congr (ihP π (by
          have h := hsize
          simp only [PathFormula.pathSize] at h
          omega) hrun)
      | and π ρ =>
        intro hsize run hrun
        change (PathSat lts valuation π run ∧ PathSat lts valuation ρ run) ↔
          (UpstreamPathSat (lts) valuation π ⟨run⟩ ∧
            UpstreamPathSat (lts) valuation ρ ⟨run⟩)
        exact and_congr
          (ihP π (by
            have h := hsize
            simp only [PathFormula.pathSize] at h
            omega) hrun)
          (ihP ρ (by
            have h := hsize
            simp only [PathFormula.pathSize] at h
            omega) hrun)
      | next π =>
        intro hsize run hrun
        change PathSat lts valuation π (Semantics.shiftSeq run 1) ↔
          UpstreamPathSat (lts) valuation π
            ((⟨run⟩ : ωSequence State).drop 1)
        rw [← LTS.shiftSeq_eq_drop run 1]
        exact ihP π (by
          have h := hsize
          simp only [PathFormula.pathSize] at h
          omega) (LTS.omegaRun_shift hrun 1)
      | «until» π ρ =>
        intro hsize run hrun
        change (∃ k, PathSat lts valuation ρ (Semantics.shiftSeq run k) ∧
              ∀ j, j < k → PathSat lts valuation π (Semantics.shiftSeq run j)) ↔
            (∃ k, UpstreamPathSat (lts) valuation ρ
                ((⟨run⟩ : ωSequence State).drop k) ∧
              ∀ j, j < k → UpstreamPathSat (lts) valuation π
                ((⟨run⟩ : ωSequence State).drop j))
        refine exists_congr fun k => ?_
        have hdrop : ∀ j, (⟨run⟩ : ωSequence State).drop j = ⟨Semantics.shiftSeq run j⟩ :=
          fun j => (LTS.shiftSeq_eq_drop run j).symm
        rw [hdrop k]
        refine and_congr
          (ihP ρ (by
            have h := hsize
            simp only [PathFormula.pathSize] at h
            omega) (LTS.omegaRun_shift hrun k)) ?_
        refine forall_congr' fun j => ?_
        rw [hdrop j]
        refine imp_congr_right fun _ => ?_
        exact ihP π (by
          have h := hsize
          simp only [PathFormula.pathSize] at h
          omega) (LTS.omegaRun_shift hrun j)

/-- **CTL* state-sequence/execution bridge, state formulas.** CTL* state satisfaction
over `lts` agrees with satisfaction quantified over canonical `OmegaExecution`s. -/
theorem stateSat_iff_upstream (φ : StateFormula Atom) (s : State) :
    StateSat lts valuation φ s ↔
      UpstreamStateSat (lts) valuation φ s :=
  (bridge_aux (StateFormula.size φ)).1 φ (le_refl _)

/-- **CTL* state-sequence/execution bridge, path formulas.** CTL* path
satisfaction on a state run agrees with the canonical labeled-execution
presentation on the same state sequence. -/
theorem pathSat_iff_upstream (π : PathFormula Atom) {run : ℕ → State}
    (hrun : LTS.OmegaRun (lts := lts) run) :
    PathSat lts valuation π run ↔
      UpstreamPathSat (lts) valuation π ⟨run⟩ :=
  (bridge_aux (PathFormula.pathSize π)).2 π (le_refl _) hrun

end CTLStar
end Cslib

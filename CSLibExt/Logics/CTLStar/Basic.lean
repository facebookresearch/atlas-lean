/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

/-
Ported from fairinternal/formal-math, CSLibExt/Logics/CTLStar/Basic.lean,
commit cbe67c4f99b625a43c98959d53f88f7b137d7119 (PR 10058).
The original attribution above is preserved. Adaptations use Atlas's
canonical LTS run API and LTL omega-word semantics.
-/
module

public import CSLibExt.Logics.CTL.Basic
public import CSLibExt.Logics.LTL.OmegaWord

/-!
# CTL*: state and path formulas

CTL* (Emerson and Halpern, *Sometimes and Not Never Revisited: On
Branching Versus Linear Time Temporal Logic*, Journal of the ACM 33
(1986), 151-178; conference version, POPL 1983) unifies CTL and LTL.
CTL itself is due to Clarke and Emerson, *Design and synthesis of
synchronization skeletons using branching time temporal logic*, 1981.
State formulas quantify over paths (`E π`, `A π`), and path formulas
combine state formulas with the linear-time operators `X` (`next`) and
`U` (`until`). A path quantifier may wrap an arbitrary path formula,
including `E G F p` (some infinite path visits `p` infinitely often).
The toggle example below establishes satisfaction, not an expressiveness
separation between CTL and CTL*.

Semantics is over infinite runs only, so the CTL agreement theorem
`embedCTL_sat` is stated for serial systems (no deadlocks), where
maximal paths are exactly infinite runs. On non-serial systems CTL's
`AU`/`AF` use maximal-path semantics (see `CSLibExt/Logics/CTL/Basic`),
which CTL* does not reproduce. Even a zero-step `EU` witness may not
extend to an infinite run without seriality.
The CTL* semantics uses Atlas's `OmegaRun` state-sequence extension on
canonical `Cslib.LTS`. The equivalent presentation using canonical
labeled `Cslib.LTS.OmegaExecution` is in `UpstreamBridge.lean`.
The LTL embedding targets the existing `LTL.Word.Satisfies` semantics
and requires neither a valid transition run nor seriality.

Main results:

* `pathSat_always`: `G π` holds on a run iff `π` holds on every
  suffix.
* `embedLTL_sat`: the LTL embedding is semantics-preserving on every
  run.
* `embedCTL_sat`: the CTL embedding is semantics-preserving on serial
  systems.
* `toggle_egf_p`: `E G F p` holds at `false` in the toggle system.
-/

@[expose] public section

namespace Cslib
namespace CTLStar

universe u

mutual
/-- State formulas of CTL*: atoms, truth, negation, conjunction, and
the path quantifiers `E π` and `A π`. -/
inductive StateFormula (Atom : Type u) where
  | atom (a : Atom) : StateFormula Atom
  | top : StateFormula Atom
  | not (φ : StateFormula Atom) : StateFormula Atom
  | and (φ ψ : StateFormula Atom) : StateFormula Atom
  | exists (π : PathFormula Atom) : StateFormula Atom
  | forall (π : PathFormula Atom) : StateFormula Atom

/-- Path formulas of CTL*: a state formula at the first position,
negation, conjunction, `next`, and `until`. -/
inductive PathFormula (Atom : Type u) where
  | state (φ : StateFormula Atom) : PathFormula Atom
  | not (π : PathFormula Atom) : PathFormula Atom
  | and (π ρ : PathFormula Atom) : PathFormula Atom
  | next (π : PathFormula Atom) : PathFormula Atom
  | until (π ρ : PathFormula Atom) : PathFormula Atom
end

namespace PathFormula

variable {Atom : Type u}

/-- `G π`: `π` holds at every position, as `¬(⊤ U ¬π)`. -/
def alwaysPath (π : PathFormula Atom) : PathFormula Atom :=
  .not (.until (.state .top) (.not π))

/-- `F π`: `π` holds at some position, as `⊤ U π`. -/
def eventuallyPath (π : PathFormula Atom) : PathFormula Atom :=
  .until (.state .top) π

end PathFormula

variable {State Label Atom : Type*} {lts : _root_.Cslib.LTS State Label}
  {valuation : State → Atom → Prop} {π ρ : PathFormula Atom}

mutual
/-- Satisfaction of a CTL* state formula at a state: `E π` holds when
some infinite run from the state satisfies `π`; `A π` when every
infinite run does. -/
def StateSat (lts : _root_.Cslib.LTS State Label) (valuation : State → Atom → Prop) :
    StateFormula Atom → State → Prop
  | .atom a, s => valuation s a
  | .top, _ => True
  | .not φ, s => ¬ StateSat lts valuation φ s
  | .and φ ψ, s => StateSat lts valuation φ s ∧ StateSat lts valuation ψ s
  | .exists π, s => ∃ run, run 0 = s ∧ LTS.OmegaRun (lts := lts) run ∧ PathSat lts valuation π run
  | .forall π, s => ∀ run, run 0 = s → LTS.OmegaRun (lts := lts) run → PathSat lts valuation π run

/-- Satisfaction of a CTL* path formula on an infinite run: `next`
shifts the run, `until` asks for a target position with the guard
before it. -/
def PathSat (lts : _root_.Cslib.LTS State Label) (valuation : State → Atom → Prop) :
    PathFormula Atom → (ℕ → State) → Prop
  | .state φ, run => StateSat lts valuation φ (run 0)
  | .not π, run => ¬ PathSat lts valuation π run
  | .and π ρ, run => PathSat lts valuation π run ∧ PathSat lts valuation ρ run
  | .next π, run => PathSat lts valuation π (Semantics.shiftSeq run 1)
  | .until π ρ, run =>
      ∃ k, PathSat lts valuation ρ (Semantics.shiftSeq run k) ∧
        ∀ j, j < k → PathSat lts valuation π (Semantics.shiftSeq run j)
end

/-- Unfolding: a state formula on a run is satisfaction at its first
state. -/
theorem pathSat_state (φ : StateFormula Atom) (run : ℕ → State) :
    PathSat lts valuation (.state φ) run = StateSat lts valuation φ (run 0) :=
  rfl

/-- Unfolding: `next` shifts the run. -/
theorem pathSat_next (π : PathFormula Atom) (run : ℕ → State) :
    PathSat lts valuation (.next π) run =
      PathSat lts valuation π (Semantics.shiftSeq run 1) :=
  rfl

/-- `(shiftSeq run k) 0 = run k`: the `0 + k` is discharged by
`Nat.zero_add`. -/
theorem shiftSeq_apply_zero (run : ℕ → State) (k : ℕ) :
    Semantics.shiftSeq run k 0 = run k := by
  change run (0 + k) = run k
  rw [Nat.zero_add]

/-- A state formula on a shifted run is satisfaction at the shifted
position. -/
theorem pathSat_state_shift (φ : StateFormula Atom) (run : ℕ → State) (k : ℕ) :
    PathSat lts valuation (.state φ) (Semantics.shiftSeq run k) =
      StateSat lts valuation φ (run k) := by
  rw [pathSat_state, shiftSeq_apply_zero]

/-- `G π` holds on a run iff `π` holds on every suffix. -/
theorem pathSat_always (run : ℕ → State) :
    PathSat lts valuation (π.alwaysPath) run ↔
      ∀ i, PathSat lts valuation π (Semantics.shiftSeq run i) := by
  constructor
  · intro h i
    exact Classical.byContradiction fun hn => h ⟨i, hn, fun _ _ => True.intro⟩
  · intro h hcon
    obtain ⟨k, hk, -⟩ := hcon
    exact hk (h k)

/-- `F π` holds on a run iff `π` holds on some suffix. -/
theorem pathSat_eventually (run : ℕ → State) :
    PathSat lts valuation (π.eventuallyPath) run ↔
      ∃ k, PathSat lts valuation π (Semantics.shiftSeq run k) := by
  constructor
  · rintro ⟨k, hk, -⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk, fun _ _ => True.intro⟩

/-- The LTL embedding: every LTL formula is a CTL* path formula. -/
def embedLTL : LTL.Formula Atom → PathFormula Atom
  | .atom a => .state (.atom a)
  | .top => .state .top
  | .not φ => .not (embedLTL φ)
  | .and φ ψ => .and (embedLTL φ) (embedLTL ψ)
  | .next φ => .next (embedLTL φ)
  | .until φ ψ => .until (embedLTL φ) (embedLTL ψ)

/-- The LTL embedding preserves semantics on every state sequence,
including sequences that are not valid runs of `lts`. -/
theorem embedLTL_sat (φ : LTL.Formula Atom) :
    ∀ run, PathSat lts valuation (embedLTL φ) run ↔
      LTL.Word.Satisfies valuation ⟨run⟩ φ := by
  induction φ with
  | atom a => intro run; exact Iff.rfl
  | top => intro run; exact Iff.rfl
  | not φ ih =>
      intro run
      change (¬ PathSat lts valuation (embedLTL φ) run) ↔
        ¬ LTL.Word.Satisfies valuation ⟨run⟩ φ
      exact not_congr (ih run)
  | and φ ψ ihφ ihψ =>
      intro run
      change (PathSat lts valuation (embedLTL φ) run ∧
          PathSat lts valuation (embedLTL ψ) run) ↔
        (LTL.Word.Satisfies valuation ⟨run⟩ φ ∧
          LTL.Word.Satisfies valuation ⟨run⟩ ψ)
      exact and_congr (ihφ run) (ihψ run)
  | next φ ih =>
      intro run
      change PathSat lts valuation (embedLTL φ)
        (Semantics.shiftSeq run 1) ↔
          LTL.Word.Satisfies valuation ⟨Semantics.shiftSeq run 1⟩ φ
      exact ih (Semantics.shiftSeq run 1)
  | «until» φ ψ ihφ ihψ =>
      intro run
      change (∃ k, PathSat lts valuation (embedLTL ψ)
          (Semantics.shiftSeq run k) ∧
          ∀ j, j < k → PathSat lts valuation (embedLTL φ)
            (Semantics.shiftSeq run j)) ↔
        (∃ k, LTL.Word.Satisfies valuation ⟨Semantics.shiftSeq run k⟩ ψ ∧
          ∀ j, j < k →
            LTL.Word.Satisfies valuation ⟨Semantics.shiftSeq run j⟩ φ)
      constructor
      · rintro ⟨k, hk, hj⟩
        exact ⟨k, (ihψ _).mp hk,
          fun j hjk => (ihφ _).mp (hj j hjk)⟩
      · rintro ⟨k, hk, hj⟩
        exact ⟨k, (ihψ _).mpr hk,
          fun j hjk => (ihφ _).mpr (hj j hjk)⟩

/-- The structural LTL embedding also agrees at every position,
without assuming the sequence is a valid transition run. -/
theorem embedLTL_sat_at (φ : LTL.Formula Atom) (run : ℕ → State)
    (k : ℕ) :
    PathSat lts valuation (embedLTL φ) (Semantics.shiftSeq run k) ↔
      LTL.Word.SatisfiesAt valuation ⟨run⟩ k φ :=
  embedLTL_sat φ _

/-- The CTL embedding: every CTL formula is a CTL* state formula.
`EG φ` is `E G (state φ)`; `AU` is `A (state φ U state ψ)`. -/
def embedCTL : CTL.Formula Atom → StateFormula Atom
  | .atom a => .atom a
  | .top => .top
  | .not φ => .not (embedCTL φ)
  | .and φ ψ => .and (embedCTL φ) (embedCTL ψ)
  | .existsNext φ => .exists (.next (.state (embedCTL φ)))
  | .existsUntil φ ψ => .exists (.until (.state (embedCTL φ)) (.state (embedCTL ψ)))
  | .existsGlobally φ => .exists (.alwaysPath (.state (embedCTL φ)))
  | .forallUntil φ ψ => .forall (.until (.state (embedCTL φ)) (.state (embedCTL ψ)))

/-- The CTL embedding preserves semantics on serial systems. -/
theorem embedCTL_sat (hser : CTL.Serial lts) (φ : CTL.Formula Atom) :
    ∀ {s : State}, StateSat lts valuation (embedCTL φ) s ↔
      CTL.Satisfies lts valuation s φ := by
  induction φ with
  | atom a => intro s; exact Iff.rfl
  | top => intro s; exact Iff.rfl
  | not φ ih =>
      intro s
      exact not_congr (ih (s := s))
  | and φ ψ ihφ ihψ =>
      intro s
      exact and_congr (ihφ (s := s)) (ihψ (s := s))
  | existsNext φ ih =>
      intro s
      constructor
      · rintro ⟨run, h0, hrun, hpath⟩
        obtain ⟨label, hstep⟩ := hrun 0
        rw [pathSat_next, pathSat_state_shift] at hpath
        refine ⟨label, run 1, ?_, ?_⟩
        · rw [← h0]
          exact hstep
        · exact (ih (s := run 1)).mp hpath
      · rintro ⟨label, t, hstep, hsat⟩
        have hfin : LTS.FiniteRun (lts := lts) (fun n => if n = 0 then s else t) 1 := by
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          exact ⟨label, hstep⟩
        obtain ⟨run, hagree, hrun⟩ :=
          CTL.exists_omegaRun_extending_of_serial hser hfin
        refine ⟨run, ?_, hrun, ?_⟩
        · show run 0 = s
          rw [hagree 0 (by omega)]
          rfl
        · rw [pathSat_next, pathSat_state_shift, hagree 1 (by omega)]
          exact (ih (s := t)).mpr hsat
  | existsUntil φ ψ ihφ ihψ =>
      intro s
      constructor
      · rintro ⟨run, h0, hrun, k, hsat, hbefore⟩
        rw [pathSat_state_shift] at hsat
        refine ⟨run, k, h0, LTS.omegaRun_finiteRun hrun, ?_, ?_⟩
        · exact (ihψ (s := run k)).mp hsat
        · intro j hj
          have hb := hbefore j hj
          rw [pathSat_state_shift] at hb
          exact (ihφ (s := run j)).mp hb
      · rintro ⟨ss, k, h0, hfin, hsat, hbefore⟩
        obtain ⟨run, hagree, hrun⟩ :=
          CTL.exists_omegaRun_extending_of_serial hser hfin
        refine ⟨run, ?_, hrun, k, ?_, ?_⟩
        · show run 0 = s
          rw [hagree 0 (by omega)]
          exact h0
        · rw [pathSat_state_shift, hagree k (by omega)]
          exact (ihψ (s := ss k)).mpr hsat
        · intro j hj
          rw [pathSat_state_shift, hagree j (by omega)]
          exact (ihφ (s := ss j)).mpr (hbefore j hj)
  | existsGlobally φ ih =>
      intro s
      constructor
      · rintro ⟨run, h0, hrun, hpath⟩
        refine ⟨run, h0, hrun, fun i => ?_⟩
        have hall := (pathSat_always (lts := lts) (valuation := valuation)
          (π := .state (embedCTL φ)) (run := run)).mp hpath i
        rw [pathSat_state_shift] at hall
        exact (ih (s := run i)).mp hall
      · rintro ⟨ss, h0, hrun, hall⟩
        refine ⟨ss, h0, hrun, ?_⟩
        rw [pathSat_always]
        intro i
        rw [pathSat_state_shift]
        exact (ih (s := ss i)).mpr (hall i)
  | forallUntil φ ψ ihφ ihψ =>
      intro s
      constructor
      · intro hall
        refine ⟨?_, ?_⟩
        · intro ss h0 hrun
          obtain ⟨k, hsat, hbefore⟩ := hall ss h0 hrun
          refine ⟨k, ?_, ?_⟩
          · rw [pathSat_state_shift] at hsat
            exact (ihψ (s := ss k)).mp hsat
          · intro j hj
            have hb := hbefore j hj
            rw [pathSat_state_shift] at hb
            exact (ihφ (s := ss j)).mp hb
        · intro ss k _ _ hdead
          obtain ⟨label, t, hstep⟩ := hser (ss k)
          exact (hdead label t hstep).elim
      · intro hall run h0 hrun
        obtain ⟨k, hsat, hbefore⟩ := (hall.1 run h0 hrun)
        refine ⟨k, ?_, ?_⟩
        · rw [pathSat_state_shift]
          exact (ihψ (s := run k)).mpr hsat
        · intro j hj
          rw [pathSat_state_shift]
          exact (ihφ (s := run j)).mpr (hbefore j hj)

/-- The toggle system: every transition flips the state. -/
def toggleLTS : _root_.Cslib.LTS Bool Unit where
  Tr := fun s _ t => t = !s

/-- The valuation: `p` holds exactly at `true`. -/
def toggleValuation : Bool → Unit → Prop := fun s _ => s = true

/-- The toggle system is serial: every state has a successor. -/
theorem toggle_serial : CTL.Serial toggleLTS := by
  intro s
  exact ⟨(), !s, rfl⟩

/-- The alternating run of the toggle system: `false, true, false,
true, ...`, defined by recursion so each step flips the state. -/
def toggleRun : ℕ → Bool
  | 0 => false
  | n + 1 => !toggleRun n

/-- `E G F p` holds at `false` in the toggle system: the alternating
run visits `true` at every other position. This example makes no claim
of an expressiveness separation. -/
theorem toggle_egf_p :
    StateSat toggleLTS toggleValuation
      (.exists (.alwaysPath (.until (.state .top) (.state (.atom ())))))
      false := by
  refine ⟨toggleRun, rfl, ?_, ?_⟩
  · intro i
    exact ⟨(), rfl⟩
  · rw [pathSat_always]
    intro i
    cases hi : toggleRun i with
    | true =>
        refine ⟨0, ?_, fun j _ => True.intro⟩
        rw [pathSat_state]
        simp only [shiftSeq_apply_zero]
        exact hi
    | false =>
        refine ⟨1, ?_, fun j _ => True.intro⟩
        rw [pathSat_state, Semantics.shiftSeq_add, shiftSeq_apply_zero]
        change !toggleRun i = true
        rw [hi]
        rfl
end CTLStar
end Cslib

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear temporal logic
-/
module

public import CSLibExt.Foundations.Semantics.LTS.OmegaRun
public import CSLibExt.Logics.LTL.Syntax

/-!
# Linear temporal logic over state sequences

Linear temporal logic (LTL) is interpreted over a single infinite sequence
of states (a run).  Atoms are interpreted by a valuation on states, and the
temporal operators `next` and `until` move along suffixes of the run
(`Cslib.Semantics.shiftSeq`).  The file also gives the LTS-level notions of
satisfaction over all, respectively some, infinite runs from a state.  No
automata-theoretic (Büchi) characterisation is included.

The syntax lives in `CSLibExt.Logics.LTL.Syntax`; the same formulas are interpreted over
canonical CSLib ω-words in `CSLibExt.Logics.LTL.OmegaWord`, and
`CSLibExt.Logics.LTL.OmegaWordBridge` shows the two semantics agree.
The run-level `Satisfies`/`SatisfiesAt` API here is the primary interface for run-based
reasoning: the bakery and induction developments prove against the recursive definition and the
`shiftSeq` lemmas. Clients that need the canonical ω-word form convert through
`Cslib.LTL.satisfies_iff_word_satisfies` and `Cslib.LTL.satisfiesAt_iff_word_satisfiesAt`, so any
run-level result transports to the canonical form by rewriting with those equivalences.
-/

@[expose] public section

namespace Cslib
namespace LTL

universe u

variable {Atom : Type u}

/-- Satisfaction of an LTL formula on a run under a valuation of atoms on
states.  The temporal operators recurse on suffixes of the run. -/
def Satisfies {State : Type*} (valuation : State → Atom → Prop)
    (run : ℕ → State) : Formula Atom → Prop
  | .atom a => valuation (run 0) a
  | .top => True
  | .not φ => ¬ Satisfies valuation run φ
  | .and φ ψ => Satisfies valuation run φ ∧ Satisfies valuation run ψ
  | .next φ => Satisfies valuation (Semantics.shiftSeq run 1) φ
  | .until φ ψ =>
      ∃ k, Satisfies valuation (Semantics.shiftSeq run k) ψ ∧
        ∀ j, j < k → Satisfies valuation (Semantics.shiftSeq run j) φ

/-- Satisfaction at position `k` of a run, i.e. satisfaction on the suffix
starting at `k`. -/
def SatisfiesAt {State : Type*} (valuation : State → Atom → Prop)
    (run : ℕ → State) (k : ℕ) (φ : Formula Atom) : Prop :=
  Satisfies valuation (Semantics.shiftSeq run k) φ

namespace Satisfies

variable {State : Type*} {valuation : State → Atom → Prop} {run : ℕ → State}
  {φ ψ : Formula Atom} {a : Atom}

theorem atom_iff :
    Satisfies valuation run (.atom a) ↔ valuation (run 0) a := Iff.rfl

theorem top_iff :
    Satisfies valuation run (.top : Formula Atom) ↔ True := Iff.rfl

theorem not_iff :
    Satisfies valuation run (.not φ) ↔ ¬ Satisfies valuation run φ := Iff.rfl

theorem and_iff :
    Satisfies valuation run (.and φ ψ) ↔
      Satisfies valuation run φ ∧ Satisfies valuation run ψ := Iff.rfl

theorem next_iff :
    Satisfies valuation run (.next φ) ↔ SatisfiesAt valuation run 1 φ :=
  Iff.rfl

theorem until_iff :
    Satisfies valuation run (.until φ ψ) ↔
      ∃ k, SatisfiesAt valuation run k ψ ∧
        ∀ j, j < k → SatisfiesAt valuation run j φ := Iff.rfl

theorem or_iff :
    Satisfies valuation run (Formula.or φ ψ) ↔
      Satisfies valuation run φ ∨ Satisfies valuation run ψ := by
  change ¬ (¬ Satisfies valuation run φ ∧ ¬ Satisfies valuation run ψ) ↔ _
  constructor
  · intro h
    refine Classical.byCases (fun hφ => Or.inl hφ) (fun hφ => ?_)
    exact Or.inr (Classical.byContradiction fun hψ => h ⟨hφ, hψ⟩)
  · rintro (hφ | hψ) ⟨hnφ, hnψ⟩
    · exact hnφ hφ
    · exact hnψ hψ

theorem imp_iff :
    Satisfies valuation run (Formula.imp φ ψ) ↔
      (Satisfies valuation run φ → Satisfies valuation run ψ) := by
  change Satisfies valuation run (Formula.or (.not φ) ψ) ↔ _
  rw [or_iff, not_iff]
  constructor
  · rintro (hnφ | hψ) hφ
    · exact (hnφ hφ).elim
    · exact hψ
  · intro h
    exact Classical.byCases (fun hφ => Or.inr (h hφ)) (fun hφ => Or.inl hφ)

theorem iff_iff :
    Satisfies valuation run (Formula.iff φ ψ) ↔
      (Satisfies valuation run φ ↔ Satisfies valuation run ψ) := by
  change Satisfies valuation run
      (.and (Formula.imp φ ψ) (Formula.imp ψ φ)) ↔ _
  rw [and_iff, imp_iff, imp_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem bot_iff :
    Satisfies valuation run (Formula.bot : Formula Atom) ↔ False := by
  change ¬ True ↔ False
  exact ⟨fun h => h trivial, False.elim⟩

/-- An atom at position `k` is the valuation at the `k`-th state. -/
theorem atomAt_iff {k : ℕ} :
    SatisfiesAt valuation run k (.atom a) ↔ valuation (run k) a := by
  change valuation (run (0 + k)) a ↔ valuation (run k) a
  rw [Nat.zero_add]

/-- The expansion law for `until`: either the target holds now, or the
guard holds now and the `until` is postponed by one step. -/
theorem until_expansion :
    Satisfies valuation run (.until φ ψ) ↔
      Satisfies valuation run ψ ∨
        (Satisfies valuation run φ ∧
          Satisfies valuation run (.next (.until φ ψ))) := by
  constructor
  · rintro ⟨k, hψ, hφ⟩
    cases k with
    | zero =>
        left
        rwa [Semantics.shiftSeq_zero] at hψ
    | succ k =>
        right
        have hφ0 : Satisfies valuation run φ := by
          have h0 := hφ 0 (Nat.zero_lt_succ k)
          rwa [Semantics.shiftSeq_zero] at h0
        refine ⟨hφ0, ⟨k, ?_, ?_⟩⟩
        · rw [Semantics.shiftSeq_add]
          have h1k : (1 + k) = k + 1 := by omega
          rw [h1k]
          exact hψ
        · intro j hj
          rw [Semantics.shiftSeq_add]
          have h1j : (1 + j) = j + 1 := by omega
          rw [h1j]
          exact hφ (j + 1) (by omega)
  · rintro (hψ | ⟨hφ, hnext⟩)
    · refine ⟨0, ?_, fun j hj => (Nat.not_lt_zero j hj).elim⟩
      rw [Semantics.shiftSeq_zero]
      exact hψ
    · obtain ⟨k, hψ, hφs⟩ := hnext
      refine ⟨k + 1, ?_, ?_⟩
      · rw [Semantics.shiftSeq_add] at hψ
        have h1k : (1 + k) = k + 1 := by omega
        rwa [h1k] at hψ
      · intro j hj
        cases j with
        | zero =>
            rw [Semantics.shiftSeq_zero]
            exact hφ
        | succ j =>
            have hj' : j < k := by omega
            have h := hφs j hj'
            rw [Semantics.shiftSeq_add] at h
            have h1j : (1 + j) = j + 1 := by omega
            rw [h1j] at h
            exact h

theorem eventually_iff :
    Satisfies valuation run (Formula.eventually φ) ↔
      ∃ k, SatisfiesAt valuation run k φ := by
  constructor
  · rintro ⟨k, hk, _⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk, fun _ _ => trivial⟩

theorem always_iff :
    Satisfies valuation run (Formula.always φ) ↔
      ∀ k, SatisfiesAt valuation run k φ := by
  change ¬ Satisfies valuation run (Formula.eventually (.not φ)) ↔ _
  rw [eventually_iff]
  constructor
  · intro h k
    exact Classical.byContradiction fun hn => h ⟨k, hn⟩
  · intro h hcon
    obtain ⟨k, hk⟩ := hcon
    exact hk (h k)

theorem always_and :
    Satisfies valuation run (Formula.always (.and φ ψ)) ↔
      Satisfies valuation run (Formula.always φ) ∧
        Satisfies valuation run (Formula.always ψ) := by
  rw [always_iff, always_iff, always_iff]
  constructor
  · intro h
    exact ⟨fun k => (and_iff.mp (h k)).1, fun k => (and_iff.mp (h k)).2⟩
  · rintro ⟨hφ, hψ⟩ k
    exact and_iff.mpr ⟨hφ k, hψ k⟩

theorem eventually_or :
    Satisfies valuation run (Formula.eventually (Formula.or φ ψ)) ↔
      Satisfies valuation run (Formula.eventually φ) ∨
        Satisfies valuation run (Formula.eventually ψ) := by
  rw [eventually_iff, eventually_iff, eventually_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases or_iff.mp hk with hφ | hψ
    · exact Or.inl ⟨k, hφ⟩
    · exact Or.inr ⟨k, hψ⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨k, or_iff.mpr (Or.inl hk)⟩
    · exact ⟨k, or_iff.mpr (Or.inr hk)⟩

end Satisfies

/-- `φ` holds on every infinite run of `lts` starting at `state`.  This is
vacuously true when no infinite run starts at `state`, for instance at a
deadlocked state with no outgoing transitions. -/
def ForallRuns {State Label : Type*} (lts : _root_.Cslib.LTS State Label)
    (valuation : State → Atom → Prop) (state : State) (φ : Formula Atom) :
    Prop :=
  ∀ run, run 0 = state → Cslib.LTS.OmegaRun (lts := lts) run → Satisfies valuation run φ

/-- `φ` holds on some infinite run of `lts` starting at `state`. -/
def ExistsRun {State Label : Type*} (lts : _root_.Cslib.LTS State Label)
    (valuation : State → Atom → Prop) (state : State) (φ : Formula Atom) :
    Prop :=
  ∃ run, run 0 = state ∧ Cslib.LTS.OmegaRun (lts := lts) run ∧ Satisfies valuation run φ

theorem forallRuns_always_atom {State Label : Type*}
    {lts : _root_.Cslib.LTS State Label} {valuation : State → Atom → Prop}
    {s : State} {a : Atom} :
    ForallRuns lts valuation s (Formula.always (.atom a)) ↔
      ∀ run, run 0 = s → Cslib.LTS.OmegaRun (lts := lts) run →
        ∀ i, valuation (run i) a := by
  constructor
  · intro h run hr0 hrun i
    exact Satisfies.atomAt_iff.mp
      (Satisfies.always_iff.mp (h run hr0 hrun) i)
  · intro h run hr0 hrun
    rw [Satisfies.always_iff]
    intro i
    exact Satisfies.atomAt_iff.mpr (h run hr0 hrun i)

/-- Safety from reachability: if an atom holds at every state reachable
from `s`, it holds always on every infinite run from `s`. -/
theorem forallRuns_always_atom_of_reachable {State Label : Type*}
    {lts : _root_.Cslib.LTS State Label} {valuation : State → Atom → Prop}
    {s : State} {a : Atom}
    (h : ∀ t, lts.CanReach s t → valuation t a) :
    ForallRuns lts valuation s (Formula.always (.atom a)) := by
  rw [forallRuns_always_atom]
  intro run hr0 hrun i
  apply h
  have hreach := Cslib.LTS.canReach_omegaRun_apply hrun i
  rwa [hr0] at hreach

/-- If every state reachable from `s` lies on some infinite run from `s`, and the atom holds
at every position of every infinite run from `s`, then the atom holds at every state
reachable from `s`. This is the converse of `forallRuns_always_atom_of_reachable` under that
extra hypothesis, which is needed: no infinite run starts at a deadlocked state, so
`ForallRuns` is vacuous there. -/
theorem reachable_of_forallRuns_always_atom {State Label : Type*}
    {lts : _root_.Cslib.LTS State Label} {valuation : State → Atom → Prop}
    {s : State} {a : Atom}
    (hex : ∀ t, lts.CanReach s t →
      ∃ run, run 0 = s ∧ Cslib.LTS.OmegaRun (lts := lts) run ∧ ∃ i, run i = t)
    (h : ForallRuns lts valuation s (Formula.always (.atom a))) :
    ∀ t, lts.CanReach s t → valuation t a := by
  intro t ht
  obtain ⟨run, hr0, hrun, i, hi⟩ := hex t ht
  rw [forallRuns_always_atom] at h
  rw [← hi]
  exact h run hr0 hrun i

theorem existsRun_eventually_atom {State Label : Type*}
    {lts : _root_.Cslib.LTS State Label} {valuation : State → Atom → Prop}
    {s : State} {a : Atom} :
    ExistsRun lts valuation s (Formula.eventually (.atom a)) ↔
      ∃ t, valuation t a ∧
        ∃ run, run 0 = s ∧ Cslib.LTS.OmegaRun (lts := lts) run ∧ ∃ i, run i = t := by
  constructor
  · rintro ⟨run, hr0, hrun, hev⟩
    obtain ⟨i, hi⟩ := Satisfies.eventually_iff.mp hev
    exact ⟨run i, Satisfies.atomAt_iff.mp hi, run, hr0, hrun, i, rfl⟩
  · rintro ⟨t, ht, run, hr0, hrun, i, rfl⟩
    exact ⟨run, hr0, hrun,
      Satisfies.eventually_iff.mpr ⟨i, Satisfies.atomAt_iff.mpr ht⟩⟩

end LTL
end Cslib

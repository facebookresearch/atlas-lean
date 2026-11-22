/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Computation tree logic over labelled transition systems
-/
module

public import CSLibExt.Foundations.Semantics.LTS.OmegaRun
public import Mathlib.Order.FixedPoints

/-!
# Computation tree logic

Formulas and state satisfaction for CTL in the `EX`/`EU`/`EG`/`AU`
basis (cf. Huth and Ryan, *Logic in Computer Science*), with semantics
over an arbitrary labelled transition system from
`CSLibExt.Foundations.Semantics.LTS`.  The system may have deadlocked
states and may have infinitely many states; `AX` is vacuously true at a
deadlock, and `EG` quantifies over infinite runs (`LTS.OmegaRun`), so
`EG φ` fails at states that start no infinite run.

The universal operators use maximal-path semantics: a maximal path is
either an infinite run or a finite run ending at a deadlocked state.
`A[φ U ψ]` therefore requires `ψ` to occur, with `φ` before it, on every
infinite run and on every finite deadlocked run, and `AF φ` is
`A[⊤ U φ]`.  On systems with deadlocks the classical duality
translations of `AU` and `AF` through `EU` and `EG` are unsound: at a
deadlocked state with `φ` true and `ψ` false, `¬E[¬ψ U (¬φ ∧ ¬ψ)]` and
`¬EG ¬ψ` both hold (the unique maximal path has no `¬φ ∧ ¬ψ` position,
and it is not infinite), yet that path never reaches
`ψ`.  `AU` is accordingly a primitive constructor here, not a derived
translation.  The classical translations are recovered on serial
systems (every state has a successor) by
`Satisfies.forallFinally_iff_not_existsGlobally_not_of_serial` and
`Satisfies.forallUntil_iff_classical_of_serial`.  `AG` remains
`¬EF ¬φ`, which is correct at deadlocks: it constrains reachable
states only.

The main results are the fixed-point characterizations of `EF` and `EG`:
`EF φ` holds exactly on the least fixed point of
`Z ↦ ⟦φ⟧ ∪ PreExists Z`, and `EG φ` holds exactly on the greatest fixed
point of `Z ↦ ⟦φ⟧ ∩ PreExists Z`, where `PreExists` is the existential
predecessor operator.  The finite-state model checker built on this
semantics is in `CSLibExt.Logics.CTL.ModelChecking`.

The direction from the greatest fixed point to `EG` builds an infinite
run by repeated choice of successors and therefore depends on
`Classical.choice`.  No incomplete proof occurs in this file; the only
non-constructive dependency is that choice principle (together with the
usual `propext` and `Quot.sound` from Mathlib).
-/

@[expose] public section

namespace Cslib
namespace CTL

universe u

/-- Formulas of computation tree logic over a type of atoms, in the
basis `top`, negation, conjunction, `EX`, `EU`, `EG`, and `AU`.  `AU` is
primitive rather than the classical `EU`/`EG` translation, which is
unsound on transition systems with deadlocked states. -/
inductive Formula (Atom : Type u) : Type u where
  | atom (a : Atom) : Formula Atom
  | top : Formula Atom
  | not (φ : Formula Atom) : Formula Atom
  | and (φ ψ : Formula Atom) : Formula Atom
  | existsNext (φ : Formula Atom) : Formula Atom
  | existsUntil (φ ψ : Formula Atom) : Formula Atom
  | existsGlobally (φ : Formula Atom) : Formula Atom
  | forallUntil (φ ψ : Formula Atom) : Formula Atom

namespace Formula

variable {Atom : Type u}

/-- Falsity, as the negation of truth. -/
def bot : Formula Atom := .not .top

/-- Disjunction, by De Morgan duality. -/
def or (φ ψ : Formula Atom) : Formula Atom :=
  .not (.and (.not φ) (.not ψ))

/-- Implication, via disjunction. -/
def imp (φ ψ : Formula Atom) : Formula Atom := or (.not φ) ψ

/-- Bi-implication, as mutual implication. -/
def iff (φ ψ : Formula Atom) : Formula Atom :=
  .and (imp φ ψ) (imp ψ φ)

/-- `EF φ`: some reachable state satisfies `φ`. -/
def existsFinally (φ : Formula Atom) : Formula Atom :=
  .existsUntil .top φ

/-- `AX φ`: every successor state satisfies `φ`. -/
def forallNext (φ : Formula Atom) : Formula Atom :=
  .not (.existsNext (.not φ))

/-- `AF φ`: every maximal path reaches a state satisfying `φ`, as
`A[⊤ U φ]`. -/
def forallFinally (φ : Formula Atom) : Formula Atom :=
  .forallUntil .top φ

/-- `AG φ`: every reachable state satisfies `φ`. -/
def forallGlobally (φ : Formula Atom) : Formula Atom :=
  .not (existsFinally (.not φ))

end Formula

variable {State Label Atom : Type*}
variable {lts : LTS State Label}
variable {valuation : State → Atom → Prop}

/-- Satisfaction of a CTL formula at a state of a labelled transition
system, relative to an atom valuation.  `existsUntil φ ψ` is witnessed by
a finite run prefix ending at a `ψ`-state, with `φ` at all earlier
states; `existsGlobally φ` is witnessed by an infinite run on which `φ`
holds everywhere.  `forallUntil φ ψ` quantifies over maximal paths:
every infinite run and every finite run ending at a deadlocked state
reaches a `ψ`-state, with `φ` at all earlier states. -/
def Satisfies (lts : LTS State Label)
    (valuation : State → Atom → Prop) (state : State) :
    Formula Atom → Prop
  | .atom a => valuation state a
  | .top => True
  | .not φ => ¬Satisfies lts valuation state φ
  | .and φ ψ =>
      Satisfies lts valuation state φ ∧ Satisfies lts valuation state ψ
  | .existsNext φ =>
      ∃ label next, lts.Tr state label next ∧
        Satisfies lts valuation next φ
  | .existsUntil φ ψ =>
      ∃ ss k, ss 0 = state ∧ lts.FiniteRun ss k ∧
        Satisfies lts valuation (ss k) ψ ∧
          ∀ j, j < k → Satisfies lts valuation (ss j) φ
  | .existsGlobally φ =>
      ∃ ss, ss 0 = state ∧ lts.OmegaRun ss ∧
        ∀ i, Satisfies lts valuation (ss i) φ
  | .forallUntil φ ψ =>
      (∀ ss, ss 0 = state → lts.OmegaRun ss →
        ∃ k, Satisfies lts valuation (ss k) ψ ∧
          ∀ j, j < k → Satisfies lts valuation (ss j) φ) ∧
      (∀ ss k, ss 0 = state → lts.FiniteRun ss k →
        (∀ label t, ¬lts.Tr (ss k) label t) →
        ∃ j, j ≤ k ∧ Satisfies lts valuation (ss j) ψ ∧
          ∀ i, i < j → Satisfies lts valuation (ss i) φ)

/-- The existential predecessor operator: `s` satisfies `PreExists lts Z`
when some successor of `s` satisfies `Z`. -/
def PreExists (lts : LTS State Label) (Z : State → Prop)
    (s : State) : Prop :=
  ∃ label t, lts.Tr s label t ∧ Z t

/-- A transition system is serial (total) when every state has a
successor, so there are no deadlocked states and every maximal path is
infinite. -/
def Serial (lts : LTS State Label) : Prop :=
  ∀ s, ∃ label t, lts.Tr s label t

/-- In a serial system, every finite run extends to an infinite run
agreeing with it up to its endpoint.  The extension iterates a chosen
successor function from the endpoint, so it depends on
`Classical.choice`. -/
theorem exists_omegaRun_extending_of_serial (hser : Serial lts)
    {ss : ℕ → State} {k : ℕ} (hrun : lts.FiniteRun ss k) :
    ∃ ss', (∀ i, i ≤ k → ss' i = ss i) ∧ lts.OmegaRun ss' := by
  have hsucc : ∀ x : State, ∃ y, ∃ label, lts.Tr x label y := by
    intro x
    obtain ⟨label, t, hstep⟩ := hser x
    exact ⟨t, label, hstep⟩
  obtain ⟨next, hnext⟩ : ∃ f : State → State,
      ∀ x, ∃ label, lts.Tr x label (f x) :=
    ⟨fun x => Classical.choose (hsucc x),
      fun x => Classical.choose_spec (hsucc x)⟩
  obtain ⟨lab, hlab⟩ : ∃ g : State → Label,
      ∀ x, lts.Tr x (g x) (next x) :=
    ⟨fun x => Classical.choose (hnext x),
      fun x => Classical.choose_spec (hnext x)⟩
  let ss' : ℕ → State :=
    fun i => if i < k then ss i else next^[i - k] (ss k)
  have hagree : ∀ i, i ≤ k → ss' i = ss i := by
    intro i hi
    change (if i < k then ss i else next^[i - k] (ss k)) = ss i
    by_cases hik : i < k
    · simp [hik]
    · have hik' : i = k := by omega
      simp [hik']
  have htail : ∀ i, k ≤ i → ss' i = next^[i - k] (ss k) := by
    intro i hi
    change (if i < k then ss i else next^[i - k] (ss k)) =
      next^[i - k] (ss k)
    have hik : ¬i < k := by omega
    simp [hik]
  refine ⟨ss', hagree, ?_⟩
  intro i
  by_cases hik : i < k
  · rw [hagree i (by omega), hagree (i + 1) (by omega)]
    exact hrun i hik
  · rw [htail i (by omega), htail (i + 1) (by omega)]
    refine ⟨lab (next^[i - k] (ss k)), ?_⟩
    have hidx : i + 1 - k = (i - k) + 1 := by omega
    rw [hidx, Function.iterate_succ_apply']
    exact hlab _

namespace Satisfies

variable {s : State} {φ ψ : Formula Atom} {a : Atom}

@[simp]
theorem atom_iff : Satisfies lts valuation s (.atom a) ↔ valuation s a :=
  Iff.rfl

@[simp]
theorem top_iff : Satisfies lts valuation s .top ↔ True := Iff.rfl

@[simp]
theorem not_iff :
    Satisfies lts valuation s (.not φ) ↔ ¬Satisfies lts valuation s φ :=
  Iff.rfl

@[simp]
theorem and_iff : Satisfies lts valuation s (.and φ ψ) ↔
    Satisfies lts valuation s φ ∧ Satisfies lts valuation s ψ := Iff.rfl

@[simp]
theorem existsNext_iff :
    Satisfies lts valuation s (.existsNext φ) ↔
      ∃ label next, lts.Tr s label next ∧
        Satisfies lts valuation next φ := Iff.rfl

@[simp]
theorem existsUntil_iff :
    Satisfies lts valuation s (.existsUntil φ ψ) ↔
      ∃ ss k, ss 0 = s ∧ lts.FiniteRun ss k ∧
        Satisfies lts valuation (ss k) ψ ∧
          ∀ j, j < k → Satisfies lts valuation (ss j) φ := Iff.rfl

@[simp]
theorem existsGlobally_iff :
    Satisfies lts valuation s (.existsGlobally φ) ↔
      ∃ ss, ss 0 = s ∧ lts.OmegaRun ss ∧
        ∀ i, Satisfies lts valuation (ss i) φ := Iff.rfl

@[simp]
theorem forallUntil_iff :
    Satisfies lts valuation s (.forallUntil φ ψ) ↔
      (∀ ss, ss 0 = s → lts.OmegaRun ss →
        ∃ k, Satisfies lts valuation (ss k) ψ ∧
          ∀ j, j < k → Satisfies lts valuation (ss j) φ) ∧
      (∀ ss k, ss 0 = s → lts.FiniteRun ss k →
        (∀ label t, ¬lts.Tr (ss k) label t) →
        ∃ j, j ≤ k ∧ Satisfies lts valuation (ss j) ψ ∧
          ∀ i, i < j → Satisfies lts valuation (ss i) φ) := Iff.rfl

theorem bot_iff :
    Satisfies lts valuation s (Formula.bot : Formula Atom) ↔ False := by
  simp [Formula.bot]

theorem or_iff : Satisfies lts valuation s (φ.or ψ) ↔
    Satisfies lts valuation s φ ∨ Satisfies lts valuation s ψ := by
  change ¬(¬Satisfies lts valuation s φ ∧
      ¬Satisfies lts valuation s ψ) ↔ _
  constructor
  · intro h
    exact Classical.byCases Or.inl
      (fun hφ => Or.inr (Classical.byContradiction (fun hψ => h ⟨hφ, hψ⟩)))
  · rintro (hφ | hψ) ⟨hnotφ, hnotψ⟩
    · exact hnotφ hφ
    · exact hnotψ hψ

theorem imp_iff : Satisfies lts valuation s (φ.imp ψ) ↔
    (Satisfies lts valuation s φ → Satisfies lts valuation s ψ) := by
  rw [Formula.imp, or_iff, not_iff]
  constructor
  · rintro (h | h) hφ
    · exact absurd hφ h
    · exact h
  · intro h
    exact Classical.byCases (fun hφ => Or.inr (h hφ)) Or.inl

theorem iff_iff : Satisfies lts valuation s (φ.iff ψ) ↔
    (Satisfies lts valuation s φ ↔ Satisfies lts valuation s ψ) := by
  rw [Formula.iff, and_iff, imp_iff, imp_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- `EF φ` unfolds to `E[⊤ U φ]`: a finite run prefix to a `φ`-state. -/
theorem existsFinally_iff :
    Satisfies lts valuation s φ.existsFinally ↔
      ∃ ss k, ss 0 = s ∧ lts.FiniteRun ss k ∧
        Satisfies lts valuation (ss k) φ := by
  rw [Formula.existsFinally, existsUntil_iff]
  constructor
  · rintro ⟨ss, k, h0, hrun, hφ, -⟩
    exact ⟨ss, k, h0, hrun, hφ⟩
  · rintro ⟨ss, k, h0, hrun, hφ⟩
    exact ⟨ss, k, h0, hrun, hφ, fun _ _ => trivial⟩

/-- The one-step expansion of `E[φ U ψ]`: either `ψ` holds now, or `φ`
holds now and `E[φ U ψ]` holds at some successor. -/
theorem existsUntil_expansion :
    Satisfies lts valuation s (.existsUntil φ ψ) ↔
      Satisfies lts valuation s ψ ∨
        (Satisfies lts valuation s φ ∧
          Satisfies lts valuation s (.existsNext (.existsUntil φ ψ))) := by
  constructor
  · rintro ⟨ss, k, h0, hrun, hψ, hφ⟩
    cases k with
    | zero =>
        exact Or.inl (h0 ▸ hψ)
    | succ n =>
        right
        have hφs : Satisfies lts valuation s φ := h0 ▸ hφ 0 (by omega)
        obtain ⟨label, hstep⟩ := hrun 0 (by omega)
        rw [h0] at hstep
        refine ⟨hφs, label, ss 1, hstep, ?_⟩
        refine ⟨Semantics.shiftSeq ss 1, n, rfl, ?_, ?_, ?_⟩
        · have hrun' : lts.FiniteRun ss (1 + n) := by
            have hcomm : (1 : ℕ) + n = n + 1 := by omega
            rwa [hcomm]
          exact LTS.finiteRun_shift hrun'
        · change Satisfies lts valuation (ss (n + 1)) ψ
          exact hψ
        · intro j hj
          change Satisfies lts valuation (ss (j + 1)) φ
          exact hφ (j + 1) (by omega)
  · rintro (hψ | ⟨hφs, label, next, hstep, ss, k, h0, hrun, hψ, hφ⟩)
    · refine ⟨fun _ => s, 0, rfl, LTS.finiteRun_zero, hψ, ?_⟩
      intro j hj
      exact (Nat.not_lt_zero j hj).elim
    · refine ⟨fun i => match i with | 0 => s | i + 1 => ss i, k + 1,
        rfl, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            refine ⟨label, ?_⟩
            change lts.Tr s label (ss 0)
            rw [h0]
            exact hstep
        | succ i =>
            exact hrun i (by omega)
      · change Satisfies lts valuation (ss k) ψ
        exact hψ
      · intro j hj
        cases j with
        | zero => exact hφs
        | succ j =>
            change Satisfies lts valuation (ss j) φ
            exact hφ j (by omega)

/-- `EF φ` holds exactly when some reachable state satisfies `φ`. -/
theorem existsFinally_iff_reachable :
    Satisfies lts valuation s φ.existsFinally ↔
      ∃ t, lts.CanReach s t ∧ Satisfies lts valuation t φ := by
  rw [existsFinally_iff]
  constructor
  · rintro ⟨ss, k, h0, hrun, hφ⟩
    refine ⟨ss k, ?_, hφ⟩
    have hreach := LTS.finiteRun_canReach hrun
    rwa [h0] at hreach
  · rintro ⟨t, hreach, hφ⟩
    obtain ⟨ss, k, h0, hk, hrun⟩ :=
      LTS.exists_finiteRun_of_canReach hreach
    exact ⟨ss, k, h0, hrun, hk ▸ hφ⟩

/-- `AG φ` holds exactly when every reachable state satisfies `φ`. -/
theorem forallGlobally_iff_reachable :
    Satisfies lts valuation s φ.forallGlobally ↔
      ∀ t, lts.CanReach s t → Satisfies lts valuation t φ := by
  change ¬Satisfies lts valuation s (φ.not).existsFinally ↔ _
  rw [existsFinally_iff_reachable]
  constructor
  · intro h t hreach
    exact Classical.byContradiction (fun hnot => h ⟨t, hreach, hnot⟩)
  · rintro h ⟨t, hreach, hnot⟩
    exact hnot (h t hreach)

/-- `AX φ` holds exactly when every successor state satisfies `φ`. -/
theorem forallNext_iff :
    Satisfies lts valuation s φ.forallNext ↔
      ∀ label t, lts.Tr s label t → Satisfies lts valuation t φ := by
  change ¬(∃ label next, lts.Tr s label next ∧
      ¬Satisfies lts valuation next φ) ↔ _
  constructor
  · intro h label t hstep
    exact Classical.byContradiction
      (fun hnot => h ⟨label, t, hstep, hnot⟩)
  · rintro h ⟨label, t, hstep, hnot⟩
    exact hnot (h label t hstep)

/-- `AF φ` unfolds to `A[⊤ U φ]`: `φ` occurs on every infinite run and
on every finite run ending at a deadlocked state. -/
theorem forallFinally_iff_omega_and_finite :
    Satisfies lts valuation s φ.forallFinally ↔
      (∀ ss, ss 0 = s → lts.OmegaRun ss →
        ∃ k, Satisfies lts valuation (ss k) φ) ∧
      (∀ ss k, ss 0 = s → lts.FiniteRun ss k →
        (∀ label t, ¬lts.Tr (ss k) label t) →
        ∃ j, j ≤ k ∧ Satisfies lts valuation (ss j) φ) := by
  change Satisfies lts valuation s (.forallUntil .top φ) ↔ _
  rw [forallUntil_iff]
  constructor
  · rintro ⟨homega, hfinite⟩
    refine ⟨fun ss h0 hrun => ?_, fun ss k h0 hrun hdead => ?_⟩
    · obtain ⟨k, hk, -⟩ := homega ss h0 hrun
      exact ⟨k, hk⟩
    · obtain ⟨j, hjk, hj, -⟩ := hfinite ss k h0 hrun hdead
      exact ⟨j, hjk, hj⟩
  · rintro ⟨homega, hfinite⟩
    refine ⟨fun ss h0 hrun => ?_, fun ss k h0 hrun hdead => ?_⟩
    · obtain ⟨k, hk⟩ := homega ss h0 hrun
      exact ⟨k, hk, fun _ _ => trivial⟩
    · obtain ⟨j, hjk, hj⟩ := hfinite ss k h0 hrun hdead
      exact ⟨j, hjk, hj, fun _ _ => trivial⟩

/-- At a deadlocked state, `A[φ U ψ]` reduces to `ψ`: the infinite-run
condition is vacuous (an infinite run needs a step at index `0`), and
the constant finite run of length `0` forces `ψ` at the state itself. -/
theorem forallUntil_deadlock
    (hdead : ∀ label t, ¬lts.Tr s label t) :
    Satisfies lts valuation s (.forallUntil φ ψ) ↔
      Satisfies lts valuation s ψ := by
  rw [forallUntil_iff]
  constructor
  · intro h
    obtain ⟨j, hjk, hψ, -⟩ :=
      h.2 (fun _ => s) 0 rfl LTS.finiteRun_zero hdead
    have hj : j = 0 := by omega
    subst hj
    exact hψ
  · intro hψ
    constructor
    · intro ss h0 hrun
      obtain ⟨label, hstep⟩ := hrun 0
      rw [h0] at hstep
      exact (hdead label _ hstep).elim
    · intro ss k h0 _ _
      exact ⟨0, Nat.zero_le k, h0 ▸ hψ,
        fun i hi => (Nat.not_lt_zero i hi).elim⟩

/-- At a deadlocked state, `AF φ` reduces to `φ`. -/
theorem forallFinally_deadlock
    (hdead : ∀ label t, ¬lts.Tr s label t) :
    Satisfies lts valuation s φ.forallFinally ↔
      Satisfies lts valuation s φ := by
  change Satisfies lts valuation s (.forallUntil .top φ) ↔ _
  exact forallUntil_deadlock hdead

/-- On a serial system there are no finite deadlocked runs, so `AF`
recovers its classical form `¬EG ¬φ`. -/
theorem forallFinally_iff_not_existsGlobally_not_of_serial
    (hser : Serial lts) :
    Satisfies lts valuation s φ.forallFinally ↔
      ¬Satisfies lts valuation s (.existsGlobally (.not φ)) := by
  rw [forallFinally_iff_omega_and_finite]
  constructor
  · rintro ⟨homega, -⟩ ⟨ss, h0, hrun, hall⟩
    obtain ⟨k, hk⟩ := homega ss h0 hrun
    exact hall k hk
  · intro h
    constructor
    · intro ss h0 hrun
      exact Classical.byContradiction
        (fun hcon => h ⟨ss, h0, hrun, fun i hi => hcon ⟨i, hi⟩⟩)
    · intro ss k _ _ hdead
      obtain ⟨label, t, hstep⟩ := hser (ss k)
      exact (hdead label t hstep).elim

/-- On a serial system, `A[φ U ψ]` recovers its classical form: it is
not the case that either `¬ψ` holds until `¬φ ∧ ¬ψ` holds, or `¬ψ`
holds forever.  The forward direction extends an `EU` witness to an
infinite run; the backward direction takes, on each infinite run, the
least `ψ`-position and derives an `EU` witness from any earlier
`¬φ`-position. -/
theorem forallUntil_iff_classical_of_serial (hser : Serial lts) :
    Satisfies lts valuation s (.forallUntil φ ψ) ↔
      ¬(Satisfies lts valuation s
          (.existsUntil (.not ψ) (.and (.not φ) (.not ψ))) ∨
        Satisfies lts valuation s (.existsGlobally (.not ψ))) := by
  rw [forallUntil_iff]
  constructor
  · rintro ⟨homega, -⟩ (hEU | hEG)
    · obtain ⟨ss, k, h0, hrun, ⟨hnotφ, hnotψ⟩, hbefore⟩ := hEU
      obtain ⟨ss', hagree, hω⟩ :=
        exists_omegaRun_extending_of_serial hser hrun
      have h0' : ss' 0 = s := by
        rw [hagree 0 (Nat.zero_le k)]
        exact h0
      obtain ⟨m, hψm, hφm⟩ := homega ss' h0' hω
      by_cases hmk : m ≤ k
      · have hnotψm : ¬Satisfies lts valuation (ss m) ψ := by
          rcases lt_or_eq_of_le hmk with hlt | heq
          · exact hbefore m hlt
          · rw [heq]
            exact hnotψ
        rw [hagree m hmk] at hψm
        exact hnotψm hψm
      · have hφk := hφm k (by omega)
        rw [hagree k (by omega)] at hφk
        exact hnotφ hφk
    · obtain ⟨ss, h0, hrun, hall⟩ := hEG
      obtain ⟨m, hψm, -⟩ := homega ss h0 hrun
      exact hall m hψm
  · intro h
    constructor
    · intro ss h0 hrun
      classical
      by_cases hnone : ∀ i, ¬Satisfies lts valuation (ss i) ψ
      · exact (h (Or.inr ⟨ss, h0, hrun, hnone⟩)).elim
      · have hex : ∃ i, Satisfies lts valuation (ss i) ψ :=
          Classical.byContradiction
            (fun hcon => hnone (fun i hi => hcon ⟨i, hi⟩))
        have key : ∀ n, Satisfies lts valuation (ss n) ψ →
            ∃ k, Satisfies lts valuation (ss k) ψ ∧
              ∀ i, i < k → ¬Satisfies lts valuation (ss i) ψ := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
              intro hn
              by_cases hsmaller : ∃ i, i < n ∧
                  Satisfies lts valuation (ss i) ψ
              · obtain ⟨i, hi, hsat⟩ := hsmaller
                exact ih i hi hsat
              · exact ⟨n, hn, fun i hi hisat =>
                  hsmaller ⟨i, hi, hisat⟩⟩
        obtain ⟨k0, hk0⟩ := hex
        obtain ⟨k, hkψ, hkmin⟩ := key k0 hk0
        refine ⟨k, hkψ, fun j hjk => ?_⟩
        exact Classical.byContradiction (fun hnotφ => h (Or.inl
          ⟨ss, j, h0, LTS.omegaRun_finiteRun hrun,
            ⟨hnotφ, hkmin j hjk⟩,
            fun i hi => hkmin i (by omega)⟩))
    · intro ss k _ _ hdead
      obtain ⟨label, t, hstep⟩ := hser (ss k)
      exact (hdead label t hstep).elim

/-- The one-step expansion of `EF φ`. -/
theorem existsFinally_expansion :
    Satisfies lts valuation s φ.existsFinally ↔
      Satisfies lts valuation s φ ∨
        Satisfies lts valuation s (.existsNext φ.existsFinally) := by
  rw [Formula.existsFinally, existsUntil_expansion]
  simp only [top_iff, true_and]

/-- The one-step expansion of `EG φ`: `φ` holds now and `EG φ` holds at
some successor.  Both directions are direct manipulations of infinite
runs; no choice is needed here. -/
theorem existsGlobally_expansion :
    Satisfies lts valuation s (.existsGlobally φ) ↔
      Satisfies lts valuation s φ ∧
        Satisfies lts valuation s (.existsNext (.existsGlobally φ)) := by
  constructor
  · rintro ⟨ss, h0, hrun, hall⟩
    obtain ⟨label, hstep⟩ := hrun 0
    refine ⟨h0 ▸ hall 0, label, ss 1, h0 ▸ hstep, ?_⟩
    exact ⟨Semantics.shiftSeq ss 1, rfl,
      LTS.omegaRun_shift hrun 1, fun i => hall (i + 1)⟩
  · rintro ⟨hφs, label, next, hstep, ss, h0, hrun, hall⟩
    refine ⟨fun i => match i with | 0 => s | i + 1 => ss i, rfl, ?_, ?_⟩
    · intro i
      cases i with
      | zero =>
          refine ⟨label, ?_⟩
          change lts.Tr s label (ss 0)
          rw [h0]
          exact hstep
      | succ i => exact hrun i
    · intro i
      cases i with
      | zero => exact hφs
      | succ i =>
          change Satisfies lts valuation (ss i) φ
          exact hall i

/-- The functional whose least fixed point is `EF φ`. -/
def existsFinallyFun (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ : Formula Atom)
    (Z : State → Prop) : State → Prop :=
  fun s => Satisfies lts valuation s φ ∨ PreExists lts Z s

theorem existsFinallyFun_mono (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Monotone (existsFinallyFun lts valuation φ) := by
  intro Z₁ Z₂ hle s hs
  rcases hs with h | ⟨label, t, hstep, hZ⟩
  · exact Or.inl h
  · exact Or.inr ⟨label, t, hstep, hle t hZ⟩

/-- The `EF` functional packaged as a monotone operator. -/
def existsFinallyOrderHom (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    (State → Prop) →o (State → Prop) :=
  ⟨existsFinallyFun lts valuation φ, existsFinallyFun_mono lts valuation φ⟩

@[simp]
theorem existsFinallyOrderHom_apply (φ : Formula Atom) (Z : State → Prop) :
    existsFinallyOrderHom lts valuation φ Z =
      existsFinallyFun lts valuation φ Z := rfl

/-- The functional whose greatest fixed point is `EG φ`. -/
def existsGloballyFun (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ : Formula Atom)
    (Z : State → Prop) : State → Prop :=
  fun s => Satisfies lts valuation s φ ∧ PreExists lts Z s

theorem existsGloballyFun_mono (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Monotone (existsGloballyFun lts valuation φ) := by
  intro Z₁ Z₂ hle s hs
  obtain ⟨hφ, label, t, hstep, hZ⟩ := hs
  exact ⟨hφ, label, t, hstep, hle t hZ⟩

/-- The `EG` functional packaged as a monotone operator. -/
def existsGloballyOrderHom (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    (State → Prop) →o (State → Prop) :=
  ⟨existsGloballyFun lts valuation φ, existsGloballyFun_mono lts valuation φ⟩

@[simp]
theorem existsGloballyOrderHom_apply (φ : Formula Atom) (Z : State → Prop) :
    existsGloballyOrderHom lts valuation φ Z =
      existsGloballyFun lts valuation φ Z := rfl

/-- `EF φ` is the least fixed point of `Z ↦ ⟦φ⟧ ∪ PreExists Z`.  The
inclusion of the fixed point in `EF φ` is Park induction, using the
one-step expansion of `EF`; the other inclusion is induction on a trace
to a `φ`-state, unfolding the fixed point once per step. -/
theorem existsFinally_eq_lfp (φ : Formula Atom) :
    (fun s => Satisfies lts valuation s φ.existsFinally) =
      (existsFinallyOrderHom lts valuation φ).lfp := by
  apply le_antisymm
  · intro s hs
    rw [existsFinally_iff_reachable] at hs
    obtain ⟨t, ⟨labels, htrace⟩, hφ⟩ := hs
    have key : ∀ {a b : State} {labels : List Label},
        lts.MTr a labels b → Satisfies lts valuation b φ →
          (existsFinallyOrderHom lts valuation φ).lfp a := by
      intro a b labels htr
      induction htr with
      | refl =>
          intro hφstate
          rw [← OrderHom.map_lfp (existsFinallyOrderHom lts valuation φ)]
          exact Or.inl hφstate
      | stepL head tail ih =>
          intro hφtarget
          rw [← OrderHom.map_lfp (existsFinallyOrderHom lts valuation φ)]
          exact Or.inr ⟨_, _, head, ih hφtarget⟩
    exact key htrace hφ
  · apply OrderHom.lfp_le
    intro s hs
    exact existsFinally_expansion.mpr hs

/-- `EG φ` is the greatest fixed point of `Z ↦ ⟦φ⟧ ∩ PreExists Z`.  The
inclusion of `EG φ` in the fixed point is coinduction (`OrderHom.le_gfp`),
using the one-step expansion of `EG`.  The other inclusion builds an
infinite run by iterating a chosen successor function on the subtype of
fixed-point states; that step uses `Classical.choice`, so this theorem
depends on the choice axiom. -/
theorem existsGlobally_eq_gfp (φ : Formula Atom) :
    (fun s => Satisfies lts valuation s (.existsGlobally φ)) =
      (existsGloballyOrderHom lts valuation φ).gfp := by
  apply le_antisymm
  · apply OrderHom.le_gfp
    intro s hs
    exact existsGlobally_expansion.mp hs
  · intro s hs
    have hfix : ∀ x : State,
        (existsGloballyOrderHom lts valuation φ).gfp x →
          Satisfies lts valuation x φ ∧
            ∃ label t, lts.Tr x label t ∧
              (existsGloballyOrderHom lts valuation φ).gfp t := by
      intro x hx
      have hmem : existsGloballyOrderHom lts valuation φ
          (existsGloballyOrderHom lts valuation φ).gfp x := by
        rw [OrderHom.map_gfp]
        exact hx
      exact hmem
    have hsucc : ∀ x : {x : State //
        (existsGloballyOrderHom lts valuation φ).gfp x},
        ∃ y : {x : State //
          (existsGloballyOrderHom lts valuation φ).gfp x},
          ∃ label, lts.Tr x.1 label y.1 := by
      rintro ⟨x, hx⟩
      obtain ⟨-, label, t, hstep, ht⟩ := hfix x hx
      exact ⟨⟨t, ht⟩, label, hstep⟩
    obtain ⟨next, hnext⟩ : ∃ f : {x : State //
        (existsGloballyOrderHom lts valuation φ).gfp x} →
          {x : State // (existsGloballyOrderHom lts valuation φ).gfp x},
          ∀ x, ∃ label, lts.Tr x.1 label (f x).1 :=
      ⟨fun x => Classical.choose (hsucc x),
        fun x => Classical.choose_spec (hsucc x)⟩
    obtain ⟨lab, hlab⟩ : ∃ g : {x : State //
        (existsGloballyOrderHom lts valuation φ).gfp x} → Label,
          ∀ x, lts.Tr x.1 (g x) (next x).1 :=
      ⟨fun x => Classical.choose (hnext x),
        fun x => Classical.choose_spec (hnext x)⟩
    refine ⟨fun n => (next^[n] ⟨s, hs⟩).1, rfl, ?_, ?_⟩
    · intro i
      refine ⟨lab (next^[i] ⟨s, hs⟩), ?_⟩
      change lts.Tr (next^[i] ⟨s, hs⟩).1 _ (next^[i + 1] ⟨s, hs⟩).1
      rw [Function.iterate_succ_apply']
      exact hlab _
    · intro i
      exact (hfix _ (next^[i] ⟨s, hs⟩).2).1

end Satisfies

end CTL
end Cslib

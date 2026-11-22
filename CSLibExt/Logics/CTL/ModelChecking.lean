/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-state model checking for CTL
-/
module

public import CSLibExt.Logics.CTL.Basic
public import MathlibExt.Order.FixedPoints.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Finite-state model checking for CTL

A decision procedure for CTL satisfaction on finite labelled transition
systems, continuing `CSLibExt.Logics.CTL.Basic`.  For every formula `φ`,
`sat lts valuation φ` computes the finite set of states satisfying `φ`,
and `mem_sat` proves membership in that set equivalent to `Satisfies`.
The existential until and globally fragments are computed by iterating
their monotone `Finset` functionals `Fintype.card State` times from `∅`
respectively `Finset.univ`; the iteration has stabilized by then, by a
cardinality argument on the strictly monotone chain (`Finset.lfpFin_fixed`,
`Finset.gfpFin_fixed`), and a bridge lemma identifies the finite iterates with
the iterates of the predicate functionals whose fixed points
`existsUntil_eq_lfp` and `Satisfies.existsGlobally_eq_gfp` characterize
satisfaction.

The universal until fragment is computed through the deadlock-correct
duality `Satisfies.forallUntil_iff_not`: on systems with deadlocked
states, `A[φ U ψ]` is the negation of `EG ¬ψ` and of
`E[¬ψ U (¬ψ ∧ (¬φ ∨ ¬EX ⊤))]`, where the `¬EX ⊤` disjunct catches finite
maximal paths ending at a deadlock before reaching `ψ`.  The classical
translation without that disjunct is unsound at deadlocks (see the
documentation of `CSLibExt.Logics.CTL.Basic`).

No CTL and no model checker exists upstream in `leanprover/cslib` at the
pinned revision `5b56df99362532c46e1175381fbbdd755bd56030` (its `Logics`
directory has HML, LinearLogic, Modal, and Propositional only), so this
file is new with `CSLibExt`, as is `Basic`.

The correctness proof `mem_sat` depends on `Classical.choice`, inherited
from the greatest-fixed-point characterization of `EG` in `Basic` and
from the construction of a maximal path in `exists_maximalPath`.  The
algorithm `sat` itself is computable under the stated decidability
hypotheses, and `check` packages it as a `Bool`-valued decision
procedure with a `Decidable` instance for `Satisfies`.
-/

@[expose] public section

namespace Cslib
namespace CTL

section Duality

variable {State Label Atom : Type*}
variable {lts : LTS State Label}
variable {valuation : State → Atom → Prop}

/-- Some index attaining `p` is least such. -/
private theorem exists_minimal_index {p : ℕ → Prop} (hex : ∃ n, p n) :
    ∃ k, p k ∧ ∀ i, i < k → ¬p i := by
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex,
    fun i hi => Nat.find_min hex hi⟩

/-- Every state starts a maximal path: either an infinite run, or a
finite run ending at a deadlocked state.  The path iterates a chosen
successor function, stopping being impossible unless a deadlock is
reached; the construction depends on `Classical.choice`. -/
theorem exists_maximalPath (s : State) :
    (∃ ss, ss 0 = s ∧ lts.OmegaRun ss) ∨
      (∃ ss k, ss 0 = s ∧ lts.FiniteRun ss k ∧
        ∀ label t, ¬lts.Tr (ss k) label t) := by
  classical
  have hchoice : ∀ x : State, (∃ label t, lts.Tr x label t) →
      ∃ t, ∃ label, lts.Tr x label t :=
    fun x ⟨label, t, hstep⟩ => ⟨t, label, hstep⟩
  let next : State → State := fun x =>
    if h : ∃ label t, lts.Tr x label t then
      Classical.choose (hchoice x h)
    else x
  have hnext : ∀ x, (∃ label t, lts.Tr x label t) →
      ∃ label, lts.Tr x label (next x) := by
    intro x hx
    have hnx : next x = Classical.choose (hchoice x hx) := dite_eq_left hx
    rw [hnx]
    exact Classical.choose_spec (hchoice x hx)
  by_cases hdead : ∃ k, ∀ label t, ¬lts.Tr (next^[k] s) label t
  · obtain ⟨k, hk⟩ := hdead
    obtain ⟨k₀, hk₀, hk₀min⟩ := exists_minimal_index
      (p := fun k => ∀ label t, ¬lts.Tr (next^[k] s) label t) ⟨k, hk⟩
    have hmin : ∀ m, m < k₀ → ∃ label t, lts.Tr (next^[m] s) label t := by
      intro m hm
      by_contra hcon
      push Not at hcon
      exact hk₀min m hm hcon
    refine Or.inr ⟨fun n => next^[n] s, k₀, rfl, ?_, hk₀⟩
    intro i hi
    obtain ⟨label, hstep⟩ := hnext _ (hmin i hi)
    refine ⟨label, ?_⟩
    show lts.Tr (next^[i] s) label (next^[i + 1] s)
    rwa [Function.iterate_succ_apply']
  · refine Or.inl ⟨fun n => next^[n] s, rfl, ?_⟩
    intro i
    have hsucc : ∃ label t, lts.Tr (next^[i] s) label t := by
      by_contra hcon
      push Not at hcon
      exact hdead ⟨i, hcon⟩
    obtain ⟨label, hstep⟩ := hnext _ hsucc
    refine ⟨label, ?_⟩
    show lts.Tr (next^[i] s) label (next^[i + 1] s)
    rwa [Function.iterate_succ_apply']

namespace Satisfies

/-- `¬EX ⊤` holds exactly at deadlocked states. -/
theorem not_existsNext_top_iff {s : State} :
    Satisfies lts valuation s (.not (.existsNext .top)) ↔
      ∀ label t, ¬lts.Tr s label t := by
  show ¬(∃ label t, lts.Tr s label t ∧ True) ↔ _
  constructor
  · intro h label t hstep
    exact h ⟨label, t, hstep, trivial⟩
  · rintro h ⟨label, t, hstep, -⟩
    exact h label t hstep

/-- The bad target of the deadlock-correct `AU` duality: `¬ψ` holds and
either `φ` fails or the state is deadlocked. -/
theorem forallUntil_bad_iff {φ ψ : Formula Atom} {t : State} :
    Satisfies lts valuation t
        (.and (.not ψ) (Formula.or (.not φ) (.not (.existsNext .top)))) ↔
      ¬Satisfies lts valuation t ψ ∧
        (¬Satisfies lts valuation t φ ∨
          ∀ label u, ¬lts.Tr t label u) := by
  rw [and_iff, or_iff, not_existsNext_top_iff, not_iff, not_iff]

/-- The forward direction of the one-step expansion of `A[φ U ψ]`: if
`ψ` does not hold now, then `φ` holds now, the state is not deadlocked,
and `A[φ U ψ]` holds at every successor.  Successor instances are
proved by prepending the step to maximal paths from the successor;
`φ` at the current state is read off any one maximal path
(`exists_maximalPath`), whose first `ψ`-index is positive. -/
theorem forallUntil_expansion_forward {s : State} {φ ψ : Formula Atom}
    (hAU : Satisfies lts valuation s (.forallUntil φ ψ)) :
    Satisfies lts valuation s ψ ∨
      (Satisfies lts valuation s φ ∧ (∃ label t, lts.Tr s label t) ∧
        ∀ label t, lts.Tr s label t →
          Satisfies lts valuation t (.forallUntil φ ψ)) := by
  classical
  by_cases hψ : Satisfies lts valuation s ψ
  · exact Or.inl hψ
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · obtain ⟨homega, hfinite⟩ := forallUntil_iff.mp hAU
      rcases exists_maximalPath (lts := lts) s with
        ⟨ss, h0, hrun⟩ | ⟨ss, k, h0, hrun, hdead⟩
      · obtain ⟨j, hψj, hφj⟩ := homega ss h0 hrun
        have hj : j ≠ 0 := fun hj0 => hψ (h0 ▸ hj0 ▸ hψj)
        have hφ0 := hφj 0 (Nat.pos_of_ne_zero hj)
        rwa [h0] at hφ0
      · obtain ⟨j, -, hψj, hφj⟩ := hfinite ss k h0 hrun hdead
        have hj : j ≠ 0 := fun hj0 => hψ (h0 ▸ hj0 ▸ hψj)
        have hφ0 := hφj 0 (Nat.pos_of_ne_zero hj)
        rwa [h0] at hφ0
    · by_contra hcon
      push Not at hcon
      exact hψ ((forallUntil_deadlock hcon).mp hAU)
    · intro label t hstep
      obtain ⟨homega, hfinite⟩ := forallUntil_iff.mp hAU
      rw [forallUntil_iff]
      constructor
      · intro ss h0 hrun
        set tt : ℕ → State :=
          fun i => match i with | 0 => s | i + 1 => ss i with htt
        have httrun : lts.OmegaRun tt := by
          intro i
          cases i with
          | zero =>
              refine ⟨label, ?_⟩
              show lts.Tr s label (ss 0)
              rw [h0]
              exact hstep
          | succ i => exact hrun i
        obtain ⟨k, hψk, hφk⟩ := homega tt rfl httrun
        have hk : k ≠ 0 := by
          rintro rfl
          exact hψ hψk
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact ⟨k', hψk, fun j hj => hφk (j + 1) (by omega)⟩
      · intro ss k h0 hrun hdead
        set tt : ℕ → State :=
          fun i => match i with | 0 => s | i + 1 => ss i with htt
        have httrun : lts.FiniteRun tt (k + 1) := by
          intro i hi
          cases i with
          | zero =>
              refine ⟨label, ?_⟩
              show lts.Tr s label (ss 0)
              rw [h0]
              exact hstep
          | succ i => exact hrun i (by omega)
        obtain ⟨j, hjk, hψj, hφj⟩ := hfinite tt (k + 1) rfl httrun hdead
        have hj : j ≠ 0 := by
          rintro rfl
          exact hψ hψj
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        exact ⟨j', by omega, hψj, fun i hi => hφj (i + 1) (by omega)⟩

/-- The deadlock-correct duality for `A[φ U ψ]`: it fails exactly when
some maximal path either stays in `¬ψ` forever (`EG ¬ψ`) or reaches a
`¬ψ`-state at which `φ` fails or which is deadlocked, with `¬ψ` before
(an `EU` witness to the bad target of `forallUntil_bad_iff`).  The
forward direction propagates `A[φ U ψ]` along an `EU` witness run by
`forallUntil_expansion_forward`; the backward direction takes, on each
maximal path, the least `ψ`-index and an earlier `¬φ`-index if one
exists, and uses the deadlocked endpoint when a finite maximal path
never reaches `ψ`. -/
theorem forallUntil_iff_not {s : State} {φ ψ : Formula Atom} :
    Satisfies lts valuation s (.forallUntil φ ψ) ↔
      ¬(Satisfies lts valuation s
          (.existsUntil (.not ψ)
            (.and (.not ψ)
              (Formula.or (.not φ) (.not (.existsNext .top))))) ∨
        Satisfies lts valuation s (.existsGlobally (.not ψ))) := by
  classical
  constructor
  · intro hAU
    rintro (hEU | hEG)
    · obtain ⟨ss, k, h0, hrun, hχk, hside⟩ := hEU
      have hprop : ∀ i, i ≤ k →
          Satisfies lts valuation (ss i) (.forallUntil φ ψ) := by
        intro i
        induction i with
        | zero =>
            intro _
            rwa [h0]
        | succ i ih =>
            intro hi
            have hAUi := ih (by omega)
            have hnotψi : ¬Satisfies lts valuation (ss i) ψ :=
              hside i (by omega)
            rcases forallUntil_expansion_forward hAUi with
              hψi | ⟨-, -, hsuccs⟩
            · exact (hnotψi hψi).elim
            · obtain ⟨label, hstep⟩ := hrun i (by omega)
              exact hsuccs label _ hstep
      have hAUk := hprop k le_rfl
      obtain ⟨hnotψk, hbad⟩ := forallUntil_bad_iff.mp hχk
      rcases forallUntil_expansion_forward hAUk with
        hψk | ⟨hφk, hsucc, -⟩
      · exact hnotψk hψk
      · rcases hbad with hnotφ | hdead
        · exact hnotφ hφk
        · obtain ⟨label, t, hstep⟩ := hsucc
          exact hdead label t hstep
    · obtain ⟨ss, h0, hrun, hall⟩ := hEG
      obtain ⟨homega, -⟩ := forallUntil_iff.mp hAU
      obtain ⟨k, hψk, -⟩ := homega ss h0 hrun
      exact hall k hψk
  · intro hnot
    rw [forallUntil_iff]
    constructor
    · intro ss h0 hrun
      by_contra hcon
      apply hnot
      by_cases hnone : ∀ i, ¬Satisfies lts valuation (ss i) ψ
      · exact Or.inr ⟨ss, h0, hrun, hnone⟩
      · have hex : ∃ i, Satisfies lts valuation (ss i) ψ :=
          Classical.byContradiction
            (fun hcon2 => hnone (fun i hi => hcon2 ⟨i, hi⟩))
        obtain ⟨k, hψk, hkmin⟩ := exists_minimal_index hex
        have hnotall : ¬∀ j, j < k → Satisfies lts valuation (ss j) φ :=
          fun hall => hcon ⟨k, hψk, hall⟩
        have hexbad : ∃ j, j < k ∧ ¬Satisfies lts valuation (ss j) φ := by
          by_contra hcon2
          apply hnotall
          intro j hj
          exact Classical.byContradiction
            (fun hnφ => hcon2 ⟨j, hj, hnφ⟩)
        obtain ⟨j0, hj0k, hnotφ⟩ := hexbad
        refine Or.inl ⟨ss, j0, h0,
          LTS.omegaRun_finiteRun hrun, ?_, ?_⟩
        · exact forallUntil_bad_iff.mpr ⟨hkmin j0 hj0k, Or.inl hnotφ⟩
        · intro i hi
          exact hkmin i (by omega)
    · intro ss k h0 hrun hdead
      by_contra hcon
      apply hnot
      by_cases hsome : ∃ i, Satisfies lts valuation (ss i) ψ ∧ i ≤ k
      · obtain ⟨k₀, ⟨hψk₀, hk₀le⟩, hk₀min⟩ := exists_minimal_index hsome
        have hmin' : ∀ i, i < k₀ → ¬Satisfies lts valuation (ss i) ψ :=
          fun i hi hψi => hk₀min i hi ⟨hψi, by omega⟩
        have hnotall : ¬∀ j, j < k₀ → Satisfies lts valuation (ss j) φ :=
          fun hall => hcon ⟨k₀, hk₀le, hψk₀, hall⟩
        have hexbad : ∃ j, j < k₀ ∧ ¬Satisfies lts valuation (ss j) φ := by
          by_contra hcon2
          apply hnotall
          intro j hj
          exact Classical.byContradiction
            (fun hnφ => hcon2 ⟨j, hj, hnφ⟩)
        obtain ⟨j0, hj0k, hnotφ⟩ := hexbad
        refine Or.inl ⟨ss, j0, h0,
          LTS.finiteRun_mono hrun (by omega), ?_, ?_⟩
        · exact forallUntil_bad_iff.mpr ⟨hmin' j0 hj0k, Or.inl hnotφ⟩
        · intro i hi
          exact hmin' i (by omega)
      · have hnoψ : ∀ i, i ≤ k → ¬Satisfies lts valuation (ss i) ψ :=
          fun i hi hψi => hsome ⟨i, hψi, hi⟩
        by_cases hbad : ∃ j, j ≤ k ∧ ¬Satisfies lts valuation (ss j) φ
        · obtain ⟨j0, hj0le, hnotφ⟩ := hbad
          refine Or.inl ⟨ss, j0, h0,
            LTS.finiteRun_mono hrun hj0le, ?_, ?_⟩
          · exact forallUntil_bad_iff.mpr
              ⟨hnoψ j0 hj0le, Or.inl hnotφ⟩
          · intro i hi
            exact hnoψ i (by omega)
        · refine Or.inl ⟨ss, k, h0, hrun, ?_, ?_⟩
          · exact forallUntil_bad_iff.mpr
              ⟨hnoψ k le_rfl, Or.inr hdead⟩
          · intro i hi
            exact hnoψ i (by omega)

/-- `EU` is congruent in its target formula under pointwise
satisfaction equivalence. -/
theorem existsUntil_congr {ρ α β : Formula Atom}
    (h : ∀ t, Satisfies lts valuation t α ↔ Satisfies lts valuation t β)
    {s : State} :
    Satisfies lts valuation s (.existsUntil ρ α) ↔
      Satisfies lts valuation s (.existsUntil ρ β) := by
  constructor <;> rintro ⟨ss, k, h0, hrun, htgt, hside⟩
  · exact ⟨ss, k, h0, hrun, (h _).mp htgt, hside⟩
  · exact ⟨ss, k, h0, hrun, (h _).mpr htgt, hside⟩

/-- The deadlock-correct duality for `AF`, the case `φ = ⊤` of
`forallUntil_iff_not`: the bad target simplifies to `¬φ ∧ ¬EX ⊤`. -/
theorem forallFinally_iff_not {s : State} {φ : Formula Atom} :
    Satisfies lts valuation s φ.forallFinally ↔
      ¬(Satisfies lts valuation s
          (.existsUntil (.not φ)
            (.and (.not φ) (.not (.existsNext .top)))) ∨
        Satisfies lts valuation s (.existsGlobally (.not φ))) := by
  have hχ : ∀ t, Satisfies lts valuation t
        (.and (.not φ)
          (Formula.or (.not .top) (.not (.existsNext .top)))) ↔
      Satisfies lts valuation t
        (.and (.not φ) (.not (.existsNext .top))) := by
    intro t
    show (_ ∧ Satisfies lts valuation t
        (Formula.or (.not .top) (.not (.existsNext .top)))) ↔
          (_ ∧ Satisfies lts valuation t (.not (.existsNext .top)))
    rw [or_iff]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact (h2 trivial).elim
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩
  show Satisfies lts valuation s (.forallUntil .top φ) ↔ _
  rw [forallUntil_iff_not, existsUntil_congr hχ]

/-- `EX φ` is `PreExists` of the satisfaction predicate of `φ`. -/
theorem existsNext_iff_preExists {s : State} {φ : Formula Atom} :
    Satisfies lts valuation s (.existsNext φ) ↔
      PreExists lts (fun t => Satisfies lts valuation t φ) s := Iff.rfl

/-- The functional whose least fixed point is `E[φ U ψ]`. -/
def existsUntilFun (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ ψ : Formula Atom)
    (Z : State → Prop) : State → Prop :=
  fun s => Satisfies lts valuation s ψ ∨
    (Satisfies lts valuation s φ ∧ PreExists lts Z s)

theorem existsUntilFun_mono (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ ψ : Formula Atom) :
    Monotone (existsUntilFun lts valuation φ ψ) := by
  intro Z₁ Z₂ hle s hs
  rcases hs with h | ⟨hφ, label, t, hstep, hZ⟩
  · exact Or.inl h
  · exact Or.inr ⟨hφ, label, t, hstep, hle t hZ⟩

/-- The `EU` functional packaged as a monotone operator. -/
def existsUntilOrderHom (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ ψ : Formula Atom) :
    (State → Prop) →o (State → Prop) :=
  ⟨existsUntilFun lts valuation φ ψ,
    existsUntilFun_mono lts valuation φ ψ⟩

/-- `E[φ U ψ]` is the least fixed point of
`Z ↦ ⟦ψ⟧ ∪ (⟦φ⟧ ∩ PreExists Z)`.  The inclusion of the fixed point in
`E[φ U ψ]` is Park induction via `existsUntil_expansion`; the other
inclusion is induction on the length of the witnessing finite run,
unfolding the fixed point once per step. -/
theorem existsUntil_eq_lfp (φ ψ : Formula Atom) :
    (fun s => Satisfies lts valuation s (.existsUntil φ ψ)) =
      (existsUntilOrderHom lts valuation φ ψ).lfp := by
  apply le_antisymm
  · intro s hs
    obtain ⟨ss, k, h0, hrun, hψ, hφ⟩ := hs
    have key : ∀ (k : ℕ) (ss : ℕ → State), lts.FiniteRun ss k →
        Satisfies lts valuation (ss k) ψ →
        (∀ j, j < k → Satisfies lts valuation (ss j) φ) →
        (existsUntilOrderHom lts valuation φ ψ).lfp (ss 0) := by
      intro k
      induction k with
      | zero =>
          intro ss _ hψ _
          rw [← OrderHom.map_lfp (existsUntilOrderHom lts valuation φ ψ)]
          exact Or.inl hψ
      | succ n ih =>
          intro ss hrun hψ hφ
          rw [← OrderHom.map_lfp (existsUntilOrderHom lts valuation φ ψ)]
          refine Or.inr ⟨hφ 0 (Nat.zero_lt_succ n), ?_⟩
          obtain ⟨label, hstep⟩ := hrun 0 (Nat.zero_lt_succ n)
          refine ⟨label, ss 1, hstep, ?_⟩
          have hrun' : lts.FiniteRun ss (1 + n) := by
            have hcomm : (1 : ℕ) + n = n + 1 := by omega
            rwa [hcomm]
          exact ih (Semantics.shiftSeq ss 1)
            (LTS.finiteRun_shift hrun') hψ
            (fun j hj => hφ (j + 1) (by omega))
    have hs0 := key k ss hrun hψ hφ
    rwa [h0] at hs0
  · apply OrderHom.lfp_le
    intro s hs
    exact existsUntil_expansion.mpr hs

end Satisfies

end Duality

section Checker

variable {State Label Atom : Type*}

variable [Fintype State]

variable [Fintype Label] {lts : LTS State Label}
  {valuation : State → Atom → Prop}
variable [∀ s μ t, Decidable (lts.Tr s μ t)]

/-- The finite existential predecessor set: states with a step into
`Z`.  It computes `PreExists` of the membership predicate of `Z`
(`mem_preExistsFin`). -/
def preExistsFin (lts : LTS State Label)
    [∀ s μ t, Decidable (lts.Tr s μ t)] (Z : Finset State) :
    Finset State :=
  Finset.univ.filter (fun s => ∃ μ, ∃ t ∈ Z, lts.Tr s μ t)

theorem mem_preExistsFin {Z : Finset State} {s : State} :
    s ∈ preExistsFin lts Z ↔ PreExists lts (fun t => t ∈ Z) s := by
  show s ∈ Finset.univ.filter (fun s => ∃ μ, ∃ t ∈ Z, lts.Tr s μ t) ↔
    PreExists lts (fun t => t ∈ Z) s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨μ, t, htZ, hstep⟩
    exact ⟨μ, t, hstep, htZ⟩
  · rintro ⟨μ, t, hstep, htZ⟩
    exact ⟨μ, t, htZ, hstep⟩

theorem preExistsFin_mono {Z₁ Z₂ : Finset State} (h : Z₁ ⊆ Z₂) :
    preExistsFin lts Z₁ ⊆ preExistsFin lts Z₂ := by
  intro s hs
  rw [mem_preExistsFin] at hs ⊢
  obtain ⟨μ, t, hstep, ht⟩ := hs
  exact ⟨μ, t, hstep, h ht⟩

variable [DecidableEq State]

/-- The finite set of states satisfying an existential until with side
set `A` and target set `B`, as the least fixed point of
`Z ↦ B ∪ (A ∩ preExistsFin Z)`. -/
def eUntilFin (lts : LTS State Label)
    [∀ s μ t, Decidable (lts.Tr s μ t)] (A B : Finset State) :
    Finset State :=
  Finset.lfpFin (fun Z => B ∪ (A ∩ preExistsFin lts Z))

/-- The finite set of states satisfying an existential globally with
set `A`, as the greatest fixed point of `Z ↦ A ∩ preExistsFin Z`. -/
def eGloballyFin (lts : LTS State Label)
    [∀ s μ t, Decidable (lts.Tr s μ t)] (A : Finset State) :
    Finset State :=
  Finset.gfpFin (fun Z => A ∩ preExistsFin lts Z)

theorem eUntilFin_fun_mono (lts : LTS State Label)
    [∀ s μ t, Decidable (lts.Tr s μ t)] (A B : Finset State) :
    Monotone (fun Z => B ∪ (A ∩ preExistsFin lts Z)) := by
  intro Z₁ Z₂ hZ
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.inter_subset_inter (Finset.Subset.refl _)
      (preExistsFin_mono hZ))

theorem eGloballyFin_fun_mono (lts : LTS State Label)
    [∀ s μ t, Decidable (lts.Tr s μ t)] (A : Finset State) :
    Monotone (fun Z => A ∩ preExistsFin lts Z) := by
  intro Z₁ Z₂ hZ
  exact Finset.inter_subset_inter (Finset.Subset.refl _)
    (preExistsFin_mono hZ)

/-- `eUntilFin` computes `E[φ U ψ]` from sets computing `φ` and `ψ`,
via `Finset.mem_lfpFin_iff_lfp` and `Satisfies.existsUntil_eq_lfp`. -/
theorem mem_eUntilFin_iff {A B : Finset State} {φ ψ : Formula Atom}
    (hA : ∀ t, t ∈ A ↔ Satisfies lts valuation t φ)
    (hB : ∀ t, t ∈ B ↔ Satisfies lts valuation t ψ) (s : State) :
    s ∈ eUntilFin lts A B ↔
      Satisfies lts valuation s (.existsUntil φ ψ) := by
  have hbridge : ∀ (Z : Finset State) (t : State),
      t ∈ (B ∪ (A ∩ preExistsFin lts Z)) ↔
        Satisfies.existsUntilFun lts valuation φ ψ
          (fun u => u ∈ Z) t := by
    intro Z t
    show t ∈ (B ∪ (A ∩ preExistsFin lts Z)) ↔
      (Satisfies lts valuation t ψ ∨
        (Satisfies lts valuation t φ ∧
          PreExists lts (fun u => u ∈ Z) t))
    rw [Finset.mem_union, Finset.mem_inter, hB t, hA t, mem_preExistsFin]
  have hconv := Finset.mem_lfpFin_iff_lfp
    (f := fun Z => B ∪ (A ∩ preExistsFin lts Z))
    (F := Satisfies.existsUntilFun lts valuation φ ψ)
    (eUntilFin_fun_mono lts A B)
    (Satisfies.existsUntilFun_mono lts valuation φ ψ) hbridge s
  have heq := congrFun (Satisfies.existsUntil_eq_lfp
    (lts := lts) (valuation := valuation) φ ψ) s
  exact hconv.trans (iff_of_eq heq).symm

/-- `eGloballyFin` computes `EG φ` from a set computing `φ`, via
`Finset.mem_gfpFin_iff_gfp` and `Satisfies.existsGlobally_eq_gfp`. -/
theorem mem_eGloballyFin_iff {A : Finset State} {φ : Formula Atom}
    (hA : ∀ t, t ∈ A ↔ Satisfies lts valuation t φ) (s : State) :
    s ∈ eGloballyFin lts A ↔
      Satisfies lts valuation s (.existsGlobally φ) := by
  have hbridge : ∀ (Z : Finset State) (t : State),
      t ∈ (A ∩ preExistsFin lts Z) ↔
        Satisfies.existsGloballyFun lts valuation φ
          (fun u => u ∈ Z) t := by
    intro Z t
    show t ∈ (A ∩ preExistsFin lts Z) ↔
      (Satisfies lts valuation t φ ∧
        PreExists lts (fun u => u ∈ Z) t)
    rw [Finset.mem_inter, hA t, mem_preExistsFin]
  have hconv := Finset.mem_gfpFin_iff_gfp
    (f := fun Z => A ∩ preExistsFin lts Z)
    (F := Satisfies.existsGloballyFun lts valuation φ)
    (eGloballyFin_fun_mono lts A)
    (Satisfies.existsGloballyFun_mono lts valuation φ) hbridge s
  have heq := congrFun (Satisfies.existsGlobally_eq_gfp
    (lts := lts) (valuation := valuation) φ) s
  exact hconv.trans (iff_of_eq heq).symm

variable [∀ s a, Decidable (valuation s a)]

/-- The set of states satisfying a CTL formula in a finite system,
computed by structural recursion: atoms by filtering the valuation,
`EX` by `preExistsFin`, `EU` and `EG` by the finite fixed points
`eUntilFin` and `eGloballyFin`, and `AU` by complementing the
deadlock-correct duality of `Satisfies.forallUntil_iff_not` (the
bad-target set is built from the complement sets of the subformulas
and `preExistsFin lts Finset.univ`, the set of non-deadlocked
states). -/
def sat (lts : LTS State Label)
    (valuation : State → Atom → Prop)
    [∀ s μ t, Decidable (lts.Tr s μ t)]
    [∀ s a, Decidable (valuation s a)] :
    Formula Atom → Finset State
  | .atom a => Finset.univ.filter (fun s => valuation s a)
  | .top => Finset.univ
  | .not φ => Finset.univ \ sat lts valuation φ
  | .and φ ψ => sat lts valuation φ ∩ sat lts valuation ψ
  | .existsNext φ => preExistsFin lts (sat lts valuation φ)
  | .existsUntil φ ψ =>
      eUntilFin lts (sat lts valuation φ) (sat lts valuation ψ)
  | .existsGlobally φ => eGloballyFin lts (sat lts valuation φ)
  | .forallUntil φ ψ =>
      let satφ := sat lts valuation φ
      let satψ := sat lts valuation ψ
      let notψ := Finset.univ \ satψ
      let badTarget := notψ ∩
        ((Finset.univ \ satφ) ∪
          (Finset.univ \ preExistsFin lts Finset.univ))
      Finset.univ \
        (eUntilFin lts notψ badTarget ∪ eGloballyFin lts notψ)

/-- Correctness of `sat`: membership in the computed set is
satisfaction.  The induction is on the formula; temporal cases go
through `mem_eUntilFin_iff` and `mem_eGloballyFin_iff`, and the
`AU` case additionally identifies the hand-written bad-target set
with satisfaction of the bad-target formula, via the induction
hypotheses and `mem_preExistsFin` at `Finset.univ` (membership there
is existence of a successor). -/
theorem mem_sat {φ : Formula Atom} {s : State} :
    s ∈ sat lts valuation φ ↔ Satisfies lts valuation s φ := by
  induction φ generalizing s with
  | atom a =>
      show s ∈ Finset.univ.filter (fun s => valuation s a) ↔
        Satisfies lts valuation s (.atom a)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
  | top =>
      show s ∈ (Finset.univ : Finset State) ↔
        Satisfies lts valuation s .top
      simp only [Finset.mem_univ]
      exact Iff.rfl
  | not φ ih =>
      show s ∈ Finset.univ \ sat lts valuation φ ↔
        Satisfies lts valuation s (.not φ)
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact not_congr ih
  | and φ ψ ihφ ihψ =>
      show s ∈ sat lts valuation φ ∩ sat lts valuation ψ ↔
        Satisfies lts valuation s (.and φ ψ)
      simp only [Finset.mem_inter]
      exact and_congr ihφ ihψ
  | existsNext φ ih =>
      show s ∈ preExistsFin lts (sat lts valuation φ) ↔
        Satisfies lts valuation s (.existsNext φ)
      rw [mem_preExistsFin, Satisfies.existsNext_iff]
      show (∃ label t, lts.Tr s label t ∧
          t ∈ sat lts valuation φ) ↔
        (∃ label t, lts.Tr s label t ∧
          Satisfies lts valuation t φ)
      constructor <;> rintro ⟨label, t, hstep, ht⟩
      · exact ⟨label, t, hstep, (ih (s := t)).mp ht⟩
      · exact ⟨label, t, hstep, (ih (s := t)).mpr ht⟩
  | existsUntil φ ψ ihφ ihψ =>
      show s ∈ eUntilFin lts (sat lts valuation φ)
          (sat lts valuation ψ) ↔
        Satisfies lts valuation s (.existsUntil φ ψ)
      exact mem_eUntilFin_iff (fun t => ihφ (s := t))
        (fun t => ihψ (s := t)) s
  | existsGlobally φ ih =>
      show s ∈ eGloballyFin lts (sat lts valuation φ) ↔
        Satisfies lts valuation s (.existsGlobally φ)
      exact mem_eGloballyFin_iff (fun t => ih (s := t)) s
  | forallUntil φ ψ ihφ ihψ =>
      have hA : ∀ t, t ∈ Finset.univ \ sat lts valuation ψ ↔
          Satisfies lts valuation t (.not ψ) := by
        intro t
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact not_congr (ihψ (s := t))
      have hbad : ∀ t, t ∈ (Finset.univ \ sat lts valuation ψ) ∩
            ((Finset.univ \ sat lts valuation φ) ∪
              (Finset.univ \ preExistsFin lts Finset.univ)) ↔
          Satisfies lts valuation t
            (.and (.not ψ)
              (Formula.or (.not φ) (.not (.existsNext .top)))) := by
        intro t
        rw [Satisfies.forallUntil_bad_iff]
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
          Finset.mem_union, true_and]
        rw [ihφ (s := t), ihψ (s := t)]
        refine and_congr Iff.rfl (or_congr Iff.rfl ?_)
        rw [mem_preExistsFin]
        constructor
        · intro h label u hstep
          exact h ⟨label, u, hstep, Finset.mem_univ u⟩
        · rintro h ⟨label, u, hstep, -⟩
          exact h label u hstep
      show s ∈ Finset.univ \
            (eUntilFin lts (Finset.univ \ sat lts valuation ψ)
                ((Finset.univ \ sat lts valuation ψ) ∩
                  ((Finset.univ \ sat lts valuation φ) ∪
                    (Finset.univ \ preExistsFin lts Finset.univ))) ∪
              eGloballyFin lts (Finset.univ \ sat lts valuation ψ)) ↔
          Satisfies lts valuation s (.forallUntil φ ψ)
      rw [Satisfies.forallUntil_iff_not]
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union,
        true_and]
      rw [mem_eUntilFin_iff hA hbad s, mem_eGloballyFin_iff hA s]

/-- The model checker as a boolean decision procedure: decide
membership in the computed satisfaction set. -/
def check (lts : LTS State Label)
    (valuation : State → Atom → Prop)
    [∀ s μ t, Decidable (lts.Tr s μ t)]
    [∀ s a, Decidable (valuation s a)] (s : State)
    (φ : Formula Atom) : Bool :=
  decide (s ∈ sat lts valuation φ)

theorem check_iff {s : State} {φ : Formula Atom} :
    check lts valuation s φ = true ↔ Satisfies lts valuation s φ := by
  show decide (s ∈ sat lts valuation φ) = true ↔ _
  rw [decide_eq_true_eq]
  exact mem_sat

/-- Satisfaction in a finite, decidable system is decidable, by
`mem_sat`. -/
instance {s : State} {φ : Formula Atom} :
    Decidable (Satisfies lts valuation s φ) :=
  decidable_of_iff (s ∈ sat lts valuation φ) mem_sat

end Checker

end CTL
end Cslib

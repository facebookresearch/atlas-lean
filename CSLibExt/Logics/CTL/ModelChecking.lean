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

/-- **Every state starts a maximal path.** In a labelled transition system, for every state $s$
there is an infinite run $s_0, s_1, s_2, \dots$ with $s_0 = s$, or there are a sequence of states
$s_0, s_1, s_2, \dots$ with $s_0 = s$ and a $k$ such that $s_0, \dots, s_k$ is a finite run of
length $k$ and $s_k$ is deadlocked, that is, has no outgoing transition.

The proof iterates a chosen successor function and uses the axiom of choice. -/
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

/-- **Deadlocked states are exactly those satisfying ¬EX ⊤.** A state $s$ of a labelled transition
system satisfies the CTL formula $\neg\mathsf{EX}\,\top$, under any valuation of the atoms, if and
only if $s$ is deadlocked: there is no label $a$ and state $t$ with a transition from $s$ to $t$
labelled $a$. -/
theorem not_existsNext_top_iff {s : State} :
    Satisfies lts valuation s (.not (.existsNext .top)) ↔
      ∀ label t, ¬lts.Tr s label t := by
  show ¬(∃ label t, lts.Tr s label t ∧ True) ↔ _
  constructor
  · intro h label t hstep
    exact h ⟨label, t, hstep, trivial⟩
  · rintro h ⟨label, t, hstep, -⟩
    exact h label t hstep

/-- **Bad target of the deadlock-correct until duality.** Let $\varphi$ and $\psi$ be CTL
formulas, and write $t \models \chi$ when the state $t$ of a labelled transition system satisfies
the formula $\chi$ under a given valuation of the atoms. Then
$t \models \neg\psi \land (\neg\varphi \lor \neg\mathsf{EX}\,\top)$ if and only if
$t \not\models \psi$ and either $t \not\models \varphi$ or $t$ is deadlocked, that is, there is no
label $a$ and state $u$ with a transition from $t$ to $u$ labelled $a$. -/
theorem forallUntil_bad_iff {φ ψ : Formula Atom} {t : State} :
    Satisfies lts valuation t
        (.and (.not ψ) (Formula.or (.not φ) (.not (.existsNext .top)))) ↔
      ¬Satisfies lts valuation t ψ ∧
        (¬Satisfies lts valuation t φ ∨
          ∀ label u, ¬lts.Tr t label u) := by
  rw [and_iff, or_iff, not_existsNext_top_iff, not_iff, not_iff]

/-- **One-step unfolding of universal until, forward direction.** Let $\varphi$ and $\psi$ be CTL
formulas, and write $s \models \chi$ when the state $s$ of a labelled transition system satisfies
the formula $\chi$ under a given valuation of the atoms. If
$s \models \mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$, then either $s \models \psi$, or
$s \models \varphi$, $s$ has at least one outgoing transition, and every state $t$ reached from $s$
by a single transition with any label satisfies
$t \models \mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$. -/
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

/-- **Deadlock-correct duality for universal until.** Let $\varphi$ and $\psi$ be CTL formulas,
and write $s \models \chi$ when the state $s$ of a labelled transition system satisfies the
formula $\chi$ under a given valuation of the atoms. Then
$s \models \mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$ if and only if neither
$s \models \mathsf{E}[\neg\psi \mathbin{\mathsf{U}} (\neg\psi \land (\neg\varphi \lor
\neg\mathsf{EX}\,\top))]$ nor $s \models \mathsf{EG}\,\neg\psi$.

Here $\neg\mathsf{EX}\,\top$ holds exactly at the deadlocked states, those with no outgoing
transition. So $\mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$ fails at $s$ exactly when some
infinite run starting at $s$ stays in $\neg\psi$ forever, or some finite run starting at $s$ stays
in $\neg\psi$ up to a $\neg\psi$-state at which $\varphi$ fails or which is deadlocked. -/
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

/-- **Congruence of existential until in its target.** In a labelled transition system with a
valuation of atoms, let $\rho$, $\alpha$ and $\beta$ be CTL formulas such that every state
satisfies $\alpha$ if and only if it satisfies $\beta$. Then every state $s$ satisfies
$\mathsf{E}[\rho \,\mathsf{U}\, \alpha]$ if and only if it satisfies
$\mathsf{E}[\rho \,\mathsf{U}\, \beta]$. -/
theorem existsUntil_congr {ρ α β : Formula Atom}
    (h : ∀ t, Satisfies lts valuation t α ↔ Satisfies lts valuation t β)
    {s : State} :
    Satisfies lts valuation s (.existsUntil ρ α) ↔
      Satisfies lts valuation s (.existsUntil ρ β) := by
  constructor <;> rintro ⟨ss, k, h0, hrun, htgt, hside⟩
  · exact ⟨ss, k, h0, hrun, (h _).mp htgt, hside⟩
  · exact ⟨ss, k, h0, hrun, (h _).mpr htgt, hside⟩

/-- **Deadlock-correct duality for AF.** In a labelled transition system with a valuation of
atoms, let $\varphi$ be a CTL formula. A state $s$ satisfies $\mathsf{AF}\,\varphi$ if and only
if $s$ satisfies neither $\mathsf{E}[\neg\varphi \,\mathsf{U}\, (\neg\varphi \wedge
\neg\mathsf{EX}\,\top)]$ nor $\mathsf{EG}\,\neg\varphi$.

This is the case $\mathsf{A}[\top \,\mathsf{U}\, \varphi]$ of the duality for universal until.
The formula $\neg\mathsf{EX}\,\top$ holds exactly at deadlocked states, so the first disjunct
catches finite maximal paths that end at a deadlock without reaching $\varphi$. -/
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

/-- **Existential next via the predecessor operator.** In a labelled transition system with a
valuation of atoms, let $\varphi$ be a CTL formula and write $\mathrm{Sat}(\varphi)$ for the set
of states satisfying $\varphi$. A state $s$ satisfies $\mathsf{EX}\,\varphi$ if and only if $s$
belongs to the existential predecessor set of $\mathrm{Sat}(\varphi)$, that is, some transition
leads from $s$ to a state satisfying $\varphi$. -/
theorem existsNext_iff_preExists {s : State} {φ : Formula Atom} :
    Satisfies lts valuation s (.existsNext φ) ↔
      PreExists lts (fun t => Satisfies lts valuation t φ) s := Iff.rfl

/-- **The existential-until functional.** In a labelled transition system with a valuation of
atoms, let $\varphi$ and $\psi$ be CTL formulas. The existential-until functional sends a set $Z$
of states to the set of states $s$ such that either $s$ satisfies $\psi$, or $s$ satisfies
$\varphi$ and some transition leads from $s$ to a state in $Z$.

Its least fixed point is the set of states satisfying $\mathsf{E}[\varphi \,\mathsf{U}\, \psi]$. -/
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

/-- **The existential-until functional as a monotone map.** In a labelled transition system with
a valuation of atoms, let $\varphi$ and $\psi$ be CTL formulas. The map sending a set $Z$ of
states to the set of states $s$ such that either $s$ satisfies $\psi$, or $s$ satisfies $\varphi$
and some transition leads from $s$ to a state in $Z$, is monotone for inclusion; this is that
map, regarded as an order-preserving map on sets of states. -/
def existsUntilOrderHom (lts : LTS State Label)
    (valuation : State → Atom → Prop) (φ ψ : Formula Atom) :
    (State → Prop) →o (State → Prop) :=
  ⟨existsUntilFun lts valuation φ ψ,
    existsUntilFun_mono lts valuation φ ψ⟩

/-- **Existential until as a least fixed point.** In a labelled transition system with a
valuation of atoms, let $\varphi$ and $\psi$ be CTL formulas, write $\mathrm{Sat}(\chi)$ for the
set of states satisfying a formula $\chi$, and write $\mathrm{Pre}_\exists(Z)$ for the set of
states having a transition into a set $Z$ of states. Then the set of states satisfying
$\mathsf{E}[\varphi \,\mathsf{U}\, \psi]$ is the least fixed point of the monotone map
$Z \mapsto \mathrm{Sat}(\psi) \cup (\mathrm{Sat}(\varphi) \cap \mathrm{Pre}_\exists(Z))$ on sets
of states.

One inclusion is Park induction via the one-step expansion of
$\mathsf{E}[\varphi \,\mathsf{U}\, \psi]$; the other is induction on the length of the
witnessing finite run, unfolding the fixed point once per step. -/
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

/-- **Finite existential predecessor set.** Let a labelled transition system have finitely many
states and finitely many labels, with decidable transitions. For a finite set $Z$ of states, its
existential predecessor set is the finite set of states $s$ for which there are a label $a$ and a
state $t \in Z$ with a transition from $s$ to $t$ labelled $a$.

It agrees with the existential predecessor operator applied to membership in $Z$. -/
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

/-- **Finite existential-until set.** Let $\mathcal{T}$ be a labelled transition system with
finitely many states and finitely many labels, decidable transitions and decidable equality of
states, and let $A$ and $B$ be sets of states. For a set $Z$ of states write
$\mathrm{Pre}_\exists(Z)$ for the set of states having a transition into $Z$. The
existential-until set with side set $A$ and target set $B$ is obtained by applying the map
$Z \mapsto B \cup (A \cap \mathrm{Pre}_\exists(Z))$ to the empty set $n$ times, where $n$ is the
number of states.

Since this map is monotone, the iteration has stabilized after $n$ steps and the result is its
least fixed point. -/
def eUntilFin (lts : LTS State Label)
    [∀ s μ t, Decidable (lts.Tr s μ t)] (A B : Finset State) :
    Finset State :=
  Finset.lfpFin (fun Z => B ∪ (A ∩ preExistsFin lts Z))

/-- **Finite existential-globally set.** Let $\mathcal{T}$ be a labelled transition system with
finitely many states and finitely many labels, decidable transitions and decidable equality of
states, and let $A$ be a set of states. For a set $Z$ of states write
$\mathrm{Pre}_\exists(Z)$ for the set of states having a transition into $Z$. The
existential-globally set of $A$ is obtained by applying the map
$Z \mapsto A \cap \mathrm{Pre}_\exists(Z)$ to the set of all states $n$ times, where $n$ is the
number of states.

Since this map is monotone, the iteration has stabilized after $n$ steps and the result is its
greatest fixed point. -/
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

/-- **Correctness of the finite fixed-point computation of EU.** Let a labelled transition system
have finitely many states and finitely many labels, with decidable transitions and decidable
equality of states, and fix a valuation of the atoms. For a finite set $Z$ of states let
$\mathrm{Pre}_\exists(Z)$ be the set of states with a transition into $Z$, and for finite sets
$A$ and $B$ of states let $\mathrm{EU}_{\mathrm{fin}}(A, B)$ be the least fixed point of
$Z \mapsto B \cup (A \cap \mathrm{Pre}_\exists(Z))$, computed by finite iteration. Let $\varphi$
and $\psi$ be CTL formulas and $A$ and $B$ finite sets of states such that a state lies in $A$
exactly when it satisfies $\varphi$, and lies in $B$ exactly when it satisfies $\psi$. Then every
state $s$ lies in $\mathrm{EU}_{\mathrm{fin}}(A, B)$ if and only if $s$ satisfies
$\mathsf{E}[\varphi \mathbin{\mathsf{U}} \psi]$. -/
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

/-- **Correctness of the finite fixed-point computation of EG.** Let a labelled transition system
have finitely many states and finitely many labels, with decidable transitions and decidable
equality of states, and fix a valuation of the atoms. For a finite set $Z$ of states let
$\mathrm{Pre}_\exists(Z)$ be the set of states with a transition into $Z$, and for a finite set
$A$ of states let $\mathrm{EG}_{\mathrm{fin}}(A)$ be the greatest fixed point of
$Z \mapsto A \cap \mathrm{Pre}_\exists(Z)$, computed by finite iteration. Let $\varphi$ be a CTL
formula and $A$ a finite set of states such that a state lies in $A$ exactly when it satisfies
$\varphi$. Then every state $s$ lies in $\mathrm{EG}_{\mathrm{fin}}(A)$ if and only if $s$
satisfies $\mathsf{EG}\,\varphi$. -/
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

/-- **Correctness of the CTL model checker.** Let a labelled transition system have finitely many
states and finitely many labels, with decidable transitions and decidable equality of states, and
let the valuation of the atoms be decidable. For every CTL formula $\varphi$ and every state $s$,
the state $s$ lies in the set $\mathrm{sat}(\varphi)$ computed by the model checker if and only if
$s$ satisfies $\varphi$.

The proof is by induction on $\varphi$. The temporal cases use the correctness of the finite
fixed-point computations of $\mathsf{EU}$ and $\mathsf{EG}$, and the $\mathsf{AU}$ case also
identifies the computed bad-target set with the states satisfying the bad-target formula. -/
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

/-- **The CTL model checker as a Boolean decision procedure.** Let $\mathcal{T}$ be a labelled
transition system with finitely many states and finitely many labels, decidable transitions and
decidable equality of states, and let $V$ be a decidable valuation of atoms at states. For a state
$s$ and a CTL formula $\varphi$, the model checker returns true exactly when $s$ belongs to the
set of states that the satisfaction-set algorithm computes for $\varphi$ in $\mathcal{T}$ under
$V$. -/
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

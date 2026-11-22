/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `110ea10c9842e17ce0f7478a72b3abe4346ddab1`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Observation logic for weak labelled transition systems
-/
module

public import CSLibExt.Foundations.Semantics.LTS.WeakBisimulation
public import Cslib.Logics.HML.Basic

import Mathlib.Tactic

/-!
# Weak Hennessy--Milner logic

This file equips labelled transition systems with a finitary modal observation
logic interpreted through weak transitions.  It proves two complementary
invariance results:

* weakly bisimilar states satisfy exactly the same formulas; and
* the depth-`n` weak behavioral approximant preserves every formula of modal
  depth at most `n`.

Weak Hennessy--Milner logic is canonical CSLib HML (`Cslib.Logic.Modal.HML`,
with no atoms) interpreted over the canonical saturated system
`lts.saturate`: `ObservationFormula.tr`, `satModel`, and `satisfies_iff` make
this precise. A second, alignment-free view interprets observations directly
over the weak-step relation (`toWeakHMLModel`,
`satisfies_iff_toWeakHMLModel`), reusing the same translation `tr` with no
silent-label alignment.

The presentation follows the observational logic developed for transition
systems in Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989,
Chapter 10 (ISBN 978-0-13-115007-2), specialized to the weak transition
relation from Chapter 5.
-/

@[expose] public section

namespace Cslib.Semantics

namespace LTS

variable {State Label : Type*}

/-- Finitary Hennessy--Milner formulas. -/
inductive ObservationFormula (Label : Type*) where
  | top
  | neg (body : ObservationFormula Label)
  | conj (left right : ObservationFormula Label)
  | diamond (label : Label) (body : ObservationFormula Label)
  deriving DecidableEq

namespace ObservationFormula

/-- Falsity, defined by negating truth. -/
def bottom : ObservationFormula Label := .neg .top

/-- Disjunction, defined using negation and conjunction. -/
def disj (left right : ObservationFormula Label) : ObservationFormula Label :=
  .neg (.conj (.neg left) (.neg right))

/-- The box modality, dual to diamond. -/
def box (label : Label) (body : ObservationFormula Label) : ObservationFormula Label :=
  .neg (.diamond label (.neg body))

/-- Right-associated conjunction of a finite list of formulas. -/
def conjunction : List (ObservationFormula Label) → ObservationFormula Label
  | [] => .top
  | formula :: formulas => .conj formula (conjunction formulas)

/-- Right-associated disjunction of a finite list of formulas. -/
def disjunction : List (ObservationFormula Label) → ObservationFormula Label
  | [] => .bottom
  | formula :: formulas => .disj formula (disjunction formulas)

/-- Maximum nesting depth of modalities in a formula. -/
def modalDepth : ObservationFormula Label → Nat
  | .top => 0
  | .neg body => modalDepth body
  | .conj left right => max (modalDepth left) (modalDepth right)
  | .diamond _ body => modalDepth body + 1

@[simp]
theorem modalDepth_bottom : (bottom : ObservationFormula Label).modalDepth = 0 := rfl

@[simp]
theorem modalDepth_disj (left right : ObservationFormula Label) :
    (disj left right).modalDepth = max left.modalDepth right.modalDepth := by
  simp [disj, modalDepth]

@[simp]
theorem modalDepth_box (label : Label) (body : ObservationFormula Label) :
    (box label body).modalDepth = body.modalDepth + 1 := rfl

end ObservationFormula

variable [HasTau Label]

/-- Satisfaction for observation formulas, with diamonds interpreted by weak
transitions. -/
def Satisfies (lts : _root_.Cslib.LTS State Label)
    (state : State) : ObservationFormula Label → Prop
  | .top => True
  | .neg body => ¬ Satisfies lts state body
  | .conj left right =>
      Satisfies lts state left ∧ Satisfies lts state right
  | .diamond label body =>
      ∃ next, lts.STr state label next ∧
        Satisfies lts next body

variable {lts : _root_.Cslib.LTS State Label}

@[simp]
theorem satisfies_top (state : State) :
    Satisfies lts state .top :=
  trivial

@[simp]
theorem satisfies_neg_iff {state : State} {body : ObservationFormula Label} :
    Satisfies lts state (.neg body) ↔
      ¬ Satisfies lts state body :=
  Iff.rfl

@[simp]
theorem satisfies_conj_iff {state : State} {left right : ObservationFormula Label} :
    Satisfies lts state (.conj left right) ↔
      Satisfies lts state left ∧
      Satisfies lts state right :=
  Iff.rfl

@[simp]
theorem satisfies_diamond_iff {state : State} {label : Label}
    {body : ObservationFormula Label} :
    Satisfies lts state (.diamond label body) ↔
      ∃ next, lts.STr state label next ∧
        Satisfies lts next body :=
  Iff.rfl

@[simp]
theorem not_satisfies_bottom (state : State) :
    ¬ Satisfies lts state .bottom := by
  simp [ObservationFormula.bottom, Satisfies]

@[simp]
theorem satisfies_disj_iff {state : State} {left right : ObservationFormula Label} :
    Satisfies lts state (.disj left right) ↔
      Satisfies lts state left ∨
      Satisfies lts state right := by
  classical
  simp only [ObservationFormula.disj, Satisfies]
  tauto

@[simp]
theorem satisfies_box_iff {state : State} {label : Label}
    {body : ObservationFormula Label} :
    Satisfies lts state (.box label body) ↔
      ∀ next, lts.STr state label next →
        Satisfies lts next body := by
  classical
  simp [ObservationFormula.box, Satisfies]

@[simp]
theorem satisfies_conjunction_iff {state : State}
    {formulas : List (ObservationFormula Label)} :
    Satisfies lts state (.conjunction formulas) ↔
      ∀ formula ∈ formulas, Satisfies lts state formula := by
  induction formulas with
  | nil => simp [ObservationFormula.conjunction]
  | cons formula formulas ih =>
      simp [ObservationFormula.conjunction, ih]

@[simp]
theorem satisfies_disjunction_iff {state : State}
    {formulas : List (ObservationFormula Label)} :
    Satisfies lts state (.disjunction formulas) ↔
      ∃ formula ∈ formulas, Satisfies lts state formula := by
  induction formulas with
  | nil => simp [ObservationFormula.disjunction]
  | cons formula formulas ih =>
      simp [ObservationFormula.disjunction, ih]

/-- States are logically equivalent when they satisfy the same observation
formulas. -/
def LogicallyEquivalent (left right : State) : Prop :=
  ∀ formula, Satisfies lts left formula ↔
    Satisfies lts right formula

@[refl]
theorem logicallyEquivalent_refl (state : State) :
    LogicallyEquivalent (lts := lts) state state :=
  fun _ => Iff.rfl

theorem LogicallyEquivalent.symm {left right : State}
    (hequiv : LogicallyEquivalent (lts := lts) left right) :
    LogicallyEquivalent (lts := lts) right left :=
  fun formula => (hequiv formula).symm

@[trans]
theorem LogicallyEquivalent.trans {left middle right : State}
    (hleft : LogicallyEquivalent (lts := lts) left middle)
    (hright : LogicallyEquivalent (lts := lts) middle right) :
    LogicallyEquivalent (lts := lts) left right :=
  fun formula => (hleft formula).trans (hright formula)

/-- Match a weak step of the left state by a weak step of the right state,
preserving weak bisimilarity of the continuations. -/
private theorem match_weakLeft {left right left' : State} {label : Label}
    (hbisim : lts.HomWeakBisimilarity left right)
    (hstep : lts.STr left label left') :
    ∃ right', lts.STr right label right' ∧
      lts.HomWeakBisimilarity left' right' := by
  obtain ⟨r, hrel, hsim⟩ := hbisim
  have hsat : _root_.Cslib.LTS.IsBisimulation lts.saturate lts.saturate r := hsim
  obtain ⟨right', hright', hnext⟩ := hsat.follow_fst hrel hstep
  exact ⟨right', hright', r, hnext, hsat⟩

/-- Match a weak step of the right state by a weak step of the left state,
preserving weak bisimilarity of the continuations. -/
private theorem match_weakRight {left right right' : State} {label : Label}
    (hbisim : lts.HomWeakBisimilarity left right)
    (hstep : lts.STr right label right') :
    ∃ left', lts.STr left label left' ∧
      lts.HomWeakBisimilarity left' right' := by
  obtain ⟨r, hrel, hsim⟩ := hbisim
  have hsat : _root_.Cslib.LTS.IsBisimulation lts.saturate lts.saturate r := hsim
  obtain ⟨left', hleft', hnext⟩ := hsat.follow_snd hrel hstep
  exact ⟨left', hleft', r, hnext, hsat⟩

/-- Weak bisimilarity preserves every observation formula. -/
theorem HomWeakBisimilarity.satisfies_iff {left right : State}
    (hbisim : lts.HomWeakBisimilarity left right)
    (formula : ObservationFormula Label) :
    Satisfies lts left formula ↔
      Satisfies lts right formula := by
  induction formula generalizing left right with
  | top => simp
  | neg body ih =>
      simp only [satisfies_neg_iff]
      exact not_congr (ih hbisim)
  | conj first second ihFirst ihSecond =>
      simp only [satisfies_conj_iff]
      exact and_congr (ihFirst hbisim) (ihSecond hbisim)
  | diamond label body ih =>
      simp only [satisfies_diamond_iff]
      constructor
      · rintro ⟨left', hleft', hsatisfies⟩
        obtain ⟨right', hright', hnext⟩ := match_weakLeft hbisim hleft'
        exact ⟨right', hright', (ih hnext).mp hsatisfies⟩
      · rintro ⟨right', hright', hsatisfies⟩
        obtain ⟨left', hleft', hnext⟩ := match_weakRight hbisim hright'
        exact ⟨left', hleft', (ih hnext).mpr hsatisfies⟩

/-- Weakly bisimilar states are logically equivalent. -/
theorem HomWeakBisimilarity.logicallyEquivalent {left right : State}
    (hbisim : lts.HomWeakBisimilarity left right) :
    LogicallyEquivalent (lts := lts) left right :=
  HomWeakBisimilarity.satisfies_iff hbisim

/-- The finite-depth weak behavioral approximant. At depth zero every pair is
equivalent; at successor depth, weak transitions must be mutually matched by
states equivalent at the preceding depth. -/
def WeakApproximation (lts : _root_.Cslib.LTS State Label) :
    Nat → State → State → Prop
  | 0, _, _ => True
  | depth + 1, left, right =>
      (∀ ⦃label left'⦄, lts.STr left label left' →
        ∃ right', lts.STr right label right' ∧
          WeakApproximation lts depth left' right') ∧
      (∀ ⦃label right'⦄, lts.STr right label right' →
        ∃ left', lts.STr left label left' ∧
          WeakApproximation lts depth left' right')

@[simp]
theorem weakApproximation_zero (left right : State) :
    WeakApproximation lts 0 left right :=
  trivial

@[simp]
theorem weakApproximation_succ_iff {depth : Nat} {left right : State} :
    WeakApproximation lts (depth + 1) left right ↔
      ((∀ ⦃label left'⦄, lts.STr left label left' →
        ∃ right', lts.STr right label right' ∧
          WeakApproximation lts depth left' right') ∧
      (∀ ⦃label right'⦄, lts.STr right label right' →
        ∃ left', lts.STr left label left' ∧
          WeakApproximation lts depth left' right')) :=
  Iff.rfl

@[refl]
theorem weakApproximation_refl (depth : Nat) (state : State) :
    WeakApproximation lts depth state state := by
  induction depth generalizing state with
  | zero => trivial
  | succ depth ih =>
      constructor <;> intro label next hstep
      · exact ⟨next, hstep, ih next⟩
      · exact ⟨next, hstep, ih next⟩

theorem WeakApproximation.symm {depth : Nat} {left right : State}
    (happrox : WeakApproximation lts depth left right) :
    WeakApproximation lts depth right left := by
  induction depth generalizing left right with
  | zero => trivial
  | succ depth ih =>
      constructor
      · intro label right' hstep
        obtain ⟨left', hleft', hnext⟩ := happrox.2 hstep
        exact ⟨left', hleft', ih hnext⟩
      · intro label left' hstep
        obtain ⟨right', hright', hnext⟩ := happrox.1 hstep
        exact ⟨right', hright', ih hnext⟩

/-- Increasing the observation depth can only distinguish more states. -/
theorem WeakApproximation.mono {smaller larger : Nat} {left right : State}
    (hle : smaller ≤ larger)
    (happrox : WeakApproximation lts larger left right) :
    WeakApproximation lts smaller left right := by
  induction smaller generalizing larger left right with
  | zero => trivial
  | succ smaller ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have hle' : smaller ≤ larger := Nat.succ_le_succ_iff.mp hle
          constructor
          · intro label left' hstep
            obtain ⟨right', hright', hnext⟩ := happrox.1 hstep
            exact ⟨right', hright', ih hle' hnext⟩
          · intro label right' hstep
            obtain ⟨left', hleft', hnext⟩ := happrox.2 hstep
            exact ⟨left', hleft', ih hle' hnext⟩

/-- Weak bisimilarity implies equivalence at every finite observation depth. -/
theorem HomWeakBisimilarity.weakApproximation {left right : State}
    (hbisim : lts.HomWeakBisimilarity left right) (depth : Nat) :
    WeakApproximation lts depth left right := by
  induction depth generalizing left right with
  | zero => trivial
  | succ depth ih =>
      constructor
      · intro label left' hstep
        obtain ⟨right', hright', hnext⟩ := match_weakLeft hbisim hstep
        exact ⟨right', hright', ih hnext⟩
      · intro label right' hstep
        obtain ⟨left', hleft', hnext⟩ := match_weakRight hbisim hstep
        exact ⟨left', hleft', ih hnext⟩

/-- Depth-`n` approximation preserves formulas of modal depth at most `n`. -/
theorem WeakApproximation.satisfies_iff {depth : Nat} {left right : State}
    (happrox : WeakApproximation lts depth left right)
    (formula : ObservationFormula Label) (hdepth : formula.modalDepth ≤ depth) :
    Satisfies lts left formula ↔
      Satisfies lts right formula := by
  induction formula generalizing depth left right with
  | top => simp
  | neg body ih =>
      simp only [satisfies_neg_iff]
      exact not_congr (ih happrox hdepth)
  | conj first second ihFirst ihSecond =>
      simp only [satisfies_conj_iff]
      have hfirst : first.modalDepth ≤ depth :=
        le_trans (Nat.le_max_left _ _) hdepth
      have hsecond : second.modalDepth ≤ depth :=
        le_trans (Nat.le_max_right _ _) hdepth
      exact and_congr (ihFirst happrox hfirst) (ihSecond happrox hsecond)
  | diamond label body ih =>
      cases depth with
      | zero => simp [ObservationFormula.modalDepth] at hdepth
      | succ depth =>
          have hbody : body.modalDepth ≤ depth := by
            simpa [ObservationFormula.modalDepth] using hdepth
          simp only [satisfies_diamond_iff]
          constructor
          · rintro ⟨left', hleft', hsatisfies⟩
            obtain ⟨right', hright', hnext⟩ := happrox.1 hleft'
            exact ⟨right', hright', (ih hnext hbody).mp hsatisfies⟩
          · rintro ⟨right', hright', hsatisfies⟩
            obtain ⟨left', hleft', hnext⟩ := happrox.2 hright'
            exact ⟨left', hleft', (ih hnext hbody).mpr hsatisfies⟩

section CslibBridge

open PFunctor

/-- Translation of observation formulas into canonical CSLib HML propositions with no
atoms: truth is `¬⊥`, conjunction is canonical conjunction, and a diamond is the
canonical unary diamond. -/
def ObservationFormula.tr : ObservationFormula Label → Logic.Modal.HML.Proposition Label Empty
  | .top => .not .false
  | .neg φ => .not φ.tr
  | .conj φ ψ => .and φ.tr ψ.tr
  | .diamond μ φ => .triangle μ (fun _ => φ.tr)

/-- The canonical CSLib HML model of the saturated system: the transitions of
`(lts).saturate` and the empty valuation. -/
def satModel (lts : _root_.Cslib.LTS State Label) :
    Logic.Modal.HML.Model State Label Empty :=
  { lts := (lts).saturate, v := fun _ _ => False }

/-- The canonical CSLib HML model on the weak transition relation directly, with no
atoms and no silent-label alignment: the silent modality includes the reflexive
silent closure. Unlike `satModel`, this interprets diamonds directly over
`STr` without passing through saturation. -/
def toWeakHMLModel (lts : LTS State Label) :
    Logic.Modal.HML.Model State Label Empty where
  lts := ⟨lts.STr⟩
  v := fun _ a => nomatch a

/-- The canonical translation sends diamonds to CSLib dynamic diamonds, by
definition of the modality on a constant family. -/
theorem ObservationFormula.tr_diamond_eq_dynDiamond (label : Label)
    (φ : ObservationFormula Label) :
    (ObservationFormula.diamond label φ).tr =
      Logic.HasDynamicDiamond.dynDiamond label φ.tr := rfl

/-- An observation holds exactly when its canonical translation holds in the
weak-transition HML model. This is the direct `STr` view: it
uses no saturation and no silent-label reconciliation, unlike `satisfies_iff`. Both views
share the one translation `ObservationFormula.tr`. -/
theorem satisfies_iff_toWeakHMLModel (lts : LTS State Label)
    (state : State) (φ : ObservationFormula Label) :
    Satisfies lts state φ ↔
      Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state φ.tr := by
  induction φ generalizing state with
  | top => simp [Satisfies, ObservationFormula.tr, Logic.Modal.Satisfies]
  | neg φ ih =>
      exact not_congr (ih state)
  | conj φ ψ ihφ ihψ =>
      change (Satisfies lts state φ ∧ Satisfies lts state ψ) ↔
        Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state
          (Logic.Modal.Proposition.and φ.tr ψ.tr)
      have hconj :
          Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state
            (Logic.Modal.Proposition.and φ.tr ψ.tr) ↔
          (Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state φ.tr ∧
            Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state ψ.tr) :=
        Logic.Modal.Satisfies.and_iff_and (m := (toWeakHMLModel lts).toModal)
          (w := state) (φ₁ := φ.tr) (φ₂ := ψ.tr)
      exact (and_congr (ihφ state) (ihψ state)).trans hconj.symm
  | diamond label φ ih =>
      change (∃ next, lts.STr state label next ∧
        Satisfies lts next φ) ↔
        Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state
          ((ObservationFormula.diamond label φ).tr)
      rw [ObservationFormula.tr_diamond_eq_dynDiamond]
      have hdiamond :
          Logic.Modal.Satisfies (toWeakHMLModel lts).toModal state
            (Logic.HasDynamicDiamond.dynDiamond label φ.tr) ↔
          ∃ next, lts.STr state label next ∧
            Logic.Modal.Satisfies (toWeakHMLModel lts).toModal next φ.tr :=
        Logic.Modal.Satisfies.hml_dynDiamond_iff_exists (m := toWeakHMLModel lts)
          (s := state) (μ := label) (φ := φ.tr)
      exact (exists_congr fun next => and_congr Iff.rfl (ih next)).trans hdiamond.symm

/-- The alignment-free model equals the saturated model: same carrier and labels,
coinciding empty valuations, and frame relations coinciding since the saturated
transition relation is `STr`. Record extensionality splits this into the two field
equations below, which close it. -/
private theorem toWeakHMLModel_eq_satModel
    (lts : LTS State Label) :
    toWeakHMLModel lts = satModel lts := by
  have hTr : (toWeakHMLModel lts).lts = (satModel lts).lts := by
    apply _root_.Cslib.LTS.ext
    funext s μ t
    exact propext Iff.rfl
  have hval : (toWeakHMLModel lts).v = (satModel lts).v := by
    funext _ a
    exact nomatch a
  unfold toWeakHMLModel satModel
  congr 1

/-- Weak satisfaction is canonical CSLib HML satisfaction of the translated formula
in the saturated system. This is the aligned specialization of
`satisfies_iff_toWeakHMLModel`, transported along the equality of the two
models; no second formula induction. -/
theorem satisfies_iff (lts : LTS State Label)
    (φ : ObservationFormula Label) (s : State) :
    Satisfies lts s φ ↔ Logic.Modal.Satisfies (satModel lts).toModal s φ.tr := by
  rw [satisfies_iff_toWeakHMLModel lts s φ,
    toWeakHMLModel_eq_satModel lts]

end CslibBridge

end LTS

end Cslib.Semantics

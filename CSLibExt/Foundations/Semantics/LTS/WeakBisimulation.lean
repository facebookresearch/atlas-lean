/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
Adapted to the upstream weak semantics (`Cslib.HasTau`, `LTS.τSTr`,
`LTS.STr`, `LTS.saturate`, `LTS.IsWeakBisimulation`,
`LTS.WeakBisimilarity`); only transfer lemmas missing upstream are
proved here.
-/

/-
# Weak bisimulation: transfer lemmas
-/
module

public import CSLibExt.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.HasTau

/-!
# Weak transitions and observational equivalence

The weak semantics itself is upstream: silent closure is `LTS.τSTr`,
weak transitions are `LTS.STr` (the transitions of `LTS.saturate`), weak
traces are `LTS.saturate.MTr`, and weak bisimilarity is
`LTS.WeakBisimilarity` / `LTS.HomWeakBisimilarity`.  Recorded here are
the composition and transfer lemmas the process-language developments
use that upstream does not state.

The constructions follow Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib

namespace LTS

variable {State Label : Type*} [HasTau Label] {lts : LTS State Label}

/-- A single silent step is a silent closure. -/
theorem τSTr.of_tr {source target : State}
    (hstep : lts.Tr source HasTau.τ target) : lts.τSTr source target :=
  Relation.ReflTransGen.single hstep

/-- Prepend one silent step to a silent closure. -/
theorem τSTr.cons {source middle target : State}
    (hstep : lts.Tr source HasTau.τ middle) (htail : lts.τSTr middle target) :
    lts.τSTr source target :=
  Relation.ReflTransGen.head hstep htail

/-- Silent closure is equivalent to a multistep transition consisting only
of silent labels. -/
theorem τSTr_iff_exists_mtr {source target : State} :
    lts.τSTr source target ↔
      ∃ count, lts.MTr source (List.replicate count HasTau.τ) target := by
  constructor
  · intro hclosure
    induction hclosure using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .refl⟩
    | @head source middle head tail ih =>
        obtain ⟨count, htrace⟩ := ih
        exact ⟨count + 1, by
          simpa [List.replicate_succ] using MTr.stepL head htrace⟩
  · rintro ⟨count, htrace⟩
    induction count generalizing source with
    | zero =>
        simp only [List.replicate_zero, MTr.nil_iff] at htrace
        subst target
        exact .refl
    | succ count ih =>
        rw [List.replicate_succ, MTr.cons_iff] at htrace
        obtain ⟨middle, hstep, htail⟩ := htrace
        exact τSTr.cons hstep (ih htail)

/-- A weak transition with a visible label factors as silent preparation,
one strong step, and silent cleanup. -/
theorem STr.iff_exists_of_ne {source target : State} {label : Label}
    (hne : label ≠ HasTau.τ) :
    lts.STr source label target ↔
      ∃ before after, lts.τSTr source before ∧
        lts.Tr before label after ∧ lts.τSTr after target := by
  constructor
  · intro h
    cases h with
    | refl => exact absurd rfl hne
    | tr hpre hstep hpost => exact ⟨_, _, hpre, hstep, hpost⟩
  · rintro ⟨before, after, hpre, hstep, hpost⟩
    exact .tr hpre hstep hpost

/-- Silent preparation can be prefixed to a weak transition. -/
theorem τSTr.trans_sTr {source middle target : State} {label : Label}
    (hbefore : lts.τSTr source middle) (hstep : lts.STr middle label target) :
    lts.STr source label target := by
  cases hstep with
  | refl => exact (sTr_τSTr_iff lts).mpr hbefore
  | tr hpre hstep hpost => exact .tr (hbefore.trans hpre) hstep hpost

/-- Silent cleanup can be appended to a weak transition. -/
theorem STr.trans_τSTr {source middle target : State} {label : Label}
    (hstep : lts.STr source label middle) (hafter : lts.τSTr middle target) :
    lts.STr source label target := by
  cases hstep with
  | refl => exact (sTr_τSTr_iff lts).mpr hafter
  | tr hpre hstep hpost => exact .tr hpre hstep (hpost.trans hafter)

/-- Strong multistep transitions embed into saturated ones. -/
theorem MTr.to_saturate {source target : State} {labels : List Label}
    (htrace : lts.MTr source labels target) :
    lts.saturate.MTr source labels target := by
  induction htrace with
  | refl => exact .refl
  | stepL head tail ih => exact .stepL (STr.single head) ih

/-- Weak bisimilarity is bisimilarity of the saturated systems. -/
theorem HomWeakBisimilarity.iff_homBisimilarity_saturate {left right : State} :
    HomWeakBisimilarity lts left right ↔ HomBisimilarity lts.saturate left right :=
  Iff.rfl

/-- A strong transition transfers across weak bisimilarity. -/
theorem HomWeakBisimilarity.tr {left right left' : State} {label : Label}
    (hbisim : HomWeakBisimilarity lts left right) (hstep : lts.Tr left label left') :
    ∃ right', lts.STr right label right' ∧ HomWeakBisimilarity lts left' right' := by
  obtain ⟨relation, hrel, hrelation⟩ := hbisim
  have hswb : IsSWBisimulation lts lts relation :=
    isWeakBisimulation_iff_isSWBisimulation.mp hrelation
  obtain ⟨right', hright, hnext⟩ := (hswb hrel label).1 left' hstep
  exact ⟨right', hright, relation, hnext, hrelation⟩

/-- A weak transition transfers across weak bisimilarity. -/
theorem HomWeakBisimilarity.sTr {left right left' : State} {label : Label}
    (hbisim : HomWeakBisimilarity lts left right)
    (hstep : lts.STr left label left') :
    ∃ right', lts.STr right label right' ∧ HomWeakBisimilarity lts left' right' := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  obtain ⟨right', hright, hnext⟩ := Bisimilarity.follow_fst hsat hstep
  exact ⟨right', hright, hnext⟩

/-- A saturated multistep transition transfers across weak bisimilarity. -/
theorem HomWeakBisimilarity.saturate_mtr {left right left' : State}
    {labels : List Label}
    (hbisim : HomWeakBisimilarity lts left right)
    (htrace : lts.saturate.MTr left labels left') :
    ∃ right', lts.saturate.MTr right labels right' ∧
      HomWeakBisimilarity lts left' right' := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  obtain ⟨right', hright, hnext⟩ := hsat.mtr htrace
  exact ⟨right', hright, hnext⟩

/-- Strong bisimilarity implies weak bisimilarity. -/
theorem HomBisimilarity.to_homWeakBisimilarity {left right : State}
    (h : HomBisimilarity lts left right) : HomWeakBisimilarity lts left right := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  refine ⟨relation, hrel, ?_⟩
  rw [isWeakBisimulation_iff_isSWBisimulation]
  intro s₁ s₂ hs μ
  constructor
  · intro s₁' hstep
    obtain ⟨s₂', hright, hnext⟩ := (hbisim hs μ).1 s₁' hstep
    exact ⟨s₂', STr.single hright, hnext⟩
  · intro s₂' hstep
    obtain ⟨s₁', hleft, hnext⟩ := (hbisim hs μ).2 s₂' hstep
    exact ⟨s₁', STr.single hleft, hnext⟩

/-- Weakly bisimilar states have the same saturated outgoing labels. -/
theorem HomWeakBisimilarity.hasOutLabel_saturate_iff {left right : State}
    (hbisim : HomWeakBisimilarity lts left right) (label : Label) :
    lts.saturate.HasOutLabel left label ↔ lts.saturate.HasOutLabel right label := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  exact hsat.hasOutLabel_iff label

/-- Weakly bisimilar states have equal saturated sets of outgoing labels. -/
theorem HomWeakBisimilarity.outgoingLabels_saturate_eq {left right : State}
    (hbisim : HomWeakBisimilarity lts left right) :
    lts.saturate.outgoingLabels left = lts.saturate.outgoingLabels right := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  exact hsat.outgoingLabels_eq

end LTS

end Cslib

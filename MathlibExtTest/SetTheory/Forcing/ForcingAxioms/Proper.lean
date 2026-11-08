/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

/-! # The dense-set part of a countable model

A countable model is a countable `M : Set (P ⊕ Set P)`: the `inl` half is `M ∩ P`, the `inr` half
is the dense sets belonging to `M`.  `modelSets` reads off the second.  Mirror of
`ModelConds.lean`.

Fully qualified throughout, with no `open`, so it pastes into `Corpus.lean`
(`open Cardinal Ordinal Set Order`) unchanged. -/

/-! # Properness

`P` is proper when club-many countable models admit generic conditions.  Elementarity is replaced
by the existential over a club in `[P ⊕ Set P]^ω`, which is what keeps the definition from being
too strong; `IsClubOmega.cofinal` is what keeps it from being vacuous.

The two lemmas below bracket the definition from below — it cannot be trivialised by shrinking the
club, and it is satisfiable.  The bracket from **above** is `not_isProper_coll` in `Corpus.lean`
(the Lévy collapse of an uncountable `α` is not proper), which is too long to inline here; without
it `IsProper` might have held of every poset.

`IsClubOmega`, `modelConds`, `modelSets`, `IsCompatible`, `IsPredenseBelow`, `IsGenericFor` are
copied verbatim from `Corpus.lean` as dependencies.  Fully qualified, no `open`, so it pastes into
`Corpus.lean` (`open Cardinal Ordinal Set Order`) unchanged. -/

namespace MathlibExtTest.SetTheory.Forcing.ForcingAxioms.Proper

open MetaMathlibExt

-- Logic 43: Conditions belonging to a model

/-- Adding a subset of `P` to the model leaves its conditions untouched.  This is the check that
the `P ⊕ Set P` encoding really keeps the two halves apart — with a carrier that conflated them,
`modelSets` could leak into `modelConds` and `IsGenericFor` would be quantifying over the wrong
thing. -/

theorem modelConds_insert_inr {P : Type*} (M : Set (P ⊕ Set P)) (D : Set P) :
    modelConds (insert (Sum.inr D) M) = modelConds M := by
  ext p
  simp [modelConds]

/-- A countable model has countably many conditions.  Load-bearing in `not_isProper_coll`: it is
what bounds the values of `α` occurring in `M`, leaving a `γ` outside for the incompatible
extension. -/

theorem countable_modelConds {P : Type*} {M : Set (P ⊕ Set P)} (hM : M.Countable) :
    (modelConds M).Countable :=
  hM.preimage Sum.inl_injective

-- Logic 44: Subsets belonding to a model

/-- Adding a condition to the model leaves its subsets untouched — the other half of the check
that the `P ⊕ Set P` encoding keeps conditions and dense sets apart. -/

theorem modelSets_insert_inl {P : Type*} (M : Set (P ⊕ Set P)) (p : P) :
    modelSets (insert (Sum.inl p) M) = modelSets M := by
  ext D
  simp [modelSets]

/-- A countable model knows only countably many subsets of `P`.  This is what keeps the club in
the intended proof of `isProper_of_isCCC` constructible: each dense `D ∈ modelSets M` contributes
one closure demand (a maximal antichain `A_D ⊆ D` must also lie in `modelSets M`), so countably
many demands in total, each adding countably much. -/

theorem countable_modelSets {P : Type*} {M : Set (P ⊕ Set P)} (hM : M.Countable) :
    (modelSets M).Countable :=
  hM.preimage Sum.inr_injective

-- Logic 45: Compatibility

/-- Compatibility is symmetric, so the argument order in `IsPredenseBelow A q`'s
`IsCompatible r a` carries no hidden content. -/

theorem _root_.MetaMathlibExt.IsCompatible.symm {P : Type*} [PartialOrder P] {p q : P} (h : IsCompatible p q) :
    IsCompatible q p :=
  let ⟨r, hp, hq⟩ := h; ⟨r, hq, hp⟩

/-- On a linear order *every* pair is compatible, `min` being a common extension.  So
incompatibility — and with it antichains, `IsCCC`, and the whole of `IsProper` — has content only
on genuinely partial orders.  A forcing poset that is accidentally linear is a degenerate test
case, not a hard one. -/

theorem isCompatible_of_linearOrder {P : Type*} [LinearOrder P] (p q : P) : IsCompatible p q :=
  ⟨min p q, min_le_left p q, min_le_right p q⟩

-- Logic 46: Predense below

/-- The empty set is predense below nothing — take `r = q` and there is no witness.  This is what
stops `IsGenericFor` being satisfiable for free: a model whose trace `D ∩ modelConds M` is empty
admits no generic condition at all, so genericity really does force the trace to be nonempty. -/

theorem not_isPredenseBelow_empty {P : Type*} [PartialOrder P] (q : P) :
    ¬ IsPredenseBelow (∅ : Set P) q := by
  intro h
  obtain ⟨a, ha, -⟩ := h q le_rfl
  exact ha

/-- Predensity passes to extensions.  This is the step `IsGenericFor.mono` is built from, and it
is what makes "generic condition" a usable notion: having found one, every strengthening of it is
still generic. -/

theorem IsPredenseBelow.of_le {P : Type*} [PartialOrder P] {A : Set P} {q q' : P}
    (h : IsPredenseBelow A q) (hq : q' ≤ q) : IsPredenseBelow A q' :=
  fun r hr => h r (hr.trans hq)

-- Logic 47: $(M,P)$-generic condition

/-- **Genericity is vacuous for a model that knows no sets.**  This is the one way `IsProper`
could have been satisfied for free — a club consisting of such `M` — and it is exactly what
`IsClubOmega.cofinal` rules out: every club must contain a model holding any prescribed `D`
(`exists_model_containing` in `Corpus.lean`).  Stated here so the escape route is on the record
next to the definition it would exploit. -/

theorem isGenericFor_of_modelSets_eq_empty {P : Type*} [PartialOrder P]
    {M : Set (P ⊕ Set P)} (hM : modelSets M = ∅) (q : P) : IsGenericFor M q := by
  intro D hD
  rw [hM] at hD
  exact absurd hD (Set.notMem_empty D)

/-- **What genericity buys**: for each dense `D ∈ M` the trace `D ∩ M` is nonempty.  Immediate
from predensity at `r = q`, but it is the reason a generic condition is worth having — it forces
the model's own copy of every dense set to be inhabited, which is what a filter meeting `D` is
later built from. -/

theorem IsGenericFor.nonempty_inter {P : Type*} [PartialOrder P] {M : Set (P ⊕ Set P)} {q : P}
    (h : IsGenericFor M q) {D : Set P} (hD : D ∈ modelSets M) (hcoi : IsCoinitial D) :
    (D ∩ modelConds M).Nonempty := by
  obtain ⟨a, ha, -⟩ := h D hD hcoi q le_rfl
  exact ⟨a, ha⟩

-- Logic 48: Proper Forcings

/-- `P` is **proper**: for club-many countable models `M`, every condition in `M` has an
`(M,P)`-generic extension. -/

def IsProper (P : Type*) [PartialOrder P] : Prop :=
  ∃ C : Set (Set (P ⊕ Set P)), IsClubOmega C ∧
    ∀ M ∈ C, ∀ p ∈ modelConds M, ∃ q ≤ p, IsGenericFor M q

/-- **`IsProper` cannot be trivialised by shrinking the club.**  Cofinality forces every club to
contain a model holding any prescribed condition and any prescribed dense set, so a generic
condition really has to be produced for every `(p, D)`.  In particular the escape route
`isGenericFor_of_modelSets_eq_empty` — a club of models knowing no sets — is unavailable. -/

theorem exists_model_containing {P : Type*} (C : Set (Set (P ⊕ Set P))) (hC : IsClubOmega C)
    (p : P) (D : Set P) : ∃ M ∈ C, Sum.inl p ∈ M ∧ Sum.inr D ∈ M := by
  obtain ⟨y, hy, hsub⟩ :=
    hC.cofinal {Sum.inl p, Sum.inr D} ((Set.finite_singleton _).insert _).countable
  exact ⟨y, hy, hsub (by simp), hsub (by simp)⟩

theorem isProper_punit : IsProper PUnit := by
  refine ⟨{x : Set (PUnit ⊕ Set PUnit) | x.Countable ∧ Sum.inl PUnit.unit ∈ x},
    isClubOmega_mem _, ?_⟩
  rintro M ⟨-, hM⟩ p -
  refine ⟨p, le_refl p, fun D _ hcoi r _ => ?_⟩
  obtain ⟨b, hb, -⟩ := hcoi r
  exact ⟨b, ⟨hb, by simpa [modelConds] using hM⟩, r, le_refl r, le_refl r⟩

end MathlibExtTest.SetTheory.Forcing.ForcingAxioms.Proper

end

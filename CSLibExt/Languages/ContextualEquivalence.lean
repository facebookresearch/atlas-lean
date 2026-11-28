/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.OperationalSemantics

/-!
# Generic contextual equivalence

Generic contextual equivalence (`CtxEquiv`) and approximation (`CtxApprox`) over a typed
context algebra (`CtxAlgebra`) with observations (`CtxObs`) drawn from the anchor operational
semantics. Contexts form an explicit family with plugging, hole, and composition laws.
Observations supply program judgments, outcomes, per-judgment labels, anchor semantics, and an
outcome relation. This module states the generic relations with their adequacy and closure
properties. No language instances, bridges, or compatibility results
appear here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ContextualEquivalence

universe u v

open Cslib.Languages.OperationalSemantics

/-- Typed context algebra: term and context families with plugging. -/
structure CtxAlgebra (J : Type u) where
  /-- Term family indexed by judgment. -/
  Tm : J → Type u
  /-- Context family from one judgment to another. -/
  Ctx : J → J → Type u
  /-- Plug a term into a context. -/
  plug : {j k : J} → Ctx j k → Tm j → Tm k
  /-- The identity (hole) context. -/
  hole : {j : J} → Ctx j j
  /-- Compose two contexts. -/
  comp : {j k l : J} → Ctx k l → Ctx j k → Ctx j l
  /-- Plugging into the hole returns the term. -/
  plug_hole : ∀ {j : J} (t : Tm j), plug hole t = t
  /-- Plugging into a composition plugs in sequence. -/
  plug_comp : ∀ {j k l : J} (D : Ctx k l) (C : Ctx j k) (t : Tm j),
    plug (comp D C) t = plug D (plug C t)

/-- Observations over a context algebra: programs, outcomes, and semantics. -/
structure CtxObs {J : Type u} (A : CtxAlgebra J) where
  /-- Program judgments. -/
  Prog : J → Prop
  /-- Outcome type. -/
  Outcome : Type v
  /-- Label family for the semantics `sem`. -/
  Label : J → Type v
  /-- Operational semantics at each program judgment. -/
  sem : ∀ {k : J}, Prog k → OpSem (A.Tm k) (Label k)
  /-- Outcome relation on configurations. -/
  outcome : ∀ {k : J}, A.Tm k → Outcome → Prop

/-- A program yields an outcome through a final reachable configuration. -/
def Yields {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) {k : J}
    (hk : O.Prog k) (p : A.Tm k) (o : O.Outcome) : Prop :=
  ∃ q : A.Tm k, (O.sem hk).Steps p q ∧ (O.sem hk).Final q ∧ O.outcome q o

/-- Contextual approximation: all yielded outcomes are preserved. -/
def CtxApprox {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) {j : J}
    (t u : A.Tm j) : Prop :=
  ∀ {k : J} (hk : O.Prog k) (C : A.Ctx j k) (o : O.Outcome),
    Yields O hk (A.plug C t) o → Yields O hk (A.plug C u) o

/-- Contextual equivalence: yielded outcomes coincide both ways. -/
def CtxEquiv {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) {j : J}
    (t u : A.Tm j) : Prop :=
  ∀ {k : J} (hk : O.Prog k) (C : A.Ctx j k) (o : O.Outcome),
    Yields O hk (A.plug C t) o ↔ Yields O hk (A.plug C u) o

/-- Judgment-indexed families of term relations. -/
abbrev RelFamily {J : Type u} (A : CtxAlgebra J) :=
  ∀ (j : J), A.Tm j → A.Tm j → Prop

/-- Approximation adequacy: related programs preserve yielded outcomes. -/
def ApproxAdequate {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    (R : RelFamily A) : Prop :=
  ∀ {k : J} (hk : O.Prog k) (p q : A.Tm k) (o : O.Outcome),
    R k p q → Yields O hk p o → Yields O hk q o

/-- Adequacy: related programs yield exactly the same outcomes. -/
def Adequate {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    (R : RelFamily A) : Prop :=
  ∀ {k : J} (hk : O.Prog k) (p q : A.Tm k) (o : O.Outcome),
    R k p q → (Yields O hk p o ↔ Yields O hk q o)

/-- Contextual closure: relations are preserved under plugging. -/
def CtxClosed {J : Type u} {A : CtxAlgebra J} (R : RelFamily A) : Prop :=
  ∀ {j k : J} (C : A.Ctx j k) {t u : A.Tm j},
    R j t u → R k (A.plug C t) (A.plug C u)

/-- Contextual approximation is reflexive. -/
theorem ctxApprox_refl {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    {j : J} (t : A.Tm j) : CtxApprox O t t := by
  intro _ hk C o h
  exact h

/-- Contextual approximation is transitive. -/
theorem ctxApprox_trans {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    {j : J} {t u w : A.Tm j} :
    CtxApprox O t u → CtxApprox O u w → CtxApprox O t w := by
  intro h1 h2 _ hk C o h
  exact h2 hk C o (h1 hk C o h)

/-- Contextual approximation is closed under contexts. -/
theorem ctxApprox_ctxClosed {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) :
    CtxClosed (fun (j : J) (t u : A.Tm j) => CtxApprox O t u) := by
  intro _ _ C _ _ h _ hl D o hy
  rw [← A.plug_comp D C _] at hy
  rw [← A.plug_comp D C _]
  exact h hl (A.comp D C) o hy

/-- Contextual approximation is approximately adequate. -/
theorem ctxApprox_approxAdequate {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) :
    ApproxAdequate O (fun (j : J) (t u : A.Tm j) => CtxApprox O t u) := by
  intro _ hk p q o h hy
  rw [← A.plug_hole p] at hy
  have h2 := h hk A.hole o hy
  rw [A.plug_hole] at h2
  exact h2

/-- Contextual approximation contains every approximately adequate, context-closed family. -/
theorem ctxApprox_isGreatest {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    (R : RelFamily A) :
    ApproxAdequate O R → CtxClosed R →
      (∀ (j : J) (t u : A.Tm j), R j t u → CtxApprox O t u) := by
  intro hA hC _ _ u hR _ hk C o hy
  exact hA hk _ _ o (hC C hR) hy

/-- Contextual equivalence is reflexive. -/
theorem ctxEquiv_refl {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    {j : J} (t : A.Tm j) : CtxEquiv O t t := by
  intro _ hk C o
  exact Iff.rfl

/-- Contextual equivalence is symmetric. -/
theorem ctxEquiv_symm {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    {j : J} {t u : A.Tm j} : CtxEquiv O t u → CtxEquiv O u t := by
  intro h _ hk C o
  exact (h hk C o).symm

/-- Contextual equivalence is transitive. -/
theorem ctxEquiv_trans {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    {j : J} {t u w : A.Tm j} :
    CtxEquiv O t u → CtxEquiv O u w → CtxEquiv O t w := by
  intro h1 h2 _ hk C o
  exact (h1 hk C o).trans (h2 hk C o)

/-- Contextual equivalence is closed under contexts. -/
theorem ctxEquiv_ctxClosed {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) :
    CtxClosed (fun (j : J) (t u : A.Tm j) => CtxEquiv O t u) := by
  intro _ _ C _ _ h _ hl D o
  rw [← A.plug_comp D C _]
  rw [← A.plug_comp D C _]
  exact h hl (A.comp D C) o

/-- Contextual equivalence is adequate. -/
theorem ctxEquiv_adequate {J : Type u} {A : CtxAlgebra J} (O : CtxObs A) :
    Adequate O (fun (j : J) (t u : A.Tm j) => CtxEquiv O t u) := by
  intro _ hk p q o h
  have h2 := h hk A.hole o
  rw [A.plug_hole] at h2
  rw [A.plug_hole] at h2
  exact h2

/-- Contextual equivalence contains every adequate closed family. -/
theorem ctxEquiv_isGreatest {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    (R : RelFamily A) :
    Adequate O R → CtxClosed R →
      (∀ (j : J) (t u : A.Tm j), R j t u → CtxEquiv O t u) := by
  intro hA hC _ t u hR _ hk C o
  exact hA hk _ _ o (hC C hR)

/-- Contextual equivalence is mutual contextual approximation. -/
theorem ctxEquiv_iff_ctxApprox {J : Type u} {A : CtxAlgebra J} (O : CtxObs A)
    {j : J} {t u : A.Tm j} :
    CtxEquiv O t u ↔ CtxApprox O t u ∧ CtxApprox O u t := by
  constructor
  · intro h
    constructor
    · intro _ hk C o hy
      exact (h hk C o).mp hy
    · intro _ hk C o hy
      exact (h hk C o).mpr hy
  · rintro ⟨h1, h2⟩ _ hk C o
    constructor
    · intro hy
      exact h1 hk C o hy
    · intro hy
      exact h2 hk C o hy

end Cslib.Languages.ContextualEquivalence

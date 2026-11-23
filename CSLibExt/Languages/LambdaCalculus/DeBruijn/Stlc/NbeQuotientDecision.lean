/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Decidable beta-eta quotient equality
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeDecision

/-!
# Decidable equality of beta-eta classes

The normal-form equivalence gives beta-eta quotient classes a computable
equality test whenever base types have decidable equality.  The comparison is
independent of quotient representatives and exposes useful extensionality and
classification principles.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u} [DecidableEq Base]
variable {A : Ty Base}
variable {Γ : List (Ty Base)}

namespace BetaEtaClass

/-- Compare two beta-eta classes through their unique eta-long normal forms. -/
def equivalent (q r : BetaEtaClass Base Γ A) : Bool :=
  decide (normalForm q = normalForm r)

@[simp] theorem equivalent_eq_true {q r : BetaEtaClass Base Γ A} :
    equivalent q r = true ↔ q = r := by
  rw [equivalent, decide_eq_true_eq]
  exact betaEtaClass_eq_iff_normalForm_eq.symm

@[simp] theorem equivalent_eq_false {q r : BetaEtaClass Base Γ A} :
    equivalent q r = false ↔ q ≠ r := by
  rw [Bool.eq_false_iff]
  exact not_congr equivalent_eq_true

/-- Beta-eta quotient equality is decidable through normal forms. -/
instance instDecidableEq : DecidableEq (BetaEtaClass Base Γ A) :=
  fun q r => decidable_of_iff (normalForm q = normalForm r)
    betaEtaClass_eq_iff_normalForm_eq.symm

/-- Quotient comparison is reflexive. -/
@[simp] theorem equivalent_refl (q : BetaEtaClass Base Γ A) :
    equivalent q q = true := equivalent_eq_true.mpr rfl

/-- Quotient comparison is symmetric. -/
theorem equivalent_comm (q r : BetaEtaClass Base Γ A) :
    equivalent q r = equivalent r q := by
  apply Bool.eq_iff_iff.mpr
  simp only [equivalent_eq_true]
  exact ⟨Eq.symm, Eq.symm⟩

/-- Positive quotient comparison is transitive. -/
theorem equivalent_trans {q r s : BetaEtaClass Base Γ A}
    (hqr : equivalent q r = true) (hrs : equivalent r s = true) :
    equivalent q s = true :=
  equivalent_eq_true.mpr
    ((equivalent_eq_true.mp hqr).trans (equivalent_eq_true.mp hrs))

/-- Comparing embedded terms agrees with the term-level beta-eta decision. -/
theorem equivalent_ofTm (t u : Tm Γ A) :
    equivalent (ofTm t) (ofTm u) = betaEtaEquivalent t u := by
  apply Bool.eq_iff_iff.mpr
  simp only [equivalent_eq_true, betaEtaEquivalent_eq_true]
  exact ⟨exact, sound⟩

/-- Comparing embedded normal forms reduces to structural equality. -/
theorem equivalent_nf (n m : Nf Γ A) :
    equivalent (ofTm n.toTm) (ofTm m.toTm) = decide (n = m) := by
  rw [equivalent_ofTm, betaEtaEquivalent_nf_toTm]

omit [DecidableEq Base] in
/-- A quotient class is equal to the embedding of its canonical
representative. -/
theorem eq_canonical (q : BetaEtaClass Base Γ A) :
    q = ofTm (normalForm q).toTm := betaEtaClass_eq_of_normalForm q

omit [DecidableEq Base] in
/-- Equality can be proved solely by equality of observed normal forms. -/
theorem ext {q r : BetaEtaClass Base Γ A}
    (h : normalForm q = normalForm r) : q = r :=
  betaEtaClass_eq_iff_normalForm_eq.mpr h

omit [DecidableEq Base] in
/-- Equality of observed normal forms implies equality of quotient classes;
equivalently, `normalForm` is injective. -/
theorem normalForm_injective {q r : BetaEtaClass Base Γ A}
    (h : normalForm q = normalForm r) : q = r := ext h

omit [DecidableEq Base] in
/-- The canonical representative completely classifies an embedded term. -/
theorem ofTm_eq_iff (t u : Tm Γ A) :
    ofTm t = ofTm u ↔ normalizeNf t = normalizeNf u := by
  rw [← BetaEtaEq.iff_normalizeNf_eq]
  exact ⟨exact, sound⟩

omit [DecidableEq Base] in
/-- Equality against an arbitrary quotient class can be checked after
canonicalizing only the embedded side. -/
theorem ofTm_eq_iff_normalForm (t : Tm Γ A) (q : BetaEtaClass Base Γ A) :
    ofTm t = q ↔ normalizeNf t = normalForm q := by
  rw [betaEtaClass_eq_iff_normalForm_eq]
  rfl

omit [DecidableEq Base] in
/-- The canonical representative map is surjective. -/
theorem normalForm_surjective_onto_representatives :
    ∀ q : BetaEtaClass Base Γ A,
      ∃ n : Nf Γ A, q = ofTm n.toTm := by
  intro q
  exact ⟨normalForm q, eq_canonical q⟩

end BetaEtaClass

namespace NbeClass

/-- Observational quotient equality is likewise decidable through eta-long
normal forms. -/
instance instDecidableEq : DecidableEq (NbeClass Base Γ A) :=
  fun q r => decidable_of_iff (normalForm q = normalForm r) (by
      constructor
      · intro h
        exact (equivNormalForm (Base := Base) (Γ := Γ) (A := A)).injective h
      · exact congrArg normalForm)

/-- Compare observational classes through their normal forms. -/
def equivalent (q r : NbeClass Base Γ A) : Bool := decide (q = r)

@[simp] theorem equivalent_eq_true {q r : NbeClass Base Γ A} :
    equivalent q r = true ↔ q = r := by
  simp only [equivalent, decide_eq_true_eq]

@[simp] theorem equivalent_eq_false {q r : NbeClass Base Γ A} :
    equivalent q r = false ↔ q ≠ r := by
  rw [Bool.eq_false_iff]
  exact not_congr equivalent_eq_true

/-- The declarative and observational quotient comparisons agree through the
canonical equivalence. -/
theorem equivalent_betaEta (q r : BetaEtaClass Base Γ A) :
    equivalent (betaEtaToNbe q) (betaEtaToNbe r) =
      BetaEtaClass.equivalent q r := by
  apply Bool.eq_iff_iff.mpr
  simp only [equivalent_eq_true, BetaEtaClass.equivalent_eq_true]
  exact ⟨fun h => betaEtaToNbe_injective h, congrArg betaEtaToNbe⟩

end NbeClass

end Cslib.Languages.LambdaCalculus.Stlc

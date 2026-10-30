/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Operational consequences of STLC normalization
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.LogicalRelation

/-!
# Operational consequences of STLC normalization

The logical relation establishes that every closed term evaluates to a value.
This file packages that result into an operational interface: normal forms
exist and are unique, closed functions evaluate to lambdas, closed base terms
do not exist in the constant-free calculus, and equality of evaluation results
is an equivalence and a congruence for application.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ : List (Ty Base)}

namespace Steps

/-- A value can only evaluate to itself. -/
theorem eq_of_value_source {v t : Tm Γ A} (hv : Value v) (h : Steps v t) : v = t := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rw [← ih] at hstep
      exact (Step.value_irreducible hv hstep).elim

/-- Two value endpoints of a deterministic evaluation are equal. -/
theorem value_unique {t v w : Tm Γ A} (htv : Steps t v) (hv : Value v)
    (htw : Steps t w) (hw : Value w) : v = w := by
  have hwv : Steps w v := suffix_of_value htv hv htw
  exact (eq_of_value_source hw hwv).symm

end Steps

/-- A closed term normalizes when it evaluates to a normal form. -/
def Normalizes (t : Tm [] A) : Prop := ∃ n, Steps t n ∧ Step.NormalForm n

namespace Normalizes

/-- Termination and normalization coincide for closed well-typed terms. -/
theorem iff_terminates {t : Tm [] A} : Normalizes t ↔ Terminates t := by
  constructor
  · rintro ⟨n, htn, hn⟩
    exact ⟨n, htn, (Step.closed_normalForm_iff_value n).mp hn⟩
  · rintro ⟨v, htv, hv⟩
    exact ⟨v, htv, (Step.closed_normalForm_iff_value v).mpr hv⟩

end Normalizes

/-- Every closed well-typed term evaluates to a normal form. -/
theorem normalizes_closed (t : Tm [] A) : Normalizes t :=
  Normalizes.iff_terminates.mpr (terminates_closed t)

/-- A closed term has at most one reachable normal form. -/
theorem normalForm_unique {t n m : Tm [] A} (htn : Steps t n) (hn : Step.NormalForm n)
    (htm : Steps t m) (hm : Step.NormalForm m) : n = m := by
  exact Steps.value_unique htn ((Step.closed_normalForm_iff_value n).mp hn)
    htm ((Step.closed_normalForm_iff_value m).mp hm)

/-- Every closed function evaluates to a lambda abstraction. -/
theorem closed_function_evaluates_to_lam (f : Tm [] (A ⇒ B)) :
    ∃ body : Tm [A] B, Steps f (.lam body) := by
  rcases terminates_closed f with ⟨v, hfv, hv⟩
  rcases Step.closed_function_value_is_lam hv with ⟨body, rfl⟩
  exact ⟨body, hfv⟩

/-- There are no closed terms of a base type in the pure, constant-free calculus. -/
theorem no_closed_base (b : Base) (t : Tm [] (.base b)) : False := by
  rcases terminates_closed t with ⟨v, _, hv⟩
  cases hv

/-- Two terms have the same result when they evaluate to a common value. -/
def SameResult (t u : Tm [] A) : Prop :=
  ∃ v, Steps t v ∧ Steps u v ∧ Value v

namespace SameResult

/-- Every closed term has the same result as itself. -/
theorem refl (t : Tm [] A) : SameResult t t := by
  rcases terminates_closed t with ⟨v, htv, hv⟩
  exact ⟨v, htv, htv, hv⟩

/-- Equality of results is symmetric. -/
theorem symm {t u : Tm [] A} (h : SameResult t u) : SameResult u t := by
  rcases h with ⟨v, htv, huv, hv⟩
  exact ⟨v, huv, htv, hv⟩

/-- Equality of results is transitive. -/
theorem trans {t u v : Tm [] A} (htu : SameResult t u) (huv : SameResult u v) :
    SameResult t v := by
  rcases htu with ⟨r, htr, hur, hr⟩
  rcases huv with ⟨s, hus, hvs, hs⟩
  have hrs : r = s := Steps.value_unique hur hr hus hs
  subst s
  exact ⟨r, htr, hvs, hr⟩

/-- A multi-step evaluation does not change the result of a term. -/
theorem of_steps {t u : Tm [] A} (htu : Steps t u) : SameResult t u := by
  rcases terminates_closed u with ⟨v, huv, hv⟩
  exact ⟨v, htu.trans huv, huv, hv⟩

/-- Taking steps on the left preserves equality of results. -/
theorem anti_left {t t' u : Tm [] A} (htt' : Steps t t') (h : SameResult t' u) :
    SameResult t u := (of_steps htt').trans h

/-- Taking steps on the right preserves equality of results. -/
theorem anti_right {t u u' : Tm [] A} (huu' : Steps u u') (h : SameResult t u') :
    SameResult t u := h.trans (of_steps huu').symm

/-- Application respects equality of call-by-value results. -/
theorem app {f g : Tm [] (A ⇒ B)} {a b : Tm [] A}
    (hfg : SameResult f g) (hab : SameResult a b) :
    SameResult (.app f a) (.app g b) := by
  rcases hfg with ⟨vf, hfvf, hgvf, hvf⟩
  rcases hab with ⟨va, hava, hbva, hva⟩
  rcases Step.closed_function_value_is_lam hvf with ⟨body, rfl⟩
  rcases terminates_closed (Tm.instantiate body va) with ⟨r, hbody, hvr⟩
  have left : Steps (.app f a) r :=
    (Steps.appFun a hfvf).trans <|
      (Steps.appArg (.lam body) hava).trans <|
        (Relation.ReflTransGen.single (.beta hva)).trans hbody
  have right : Steps (.app g b) r :=
    (Steps.appFun b hgvf).trans <|
      (Steps.appArg (.lam body) hbva).trans <|
        (Relation.ReflTransGen.single (.beta hva)).trans hbody
  exact ⟨r, left, right, hvr⟩

end SameResult

/-- Equality of evaluation results is an equivalence relation on closed terms. -/
theorem sameResult_equivalence : Equivalence (@SameResult Base A) :=
  ⟨SameResult.refl, SameResult.symm, SameResult.trans⟩

end Cslib.Languages.LambdaCalculus.Stlc

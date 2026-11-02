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

/-- **Values reduce only to themselves.** Let $v$ and $t$ be terms of the same type in the same
context. If $v$ is a value and $v$ reduces to $t$ in zero or more call-by-value steps, then
$v = t$. -/
theorem eq_of_value_source {v t : Tm Γ A} (hv : Value v) (h : Steps v t) : v = t := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rw [← ih] at hstep
      exact (Step.value_irreducible hv hstep).elim

/-- **Uniqueness of the value reached by evaluation.** Let $t$ be a term in any context. If $t$
reduces in zero or more call-by-value steps to a value $v$ and also to a value $w$, then
$v = w$. -/
theorem value_unique {t v w : Tm Γ A} (htv : Steps t v) (hv : Value v)
    (htw : Steps t w) (hw : Value w) : v = w := by
  have hwv : Steps w v := suffix_of_value htv hv htw
  exact (eq_of_value_source hw hwv).symm

end Steps

/-- **Normalizing closed terms.** A closed term $t$ of the simply typed lambda calculus normalizes
when it reduces, in zero or more call-by-value steps, to a term in normal form, that is, a term
with no further call-by-value reduction step. -/
def Normalizes (t : Tm [] A) : Prop := ∃ n, Steps t n ∧ Step.NormalForm n

namespace Normalizes

/-- **Normalization and termination coincide.** A closed well-typed term $t$ normalizes, that is,
reduces in zero or more call-by-value steps to a normal form (a term with no further reduction
step), if and only if it terminates, that is, reduces in zero or more call-by-value steps to a
value. -/
theorem iff_terminates {t : Tm [] A} : Normalizes t ↔ Terminates t := by
  constructor
  · rintro ⟨n, htn, hn⟩
    exact ⟨n, htn, (Step.closed_normalForm_iff_value n).mp hn⟩
  · rintro ⟨v, htv, hv⟩
    exact ⟨v, htv, (Step.closed_normalForm_iff_value v).mpr hv⟩

end Normalizes

/-- **Normalization of closed terms.** Every closed well-typed term normalizes: it reduces in
zero or more call-by-value steps to a normal form. -/
theorem normalizes_closed (t : Tm [] A) : Normalizes t :=
  Normalizes.iff_terminates.mpr (terminates_closed t)

/-- **Uniqueness of normal forms.** If a closed term $t$ reduces in zero or more call-by-value
steps to a normal form $n$ and also to a normal form $m$, then $n = m$. -/
theorem normalForm_unique {t n m : Tm [] A} (htn : Steps t n) (hn : Step.NormalForm n)
    (htm : Steps t m) (hm : Step.NormalForm m) : n = m := by
  exact Steps.value_unique htn ((Step.closed_normalForm_iff_value n).mp hn)
    htm ((Step.closed_normalForm_iff_value m).mp hm)

/-- **Closed functions evaluate to lambda abstractions.** For every closed term $f$ of a function
type $A \Rightarrow B$ there is a term $b$ of type $B$ in the context with a single variable of
type $A$ such that $f$ reduces, in zero or more call-by-value steps, to the lambda abstraction
with body $b$. -/
theorem closed_function_evaluates_to_lam (f : Tm [] (A ⇒ B)) :
    ∃ body : Tm [A] B, Steps f (.lam body) := by
  rcases terminates_closed f with ⟨v, hfv, hv⟩
  rcases Step.closed_function_value_is_lam hv with ⟨body, rfl⟩
  exact ⟨body, hfv⟩

/-- **No closed terms of base type.** In the pure, constant-free calculus there is no closed
term whose type is a base type. -/
theorem no_closed_base (b : Base) (t : Tm [] (.base b)) : False := by
  rcases terminates_closed t with ⟨v, _, hv⟩
  cases hv

/-- **Closed terms with the same result.** Two closed terms $t$ and $u$ of the same type have the
same result when there is a value $v$ such that both $t$ and $u$ reduce to $v$ in zero or more
call-by-value steps. -/
def SameResult (t u : Tm [] A) : Prop :=
  ∃ v, Steps t v ∧ Steps u v ∧ Value v

namespace SameResult

/-- Every closed term has the same result as itself. -/
theorem refl (t : Tm [] A) : SameResult t t := by
  rcases terminates_closed t with ⟨v, htv, hv⟩
  exact ⟨v, htv, htv, hv⟩

/-- **Symmetry of having the same result.** If closed terms $t$ and $u$ have the same result,
then $u$ and $t$ have the same result. -/
theorem symm {t u : Tm [] A} (h : SameResult t u) : SameResult u t := by
  rcases h with ⟨v, htv, huv, hv⟩
  exact ⟨v, huv, htv, hv⟩

/-- **Transitivity of having the same result.** If closed terms $t$ and $u$ have the same result,
and $u$ and a closed term $v$ have the same result, then $t$ and $v$ have the same result. -/
theorem trans {t u v : Tm [] A} (htu : SameResult t u) (huv : SameResult u v) :
    SameResult t v := by
  rcases htu with ⟨r, htr, hur, hr⟩
  rcases huv with ⟨s, hus, hvs, hs⟩
  have hrs : r = s := Steps.value_unique hur hr hus hs
  subst s
  exact ⟨r, htr, hvs, hr⟩

/-- **Evaluation preserves the result of a closed term.** If a closed term $t$ reduces to a
term $u$ in zero or more call-by-value steps, then $t$ and $u$ have the same result. -/
theorem of_steps {t u : Tm [] A} (htu : Steps t u) : SameResult t u := by
  rcases terminates_closed u with ⟨v, huv, hv⟩
  exact ⟨v, htu.trans huv, huv, hv⟩

/-- **Left expansion preserves having the same result.** Let $t$, $t'$ and $u$ be closed terms of
the same type. If $t$ reduces to $t'$ in zero or more call-by-value steps, and $t'$ and $u$ have
the same result, then $t$ and $u$ have the same result. -/
theorem anti_left {t t' u : Tm [] A} (htt' : Steps t t') (h : SameResult t' u) :
    SameResult t u := (of_steps htt').trans h

/-- **Right expansion preserves having the same result.** Let $t$, $u$ and $u'$ be closed terms
of the same type. If $u$ reduces to $u'$ in zero or more call-by-value steps, and $t$ and $u'$
have the same result, then $t$ and $u$ have the same result. -/
theorem anti_right {t u u' : Tm [] A} (huu' : Steps u u') (h : SameResult t u') :
    SameResult t u := h.trans (of_steps huu').symm

/-- **Application preserves having the same result.** Let $f$ and $g$ be closed terms of a
function type $A \Rightarrow B$, and let $a$ and $b$ be closed terms of type $A$. If $f$ and $g$
have the same result and $a$ and $b$ have the same result, then the applications $f\,a$ and
$g\,b$ have the same result. -/
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

/-- **Having the same result is an equivalence relation.** For every simple type $A$, the
relation of having the same result is an equivalence relation on the closed terms of type $A$. -/
theorem sameResult_equivalence : Equivalence (@SameResult Base A) :=
  ⟨SameResult.refl, SameResult.symm, SameResult.trans⟩

end Cslib.Languages.LambdaCalculus.Stlc

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
# Strong normalization of call-by-value STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.BigStep
public import Cslib.Foundations.Relation.Defs

/-!
# Strong normalization of call-by-value STLC

The logical relation supplies a finite evaluation from every closed term to a
value.  Since call-by-value reduction is deterministic, that finite path rules
out every infinite path.  This file makes the argument explicit using
accessibility, rules out infinite reduction streams, and records a step-indexed
evaluation relation whose cost and value result are unique.

`StronglyNormalizing` is upstream `Relation.SN` instantiated at the call-by-value step
relation `Step` (`stronglyNormalizing_iff_sn`).  It is termination of this weak,
deterministic strategy, not strong normalization of full beta reduction.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

universe u

variable {Base : Type u}
variable {A : Ty Base}
variable {Γ : List (Ty Base)}

/-- The converse of one-step evaluation, oriented for `Acc`. -/
def ReducesFrom (t' t : Tm Γ A) : Prop := Step t t'

/-- A term is strongly normalizing for the call-by-value step relation `Step` when the
converse of `Step` is accessible from it.  This is upstream `Relation.SN Step` (see
`stronglyNormalizing_iff_sn`).  Since `Step` never reduces under a binder, this is not
strong normalization of full beta reduction. -/
def StronglyNormalizing (t : Tm Γ A) : Prop := Acc ReducesFrom t

/-- `StronglyNormalizing` is the upstream strong-normalization predicate `Relation.SN` for
`Step`. -/
theorem stronglyNormalizing_iff_sn {t : Tm Γ A} : StronglyNormalizing t ↔ Relation.SN Step t :=
  Iff.rfl

namespace StronglyNormalizing

/-- A deterministic finite evaluation to a value establishes accessibility. -/
theorem of_steps_value {t v : Tm Γ A} (htv : Steps t v) (hv : Value v) :
    StronglyNormalizing t := by
  induction htv using Relation.ReflTransGen.head_induction_on with
  | refl =>
      apply Acc.intro
      intro y hy
      exact (Step.value_irreducible hv hy).elim
  | @head t middle hstep hrest ih =>
      apply Acc.intro
      intro y hy
      have hmiddle : middle = y := Step.deterministic hstep hy
      subst y
      exact ih

/-- Strong normalization is preserved by taking one evaluation step. -/
theorem step {t t' : Tm Γ A} (ht : StronglyNormalizing t) (htt' : Step t t') :
    StronglyNormalizing t' := ht.inv htt'

/-- Strong normalization is preserved by taking finitely many evaluation steps. -/
theorem steps {t t' : Tm Γ A} (ht : StronglyNormalizing t) (htt' : Steps t t') :
    StronglyNormalizing t' := by
  induction htt' with
  | refl => exact ht
  | tail _ hstep ih => exact ih.step hstep

end StronglyNormalizing

/-- Every closed well-typed term is strongly normalizing. -/
theorem stronglyNormalizing_closed (t : Tm [] A) : StronglyNormalizing t := by
  rcases terminates_closed t with ⟨v, htv, hv⟩
  exact StronglyNormalizing.of_steps_value htv hv

/-- An infinite reduction stream beginning at `t`. -/
def InfiniteReduction (t : Tm Γ A) : Prop :=
  ∃ stream : Nat → Tm Γ A, stream 0 = t ∧ ∀ n, Step (stream n) (stream (n + 1))

namespace StronglyNormalizing

/-- Accessibility excludes an infinite reduction stream. -/
theorem not_infinite {t : Tm Γ A} (ht : StronglyNormalizing t) : ¬InfiniteReduction t := by
  rintro ⟨stream, hzero, hstep⟩
  induction ht generalizing stream with
  | intro current hnext ih =>
      have hfirst : ReducesFrom (stream 1) current := by
        change Step current (stream 1)
        rw [← hzero]
        exact hstep 0
      apply ih (stream 1) hfirst (stream := fun n ↦ stream (n + 1))
      · rfl
      · intro n
        simpa [Nat.add_assoc] using hstep (n + 1)

end StronglyNormalizing

/-- No closed well-typed term begins an infinite call-by-value reduction. -/
theorem no_infinite_reduction (t : Tm [] A) : ¬InfiniteReduction t :=
  (stronglyNormalizing_closed t).not_infinite

/-- Exactly `n` left-to-right call-by-value steps. -/
inductive StepsN : Nat → Tm Γ A → Tm Γ A → Prop where
  | refl (t : Tm Γ A) : StepsN 0 t t
  | head {n : Nat} {t u v : Tm Γ A} : Step t u → StepsN n u v → StepsN (n + 1) t v

namespace StepsN

/-- Forget the exact length of an evaluation. -/
theorem to_steps {n : Nat} {t u : Tm Γ A} (h : StepsN n t u) : Steps t u := by
  induction h with
  | refl => exact .refl
  | head hstep _ ih => exact Relation.ReflTransGen.head hstep ih

/-- Every finite multi-step evaluation has an exact length. -/
theorem of_steps {t u : Tm Γ A} (h : Steps t u) : ∃ n, StepsN n t u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hstep _ ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, .head hstep hn⟩

/-- Exact evaluations from one term to values have the same cost and result. -/
theorem value_cost_unique {n m : Nat} {t v w : Tm Γ A}
    (htv : StepsN n t v) (hv : Value v) (htw : StepsN m t w) (hw : Value w) :
    n = m ∧ v = w := by
  induction htv generalizing m w with
  | refl =>
      cases htw with
      | refl => exact ⟨rfl, rfl⟩
      | head hstep _ => exact (Step.value_irreducible hv hstep).elim
  | @head n t u v htu huv ih =>
      cases htw with
      | refl => exact (Step.value_irreducible hw htu).elim
      | @head m _ u' w htu' hu'w =>
          have huu' : u = u' := Step.deterministic htu htu'
          subst u'
          rcases ih hv hu'w hw with ⟨hnm, hvw⟩
          exact ⟨congrArg (· + 1) hnm, hvw⟩

end StepsN

/-- Every closed term has a uniquely determined finite evaluation cost and value result. -/
theorem exists_unique_cost_value (t : Tm [] A) :
    ∃ n v, StepsN n t v ∧ Value v ∧
      ∀ m w, StepsN m t w → Value w → m = n ∧ w = v := by
  rcases terminates_closed t with ⟨v, htv, hv⟩
  rcases StepsN.of_steps htv with ⟨n, hnv⟩
  refine ⟨n, v, hnv, hv, ?_⟩
  intro m w hmw hw
  exact StepsN.value_cost_unique hmw hw hnv hv

end Cslib.Languages.LambdaCalculus.Stlc

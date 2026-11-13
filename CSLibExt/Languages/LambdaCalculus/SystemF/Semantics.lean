/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Typing

/-!
# Call-by-value safety for pure System F

Evaluation is weak, left-to-right call-by-value. Both lambda forms are values;
term beta requires a value argument, whereas type beta admits any type.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- The two value forms of pure System F. -/
inductive Value : {n m : Nat} → Tm n m → Prop where
  | lam {n m : Nat} {A : Ty n} {b : Tm n (m + 1)} : Value (.lam A b)
  | tabs {n m : Nat} {b : Tm (n + 1) m} : Value (.tabs b)

/-- One step of weak, left-to-right call-by-value evaluation. -/
inductive Step : {n m : Nat} → Tm n m → Tm n m → Prop where
  | appFun {n m : Nat} {f f' a : Tm n m} :
      Step f f' → Step (.app f a) (.app f' a)
  | appArg {n m : Nat} {f a a' : Tm n m} :
      Value f → Step a a' → Step (.app f a) (.app f a')
  | beta {n m : Nat} {A : Ty n} {b : Tm n (m + 1)} {a : Tm n m} :
      Value a → Step (.app (.lam A b) a) (b.instantiate a)
  | tappFun {n m : Nat} {f f' : Tm n m} {A : Ty n} :
      Step f f' → Step (.tapp f A) (.tapp f' A)
  | tyBeta {n m : Nat} {b : Tm (n + 1) m} {A : Ty n} :
      Step (.tapp (.tabs b) A) (b.tySubst (Fin.cases A Ty.var))

/-- Zero or more call-by-value evaluation steps. -/
abbrev Steps {n m : Nat} : Tm n m → Tm n m → Prop :=
  Relation.ReflTransGen Step

variable {n m : Nat} {Γ : Ctx n m} {A : Ty n} {t t' : Tm n m}

/-- A call-by-value step preserves the exact type in arbitrary open contexts. -/
theorem preservation (ht : Typing Γ t A) (hs : Step t t') :
    Typing Γ t' A := by
  induction hs generalizing A with
  | appFun hs ih =>
    cases ht with
    | app hf ha => exact .app (ih hf) ha
  | appArg hv hs ih =>
    cases ht with
    | app hf ha => exact .app hf (ih ha)
  | beta hv =>
    cases ht with
    | app hf ha => cases hf with
      | lam hb => exact hb.instantiate ha
  | tappFun hs ih =>
    cases ht with
    | tapp hf => exact .tapp (ih hf)
  | tyBeta =>
    cases ht with
    | tapp hf => cases hf with
      | tabs hb => exact hb.tyInstantiate _

/-- A function-typed value is a term lambda with the declared argument type. -/
theorem Typing.canonical_lam {B : Ty n} (ht : Typing Γ t (.arr A B))
    (hv : Value t) : ∃ b : Tm n (m + 1), t = .lam A b := by
  cases hv with
  | lam => cases ht with
    | lam hb => exact ⟨_, rfl⟩
  | tabs => cases ht

/-- A universally typed value is a type lambda. -/
theorem Typing.canonical_tabs {C : Ty (n + 1)}
    (ht : Typing Γ t (.all C)) (hv : Value t) :
    ∃ b : Tm (n + 1) m, t = .tabs b := by
  cases hv with
  | lam => cases ht
  | tabs => cases ht with
    | tabs hb => exact ⟨_, rfl⟩

private theorem progress_aux (h : Typing Γ t A) (hm : m = 0) :
    Value t ∨ ∃ t', Step t t' := by
  induction h with
  | var i =>
    exact (Nat.ne_of_gt
      (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) hm).elim
  | lam => exact .inl .lam
  | tabs => exact .inl .tabs
  | app hf ha ihf iha =>
    rcases ihf hm with hvf | ⟨f', hs⟩
    · rcases iha hm with hva | ⟨a', hs⟩
      · obtain ⟨b, rfl⟩ := hf.canonical_lam hvf
        exact .inr ⟨_, .beta hva⟩
      · exact .inr ⟨_, .appArg hvf hs⟩
    · exact .inr ⟨_, .appFun hs⟩
  | tapp hf ih =>
    rcases ih hm with hv | ⟨f', hs⟩
    · obtain ⟨b, rfl⟩ := hf.canonical_tabs hv
      exact .inr ⟨_, .tyBeta⟩
    · exact .inr ⟨_, .tappFun hs⟩

/-- A well-typed term with no free term variables is a value or can step. -/
theorem progress {Γ : Ctx n 0} {t : Tm n 0} (ht : Typing Γ t A) :
    Value t ∨ ∃ t', Step t t' :=
  progress_aux ht rfl

/-- Every finite evaluation sequence preserves the exact type. -/
theorem preservation_steps (ht : Typing Γ t A) (hs : Steps t t') :
    Typing Γ t' A := by
  induction hs with
  | refl => exact ht
  | tail hs hstep ih => exact preservation ih hstep

/-- No term reachable from a closed well-typed term is stuck. -/
theorem safety {Γ : Ctx n 0} {t t' : Tm n 0}
    (ht : Typing Γ t A) (hs : Steps t t') :
    Value t' ∨ ∃ t'', Step t' t'' :=
  progress (preservation_steps ht hs)

end Cslib.Languages.LambdaCalculus.SystemF

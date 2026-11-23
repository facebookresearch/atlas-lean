/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.SystemF.FullReduction
import CSLibExt.Languages.LambdaCalculus.SystemF.Semantics

/-! # Full reduction and subject reduction probes -/

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- `∀ α. α → α`. -/
private def tyIdType : Ty 0 := .all (.arr (.var 0) (.var 0))

/-- `Λ α. λ x : α. x`. -/
private def tyIdTerm : Tm 0 0 := .tabs (.lam (.var 0) (.var 0))

-- Type beta at a quantified argument substitutes into the annotation, and
-- subject reduction types the reduct.
example : FullStep (.tapp tyIdTerm tyIdType) (.lam tyIdType (.var 0)) :=
  .tyBeta

example : Typing Fin.elim0 (.lam tyIdType (.var 0) : Tm 0 0)
    (.arr tyIdType tyIdType) :=
  FullStep.preservation (t := .tapp tyIdTerm tyIdType)
    (.tapp (.tabs (.lam (.var 0)))) .tyBeta

-- Type beta under an inner type binder: in `(Λ α. Λ β. λ x : α → β → γ. x) γ`
-- the argument `γ` is shifted under `β`, so `β` does not capture it.
example : FullStep
    (.tapp (.tabs (.tabs (.lam (.arr (.var 1) (.arr (.var 0) (.var 2)))
      (.var 0)))) (.var 0) : Tm 1 0)
    (.tabs (.lam (.arr (.var 1) (.arr (.var 0) (.var 1))) (.var 0))) :=
  .tyBeta

-- Term beta under an inner term binder: in `(λ x. λ y. x) z₁` the free
-- argument `z₁` is shifted under `y`.
example (A : Ty 0) : FullStep
    (.app (.lam A (.lam A (.var 1))) (.var 1) : Tm 0 2) (.lam A (.var 2)) :=
  .beta

-- Term beta under a type binder in the body shifts the argument's free type
-- variables and leaves its term variables alone.
example (A : Ty 1) : FullStep
    (.app (.lam A (.tabs (.var 0))) (.tapp (.var 0) (.var 0)) : Tm 1 1)
    (.tabs (.tapp (.var 0) (.var 1))) :=
  .beta

-- A redex under a term binder: full reduction contracts it and keeps the type,
-- while call-by-value `Step` cannot reduce a lambda at all.
example (A : Ty 0) : FullStep
    (.lam A (.app (.lam A (.var 0)) (.var 0)) : Tm 0 0) (.lam A (.var 0)) :=
  .lam .beta

example (A : Ty 0) : Typing Fin.elim0 (.lam A (.var 0) : Tm 0 0) (.arr A A) :=
  FullStep.preservation (t := .lam A (.app (.lam A (.var 0)) (.var 0)))
    (.lam (.app (.lam (.var 0)) (.var 0))) (.lam .beta)

example (A : Ty 0) (t : Tm 0 0) :
    ¬ Step (.lam A (.app (.lam A (.var 0)) (.var 0)) : Tm 0 0) t := by
  intro h
  cases h

-- A redex under a type binder: full reduction contracts it to the polymorphic
-- identity, which keeps the type `∀ α. α → α`.
example : FullStep
    (.tabs (.app (.lam (.arr (.var 0) (.var 0)) (.var 0))
      (.lam (.var 0) (.var 0))) : Tm 0 0) tyIdTerm :=
  .tabs .beta

example : Typing Fin.elim0 tyIdTerm tyIdType :=
  FullStep.preservation
    (t := .tabs (.app (.lam (.arr (.var 0) (.var 0)) (.var 0))
      (.lam (.var 0) (.var 0))))
    (.tabs (.app (.lam (.var 0)) (.lam (.var 0)))) (.tabs .beta)

-- The argument of a neutral application reduces under full reduction, while
-- call-by-value `Step` is stuck because a variable is not a value.
example (A : Ty 0) : FullStep
    (.app (.var 0) (.app (.lam A (.var 0)) (.var 0)) : Tm 0 1)
    (.app (.var 0) (.var 0)) :=
  .appArg .beta

example (A : Ty 0) (t : Tm 0 1) :
    ¬ Step (.app (.var 0) (.app (.lam A (.var 0)) (.var 0)) : Tm 0 1) t := by
  intro h
  cases h with
  | appFun h => cases h
  | appArg hv _ => cases hv

end Cslib.Languages.LambdaCalculus.SystemF

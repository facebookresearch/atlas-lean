/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.MorphismProperty.Factorization.WholeFunctor
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.EquivalenceComposition

/-!
# Entire original two-factor diagrams from the same data through composition

Both complete factorizations are the original supplied source, middle and
target, with the same i/p and caller composite. Their whole functor identity
is determined by the original Z/i/p fields, across all Arrow squares.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD uE vE
open CategoryTheory

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]

/-- The entire original two-factor functor depends on the same complete original map fields. -/
theorem originalFactorizationFunctor_congr {W₁ W₂ V₁ V₂ : MorphismProperty C}
    (data : FunctorialFactorizationData W₁ W₂) (data' : FunctorialFactorizationData V₁ V₂)
    (hZ : data.Z = data'.Z) (hi : HEq data.i data'.i) (hp : HEq data.p data'.p) :
    data.originalFactorizationFunctor = data'.originalFactorizationFunctor := by
  cases data with
  | mk Z i p fac hI hP =>
    cases data' with
    | mk Z' i' p' fac' hI' hP' =>
      cases hZ
      cases hi
      cases hp
      rfl

section Composition

variable {W₁ W₂ : MorphismProperty E} [W₁.RespectsIso] [W₂.RespectsIso]

/-- The entire original factorization functor is the same direct and iterated carrier route. -/
theorem originalFactorizationFunctor_trans
    (data : FunctorialFactorizationData W₁ W₂) (e : C ≌ D) (f : D ≌ E) :
    ((data.ofEquivalence f).ofEquivalence e).originalFactorizationFunctor =
      (data.ofEquivalence (e.trans f)).originalFactorizationFunctor := by
  apply originalFactorizationFunctor_congr
  · exact data.ofEquivalence_trans_Z e f
  · apply heq_of_eq
    ext a
    exact data.ofEquivalence_trans_i e f a
  · apply heq_of_eq
    ext a
    exact data.ofEquivalence_trans_p e f a

end Composition
end CategoryTheory.MorphismProperty.FunctorialFactorizationData

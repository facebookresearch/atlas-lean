/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.GradedCompositionActions
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.GradedCompositionActionsTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]

example {Γ Δ : Center V} {F G H K : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor)
    (u : GradedNatTrans Δ G.toEnrichedFunctor H.toEnrichedFunctor) (q : H ⟶ K) :
    gradedPostcomp (Γ ⊗ Δ) (GradedNatTrans.tensorComp t u) q =
      GradedNatTrans.tensorComp t (gradedPostcomp Δ u q) :=
  tensorComp_gradedPostcomp t u q

example {Γ Δ : Center V} {F' F G H : EnrichedFunctorCat V A}
    (p : F' ⟶ F) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor)
    (u : GradedNatTrans Δ G.toEnrichedFunctor H.toEnrichedFunctor) :
    gradedPrecomp (Γ ⊗ Δ) p (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (gradedPrecomp Γ p t) u :=
  tensorComp_gradedPrecomp p t u

example {Γ Δ : Center V} {F G H K : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H)
    (u : GradedNatTrans Δ H.toEnrichedFunctor K.toEnrichedFunctor) :
    GradedNatTrans.tensorComp (gradedPostcomp Γ t q) u =
      GradedNatTrans.tensorComp t (gradedPrecomp Δ q u) :=
  tensorComp_gradedMiddle t q u

end CategoryTheory.EnrichedFunctorCat.GradedCompositionActionsTests

#check CategoryTheory.EnrichedFunctorCat.tensorComp_gradedPostcomp
#check CategoryTheory.EnrichedFunctorCat.tensorComp_gradedPrecomp
#check CategoryTheory.EnrichedFunctorCat.tensorComp_gradedMiddle
#print axioms CategoryTheory.EnrichedFunctorCat.tensorComp_gradedPostcomp
#print axioms CategoryTheory.EnrichedFunctorCat.tensorComp_gradedPrecomp
#print axioms CategoryTheory.EnrichedFunctorCat.tensorComp_gradedMiddle
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.GradedCompositionActions

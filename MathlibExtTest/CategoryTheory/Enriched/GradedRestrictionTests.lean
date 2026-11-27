/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.GradedRestriction
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxRecDepth 512
universe uA uB uC uV vV
open CategoryTheory MonoidalCategory

namespace CategoryTheory.GradedRestrictionTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]
  (j : EnrichedFunctor V A B)

example {Γ : Center V} {F G : EnrichedFunctor V B C}
    (t : GradedNatTrans Γ F G) (a : A) :
    (GradedNatTrans.restrict j t).app a = t.app (j.obj a) :=
  GradedNatTrans.restrict_app j t a

example {Γ Δ : Center V} {F G H : EnrichedFunctor V B C}
    (t : GradedNatTrans Γ F G) (u : GradedNatTrans Δ G H) :
    GradedNatTrans.restrict j (GradedNatTrans.tensorComp t u) =
      GradedNatTrans.tensorComp (GradedNatTrans.restrict j t) (GradedNatTrans.restrict j u) :=
  GradedNatTrans.restrict_tensorComp j t u

example {Γ Δ : Center V} (h : Γ ⟶ Δ) {F G : EnrichedFunctor V B C}
    (t : GradedNatTrans Δ F G) :
    GradedNatTrans.restrict j (GradedNatTrans.regrade h t) =
      GradedNatTrans.regrade h (GradedNatTrans.restrict j t) :=
  GradedNatTrans.restrict_regrade j h t

end CategoryTheory.GradedRestrictionTests

#check CategoryTheory.GradedNatTrans.restrict
#check CategoryTheory.GradedNatTrans.restrict_app
#check CategoryTheory.GradedNatTrans.restrict_tensorComp
#check CategoryTheory.GradedNatTrans.restrict_regrade
#print axioms CategoryTheory.GradedNatTrans.restrict
#print axioms CategoryTheory.GradedNatTrans.restrict_app
#print axioms CategoryTheory.GradedNatTrans.restrict_tensorComp
#print axioms CategoryTheory.GradedNatTrans.restrict_regrade
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.GradedRestriction

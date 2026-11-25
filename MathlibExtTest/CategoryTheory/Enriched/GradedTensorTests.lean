/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.GradedTensor
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.GradedTensorTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {F G H : EnrichedFunctorCat V A}

example (Γ : Center V)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (a : A) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.gradedTensorToUnit Γ t) a =
      GradedNatTrans.gradeFirstComponent Γ t a :=
  EnrichedFunctorCat.gradedTensorToUnit_component Γ t a

example (Γ : Center V) (q : EnrichedFunctorCat.tensorLeftObject Γ.1 F ⟶ G)
    (a : A) :
    (EnrichedFunctorCat.gradedTensorOfUnit Γ q).app a =
      MonoidalClosed.curry
        ((Γ.2.β (F.toEnrichedFunctor.obj a)).inv ≫ EnrichedFunctorCat.component q a) :=
  EnrichedFunctorCat.gradedTensorOfUnit_app Γ q a

example (Γ : Center V)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    (EnrichedFunctorCat.gradedTensorHomEquiv Γ F G).symm
        ((EnrichedFunctorCat.gradedTensorHomEquiv Γ F G) t) = t :=
  (EnrichedFunctorCat.gradedTensorHomEquiv Γ F G).symm_apply_apply t

example (Γ : Center V) (q : EnrichedFunctorCat.tensorLeftObject Γ.1 F ⟶ G) :
    (EnrichedFunctorCat.gradedTensorHomEquiv Γ F G)
        ((EnrichedFunctorCat.gradedTensorHomEquiv Γ F G).symm q) = q :=
  (EnrichedFunctorCat.gradedTensorHomEquiv Γ F G).apply_symm_apply q

example (Γ : Center V)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H)
    (a : A) :
    GradedNatTrans.gradeFirstComponent Γ
        (EnrichedFunctorCat.gradedPostcomp Γ t q) a =
      GradedNatTrans.gradeFirstComponent Γ t a ≫ EnrichedFunctorCat.component q a :=
  EnrichedFunctorCat.gradeFirstComponent_gradedPostcomp Γ t q a

example (Γ : Center V)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H)
    (a : A) :
    EnrichedFunctorCat.component
        (EnrichedFunctorCat.gradedTensorToUnit Γ
          (EnrichedFunctorCat.gradedPostcomp Γ t q)) a =
      GradedNatTrans.gradeFirstComponent Γ t a ≫ EnrichedFunctorCat.component q a :=
  (EnrichedFunctorCat.gradedTensorToUnit_component Γ
    (EnrichedFunctorCat.gradedPostcomp Γ t q) a).trans
      (EnrichedFunctorCat.gradeFirstComponent_gradedPostcomp Γ t q a)

example {Γ Γ' : Center V} (u : Γ ⟶ Γ')
    (t : GradedNatTrans Γ' F.toEnrichedFunctor G.toEnrichedFunctor) :
    EnrichedFunctorCat.gradedTensorToUnit Γ (GradedNatTrans.regrade u t) =
      EnrichedFunctorCat.scalarTensorMap u.f F ≫
        EnrichedFunctorCat.gradedTensorToUnit Γ' t :=
  EnrichedFunctorCat.gradedTensorToUnit_regrade u t

example (q : F ⟶ G) (a : A) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj (𝟙_ V)) q a =
      (λ_ (F.toEnrichedFunctor.obj a)).hom ≫ EnrichedFunctorCat.component q a :=
  EnrichedFunctorCat.gradeFirstUnit_component q a

example : True := by
  fail_if_success have _sourceCategory : Category A := inferInstance
  trivial

end CategoryTheory.GradedTensorTests

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.GradedComponentActions
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.GradedTensor

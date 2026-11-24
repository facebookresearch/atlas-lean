/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.GradedInputComposition
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (Γ : Center V) {F G H : EnrichedFunctorCat V A} (p : F ⟶ G)
    (t : GradedNatTrans Γ G.toEnrichedFunctor H.toEnrichedFunctor) (a : A) :
    (gradedPrecomp Γ p t).app a =
      t.app a ≫ (MonoidalClosed.pre (component p a)).app (H.toEnrichedFunctor.obj a) :=
  gradedPrecomp_app Γ p t a

example (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) (a : A) :
    (gradedPostcomp Γ t q).app a =
      t.app a ≫ (ihom (F.toEnrichedFunctor.obj a)).map (component q a) :=
  gradedPostcomp_app Γ t q a

example {Γ Γ' : Center V} (u : Γ ⟶ Γ') {F G H : EnrichedFunctorCat V A} (p : F ⟶ G)
    (t : GradedNatTrans Γ' G.toEnrichedFunctor H.toEnrichedFunctor) :
    gradedPrecomp Γ p (GradedNatTrans.regrade u t) =
      GradedNatTrans.regrade u (gradedPrecomp Γ' p t) :=
  gradedPrecomp_regrade u p t

example {Γ Γ' : Center V} (u : Γ ⟶ Γ') {F G H : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ' F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) :
    gradedPostcomp Γ (GradedNatTrans.regrade u t) q =
      GradedNatTrans.regrade u (gradedPostcomp Γ' t q) :=
  gradedPostcomp_regrade u t q

example (Γ : Center V) {F' F G G' : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ G') :
    gradedPrecomp Γ p (gradedPostcomp Γ t q) = gradedPostcomp Γ (gradedPrecomp Γ p t) q :=
  gradedPrecomp_postcomp Γ p t q

example {F G H : EnrichedFunctorCat V A} (p : F ⟶ G) (t : G ⟶ H) :
    gradedPrecomp ((Center.ofBraided V).obj (𝟙_ V)) p t = p ≫ t :=
  gradedPrecomp_unit p t

example {F G H : EnrichedFunctorCat V A} (t : F ⟶ G) (q : G ⟶ H) :
    gradedPostcomp ((Center.ofBraided V).obj (𝟙_ V)) t q = t ≫ q :=
  gradedPostcomp_unit t q

example (Γ : Center V) {F G H K : EnrichedFunctorCat V A} (p : F ⟶ G) (q : G ⟶ H)
    (t : GradedNatTrans Γ H.toEnrichedFunctor K.toEnrichedFunctor) :
    gradedPrecomp Γ (p ≫ q) t = gradedPrecomp Γ p (gradedPrecomp Γ q t) :=
  gradedPrecomp_comp Γ p q t

example (Γ : Center V) {F G H K : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) (r : H ⟶ K) :
    gradedPostcomp Γ t (q ≫ r) = gradedPostcomp Γ (gradedPostcomp Γ t q) r :=
  gradedPostcomp_comp Γ t q r

end CategoryTheory.EnrichedFunctorCat

#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp
#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp_app
#check CategoryTheory.EnrichedFunctorCat.gradedPostcomp
#check CategoryTheory.EnrichedFunctorCat.gradedPostcomp_app
#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp_id
#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp_comp
#check CategoryTheory.EnrichedFunctorCat.gradedPostcomp_id
#check CategoryTheory.EnrichedFunctorCat.gradedPostcomp_comp
#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp_regrade
#check CategoryTheory.EnrichedFunctorCat.gradedPostcomp_regrade
#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp_postcomp
#check CategoryTheory.EnrichedFunctorCat.gradedPrecomp_unit
#check CategoryTheory.EnrichedFunctorCat.gradedPostcomp_unit

#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp_app
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPostcomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPostcomp_app
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp_id
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp_comp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPostcomp_id
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPostcomp_comp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPostcomp_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPrecomp_unit
#print axioms CategoryTheory.EnrichedFunctorCat.gradedPostcomp_unit

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.GradedInputComposition

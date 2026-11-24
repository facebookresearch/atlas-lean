/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.GradeNaturality
import Batteries.Tactic.Lint

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace GradeNaturalityInterfaceTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]
  (Γ : Center V) {F G : EnrichedFunctor V A V}
  (q : ∀ a, Γ.1 ⊗ F.obj a ⟶ G.obj a)
  (hq : ∀ a b, (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
    (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ q b =
    (q a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.map a b))

set_option maxHeartbeats 200000 in
example : True := by
  fail_if_success letI : Category A := inferInstance
  fail_if_success letI : BraidedCategory V := inferInstance
  trivial

set_option maxHeartbeats 200000 in
example (t : GradedNatTrans Γ F G) (a b : A) :
    (α_ Γ.1 (F.obj a) (a ⟶[V] b)).hom ≫
      (Γ.1 ◁ MonoidalClosed.uncurry (F.map a b)) ≫ GradedNatTrans.gradeFirstComponent Γ t b =
    (GradedNatTrans.gradeFirstComponent Γ t a ▷ (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (G.map a b) :=
  GradedNatTrans.gradeFirstComponent_naturality Γ t a b

set_option maxHeartbeats 200000 in
example (a : A) :
    (GradedNatTrans.ofGradeFirstComponents Γ q hq).app a =
      MonoidalClosed.curry ((Γ.2.β (F.obj a)).inv ≫ q a) :=
  GradedNatTrans.ofGradeFirstComponents_app Γ q hq a

set_option maxHeartbeats 200000 in
example (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (GradedNatTrans.ofGradeFirstComponents Γ q hq) a = q a :=
  GradedNatTrans.ofGradeFirstComponents_gradeFirstComponent Γ q hq a

set_option maxHeartbeats 200000 in
example (t : GradedNatTrans Γ F G) :
    GradedNatTrans.ofGradeFirstComponents Γ (GradedNatTrans.gradeFirstComponent Γ t)
      (fun a b => GradedNatTrans.gradeFirstComponent_naturality Γ t a b) = t :=
  GradedNatTrans.ofGradeFirstComponents_reconstruct Γ t

set_option maxHeartbeats 200000 in
example (t t' : GradedNatTrans Γ F G)
    (h : ∀ a, GradedNatTrans.gradeFirstComponent Γ t a =
      GradedNatTrans.gradeFirstComponent Γ t' a) : t = t' :=
  GradedNatTrans.gradeFirstComponent_ext Γ t t' h

set_option maxHeartbeats 200000 in
example {Γ' : Center V} (u : Γ ⟶ Γ') (t : GradedNatTrans Γ' F G) (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (GradedNatTrans.regrade u t) a =
      (u.f ▷ F.obj a) ≫ GradedNatTrans.gradeFirstComponent Γ' t a :=
  GradedNatTrans.gradeFirstComponent_regrade Γ u t a

#print axioms GradedNatTrans.gradeFirstComponent
#print axioms GradedNatTrans.gradeFirstNaturality_iff
#print axioms GradedNatTrans.gradeFirstComponent_naturality
#print axioms GradedNatTrans.ofGradeFirstComponents
#print axioms GradedNatTrans.ofGradeFirstComponents_app
#print axioms GradedNatTrans.ofGradeFirstComponents_gradeFirstComponent
#print axioms GradedNatTrans.ofGradeFirstComponents_reconstruct
#print axioms GradedNatTrans.gradeFirstComponent_ext
#print axioms GradedNatTrans.gradeFirstComponent_regrade
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.GradeNaturality

end GradeNaturalityInterfaceTests

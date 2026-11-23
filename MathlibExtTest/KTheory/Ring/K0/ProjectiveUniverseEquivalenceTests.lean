/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.K0.ProjectiveUniverseEquivalence

noncomputable section

open CategoryTheory AlgebraicKTheory

universe u v

#check FGProjectiveCat.universeEquivalence
#print axioms FGProjectiveCat.universeEquivalence
#check FGProjectiveCat.UniverseEquivalence.shrinkFunctor_map_apply
#print axioms FGProjectiveCat.UniverseEquivalence.shrinkFunctor_map_apply
#check FGProjectiveCat.UniverseEquivalence.liftFunctor_map_apply
#print axioms FGProjectiveCat.UniverseEquivalence.liftFunctor_map_apply
#check FGProjectiveCat.universeEquivalence_unit_hom_apply
#print axioms FGProjectiveCat.universeEquivalence_unit_hom_apply
#check FGProjectiveCat.universeEquivalence_counit_hom_apply
#print axioms FGProjectiveCat.universeEquivalence_counit_hom_apply
#check RingK0.projectiveUniverseEquiv
#print axioms RingK0.projectiveUniverseEquiv
#check RingK0.projectiveUniverseEquiv_mk
#print axioms RingK0.projectiveUniverseEquiv_mk
#check RingK0.projectiveUniverseEquiv_symm_mk
#print axioms RingK0.projectiveUniverseEquiv_symm_mk
#check @RingK0.mk_shrink_lift
#print axioms RingK0.mk_shrink_lift
#check RingK0.projectiveUniverseEquiv_regular
#print axioms RingK0.projectiveUniverseEquiv_regular
#check RingK0.sInverseSComponentsUniverseEquiv
#print axioms RingK0.sInverseSComponentsUniverseEquiv
#check RingK0.sInverseSComponentsUniverseEquiv_mk
#print axioms RingK0.sInverseSComponentsUniverseEquiv_mk

section

variable (R : Type u) [Ring R]

example : FGProjectiveCat.{max u v} R ≌ FGProjectiveCat.{u} R :=
  FGProjectiveCat.universeEquivalence.{u, v} R

example (M : FGProjectiveCat.{max u v} R) (x : M) :
    FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{u, v} R M
      ((FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{u, v} R M).symm x) = x :=
  (FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{u, v} R M).apply_symm_apply x

example {M N : FGProjectiveCat.{max u v} R} (f : M ⟶ N)
    (x : FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R M) :
    ((FGProjectiveCat.UniverseEquivalence.shrinkFunctor.{u, v} R).map f).hom.hom x =
      (FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{u, v} R N).symm
        (f.hom.hom (FGProjectiveCat.UniverseEquivalence.shrinkLinearEquiv.{u, v} R M x)) :=
  FGProjectiveCat.UniverseEquivalence.shrinkFunctor_map_apply.{u, v} R f x

example {M N : FGProjectiveCat.{u} R} (f : M ⟶ N)
    (x : FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M) :
    ((FGProjectiveCat.UniverseEquivalence.liftFunctor.{u, v} R).map f).hom.hom x =
      (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{u, v} R N).symm
        (f.hom.hom (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{u, v} R M x)) :=
  FGProjectiveCat.UniverseEquivalence.liftFunctor_map_apply.{u, v} R f x

example (M : FGProjectiveCat.{max u v} R) :
    (FGProjectiveCat.universeEquivalence.{u, v} R).unitIso.hom.app M ≫
        (FGProjectiveCat.universeEquivalence.{u, v} R).unitIso.inv.app M = 𝟙 M :=
  ((FGProjectiveCat.universeEquivalence.{u, v} R).unitIso.app M).hom_inv_id

example (M : FGProjectiveCat.{u} R) :
    (FGProjectiveCat.universeEquivalence.{u, v} R).counitIso.inv.app M ≫
        (FGProjectiveCat.universeEquivalence.{u, v} R).counitIso.hom.app M = 𝟙 M :=
  ((FGProjectiveCat.universeEquivalence.{u, v} R).counitIso.app M).inv_hom_id

example : (FGProjectiveCat.universeEquivalence.{u, v} R).functor.Additive ∧
    (FGProjectiveCat.universeEquivalence.{u, v} R).inverse.Additive ∧
    (FGProjectiveCat.universeEquivalence.{u, v} R).functor.IsExact ∧
    (FGProjectiveCat.universeEquivalence.{u, v} R).inverse.IsExact :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

example (M : FGProjectiveCat.{max u v} R) :
    RingK0.projectiveUniverseEquiv.{u, v} R (K0.mk M) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R M) :=
  RingK0.projectiveUniverseEquiv_mk.{u, v} R M

example (M : FGProjectiveCat.{u} R) :
    (RingK0.projectiveUniverseEquiv.{u, v} R).symm (K0.mk M) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M) :=
  RingK0.projectiveUniverseEquiv_symm_mk.{u, v} R M

-- Plain simp preserves the public lifted-generator API through its normal-form rule.
example (M : FGProjectiveCat.{u} R) :
    RingK0.projectiveUniverseEquiv.{u, v} R
      (K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R M)) = K0.mk M := by
  simp

example :
    RingK0.projectiveUniverseEquiv.{u, v} R
        (K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R
          (FGProjectiveCat.of (R := R) R))) =
      K0.mk (FGProjectiveCat.of (R := R) R) :=
  RingK0.projectiveUniverseEquiv_regular.{u, v} R

example (P Q : FGProjectiveCat.{u} R) :
    RingK0.projectiveUniverseEquiv.{u, v} R
        (K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R P) -
          K0.mk (FGProjectiveCat.UniverseEquivalence.liftObject.{u, v} R Q)) =
      K0.mk P - K0.mk Q := by
  simp

example (P Q : FGProjectiveCat.{max u v} R) :
    RingK0.projectiveUniverseEquiv.{u, v} R (K0.mk P - K0.mk Q) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R P) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R Q) := by
  simp only [map_sub, RingK0.projectiveUniverseEquiv_mk]


example (P Q : FGProjectiveCat.{max u v} R) :
    RingK0.sInverseSComponentsUniverseEquiv.{u, v} R
        (ConnectedComponents.mk (⟨P, Q⟩ : SInverseS.Pair (FGProjectiveCat.{max u v} R))) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R P) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{u, v} R Q) :=
  RingK0.sInverseSComponentsUniverseEquiv_mk.{u, v} R _

end

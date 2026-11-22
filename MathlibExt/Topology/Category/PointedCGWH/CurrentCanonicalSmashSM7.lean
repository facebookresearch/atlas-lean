/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Internal-Hom corner fibrations for pointed CGWH

A smash cofibration and a fibration give a fibration of the supplied internal-Hom pullback
corner. If either input is trivial, the corner is a trivial fibration.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.CurrentCanonicalSmashSM7

/-- Actual smash cofibrations and fibrations give the full original internal-Hom
corner fibration. -/
theorem fibration {A B X Y : PointedCGWH.{u, v}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : cofibrations PointedCGWH.{u, v} i) (hp : fibrations PointedCGWH.{u, v} p)
    (pb : MonoidalClosed.internalHom.PullbackObjObj i p) :
    fibrations PointedCGWH.{u, v} pb.π := by
  rw [← trivialCofibrations_rlp]
  rw [← trivialCofibrations_rlp] at hp
  intro M N j hj
  let po := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedCGWH.{u, v}) i j
  have hpo : trivialCofibrations PointedCGWH.{u, v} po.ι :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right i j hi hj
  exact (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff po pb).mp (hp _ hpo)

/-- Actual trivial smash cofibrations give the full original internal-Hom trivial fibration. -/
theorem trivial_left {A B X Y : PointedCGWH.{u, v}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : trivialCofibrations PointedCGWH.{u, v} i) (hp : fibrations PointedCGWH.{u, v} p)
    (pb : MonoidalClosed.internalHom.PullbackObjObj i p) :
    trivialFibrations PointedCGWH.{u, v} pb.π := by
  rw [← cofibrations_rlp]
  rw [← trivialCofibrations_rlp] at hp
  intro M N j hj
  let po := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedCGWH.{u, v}) i j
  have hpo : trivialCofibrations PointedCGWH.{u, v} po.ι :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left i j hi hj
  exact (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff po pb).mp (hp _ hpo)

/-- Actual trivial target fibrations give the same full original internal-Hom trivial corner. -/
theorem trivial_right {A B X Y : PointedCGWH.{u, v}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : cofibrations PointedCGWH.{u, v} i) (hp : trivialFibrations PointedCGWH.{u, v} p)
    (pb : MonoidalClosed.internalHom.PullbackObjObj i p) :
    trivialFibrations PointedCGWH.{u, v} pb.π := by
  rw [← cofibrations_rlp]
  rw [← cofibrations_rlp] at hp
  intro M N j hj
  let po := Functor.PushoutObjObj.ofHasPushout (curriedTensor PointedCGWH.{u, v}) i j
  have hpo : cofibrations PointedCGWH.{u, v} po.ι :=
    IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct i j hi hj
  exact (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff po pb).mp (hp _ hpo)

end PointedCGWH.CurrentCanonicalSmashSM7

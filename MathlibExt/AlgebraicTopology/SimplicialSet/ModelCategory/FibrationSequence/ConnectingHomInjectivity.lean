/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors

/-!
# Injectivity of the original Kan connecting homomorphism

Exactness at the base gives injectivity of the original degree-two-to-degree-one
connecting map when the total second homotopy group is trivial. Transport along
specified multiplicative equivalences retains that same map and independent
source/target group universes.
-/

noncomputable section

universe u v w

namespace SSet.FibrationSequence.Geometry

private abbrev nativeProjectionTwoHom (S : SSet.FibrationSequence.{u}) :
    SSet.KanComplex.π 2 S.E S.e →* SSet.KanComplex.π 2 S.B S.b :=
  ((SSet.FibrationSequence.Geometry.projectionGroupNatTrans 1).app S).hom

/-- Trivial total second homotopy gives injectivity of the original connecting homomorphism. -/
theorem sequenceConnectingGroupHom_injective (S : SSet.FibrationSequence.{u})
    (hE : Subsingleton (SSet.KanComplex.π 2 S.E S.e)) :
    Function.Injective (SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom S 0) := by
  intro a b hab
  let δ := SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom S 0
  have hδ : δ (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
    rfl
  have hExact : Function.MulExact (nativeProjectionTwoHom S) δ :=
    SSet.FibrationSequence.Geometry.groupExact_at_base 0 S
  obtain ⟨z, hz⟩ := (hExact (a⁻¹ * b)).1 hδ
  have hOne : a⁻¹ * b = 1 :=
    hz.symm.trans ((congrArg (nativeProjectionTwoHom S) (hE.elim z 1)).trans (map_one _))
  exact inv_mul_eq_one.mp hOne

/-- Transport preserves that same connecting injection across independent group universes. -/
theorem sequenceConnectingGroupHom_transport_injective
    {A : Type v} {D : Type w} [Group A] [Group D]
    (S : SSet.FibrationSequence.{u})
    (l : A ≃* SSet.KanComplex.π 2 S.B S.b)
    (r : SSet.KanComplex.π 1 S.fiber S.fiberPoint ≃* D)
    (hE : Subsingleton (SSet.KanComplex.π 2 S.E S.e)) :
    Function.Injective (r.toMonoidHom.comp
      ((SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom S 0).comp l.toMonoidHom)) :=
  r.injective.comp ((sequenceConnectingGroupHom_injective S hE).comp l.injective)

end SSet.FibrationSequence.Geometry

end

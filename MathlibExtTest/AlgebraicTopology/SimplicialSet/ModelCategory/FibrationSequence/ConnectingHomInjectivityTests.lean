/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.ConnectingHomInjectivity

/-!
# Clients of the original Kan connecting injection

The actual connecting kernel is trivial under the total-second-group
criterion, and equality is reflected after transports with independent
source and target group universes.
-/

noncomputable section

universe u v w

namespace SSet.FibrationSequence.Geometry

/-- The original native connecting map has no nonunit kernel value under the total criterion. -/
theorem sequenceConnectingGroupHom_kernel_test (S : SSet.FibrationSequence.{u})
    (hE : Subsingleton (SSet.KanComplex.π 2 S.E S.e))
    (a : SSet.KanComplex.π 2 S.B S.b) (ha : sequenceConnectingGroupHom S 0 a = 1) :
    a = 1 :=
  sequenceConnectingGroupHom_injective S hE (ha.trans (map_one _).symm)

/-- Transported equality reflects equality of the same original source classes. -/
theorem sequenceConnectingGroupHom_transport_eq_iff_test
    {A : Type v} {D : Type w} [Group A] [Group D]
    (S : SSet.FibrationSequence.{u})
    (l : A ≃* SSet.KanComplex.π 2 S.B S.b)
    (r : SSet.KanComplex.π 1 S.fiber S.fiberPoint ≃* D)
    (hE : Subsingleton (SSet.KanComplex.π 2 S.E S.e)) (a b : A) :
    r (sequenceConnectingGroupHom S 0 (l a)) = r (sequenceConnectingGroupHom S 0 (l b)) ↔
      a = b :=
  (sequenceConnectingGroupHom_transport_injective S l r hE).eq_iff

end SSet.FibrationSequence.Geometry

end

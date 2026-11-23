/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GeometricHallStackFunctions
import MathlibExt.AlgebraicGeometry.HallExactSequenceFamilies
import MathlibExt.AlgebraicGeometry.IntegralChowChernModels

/-!
# Integral zero-section and genuine sequence-family probes

The first-Chern probe uses its actual zero-section push and smooth
pullback inverse. The Hall projections retain every component of
an actual sequence isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.HallGeometricFoundations

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open IntegralChowChernModels

example {X : SchemeData} {L : X.scheme.left.Modules}
    (V : LineTotalModel X L) (D : LineChowComparison V) (d : ℤ) (a : Chow X d) :
    smoothPull D.pull (d-1) (firstChern V D d a) =
      chowCast V.total (show d=(d-1)+1 by omega) (properPush D.zeroPush d a) := by
  let e := Equiv.ofBijective (smoothPull D.pull (d-1)) (D.bijective (d-1))
  change e (e.symm _) = _
  exact e.apply_symm_apply _

example {X T : Over (Spec (.of ℂ))}
    {A B : HallExactSequenceFamilies.Sequence (X := X) (T := T)}
    (a : A ⟶ B) :
    (HallExactSequenceFamilies.subobject.map a,
      HallExactSequenceFamilies.middleTerm.map a,
      HallExactSequenceFamilies.quotient.map a) = (a.sub,a.middle,a.quotient) := rfl

end MathlibExtTest.AlgebraicGeometry.HallGeometricFoundations

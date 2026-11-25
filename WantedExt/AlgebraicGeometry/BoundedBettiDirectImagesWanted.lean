/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BoundedBettiDirectImages

/-!
# Native bounded-below sheaf derived adjunction construction

The target uses the native rightDerivedFunctorPlus and its native units,
the actual ordinary sheaf adjunction on every cochain, and the existing
exact derivedPullback. Bijectivity concerns the map defined from that
adjunction and canonical coefficient/shift comparisons.
Source: Kashiwara--Schapira, Sheaves on Manifolds, Section 2.6.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BoundedBettiDirectImagesWanted

open _root_.CategoryTheory _root_.MathlibExt.AlgebraicGeometry.BoundedBettiDirectImages

def_wanted nativeBoundedBettiAdjunction {X Y : TopCat.{0}} (f : X ⟶ Y) : BoundedDerivedAdjunction f

theorem_wanted nativeBoundedBettiComparison {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A : BoundedDerivedAdjunction f) (d : ℤ) : Function.Bijective (cohomologyComparison A d)

end WantedExt.AlgebraicGeometry.BoundedBettiDirectImagesWanted

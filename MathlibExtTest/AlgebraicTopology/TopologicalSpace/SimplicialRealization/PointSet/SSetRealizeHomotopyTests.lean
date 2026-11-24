/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy

/-!
# Realized simplicial homotopy wrapper clients

Direct universe-zero clients of the public `SSet.realizeHomotopy` wrapper:
its exact type plus both endpoint fields for arbitrary simplicial maps/homotopy,
with all homotopy arguments explicit.

Restricted to `SSet.{0}`.

Nonclaims: no homotopy-equivalence, weak-equivalence, additivity,
K-space, or `π₀` content.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial unitInterval

noncomputable section

namespace SSet

example (X Y : SSet.{0}) (f g : X ⟶ Y) (H : SSet.Homotopy f g) :
    ContinuousMap.Homotopy (SSet.toTop.map f).hom (SSet.toTop.map g).hom :=
  SSet.realizeHomotopy X Y f g H

example (X Y : SSet.{0}) (f g : X ⟶ Y) (H : SSet.Homotopy f g)
    (x : ↥(SSet.toTop.obj X)) :
    (SSet.realizeHomotopy X Y f g H) (0, x) = (SSet.toTop.map f).hom x :=
  (SSet.realizeHomotopy X Y f g H).map_zero_left x

example (X Y : SSet.{0}) (f g : X ⟶ Y) (H : SSet.Homotopy f g)
    (x : ↥(SSet.toTop.obj X)) :
    (SSet.realizeHomotopy X Y f g H) (1, x) = (SSet.toTop.map g).hom x :=
  (SSet.realizeHomotopy X Y f g H).map_one_left x

end SSet

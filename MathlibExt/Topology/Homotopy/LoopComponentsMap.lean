/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Topology.Homotopy.LoopComponents

/-!
# Based maps on fundamental groups and loop components

A continuous map `f : X → Y` together with a path from `f x` to a chosen
basepoint `y` induces the usual based map on fundamental groups: first map a
loop based at `x`, then conjugate by the basepoint-change path.  Transporting
this map across `loopComponentsEquivFundamentalGroup` gives a map on path
components of loop spaces.

The representative formula fixes the conjugation order as the inverse
basepoint path, followed by the mapped loop, followed by the basepoint path.
The construction is mixed-universe.  It installs no group structure on loop
components and makes no continuity, equivalence, or homotopy-equivalence
claim about the resulting function.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (p : Path (f x) y)

/-- The based fundamental-group map induced by a continuous map and a path
from the mapped source basepoint to the selected target basepoint. -/
noncomputable def basedFundamentalGroupMap :
    FundamentalGroup X x →* FundamentalGroup Y y :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom.comp
    (FundamentalGroup.map f x)

set_option backward.isDefEq.respectTransparency false in
/-- On a loop representative, `basedFundamentalGroupMap` is literal
conjugation in the order `p⁻¹`, mapped loop, `p`. -/
@[simp]
theorem basedFundamentalGroupMap_mk (gamma : LoopSpace X x) :
    basedFundamentalGroupMap f p
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (p.symm.trans ((gamma.map f.continuous).trans p))) := by
  rfl

/-- The map on path components of loop spaces induced by a continuous map
and an explicit path between the mapped and selected target basepoints. -/
noncomputable def loopComponentsMap :
    ZerothHomotopy (LoopSpace X x) →
      ZerothHomotopy (LoopSpace Y y) :=
  fun q =>
    (loopComponentsEquivFundamentalGroup Y y).symm
      (basedFundamentalGroupMap f p
        (loopComponentsEquivFundamentalGroup X x q))

/-- `loopComponentsMap` sends the component of a loop to the component of
the explicitly conjugated mapped loop. -/
@[simp]
theorem loopComponentsMap_mk (gamma : LoopSpace X x) :
    loopComponentsMap f p (ZerothHomotopy.mk gamma) =
      ZerothHomotopy.mk
        (p.symm.trans ((gamma.map f.continuous).trans p)) := by
  apply (loopComponentsEquivFundamentalGroup Y y).injective
  simp [loopComponentsMap]

/-- Endpoint-fixed homotopic loops determine the same loop-space path
component. -/
theorem zerothHomotopy_mk_eq_of_pathHomotopic
    {gamma delta : LoopSpace X x} (h : gamma.Homotopic delta) :
    ZerothHomotopy.mk gamma = ZerothHomotopy.mk delta := by
  apply (loopComponentsEquivFundamentalGroup X x).injective
  simpa only [loopComponentsEquivFundamentalGroup_mk] using
    (congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr h))

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullbackMappingPath

/-!
# Clients for the actual homotopy-pullback mapping-path projection

The SAME whole left point, right point and carried curve determine the
original mapping-path point. Its original universal property earns
projection fibrancy and the actual all-point fiber map's weakness.
The arbitrary base map is retained without a preservation premise.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackMappingPathTests

open _root_.TopCat.HomotopyPullbackMappingPath

variable {E W B : _root_.TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B)

/-- The actual replacement map retains the full original left point. -/
theorem originalLeftPoint : toReplacement p h ≫ (_root_.TopCat.mappingPathReplacement p).toSource =
    _root_.TopCat.homotopyPullbackLeft p h := toReplacement_toSource p h

/-- The actual replacement map retains the entire original carried path. -/
theorem originalWholePath : toReplacement p h ≫ (_root_.TopCat.mappingPathReplacement p).pathMap =
    _root_.TopCat.homotopyPullbackPath p h := toReplacement_path p h

/-- The actual replacement endpoint is the SAME original right point's base-map image. -/
theorem originalEndpoint : toReplacement p h ≫ (_root_.TopCat.mappingPathReplacement p).toBase =
    _root_.TopCat.homotopyPullbackRight p h ≫ h := toReplacement_toBase p h

/-- The whole original pullback universal property is earned from the actual mapping-path getter. -/
theorem originalPullback :
    IsPullback (toReplacement p h) (_root_.TopCat.homotopyPullbackRight p h)
      (_root_.TopCat.mappingPathReplacement p).toBase h := isPullback p h

/-- The SAME original projection earns actual fibrancy internally. -/
theorem originalProjectionFibration : Fibration (_root_.TopCat.homotopyPullbackRight p h) :=
  rightProjection_fibration p h

/-- The all-point fiber map retains the actual original replacement and arbitrary base map. -/
theorem originalFiberMapWeak (w : W) : _root_.TopCat.weakHomotopyEquivalences
    (_root_.TopCat.homotopyFiberMapOfSquare (toReplacement p h) h
      (toReplacement_toBase p h).symm w) := fiberMap_mem_weakHomotopyEquivalences p h w

/-- The exact old mapping-path inclusion has both original whole inverse families. -/
def originalInclusionEquiv : ContinuousMap.HomotopyEquiv E
    (_root_.TopCat.mappingPathReplacement p).space := inclusionEquiv p

/-- The literal original mapping-path inclusion is weak. -/
theorem originalInclusionWeak : _root_.TopCat.weakHomotopyEquivalences
    (_root_.TopCat.mappingPathReplacement p).inclusion := inclusion_mem_weakHomotopyEquivalences p

/-- The original inclusion fiber map is weak over every point of the SAME identity base. -/
theorem originalInclusionFiberWeak (b : B) : _root_.TopCat.weakHomotopyEquivalences
    (_root_.TopCat.homotopyFiberMapOfSquare (p := p)
      (q := (_root_.TopCat.mappingPathReplacement p).toBase)
      (_root_.TopCat.mappingPathReplacement p).inclusion (𝟙 B)
      (by simpa only [Category.comp_id] using
        (_root_.TopCat.mappingPathReplacement p).inclusionToBase.symm) b) :=
  inclusionFiberMap_mem_weakHomotopyEquivalences p b

end MathlibExtTest.Topology.Category.TopCat.HomotopyPullbackMappingPathTests

end

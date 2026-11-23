/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpace
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence
import MathlibExt.Topology.Homotopy.TopCat.Path

/-!
# Exact-functor maps on the Quillen loop-space carrier

For same-universe exact categories and an additive exact functor `F : C ⥤ D`,
map a loop through `NQReal.map F` and conjugate it by the realized
zero-comparison path. The root path is oriented from the mapped source
basepoint to the chosen target basepoint. Thus, for
`p := NQKSpace.zeroComparisonRootPath F`, the map sends `γ` to

`p.symm.trans ((NQKSpace.mapLoop F γ).trans p)`.

This source layer follows the existing Waldhausen K-space convention. It
does not bundle continuity, prove identity or composition laws, establish
equivalence invariance, identify `π₀` with `K₀`, construct a Q/S comparison,
or define spectra.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Root path from the mapped source basepoint to the chosen target
basepoint. -/
noncomputable def NQKSpace.zeroComparisonRootPath :
    Path (NQReal.map F (NQReal.basepoint C)) (NQReal.basepoint D) :=
  TopCat.pathEquiv (NQReal.zeroComparisonPath F)

/-- The root path is exactly the canonical conversion of the realized
zero-comparison path. -/
@[simp]
theorem NQKSpace.zeroComparisonRootPath_eq :
    NQKSpace.zeroComparisonRootPath C D F =
      TopCat.pathEquiv (NQReal.zeroComparisonPath F) :=
  rfl

/-- Map a loop to the loop based at the mapped source basepoint, before
conjugating to the chosen target basepoint. -/
noncomputable def NQKSpace.mapLoop :
    NQKSpace C →
      Path (NQReal.map F (NQReal.basepoint C))
        (NQReal.map F (NQReal.basepoint C)) :=
  fun γ => γ.map (map_continuous (NQReal.map F).hom)

/-- Pointwise computation for the mapped loop. -/
@[simp]
theorem NQKSpace.mapLoop_apply (γ : NQKSpace C) (t : unitInterval) :
    NQKSpace.mapLoop C D F γ t = NQReal.map F (γ t) :=
  rfl

/-- Exact-functor map on the Quillen K-space carrier, by conjugation with the
mapped-zero-to-target-zero root path. -/
noncomputable def NQKSpaceMap : NQKSpace C → NQKSpace D :=
  fun γ =>
    (NQKSpace.zeroComparisonRootPath C D F).symm.trans
      ((NQKSpace.mapLoop C D F γ).trans
        (NQKSpace.zeroComparisonRootPath C D F))

/-- Exact computation and orientation of the Quillen K-space map. -/
theorem NQKSpaceMap_apply (γ : NQKSpace C) :
    NQKSpaceMap C D F γ =
      (NQKSpace.zeroComparisonRootPath C D F).symm.trans
        ((NQKSpace.mapLoop C D F γ).trans
          (NQKSpace.zeroComparisonRootPath C D F)) :=
  rfl

end AlgebraicKTheory

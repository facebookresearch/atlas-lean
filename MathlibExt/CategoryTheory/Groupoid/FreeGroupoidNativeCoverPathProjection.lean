/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidPositiveCoverFunctor

/-!
# The SAME native original cover path projection

The full native Paths projection is literally the original quiver
prefunctor's full mapPath. All individual original generators and
entire path compositions are read back without replacing arrows.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in the native path readback. -/
private local instance coverQuiverForNativeProjection : Quiver.{v} (CoverVertex V z) :=
  coverQuiver V z

/-- The entire native positive-cover path projection is the SAME original full mapPath. -/
theorem coverPathsProjection_mapPath {a b : CoverVertex V z}
    (p : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b) :
    (coverPathsProjection V z).map p = (coverProjection V z).mapPath p := by
  induction p with
  | nil => rfl
  | cons p f ih =>
    change ((coverPathsProjection V z).map p).cons f.arrow =
      ((coverProjection V z).mapPath p).cons f.arrow
    exact congrArg (fun p => p.cons f.arrow) ih

end Quiver.FreeGroupoid.OriginalWords

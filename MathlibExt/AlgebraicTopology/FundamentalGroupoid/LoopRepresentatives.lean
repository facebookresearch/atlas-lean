/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Based loops representing the original fundamental group

An element of the fundamental group is an endomorphism in the fundamental
groupoid, whose underlying morphism is a homotopy class of based paths. Choose
an actual path in that original class. The quotient and group characteristics
retain the original element, and the mapped-path characteristic uses the actual
based map on fundamental groups.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- An actual based loop representing the original fundamental-group element. -/
noncomputable def loopRepresentative (p : FundamentalGroup X x) : Path x x :=
  Classical.choose (Path.Homotopic.Quotient.mk_surjective p.toPath)

/-- The chosen loop has exactly the original quotient class. -/
theorem mk_loopRepresentative (p : FundamentalGroup X x) :
    Path.Homotopic.Quotient.mk (loopRepresentative p) = p.toPath := by
  unfold loopRepresentative
  exact Classical.choose_spec (Path.Homotopic.Quotient.mk_surjective p.toPath)

/-- Wrapping the chosen path class in the original vertex group recovers the element. -/
theorem fromPath_loopRepresentative (p : FundamentalGroup X x) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopRepresentative p)) = p := by
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk (loopRepresentative p) = p.toPath
  exact mk_loopRepresentative p

/-- The mapped representative, with the actual endpoint casts, represents the
image under the original based fundamental-group map. No strict naturality of
the chosen paths is asserted. -/
theorem fromPath_mapOfEq_loopRepresentative
    {Y : Type v} [TopologicalSpace Y] {y : Y}
    (f : C(X, Y)) (h : f x = y) (p : FundamentalGroup X x) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((loopRepresentative p).map f.continuous).cast h.symm h.symm)) =
      FundamentalGroup.mapOfEq f h p := by
  apply CategoryTheory.End.ext
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
      (((loopRepresentative p).map f.continuous).cast h.symm h.symm) =
    (p.toPath.map f).cast h.symm h.symm
  rw [Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map,
    mk_loopRepresentative]

end FundamentalGroup

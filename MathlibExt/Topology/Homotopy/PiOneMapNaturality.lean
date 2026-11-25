/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.HomotopyGroupMap

/-!
# The original Pi1 comparison commutes with ordinary maps

Postcomposition of the original singleton cube is postcomposition of its
original loop. This gives the Pi1/fundamental-group naturality formula in
independent space universes, its inverse dictionary formula and the whole
monoid-homomorphism square. No singular or Hurewicz comparison is imported.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

namespace HomotopyGroup

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original Pi1 comparison preserves the same ordinary mapped loop class. -/
theorem piOneMulEquivFundamentalGroup_map (f : C(X, Y)) (x : X)
    (a : Pi 1 X x) :
    pi1MulEquivFundamentalGroup (X := Y) (x := f x) (map f a) =
      FundamentalGroup.map f x (pi1MulEquivFundamentalGroup (X := X) (x := x) a) := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [map_mk]
  rfl

/-- The inverse Pi1 dictionary preserves the same original map. -/
theorem piOneMulEquivFundamentalGroup_symm_map (f : C(X, Y)) (x : X)
    (b : FundamentalGroup X x) :
    (pi1MulEquivFundamentalGroup (X := Y) (x := f x)).symm (FundamentalGroup.map f x b) =
      map f ((pi1MulEquivFundamentalGroup (X := X) (x := x)).symm b) := by
  let A := pi1MulEquivFundamentalGroup (X := X) (x := x)
  let B := pi1MulEquivFundamentalGroup (X := Y) (x := f x)
  apply B.injective
  exact (B.apply_symm_apply _).trans
    ((piOneMulEquivFundamentalGroup_map f x (A.symm b)).trans
      (congrArg (FundamentalGroup.map f x) (A.apply_symm_apply b))).symm

/-- The entire original Pi1 and fundamental-group monoid-homomorphism square commutes. -/
theorem piOneMulEquivFundamentalGroup_mapHom (f : C(X, Y)) (x : X) :
    (pi1MulEquivFundamentalGroup (X := Y) (x := f x)).toMonoidHom.comp (mapHom f) =
      (FundamentalGroup.map f x).comp
        (pi1MulEquivFundamentalGroup (X := X) (x := x)).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  exact piOneMulEquivFundamentalGroup_map f x a

end HomotopyGroup

end

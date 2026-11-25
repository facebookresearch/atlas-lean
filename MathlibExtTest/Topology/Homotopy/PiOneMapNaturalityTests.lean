/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.PiOneMapNaturality

/-!
# Clients for the shared original Pi1 map formula

The original singleton-cube and fundamental-group maps commute with the
canonical forward and inverse dictionaries. Independent source, middle
and target universes are retained in the composition client.
-/

public section

noncomputable section

set_option autoImplicit false

universe u v w

namespace MathlibExtTest.Topology.Homotopy.PiOneMapNaturalityTests

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Every original singleton-cube class follows the original mapped-loop dictionary. -/
theorem originalForward (f : C(X, Y)) (x : X) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := f x) (HomotopyGroup.map f a) =
      FundamentalGroup.map f x
        (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x) a) :=
  HomotopyGroup.piOneMulEquivFundamentalGroup_map f x a

/-- Every original fundamental-group class follows the same inverse dictionary. -/
theorem originalInverse (f : C(X, Y)) (x : X) (b : FundamentalGroup X x) :
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := f x)).symm
        (FundamentalGroup.map f x b) =
      HomotopyGroup.map f
        ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).symm b) :=
  HomotopyGroup.piOneMulEquivFundamentalGroup_symm_map f x b

/-- The entire original monoid-homomorphism square uses the same two maps. -/
theorem originalMapSquare (f : C(X, Y)) (x : X) :
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := f x)).toMonoidHom.comp
        (HomotopyGroup.mapHom f) =
      (FundamentalGroup.map f x).comp
        (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).toMonoidHom :=
  HomotopyGroup.piOneMulEquivFundamentalGroup_mapHom f x

/-- Original map composition respects the dictionary in three independent universes. -/
theorem originalComposition (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (X := Z) (x := g (f x))
        (HomotopyGroup.map (g.comp f) a) =
      FundamentalGroup.map g (f x)
        (FundamentalGroup.map f x
          (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x) a)) :=
  (congrArg (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Z) (x := g (f x)))
    (HomotopyGroup.map_comp f g a)).trans
      ((HomotopyGroup.piOneMulEquivFundamentalGroup_map g (f x) (HomotopyGroup.map f a)).trans
        (congrArg (FundamentalGroup.map g (f x))
          (HomotopyGroup.piOneMulEquivFundamentalGroup_map f x a)))

end MathlibExtTest.Topology.Homotopy.PiOneMapNaturalityTests

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.HomotopyGroup
public import MathlibExt.Topology.Category.PointedCGWH.ToPointedTop
public import MathlibExt.Topology.Category.PointedTopCat.HomotopyGroup

/-!
# Homotopy groups of pointed CGWH spaces

The direct inclusion of pointed CGWH spaces into pointed topological spaces
transports the existing literal-degree cube homotopy-group functors.  Degree
`n` means the actual `n`th homotopy type; positive groups are exposed
separately at actual degree `n + 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory

namespace PointedCGWH

/-- The selected point after inclusion is evaluation of the included point
map at `PUnit.unit`. -/
@[simp]
theorem toPointedTop_obj_underlyingBasepoint (X : PointedCGWH.{u, v}) :
    PointedTopCat.underlyingBasepoint (toPointedTop.obj X) =
      (CGWH.cgwhToTop.map X.hom).hom PUnit.unit :=
  rfl

/-- The point of the underlying pointed topological space. -/
def underlyingBasepoint (X : PointedCGWH.{u, v}) :
    CGWH.cgwhToTop.obj X.right :=
  PointedTopCat.underlyingBasepoint (toPointedTop.obj X)

/-- A pointed CGWH map preserves the selected underlying point. -/
theorem underlyingBasepoint_naturality
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (CGWH.cgwhToTop.map f.right).hom (underlyingBasepoint X) =
      underlyingBasepoint Y :=
  PointedTopCat.underlyingBasepoint_naturality (toPointedTop.map f)

/-- The literal degree-`n` cube homotopy type of a pointed CGWH space. -/
noncomputable abbrev piN (n : ℕ) (X : PointedCGWH.{u, v}) : Type v :=
  HomotopyGroup.Pi n (CGWH.cgwhToTop.obj X.right)
    (underlyingBasepoint X)

/-- Literal degree-`n` homotopy as a Type-valued functor. -/
noncomputable def piNFunctor (n : ℕ) :
    PointedCGWH.{u, v} ⥤ Type v :=
  toPointedTop.{u, v} ⋙ PointedTopCat.homotopyGroupTypeFunctor n

/-- The map on literal degree-`n` homotopy induced by a pointed CGWH map. -/
noncomputable def piNMap (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) : piN n X → piN n Y :=
  (piNFunctor n).map f

/-- After reversing the selected-point transport, `piNMap` is the existing
cube-map construction on the underlying topological map. -/
theorem piNMap_apply (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (a : piN n X) :
    Eq.mp
        (congrArg
          (fun y => HomotopyGroup.Pi n
            (CGWH.cgwhToTop.obj Y.right) y)
          (underlyingBasepoint_naturality f).symm)
        (piNMap n f a) =
      HomotopyGroup.map (CGWH.cgwhToTop.map f.right).hom a :=
  PointedTopCat.homotopyGroupTypeFunctor_map n
    (toPointedTop.map f) a

/-- Positive homotopy groups, at actual degree `n + 1`, as a group-valued
functor. -/
noncomputable def piNPositiveFunctor (n : ℕ) :
    PointedCGWH.{u, v} ⥤ GrpCat.{v} :=
  toPointedTop.{u, v} ⋙ PointedTopCat.homotopyGroupPositiveFunctor n

/-- The group homomorphism on actual degree `n + 1` induced by a pointed
CGWH map. -/
noncomputable def piNPositiveMap (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (piNPositiveFunctor n).obj X ⟶ (piNPositiveFunctor n).obj Y :=
  (piNPositiveFunctor n).map f

/-- The underlying function of the positive group map is `piNMap` in actual
degree `n + 1`. -/
@[simp]
theorem piNPositiveMap_apply (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (a : piN (n + 1) X) :
    (piNPositiveMap n f).hom a = piNMap (n + 1) f a :=
  PointedTopCat.homotopyGroupPositiveFunctor_map n
    (toPointedTop.map f) a

/-- Literal degree zero agrees with the path components of the underlying
CGWH space. -/
noncomputable def piNZeroEquivPiZero (X : PointedCGWH.{u, v}) :
    piN 0 X ≃ CGWH.piZero X.right :=
  PointedTopCat.homotopyGroupZeroEquivZerothHomotopy
    (toPointedTop.obj X)

/-- The degree-zero comparison is natural in pointed CGWH maps. -/
theorem piNZeroEquivPiZero_naturality
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (a : piN 0 X) :
    piNZeroEquivPiZero Y (piNMap 0 f a) =
      CGWH.piZeroMap f.right (piNZeroEquivPiZero X a) :=
  PointedTopCat.homotopyGroupZeroEquivZerothHomotopy_naturality
    (toPointedTop.map f) a

/-- Literal degree one agrees multiplicatively with the fundamental group
of the underlying based topological space. -/
noncomputable def piNOneMulEquivFundamentalGroup
    (X : PointedCGWH.{u, v}) :
    piN 1 X ≃*
      FundamentalGroup (CGWH.cgwhToTop.obj X.right)
        (underlyingBasepoint X) :=
  PointedTopCat.homotopyGroupOneMulEquivFundamentalGroup
    (toPointedTop.obj X)

end PointedCGWH

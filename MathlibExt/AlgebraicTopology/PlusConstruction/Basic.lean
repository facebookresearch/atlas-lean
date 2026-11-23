/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced
public import MathlibExt.Topology.Category.CGWH.Basic
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.IsPerfect

/-!
# Acyclic maps and plus-construction data

This file formalizes the homological definitions used in Weibel IV.1.3--1.4
and Quillen's plus construction.

* A space is acyclic when all of its reduced integral singular homology
  groups vanish.
* A map is acyclic at a chosen target point when its homotopy fiber there is
  acyclic.
* A plus construction relative to `P` is an acyclic based map whose induced
  fundamental-group map has kernel `P`, with `P` perfect and normal.

The chosen-point formulation is intentional: the point-set homotopy fiber is
based at a literal target point. For connected targets the different choices
are related by the existing homotopy-fiber basepoint-change maps.

Existence and uniqueness require additional CW-type hypotheses and
obstruction theory; neither is claimed here. This file also does not define
`BGL(R)⁺` merely by naming an arbitrary target satisfying no conditions.

## References

* C. Weibel, *The K-book*, IV.1.3--1.6.
* J.-C. Hausmann and D. Husemoller, *Acyclic maps*, Enseign. Math. 25
  (1979), 53--75.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w u

namespace TopCat

/-- A topological space is acyclic when its reduced integral singular
homology vanishes in every nonnegative degree. -/
def IsAcyclicSpace (X : TopCat.{u}) : Prop :=
  ∀ n : ℕ,
    IsZero
      (AlgebraicTopology.reducedSingularHomology
        AddCommGrpCat.{u}
        AlgebraicTopology.singularIntegralCoefficients n X)

/-- A map is acyclic at `y` when its homotopy fiber over `y` is an acyclic
space. -/
def IsAcyclicMapAt {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) : Prop :=
  IsAcyclicSpace (TopCat.homotopyFiber f y)

/-- The one-point space is acyclic. -/
theorem isAcyclicSpace_punit :
    IsAcyclicSpace (TopCat.of PUnit : TopCat.{u}) := by
  intro n
  exact AlgebraicTopology.isZero_reducedSingularHomology_punit
    AddCommGrpCat.{u}
    AlgebraicTopology.singularIntegralCoefficients n

/-- The defining data of a plus construction at chosen basepoints.

The field `kernel_eq` uses the based fundamental-group map, including the
explicit equality identifying the image of the source basepoint with the
chosen target basepoint. -/
structure IsPlusConstructionAt {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] : Prop where
  /-- The map has acyclic homotopy fiber over the selected target point. -/
  acyclic : IsAcyclicMapAt f y
  /-- The selected subgroup is exactly the kernel on fundamental groups. -/
  kernel_eq :
    MonoidHom.ker (FundamentalGroup.mapOfEq f.hom hxy) = P

namespace IsPlusConstructionAt

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup X x)}
  [P.Normal] [Group.IsPerfect P]

/-- A plus construction has an acyclic homotopy fiber. -/
theorem homotopyFiber_acyclic
    (h : IsPlusConstructionAt f x y hxy P) :
    IsAcyclicSpace (TopCat.homotopyFiber f y) :=
  h.acyclic

end IsPlusConstructionAt

end TopCat

namespace CGWH

/-- A CGWH space is acyclic when its underlying topological space is
acyclic. -/
abbrev IsAcyclicSpace (X : CGWH.{w, u}) : Prop :=
  TopCat.IsAcyclicSpace (cgwhToTop.obj X)

/-- A CGWH map is acyclic at a chosen target point when its underlying
topological map is acyclic there. -/
abbrev IsAcyclicMapAt {X Y : CGWH.{w, u}}
    (f : X ⟶ Y) (y : Y) : Prop :=
  TopCat.IsAcyclicMapAt (cgwhToTop.map f) y

/-- Plus-construction data for a map of CGWH spaces, defined through the
fully faithful forgetful functor to topological spaces. -/
abbrev IsPlusConstructionAt {X Y : CGWH.{w, u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x))
    [P.Normal] [Group.IsPerfect P] : Prop :=
  TopCat.IsPlusConstructionAt (cgwhToTop.map f) x y hxy P

/-- Forgetting CGWH structure does not change plus-construction data. -/
theorem isPlusConstructionAt_iff_toTop
    {X Y : CGWH.{w, u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup (cgwhToTop.obj X) x))
    [P.Normal] [Group.IsPerfect P] :
    IsPlusConstructionAt f x y hxy P ↔
      TopCat.IsPlusConstructionAt (cgwhToTop.map f) x y hxy P :=
  Iff.rfl

end CGWH

end

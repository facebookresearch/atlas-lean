/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberReparametrizationFixedPoint

/-! Importing consumer of the actual full-fiber constant-path fixedness law. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

#check TopCat.homotopyFiberReparamHomotopy_fixed_of_path_eq_const
#print axioms TopCat.homotopyFiberReparamHomotopy_fixed_of_path_eq_const

example {A E B : TopCat.{u}} (p : E ⟶ B) (b : B)
    (f g : A ⟶ TopCat.homotopyFiber p b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : f ≫ TopCat.homotopyFiberToTotal p b =
      g ≫ TopCat.homotopyFiberToTotal p b)
    (hpath : ∀ (a : A) (t : TopCat.I.{u}),
      (f ≫ TopCat.homotopyFiberPath p b) a t =
        (g ≫ TopCat.homotopyFiberPath p b) a
          ((TopCat.I.homeomorph.{u}).symm (r ((TopCat.I.homeomorph.{u}) t))))
    (a : A)
    (hconst : TopCat.homotopyFiberPath p b (g a) =
      ContinuousMap.const TopCat.I.{u} b) (s : unitInterval) :
    TopCat.homotopyFiberReparamHomotopy p b f g r hr hr0 hr1 htotal hpath (s, a) =
      g a :=
  TopCat.homotopyFiberReparamHomotopy_fixed_of_path_eq_const
    p b f g r hr hr0 hr1 htotal hpath a hconst s

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathHomotopyFiberIso

/-!
# Tests for the singular path-homotopy-fiber comparison

These clients exercise the exact three-name API, both inverse laws, total and
complete path projections, universe polymorphism, privacy, and explicit
nonclaims.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace SingularPathHomotopyFiberIsoTests

open CategoryTheory

universe w

variable {E B : TopCat.{w}} (p : E ⟶ B) (b : B)

#check SSet.singularPathHomotopyFiberIso
#check SSet.singularPathHomotopyFiberIso_hom_toTotal
#check SSet.singularPathHomotopyFiberIso_hom_path
#check @SSet.singularPathHomotopyFiberIso.{1}
#check @SSet.singularPathHomotopyFiberIso.{0}
#check @SSet.singularPathHomotopyFiberIso_hom_toTotal.{1}
#check @SSet.singularPathHomotopyFiberIso_hom_toTotal.{0}
#check @SSet.singularPathHomotopyFiberIso_hom_path.{1}
#check @SSet.singularPathHomotopyFiberIso_hom_path.{0}

example :
    (SSet.singularPathHomotopyFiberIso p b).hom ≫
        (SSet.singularPathHomotopyFiberIso p b).inv = 𝟙 _ :=
  (SSet.singularPathHomotopyFiberIso p b).hom_inv_id

example :
    (SSet.singularPathHomotopyFiberIso p b).inv ≫
        (SSet.singularPathHomotopyFiberIso p b).hom = 𝟙 _ :=
  (SSet.singularPathHomotopyFiberIso p b).inv_hom_id

example :
    (SSet.singularPathHomotopyFiberIso p b).hom ≫
        SSet.pathHomotopyFiberToTotal (TopCat.toSSet.map p)
          (TopCat.toSSetObj₀Equiv.symm b) =
      TopCat.toSSet.map (TopCat.homotopyFiberToTotal p b) :=
  SSet.singularPathHomotopyFiberIso_hom_toTotal p b

example :
    (SSet.singularPathHomotopyFiberIso p b).hom ≫
        SSet.pathHomotopyFiberPath (TopCat.toSSet.map p)
          (TopCat.toSSetObj₀Equiv.symm b) =
      TopCat.toSSet.map (TopCat.homotopyFiberPath p b) ≫
        TopCat.toSSet.map
          (TopCat.isoOfHomeo
            (Homeomorph.arrowCongr TopCat.I.homeomorph
              (Homeomorph.refl B))).hom ≫
          (SSet.singularPathIso B).hom :=
  SSet.singularPathHomotopyFiberIso_hom_path p b

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberIntervalBridge

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberCarrierEquiv

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberIso_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check SSet.singularTopEndingPath

#guard_msgs (error, substring := true) in
#check SSet.singularIntervalBridgeIso

#guard_msgs (error, substring := true) in
#check SSet.singularEndingPathIso

#guard_msgs (error, substring := true) in
#check SSet.singularCoreEndingPullbackIso

#guard_msgs (error, substring := true) in
#check SSet.singularHomotopyFiberPreservedPullbackIso

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberIso_hom_evalZero

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberBarComparison

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberQuillenB

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberQuasifibration

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberPrincipalBundle

#guard_msgs (error, substring := true) in
#check SSet.singularPathHomotopyFiberDelooping

#guard_msgs (error, substring := true) in
#synth HomotopicalAlgebra.ModelCategory SSet.{w}

#guard_msgs (error, substring := true) in
#synth HomotopicalAlgebra.IsRightProper SSet.{w}

#print axioms SSet.singularPathHomotopyFiberIso
#print axioms SSet.singularPathHomotopyFiberIso_hom_toTotal
#print axioms SSet.singularPathHomotopyFiberIso_hom_path

end SingularPathHomotopyFiberIsoTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

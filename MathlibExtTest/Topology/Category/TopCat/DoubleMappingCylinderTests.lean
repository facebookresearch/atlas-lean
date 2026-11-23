/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderOpenCharts
import Mathlib.Tactic.NormNum

/-!
Direct original-pushout and whole-relative-family uses of the shared
collar geometry. No caller inverse, relative homotopy, selected model,
ambient connectedness or expected weak equivalence is supplied.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra TopCat
open scoped TopCat.modelCategory

universe u

#check @TopCat.mappingCylinderPairEquivalence
#print axioms TopCat.mappingCylinderPairEquivalence
#check @TopCat.mappingCylinderNaturalHomotopy
#print axioms TopCat.mappingCylinderNaturalHomotopy
#check @TopCat.doubleMappingCylinderPairEquivalence
#print axioms TopCat.doubleMappingCylinderPairEquivalence
#check @TopCat.doubleMappingCylinderProjection_mem_weakHomotopyEquivalences
#print axioms TopCat.doubleMappingCylinderProjection_mem_weakHomotopyEquivalences
#check @TopCat.doubleMappingCylinderOpenHHomotopy
#print axioms TopCat.doubleMappingCylinderOpenHHomotopy
#check @TopCat.doubleMappingCylinderOpenBHomotopy
#print axioms TopCat.doubleMappingCylinderOpenBHomotopy
#check @TopCat.doubleMappingCylinderOpenHRetraction_mem_weakHomotopyEquivalences
#print axioms TopCat.doubleMappingCylinderOpenHRetraction_mem_weakHomotopyEquivalences
#check @TopCat.doubleMappingCylinderOpenBRetraction_mem_weakHomotopyEquivalences
#print axioms TopCat.doubleMappingCylinderOpenBRetraction_mem_weakHomotopyEquivalences
#check @TopCat.doubleMappingCylinderOverlap_H_square
#print axioms TopCat.doubleMappingCylinderOverlap_H_square
#check @TopCat.doubleMappingCylinderOverlap_B_square
#print axioms TopCat.doubleMappingCylinderOverlap_B_square
#check @TopCat.doubleMappingCylinderMidpoint_inclusion
#print axioms TopCat.doubleMappingCylinderMidpoint_inclusion

example {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    weakHomotopyEquivalences (doubleMappingCylinderProjection i f) ∧
    ∃ r : pushout i f ⟶ doubleMappingCylinder i f,
      pushout.inr i f ≫ r = doubleMappingCylinderH i f ∧
      Nonempty (ContinuousMap.HomotopyRel (doubleMappingCylinderProjection i f ≫ r).hom
        (𝟙 (doubleMappingCylinder i f) :
          doubleMappingCylinder i f ⟶ doubleMappingCylinder i f).hom
        (Set.range (doubleMappingCylinderH i f))) ∧
      Nonempty (ContinuousMap.HomotopyRel (r ≫ doubleMappingCylinderProjection i f).hom
        (𝟙 (pushout i f) : pushout i f ⟶ pushout i f).hom
        (Set.range (pushout.inr i f))) := by
  let e := doubleMappingCylinderPairEquivalence i f
  exact ⟨doubleMappingCylinderProjection_mem_weakHomotopyEquivalences i f,
    e.inverse, e.inverse_H, ⟨e.cylinderHomotopy.symm⟩, ⟨e.pushoutHomotopy.symm⟩⟩

example {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderHToOpenH i f ≫ doubleMappingCylinderOpenHRetraction i f = 𝟙 H ∧
      weakHomotopyEquivalences (doubleMappingCylinderOpenHRetraction i f) :=
  ⟨doubleMappingCylinderHToOpenH_retraction i f,
    doubleMappingCylinderOpenHRetraction_mem_weakHomotopyEquivalences i f⟩

example {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderBToOpenB i f ≫ doubleMappingCylinderOpenBRetraction i f = 𝟙 B ∧
      weakHomotopyEquivalences (doubleMappingCylinderOpenBRetraction i f) :=
  ⟨doubleMappingCylinderBToOpenB_retraction i f,
    doubleMappingCylinderOpenBRetraction_mem_weakHomotopyEquivalences i f⟩

example {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderOverlapToOpenH i f ≫ doubleMappingCylinderOpenHRetraction i f =
        doubleMappingCylinderOverlapProjection i f ≫ f ∧
      doubleMappingCylinderOverlapToOpenB i f ≫ doubleMappingCylinderOpenBRetraction i f =
        doubleMappingCylinderOverlapProjection i f ≫ i :=
  ⟨doubleMappingCylinderOverlap_H_square i f, doubleMappingCylinderOverlap_B_square i f⟩

example {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapProjection i f = 𝟙 X ∧
      doubleMappingCylinderMidpoint i f ≫ AlgebraicTopology.subspaceIncl
          (X := doubleMappingCylinder i f)
          (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) =
        mappingCylinderEndpoint X
          ((TopCat.I.homeomorph.{u}).symm (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)) ≫
            doubleMappingCylinderMiddle i f :=
  ⟨doubleMappingCylinderMidpoint_projection i f, doubleMappingCylinderMidpoint_inclusion i f⟩

end

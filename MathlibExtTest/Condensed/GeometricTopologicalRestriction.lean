/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.GeometricTopologicalRestriction
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Category.CompHaus.Basic

/-! A continuous coefficient map acts on nonconstant polynomial sections
of a genuine compact two-point test, including the actual sheaf ring map.
The two values distinguish geometric sections from constant coefficients.
-/

open CategoryTheory Opposite
open MathlibExt.Condensed.GeometricTopologicalRestriction

noncomputable section

private abbrev A := ULift.{1} (Polynomial ℤ)
private abbrev B := ULift.{1} ℤ
private instance : TopologicalSpace A := ⊥
private instance : TopologicalSpace B := ⊥
private instance : TopologicalSpace (Fin 2) := ⊥
private instance : DiscreteTopology A := ⟨rfl⟩
private instance : DiscreteTopology B := ⟨rfl⟩
private instance : DiscreteTopology (Fin 2) := ⟨rfl⟩
private instance : IsTopologicalRing A := inferInstance
private instance : IsTopologicalRing B := inferInstance

private abbrev test : CompHaus.{0} := CompHaus.of (Fin 2)
private def coefficient : A →+* B :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Polynomial.evalRingHom (2 : ℤ)).comp ULift.ringEquiv.toRingHom)
private theorem continuous_coefficient : Continuous coefficient :=
  continuous_of_discreteTopology
private def sections : C(test, A) :=
  ⟨fun i ↦ ULift.up (if i = 0 then Polynomial.X else Polynomial.X ^ 2),
    continuous_of_discreteTopology⟩

example : sectionMap coefficient continuous_coefficient (op test) sections 0 =
    (2 : B) := by
  change coefficient (sections 0) = _
  simp [coefficient, sections, ULift.ringEquiv]

example : sectionMap coefficient continuous_coefficient (op test) sections 1 =
    (4 : B) := by
  change coefficient (sections 1) = _
  simp [coefficient, sections, ULift.ringEquiv]

example : (show C(test, B) from
    (((ringMap coefficient continuous_coefficient).hom.app (op test)) sections)) 1 =
      (4 : B) := by
  change coefficient (sections 1) = _
  simp [coefficient, sections, ULift.ringEquiv]

#print axioms MathlibExt.Condensed.GeometricTopologicalRestriction.sectionMap
#print axioms MathlibExt.Condensed.GeometricTopologicalRestriction.unitExtension_mate

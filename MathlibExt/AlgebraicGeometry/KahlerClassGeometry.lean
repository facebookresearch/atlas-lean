/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Actual Kähler classes on a complex manifold

The Kähler cone is the image in the closed/exact de Rham quotient of actual
closed real two-forms invariant under the complex structure and positive
on every complex line. Neither a cone nor its class map is selected as data.
The finite-dimensional cohomology topology is fixed by a native finite basis.

This is the geometric input language of Demailly--Păun,
*Numerical characterization of the Kähler cone of a compact Kähler manifold*,
math/0105176v2, Main Theorem 0.1. Numerical positivity on analytic cycles
and the connected-component equality require the independently normalized
analytic integration construction. The ordinary smooth Kähler-form condition
is source-covered by TauCetiProject/TauCeti 62bbc0596dc3539d488232e4e924a338548ea0a9,
`TauCeti/Geometry/Symplectic/Manifold/Kahler.lean` (Apache 2.0).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.KahlerClassGeometry

open ManifoldDifferentialForms
open scoped Manifold ContDiff

abbrev Coordinates (n : ℕ) := EuclideanSpace ℂ (Fin n)

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
  [ExteriorTheory ℝ (Coordinates n) M]

abbrev RealTwoForms := GlobalForms ℝ (Coordinates n) M 2
abbrev ClosedTwoForms := closedForms ℝ (Coordinates n) M 2
abbrev H2 := DeRhamH2 ℝ (Coordinates n) M

def evaluateTwoForm (α : RealTwoForms n M) (x : M) (u v : Coordinates n) : ℝ :=
  α.val ⟨x, by trivial⟩ ![u, v]

/-- Invariance under the actual complex tangent multiplication. -/
def IsTypeOneOne [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (α : RealTwoForms n M) : Prop :=
  ∀ x u v, evaluateTwoForm n M α x (Complex.I • u) (Complex.I • v) =
    evaluateTwoForm n M α x u v

/-- Strict positivity of the actual form on every nonzero complex line. -/
def IsPositive [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (α : RealTwoForms n M) : Prop :=
  ∀ x (v : Coordinates n), v ≠ 0 →
    0 < evaluateTwoForm n M α x v (Complex.I • v)

variable [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]

def KahlerForms : Set (ClosedTwoForms n M) :=
  {α | IsTypeOneOne n M α.val ∧ IsPositive n M α.val}

def realOneOneClasses : Set (H2 n M) :=
  classOfClosedTwoForm ℝ (Coordinates n) M '' {α | IsTypeOneOne n M α.val}

def kahlerCone : Set (H2 n M) :=
  classOfClosedTwoForm ℝ (Coordinates n) M '' KahlerForms n M

/-- A Kähler witness is a concrete closed positive form, not a cone field. -/
structure KahlerStructure [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] where
  form : ClosedTwoForms n M
  type : IsTypeOneOne n M form.val
  positive : IsPositive n M form.val

def KahlerStructure.cohomologyClass (eta : KahlerStructure n M) : H2 n M :=
  classOfClosedTwoForm ℝ (Coordinates n) M eta.form

theorem KahlerStructure.class_mem (eta : KahlerStructure n M) :
    KahlerStructure.cohomologyClass n M eta ∈ kahlerCone n M :=
  ⟨eta.form, ⟨eta.type, eta.positive⟩, rfl⟩

theorem kahlerCone_subset_realOneOne : kahlerCone n M ⊆ realOneOneClasses n M := by
  rintro a ⟨α, hα, rfl⟩
  exact ⟨α, hα.1, rfl⟩

/-- The usual finite-dimensional topology, independent of a pointwise-form
quotient topology. Its coordinates are the native cohomology finite basis. -/
@[instance_reducible]
def cohomologyTopology [FiniteDimensional ℝ (H2 n M)] : TopologicalSpace (H2 n M) :=
  TopologicalSpace.induced (Module.finBasis ℝ (H2 n M)).equivFun inferInstance

end MathlibExt.AlgebraicGeometry.KahlerClassGeometry

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The tangent-covector description is adapted from AxiomMath/TauCeti,
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/Geometry/Manifold/DifferentialForm/Basic.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. Apache License 2.0.
Modification: complex coefficients, holomorphic coordinate regularity and
sectionwise normalization of the sheaf de Rham differential.
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
public import MathlibExt.AlgebraicGeometry.AnalyticRealization
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

/-!
# A sectionwise characterized holomorphic de Rham complex

The forms are actual complex tangent covectors with holomorphic chart
coefficients. A supplied sheaf realization is characterized on every open
set by a linear equivalence to these forms, actual restriction, and the
coordinate exterior-derivative formula. Its differential is complex linear;
no linearity over the holomorphic function sheaf is asserted.

This is completed interface data, not an existence axiom. It allows geometric
Hodge and Riemann--Hilbert requests to use the same precisely identified
de Rham complex. Sources: Griffiths--Harris, *Principles of Algebraic
Geometry*, Chapter 0; Peters--Steenbrink, *Mixed Hodge Structures*, §2.2.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolomorphicDeRham

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Manifold ContDiff
open AnalyticRealization ConstructibleComplexes

variable (X : AnalyticRealization.ComplexScheme) (d : ℕ) [AnalyticManifold X d]

/-- A complex tangent covector at every point of an open set. -/
abbrev RoughForm (U : Opens (ComplexAnalytification.space X)) (p : ℕ) :=
  (x : U) → TangentSpace 𝓘(ℂ, CoordinateSpace d) x.1 [⋀^Fin p]→L[ℂ] ℂ

/-- The chart domain corresponding to an actual open set. -/
def chartDomain (U : Opens (ComplexAnalytification.space X))
    (a : ComplexAnalytification.space X) : Set (CoordinateSpace d) :=
  (extChartAt 𝓘(ℂ, CoordinateSpace d) a).target ∩
    (extChartAt 𝓘(ℂ, CoordinateSpace d) a).symm ⁻¹' (U : Set _)

/-- A coefficient of the pullback of a form to a chart. The arbitrary value
outside the chart domain is discarded by all differentiability conditions. -/
def chartCoefficient {U : Opens (ComplexAnalytification.space X)} {p : ℕ}
    (α : RoughForm X d U p) (a : ComplexAnalytification.space X)
    (σ : Fin p → Fin d) (z : CoordinateSpace d) : ℂ := by
  classical
  exact if h : z ∈ chartDomain X d U a then
    α ⟨(extChartAt 𝓘(ℂ, CoordinateSpace d) a).symm z, h.2⟩
      (fun i ↦ mfderiv 𝓘(ℂ, CoordinateSpace d) 𝓘(ℂ, CoordinateSpace d)
        (extChartAt 𝓘(ℂ, CoordinateSpace d) a).symm z
        (EuclideanSpace.single (σ i) 1))
  else 0

/-- Holomorphic regularity is checked on the actual coordinate coefficients. -/
def IsHolomorphicForm {U : Opens (ComplexAnalytification.space X)} {p : ℕ}
    (α : RoughForm X d U p) : Prop :=
  ∀ a σ, DifferentiableOn ℂ (chartCoefficient X d α a σ) (chartDomain X d U a)

@[simp] theorem chartCoefficient_zero {U : Opens (ComplexAnalytification.space X)}
    {p : ℕ} (a : ComplexAnalytification.space X) (σ : Fin p → Fin d) :
    chartCoefficient X d (0 : RoughForm X d U p) a σ = 0 := by
  classical
  funext z
  simp only [chartCoefficient]
  split_ifs
  · rfl
  · rfl

theorem chartCoefficient_add {U : Opens (ComplexAnalytification.space X)} {p : ℕ}
    (α β : RoughForm X d U p) (a : ComplexAnalytification.space X)
    (σ : Fin p → Fin d) :
    chartCoefficient X d (α + β) a σ =
      chartCoefficient X d α a σ + chartCoefficient X d β a σ := by
  classical
  funext z
  by_cases h : z ∈ chartDomain X d U a
  · simp only [chartCoefficient, h, dite_eq_left, Pi.add_apply]
    exact ContinuousAlternatingMap.add_apply _ _ _
  · simp [chartCoefficient, h]

theorem chartCoefficient_smul {U : Opens (ComplexAnalytification.space X)} {p : ℕ}
    (c : ℂ) (α : RoughForm X d U p) (a : ComplexAnalytification.space X)
    (σ : Fin p → Fin d) :
    chartCoefficient X d (c • α) a σ = c • chartCoefficient X d α a σ := by
  classical
  funext z
  by_cases h : z ∈ chartDomain X d U a
  · simp only [chartCoefficient, h, dite_eq_left, Pi.smul_apply]
    exact ContinuousAlternatingMap.smul_apply _ _ _
  · simp [chartCoefficient, h]

/-- The actual vector space of holomorphic forms on an open set. -/
def holomorphicForms (U : Opens (ComplexAnalytification.space X)) (p : ℕ) :
    Submodule ℂ (RoughForm X d U p) where
  carrier := {α | IsHolomorphicForm X d α}
  zero_mem' := by
    intro a σ
    rw [chartCoefficient_zero]
    exact differentiableOn_const (0 : ℂ)
  add_mem' := by
    intro α β hα hβ a σ
    rw [chartCoefficient_add]
    exact (hα a σ).add (hβ a σ)
  smul_mem' := by
    intro c α hα a σ
    rw [chartCoefficient_smul]
    exact (hα a σ).const_smul c

/-- Rational coefficients of a complex sheaf, with the sheaf preserved by
the actual restriction-of-scalars functor. -/
def rationalRestriction : CoefficientSheaf ℂ (ComplexAnalytification.space X) ⥤
    CoefficientSheaf ℚ (ComplexAnalytification.space X) :=
  sheafCompose (Opens.grothendieckTopology (ComplexAnalytification.space X))
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))

instance rationalRestriction_additive : (rationalRestriction X).Additive where
  map_add := by intro A B f g; rfl

/-- The constant rational sheaf concentrated in degree zero. -/
def rationalUnitComplex : CochainComplex
    (CoefficientSheaf ℚ (ComplexAnalytification.space X)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (PerverseSheaves.rationalConstantSheaf (ComplexAnalytification.space X))

/-- The constant complex sheaf concentrated in degree zero. -/
def complexUnitComplex : CochainComplex
    (CoefficientSheaf ℂ (ComplexAnalytification.space X)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((constantSheaf (Opens.grothendieckTopology (ComplexAnalytification.space X))
      (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ))

/-- A geometric sheaf realization of holomorphic forms with its fixed
coordinate differential and constant-unit map. No realization is asserted
to exist by this structure definition. -/
structure HolomorphicDeRhamData where
  complex : CochainComplex (CoefficientSheaf ℂ (ComplexAnalytification.space X)) ℤ
  negative : ∀ j : ℤ, j < 0 → IsZero (complex.X j)
  sections (U : Opens (ComplexAnalytification.space X)) (p : ℕ) :
    (complex.X (p : ℤ)).obj.obj (op U) ≃ₗ[ℂ] holomorphicForms X d U p
  restriction (U V : Opens (ComplexAnalytification.space X)) (h : V ≤ U)
      (p : ℕ) (s : (complex.X (p : ℤ)).obj.obj (op U)) (x : V) :
    (sections V p ((complex.X (p : ℤ)).obj.map (homOfLE h).op s)).1 x =
      (sections U p s).1 ⟨x.1, h x.2⟩
  exteriorDerivative (U : Opens (ComplexAnalytification.space X)) (p : ℕ)
      (s : (complex.X (p : ℤ)).obj.obj (op U))
      (a : ComplexAnalytification.space X) (σ : Fin (p + 1) → Fin d)
      (z : CoordinateSpace d) (hz : z ∈ chartDomain X d U a) :
    chartCoefficient X d
      (sections U (p + 1)
        (((complex.d (p : ℤ) ((p : ℤ) + 1)).hom.app (op U)) s)).1 a σ z =
      ∑ i : Fin (p + 1), (-1 : ℂ) ^ (i : ℕ) *
        fderivWithin ℂ
          (chartCoefficient X d (sections U p s).1 a (σ ∘ i.succAbove))
          (chartDomain X d U a) z (EuclideanSpace.single (σ i) 1)
  rationalUnit : rationalUnitComplex X ⟶
    ((rationalRestriction X).mapHomologicalComplex (ComplexShape.up ℤ)).obj complex
  unit_normalization : ∀ x : (⊤ : Opens (ComplexAnalytification.space X)),
    (sections ⊤ 0
      (((constantSheafAdj
        (Opens.grothendieckTopology (ComplexAnalytification.space X))
        (ModuleCat.{0} ℚ) isTerminalTop).homEquiv _ _
          ((HomologicalComplex.singleObjXSelf (c := ComplexShape.up ℤ) 0 _).inv ≫
            rationalUnit.f 0)) 1)).1 x 0 = 1
  complexUnit : complexUnitComplex X ⟶ complex
  complex_unit_normalization : ∀ x : (⊤ : Opens (ComplexAnalytification.space X)),
    (sections ⊤ 0
      (((constantSheafAdj
        (Opens.grothendieckTopology (ComplexAnalytification.space X))
        (ModuleCat.{0} ℂ) isTerminalTop).homEquiv _ _
          ((HomologicalComplex.singleObjXSelf (c := ComplexShape.up ℤ) 0 _).inv ≫
            complexUnit.f 0)) 1)).1 x 0 = 1

/-- The geometric brutal Hodge cut, characterized termwise by zero below
the form degree and unchanged terms at and above that degree. This is not
the cohomological truncation of a complex after taking global sections. -/
structure HodgeCut {X : AnalyticRealization.ComplexScheme} {d : ℕ}
    [AnalyticManifold X d] (D : HolomorphicDeRhamData X d) (p : ℤ) where
  complex : CochainComplex (CoefficientSheaf ℂ (ComplexAnalytification.space X)) ℤ
  inclusion : complex ⟶ D.complex
  zero_below : ∀ j, j < p → IsZero (complex.X j)
  unchanged_above : ∀ j, p ≤ j → IsIso (inclusion.f j)

end MathlibExt.AlgebraicGeometry.HolomorphicDeRham

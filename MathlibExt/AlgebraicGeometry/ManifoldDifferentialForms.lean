/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Coordinate-normalized smooth forms and their actual de Rham quotient

A form is an alternating tangent covector at every point. Regularity is
checked on its actual pullback to manifold charts. The exterior derivative
is Mathlib's alternating derivative in the chart at that point, transported
back by the actual chart derivative. There is no selected operator called d.

`ExteriorTheory` records the smoothness, linearity and `d² = 0` laws of this
fixed formula on global forms as a hypothesis class; everything below that uses
`d` is conditional on it. Its instance on every smooth manifold over `ℝ` or `ℂ`
is requested in `WantedExt/AlgebraicGeometry/ManifoldDifferentialFormsWanted.lean`
(TauCetiProject/TauCeti at 62bbc0596dc3539d488232e4e924a338548ea0a9 proves the
corresponding facts for its own form API in
`TauCeti/Geometry/Manifold/DifferentialForm/`). The closed/exact quotient is
then constructed below. The chart normalization extends the local
`HolomorphicDeRham` pattern to arbitrary manifolds.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms

open CategoryTheory TopologicalSpace Set
open scoped Manifold ContDiff

variable (k : Type) [NontriviallyNormedField k]
  (E : Type) [NormedAddCommGroup E] [NormedSpace k E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- An alternating `p`-covector at every point of an open set, with no
regularity condition. -/
abbrev RoughForm (U : Opens M) (p : ℕ) :=
  (x : U) → TangentSpace 𝓘(k, E) x.val [⋀^Fin p]→L[k] k

/-- The part of the target of the chart at `a` lying over the open set `U`. -/
def chartDomain (U : Opens M) (a : M) : Set E :=
  (extChartAt 𝓘(k, E) a).target ∩
    (extChartAt 𝓘(k, E) a).symm ⁻¹' (U : Set M)

/-- The actual pullback alternating covector on a chart domain. -/
def chartForm {U : Opens M} {p : ℕ} (α : RoughForm k E M U p) (a : M) :
    E → E [⋀^Fin p]→L[k] k := by
  classical
  exact fun z ↦ if h : z ∈ chartDomain k E M U a then
    (α ⟨(extChartAt 𝓘(k, E) a).symm z, h.2⟩).compContinuousLinearMap
      (mfderiv 𝓘(k, E) 𝓘(k, E) (extChartAt 𝓘(k, E) a).symm z)
  else 0

/-- A form is smooth if its pullback to every chart is smooth on the chart
domain. -/
def IsSmooth {U : Opens M} {p : ℕ} (α : RoughForm k E M U p) : Prop :=
  ∀ a : M, ContDiffOn k ∞ (chartForm k E M α a) (chartDomain k E M U a)

@[simp]
theorem chartForm_zero (U : Opens M) (p : ℕ) (a : M) :
    chartForm k E M (0 : RoughForm k E M U p) a = 0 := by
  classical
  ext z v
  by_cases h : z ∈ chartDomain k E M U a
  · simp only [chartForm, dite_eq_left h]
    rfl
  · simp [chartForm, h]

theorem chartForm_add {U : Opens M} {p : ℕ} (α β : RoughForm k E M U p) (a : M) :
    chartForm k E M (α + β) a = chartForm k E M α a + chartForm k E M β a := by
  classical
  ext z v
  by_cases h : z ∈ chartDomain k E M U a
  · simp only [Pi.add_apply, chartForm, dite_eq_left h]
    rfl
  · simp [chartForm, h]

theorem chartForm_smul {U : Opens M} {p : ℕ} (c : k) (α : RoughForm k E M U p) (a : M) :
    chartForm k E M (c • α) a = c • chartForm k E M α a := by
  classical
  ext z v
  by_cases h : z ∈ chartDomain k E M U a
  · simp only [Pi.smul_apply, chartForm, dite_eq_left h]
    rfl
  · simp [chartForm, h]

/-- The concrete vector space of smooth tangent forms. -/
def smoothForms (U : Opens M) (p : ℕ) : Submodule k (RoughForm k E M U p) where
  carrier := {α | IsSmooth k E M α}
  zero_mem' := by
    intro a
    rw [chartForm_zero]
    exact contDiffOn_const
  add_mem' hα hβ := by
    intro a
    rw [chartForm_add]
    exact (hα a).add (hβ a)
  smul_mem' c α hα := by
    intro a
    rw [chartForm_smul]
    exact (hα a).const_smul c

/-- Smooth `p`-forms on the whole manifold. -/
abbrev GlobalForms (p : ℕ) := smoothForms k E M ⊤ p

instance globalFormsAddCommGroup (p : ℕ) : AddCommGroup (GlobalForms k E M p) :=
  Submodule.addCommGroup _

/-- Exterior differentiation is the fixed local alternating derivative. -/
def exteriorDerivative {U : Opens M} {p : ℕ} (α : RoughForm k E M U p) :
    RoughForm k E M U (p + 1) := fun x ↦
  (extDerivWithin (chartForm k E M α x.val) (chartDomain k E M U x.val)
    (extChartAt 𝓘(k, E) x.val x.val)).compContinuousLinearMap
      (mfderiv 𝓘(k, E) 𝓘(k, E) (extChartAt 𝓘(k, E) x.val) x.val)

/-- For a smooth manifold $M$ modelled on a normed space $E$ over a nontrivially normed field
$k$, an instance asserts the basic laws of the exterior derivative `exteriorDerivative`
(computed in charts) on smooth global forms: the exterior derivative of a smooth form is smooth,
it is $k$-linear, and $d(dα) = 0$. -/
class ExteriorTheory [IsManifold 𝓘(k, E) ∞ M] : Prop where
  smooth : ∀ p (α : GlobalForms k E M p), IsSmooth k E M (exteriorDerivative k E M α.val)
  add : ∀ p (α β : GlobalForms k E M p),
    exteriorDerivative k E M (α.val + β.val) =
      exteriorDerivative k E M α.val + exteriorDerivative k E M β.val
  smul : ∀ p (c : k) (α : GlobalForms k E M p),
    exteriorDerivative k E M (c • α.val) = c • exteriorDerivative k E M α.val
  square_zero : ∀ p (α : GlobalForms k E M p),
    exteriorDerivative k E M (exteriorDerivative k E M α.val) = 0

variable [IsManifold 𝓘(k, E) ∞ M] [ExteriorTheory k E M]

/-- The exterior derivative on smooth global forms, as a linear map. -/
def d (p : ℕ) : GlobalForms k E M p →ₗ[k] GlobalForms k E M (p + 1) where
  toFun α := ⟨exteriorDerivative k E M α.val, ExteriorTheory.smooth p α⟩
  map_add' α β := Subtype.ext (ExteriorTheory.add p α β)
  map_smul' c α := Subtype.ext (ExteriorTheory.smul p c α)

/-- Closed smooth global forms. -/
abbrev closedForms (p : ℕ) := LinearMap.ker (d k E M p)

instance closedFormsAddCommGroup (p : ℕ) : AddCommGroup (closedForms k E M p) :=
  Submodule.addCommGroup _

/-- The exterior derivative lands in closed forms, since `d² = 0`. -/
def dToClosed (p : ℕ) : GlobalForms k E M p →ₗ[k] closedForms k E M (p + 1) where
  toFun α := ⟨d k E M p α, by
    apply Subtype.ext
    exact ExteriorTheory.square_zero p α⟩
  map_add' α β := by apply Subtype.ext; exact map_add (d k E M p) α β
  map_smul' c α := by apply Subtype.ext; exact map_smul (d k E M p) c α

/-- H² is the actual quotient of closed two-forms by exact two-forms. -/
abbrev DeRhamH2 := (closedForms k E M 2) ⧸ (LinearMap.range (dToClosed k E M 1))

/-- The de Rham class of a closed two-form. -/
def classOfClosedTwoForm : closedForms k E M 2 →ₗ[k] DeRhamH2 k E M :=
  (LinearMap.range (dToClosed k E M 1)).mkQ

end MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms

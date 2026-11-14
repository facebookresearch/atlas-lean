/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The coherent-cohomology and linear-series interface follows
`StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean` in
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b,
licensed under Apache 2.0. That source has no individual author or
copyright notice. Modification notice: use Mathlib's right-derived
global-section functor directly, define degree by the actual Euler
characteristic difference, and state rank one by local trivializations.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public noncomputable section

/-!
# Coherent cohomology and linear series on curves

The spaces in this interface are the actual right-derived global-section
modules. Their scalar action is restricted along the structure morphism.
On a proper curve, the degree of an invertible sheaf is
`χ(L) - χ(𝒪)`. A linear series selects an `(r + 1)`-dimensional subspace
of `H⁰(L)`, retaining the finite-dimensionality of `H⁰(L)` and `H¹(L)`.

Reference: Arbarello--Cornalba--Griffiths--Harris, *Geometry of Algebraic
Curves I*, Chapters II and V; Stacks Project, Tag 0CCN.
-/

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

universe u

/-- The structure sheaf as a sheaf of modules over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Local triviality of rank one, on actual Zariski open subschemes. -/
def IsLineBundle {X : Scheme.{u}} (L : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ structureModule U)

/-- The scalar homomorphism on global regular functions is induced by `f`. -/
def globalScalarMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- Actual global sections, with scalars restricted along the structure map. -/
def sectionsFunctor {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : X.Modules ⥤ ModuleCat.{u} k :=
  SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
    ModuleCat.restrictScalars (globalScalarMap f)

/-- Global-section evaluation and restriction of scalars preserve addition. -/
instance sectionsFunctor_additive {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : (sectionsFunctor f).Additive where
  map_add := by
    intro M N a b
    rfl

/-- Coherent cohomology is the right-derived global-section functor. -/
abbrev cohomology {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) (n : ℕ) : ModuleCat.{u} k :=
  ((sectionsFunctor f).rightDerived n).obj L

/-- Arithmetic genus, computed from the actual first cohomology of `𝒪`. -/
def genus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ℕ :=
  Module.finrank k (cohomology f (structureModule X) 1)

/-- Degree on a proper curve, as `χ(L) - χ(𝒪)`. -/
def degree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) : ℤ :=
  (Module.finrank k (cohomology f L 0) : ℤ) -
    Module.finrank k (cohomology f L 1) -
    Module.finrank k (cohomology f (structureModule X) 0) +
    Module.finrank k (cohomology f (structureModule X) 1)

/-- A linear series on a fixed actual curve and invertible module. -/
structure LinearSeries {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (d : ℤ) (r : ℕ) where
  /-- The actual sheaf underlying the linear series. -/
  L : X.Modules
  /-- Its local rank-one trivializations. -/
  isLineBundle : IsLineBundle L
  /-- Its degree-zero cohomology is finite-dimensional. -/
  finiteH0 : FiniteDimensional k (cohomology f L 0)
  /-- Its degree-one cohomology is finite-dimensional. -/
  finiteH1 : FiniteDimensional k (cohomology f L 1)
  /-- The Euler-characteristic degree has the prescribed value. -/
  degree_eq : degree f L = d
  /-- The selected space of sections. -/
  V : Submodule k (cohomology f L 0)
  /-- The selected space has projective dimension `r`. -/
  finrank_eq : Module.finrank k V = r + 1

/-- The Brill--Noether expected dimension, with integer subtraction. -/
def brillNoetherNumber (g d r : ℕ) : ℤ :=
  (g : ℤ) - ((r : ℤ) + 1) * ((g : ℤ) - d + r)

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

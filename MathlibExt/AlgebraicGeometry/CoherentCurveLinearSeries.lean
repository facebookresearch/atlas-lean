/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean` (AxiomMath/Stacks at
commit c496df0d9beea9deaeabcea8492605f9a0a2313b, https://github.com/AxiomMath/Stacks):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modification notice: use Mathlib's right-derived global-section functor
directly, define degree by the actual Euler characteristic difference, state
rank one by local trivializations, and define genus, degree and linear series
only on proper curves.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.KrullDimension
public import MathlibExt.AlgebraicGeometry.SchemeModulesEvaluation
public import MathlibExt.AlgebraicGeometry.SmoothKrullDim

@[expose] public noncomputable section

/-!
# Coherent cohomology and linear series on curves

The cohomology spaces are the right-derived functors of global sections on
sheaves of modules, with scalars restricted along the structure morphism
`X ⟶ Spec k`. They are defined for every scheme over `k`.

The curve invariants are defined only on a proper curve over `k`
(`IsProperCurve`): a proper scheme of dimension one over `k`. Every smooth proper
curve is one. On a proper curve, the cohomology of a coherent sheaf is
finite-dimensional and all cohomology vanishes above degree one, so
`Module.finrank` is the actual dimension of every cohomology space used below,
and `h⁰ - h¹` is the actual Euler characteristic.

* `genus f` is `dim H¹(X, 𝒪_X)` for a proper curve with `H⁰(X, 𝒪_X) = k`
  (Stacks, Tag 0BY7).
* `degree f L hL` is `χ(L) - χ(𝒪_X)` for an invertible sheaf `L`
  (Stacks, Tag 0AYR).
* `LinearSeries f d r` is a linear series `g^r_d`: an invertible sheaf of
  degree `d ≥ 0` with an `(r + 1)`-dimensional space of global sections
  (Stacks, Tag 0CCN).

References: Arbarello--Cornalba--Griffiths--Harris, *Geometry of Algebraic
Curves I*, Chapters II and V; Stacks Project, Sections 33.44 (Tag 0AYQ) and 53.8
(Tag 0BY6).
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

/-- The structure sheaf is invertible: it is trivial on the whole scheme. -/
theorem isLineBundle_structureModule (X : Scheme.{u}) :
    IsLineBundle (structureModule X) := fun _ ↦
  ⟨⊤, trivial,
    ⟨((Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

/-- The scalar homomorphism on global regular functions is induced by `f`. -/
def globalScalarMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- Actual global sections, with scalars restricted along the structure map.
This is reducible, so that the additivity instance
`Scheme.Modules.evaluation_top_comp_restrictScalars_additive` applies to it. -/
abbrev sectionsFunctor {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : X.Modules ⥤ ModuleCat.{u} k :=
  SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
    ModuleCat.restrictScalars (globalScalarMap f)

/-- Coherent cohomology is the right-derived global-section functor. -/
abbrev cohomology {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) (n : ℕ) : ModuleCat.{u} k :=
  ((sectionsFunctor f).rightDerived n).obj L

/-- `f : X ⟶ Spec k` exhibits `X` as a proper curve over `k`: `f` is proper and
the underlying space of `X` has Krull dimension one.

On a proper curve, the cohomology of a coherent sheaf, for instance an invertible
sheaf, is finite-dimensional (Stacks, Tag 02O5), and the cohomology of every
sheaf of modules vanishes above degree one (Grothendieck vanishing, Stacks,
Tag 02UZ, for the noetherian space `X` of dimension one; the cohomology of
`𝒪_X`-modules is that of their underlying abelian sheaves, Hartshorne,
*Algebraic Geometry*, III.2.6). These are the facts that make `genus` and
`degree` below the actual dimension and Euler characteristic. -/
class IsProperCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop extends IsProper f where
  /-- The underlying space has Krull dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1

/-- A nonempty proper scheme that is smooth of relative dimension one over `k` is
a proper curve. -/
instance IsProperCurve.of_smoothOfRelativeDimension {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f] [Nonempty X] :
    IsProperCurve f where
  topologicalKrullDim_eq_one :=
    le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f 1)
      (by exact_mod_cast SmoothOfRelativeDimension.le_topologicalKrullDim f 1)

/-- The global regular functions on `X` are exactly the constants in `k`:
`globalScalarMap f` is bijective, that is, `H⁰(X, 𝒪_X) = k`. -/
class HasConstantGlobalSections {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop where
  /-- The map from the constants to the global regular functions is bijective. -/
  bijective : Function.Bijective (globalScalarMap f)

/-- An integral scheme that is universally closed over an algebraically closed
field has only constant global regular functions. -/
instance HasConstantGlobalSections.of_isIntegral {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f] :
    HasConstantGlobalSections f where
  bijective := IsAlgClosed.ringHom_bijective_of_isIntegral _ <| by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f

/-- With only constant global functions, `H⁰(X, 𝒪_X)` is one-dimensional. -/
theorem finrank_cohomology_zero_structureModule {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasConstantGlobalSections f] :
    Module.finrank k (cohomology f (structureModule X) 0) = 1 := by
  let g : k →ₗ[k] (sectionsFunctor f).obj (structureModule X) :=
    { toFun := fun c ↦ globalScalarMap f c
      map_add' := (globalScalarMap f).map_add
      map_smul' := (globalScalarMap f).map_mul }
  rw [((sectionsFunctor f).rightDerivedZeroIsoSelf.app _).toLinearEquiv.finrank_eq,
    ← (LinearEquiv.ofBijective g HasConstantGlobalSections.bijective).finrank_eq,
    Module.finrank_self]

/-- The genus `dim_k H¹(X, 𝒪_X)` of a proper curve with `H⁰(X, 𝒪_X) = k`
(Stacks, Tag 0BY7). -/
def genus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] [HasConstantGlobalSections f] : ℕ :=
  Module.finrank k (cohomology f (structureModule X) 1)

/-- The degree `χ(L) - χ(𝒪_X)` of an invertible sheaf `L` on a proper curve
(Stacks, Tag 0AYR). Higher cohomology vanishes, so `χ = h⁰ - h¹`. -/
def degree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (L : X.Modules) (_hL : IsLineBundle L) : ℤ :=
  (Module.finrank k (cohomology f L 0) : ℤ) -
    Module.finrank k (cohomology f L 1) -
    Module.finrank k (cohomology f (structureModule X) 0) +
    Module.finrank k (cohomology f (structureModule X) 1)

/-- The structure sheaf has degree zero. -/
@[simp]
theorem degree_structureModule {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (h : IsLineBundle (structureModule X)) :
    degree f (structureModule X) h = 0 := by
  simp [degree]

/-- A linear series `g^r_d` on a proper curve: an invertible sheaf `L` of
degree `d` with an `(r + 1)`-dimensional space `V` of global sections. As in the Stacks
Project's definition for proper schemes of dimension at most one (Tag 0CCN, Definition
53.3.1), the degree `d` is a natural number. On an integral curve this excludes nothing,
since a line bundle with a nonzero section has nonnegative degree. On a reducible or
disconnected curve a line bundle of negative total degree can have nonzero sections, for
example `𝒪(1) ⊔ 𝒪(-2)` on `ℙ¹ ⊔ ℙ¹`; it is not a linear series in this sense, and its
signed degree is still `degree`. -/
structure LinearSeries {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProperCurve f] (d r : ℕ) where
  /-- The invertible sheaf. -/
  L : X.Modules
  /-- `L` is invertible. -/
  isLineBundle : IsLineBundle L
  /-- `L` has degree `d`. -/
  degree_eq : degree f L isLineBundle = (d : ℤ)
  /-- The selected space of global sections. -/
  V : Submodule k (cohomology f L 0)
  /-- The selected space has projective dimension `r`. -/
  finrank_eq : Module.finrank k V = r + 1

/-- `brillNoetherNumber g d r` is the Brill--Noether number
`ρ = g - (r + 1)(g - d + r)` of linear series `g^r_d` on a curve of genus `g`,
computed with integer subtraction. -/
def brillNoetherNumber (g d r : ℕ) : ℤ :=
  (g : ℤ) - ((r : ℤ) + 1) * ((g : ℤ) - d + r)

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

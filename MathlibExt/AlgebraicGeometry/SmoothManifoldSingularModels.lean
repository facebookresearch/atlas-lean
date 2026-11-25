/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ManifoldSingularCohomologyModels
public import MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Actual smooth singular simplices and integration

A smooth simplex is an actual native continuous singular simplex with a
smooth extension on a neighborhood of the standard full-dimensional
parameter simplex. The chosen extension only realizes that same simplex.
The simplicial object retains actual native face and degeneracy maps.
Integration is the literal pullback form on that parameter simplex,
evaluated on the standard oriented basis and integrated with native volume.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels

open CategoryTheory Opposite TopologicalSpace Set MeasureTheory
open KahlerClassGeometry ManifoldDifferentialForms ManifoldSingularCohomologyModels
open scoped Manifold ContDiff Simplicial BigOperators

abbrev SimplexCoordinates (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The standard p-simplex in its actual oriented p-dimensional parameter space. -/
def standardParameterDomain (p : ℕ) : Set (SimplexCoordinates p) :=
  {t | (∀ i : Fin p, 0 ≤ t i) ∧ ∑ i : Fin p, t i ≤ 1}

/-- Tail barycentric coordinates give the actual native simplex parameter. -/
def simplexCoordinates (p : ℕ) (x : SimplexCategory.toTop.obj ⦋p⦌) : SimplexCoordinates p :=
  WithLp.toLp 2 (fun i : Fin p => x.down.weights i.succ)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]

abbrev nativeSingularSet := TopCat.toSSet.obj (TopCat.of M)

/-- An actual smooth extension realizes the same continuous native singular simplex. -/
structure SmoothSimplexModel (p : ℕ) (σ : nativeSingularSet (M := M) _⦋p⦌) where
  neighborhood : Set (SimplexCoordinates p)
  open_neighborhood : IsOpen neighborhood
  contains : standardParameterDomain p ⊆ neighborhood
  map : SimplexCoordinates p → M
  smooth : ContMDiffOn 𝓘(ℝ, SimplexCoordinates p) 𝓘(ℝ, Coordinates n) ∞ map neighborhood
  normalized : ∀ x : SimplexCategory.toTop.obj ⦋p⦌, (show SimplexCategory.toTop.obj ⦋p⦌ ⟶ TopCat.of M from σ.down).hom x =
    map (simplexCoordinates p x)

/-- Smoothness is a property of the actual continuous simplex, with no extra witness labels. -/
def IsSmoothSimplex (p : ℕ) (σ : nativeSingularSet (M := M) _⦋p⦌) : Prop :=
  Nonempty (SmoothSimplexModel (n := n) (M := M) p σ)

/-- Native affine simplex precomposition preserves this same geometric smoothness predicate. -/
class SmoothSingularSource : Prop where
  closed : ∀ (p q : SimplexCategoryᵒᵖ) (f : p ⟶ q)
    (σ : (nativeSingularSet (M := M)).obj p),
      IsSmoothSimplex (n := n) p.unop.len σ →
        IsSmoothSimplex (n := n) q.unop.len ((nativeSingularSet (M := M)).map f σ)

variable [SmoothSingularSource (n := n) (M := M)]

/-- Smooth singular simplices with the literal native face and degeneracy maps. -/
def smoothSingularSet : SSet.{0} where
  obj p := Subtype (fun σ : (nativeSingularSet (M := M)).obj p =>
    IsSmoothSimplex (n := n) p.unop.len σ)
  map f := ↾fun σ => ⟨(nativeSingularSet (M := M)).map f σ.val,
    SmoothSingularSource.closed _ _ f σ.val σ.property⟩
  map_id p := by
    ext σ
    change (nativeSingularSet (M := M)).map (𝟙 p) σ.val = σ.val
    rw [_root_.CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext σ
    change (nativeSingularSet (M := M)).map (f ≫ g) σ.val =
      (nativeSingularSet (M := M)).map g ((nativeSingularSet (M := M)).map f σ.val)
    rw [_root_.CategoryTheory.Functor.map_comp]
    rfl

/-- The inclusion is the actual underlying continuous native simplex in every degree. -/
def smoothSingularInclusion : smoothSingularSet (n := n) (M := M) ⟶ nativeSingularSet (M := M) where
  app p := ↾fun σ => σ.val
  naturality _ _ _ := by ext σ; rfl

variable (R : Type) [CommRing R]

/-- The native free-module alternating chain complex of these actual smooth simplices. -/
def smoothSingularChains : ChainComplex (ModuleCat.{0} R) ℕ :=
  (smoothSingularSet (n := n) (M := M)).chainComplex (ModuleCat.of R R)

/-- Its full native linear dual, without restricting support of cochains. -/
def smoothSingularCochains : CochainComplex (ModuleCat.{0} R) ℕ :=
  ((coefficientDual R).mapHomologicalComplex (.up ℕ)).obj
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (.down ℕ)).obj
      (op (smoothSingularChains (n := n) (M := M) R)))

/-- Actual restriction from continuous cochains is dual to the literal smooth-chain inclusion. -/
def continuousToSmoothCochains : singularCochains R (TopCat.of M) ⟶
    smoothSingularCochains (n := n) (M := M) R :=
  ((coefficientDual R).mapHomologicalComplex (.up ℕ)).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (.down ℕ)).map
      ((((SSet.chainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (smoothSingularInclusion (n := n) (M := M)))).op)

/-- Cochain evaluation on the actual generator represented by the specified smooth simplex. -/
def smoothCochainValue (p : ℕ)
    (α : (smoothSingularCochains (n := n) (M := M) R).X p)
    (σ : (smoothSingularSet (n := n) (M := M)) _⦋p⦌) : R :=
  (((smoothSingularSet (n := n) (M := M)).ιChainComplex (R := ModuleCat.of R R) σ) ≫
    (show (smoothSingularChains (n := n) (M := M) R).X p ⟶ ModuleCat.of R R from α)).hom 1

/-- Pullback integration uses the actual extension of the same simplex and native volume. -/
def integrateSmoothSimplex (p : ℕ) (α : GlobalForms ℝ (Coordinates n) M p)
    (σ : (smoothSingularSet (n := n) (M := M)) _⦋p⦌) : ℝ :=
  let S := Classical.choice σ.property
  ∫ t in standardParameterDomain p,
    α.val ⟨S.map t, by trivial⟩ (fun i : Fin p =>
      mfderivWithin 𝓘(ℝ, SimplexCoordinates p) 𝓘(ℝ, Coordinates n)
        S.map S.neighborhood t (EuclideanSpace.single i 1))

end MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels

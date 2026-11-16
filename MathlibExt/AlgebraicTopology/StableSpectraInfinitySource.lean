/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.Stabilization

/-!
# The stable infinity category of the actual native symmetric spectra

The source category is Tau Ceti's sphere-module category of symmetric
spectra. Level weak maps use the actual pointed simplicial levels and
geometric weak homotopy equivalence. Stabilization uses the completed
native free stabilization maps F_(1+n)(S1 smash K) to F_n(K).

The stable source is a full infinity-categorical localization of that
entire category at these maps. Its universal condition uses full functor
categories, retaining every higher natural transformation. No K spectrum,
K vanishing, additive invariant or motive equivalence defines this source.

References: Hovey--Shipley--Smith, Symmetric spectra, Sections 3.1--3.4;
Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.1 and 2.3.
The native completed Tau Ceti ports retain their source attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableSpectraInfinitySource

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The actual native pointed level of a sphere module. -/
abbrev level (E : SymmetricSpectrum) (n : ℕ) : PointedSSet.{0} :=
  (SymmetricSpectrum.evaluation n).obj E

/-- Level equivalence uses every native pointed simplicial component. -/
def IsLevelWeak {E F : SymmetricSpectrum} (f : E ⟶ F) : Prop :=
  ∀ n : ℕ, WeakEquivalence (((SymmetricSpectrum.evaluation n).map f).right)

/-- These are the actual source maps generating stable localization. -/
def StableGenerator {E F : SymmetricSpectrum} (f : E ⟶ F) : Prop :=
  IsLevelWeak f ∨ ∃ (n : ℕ) (K : PointedSSet.{0}),
    HEq f (SymmetricSpectrum.freeStabilizationMap n K)

/-- A functor vertex inverts exactly the stated native generating maps. -/
def InvertsStableGenerators (Z : SSet.{1})
    (a : (mapping (nerve SymmetricSpectrum) Z) _⦋0⦌) : Prop :=
  ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), StableGenerator f →
    IsEquivalenceEdge Z
      (((mappingZero (nerve SymmetricSpectrum) Z).symm a).app (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- The full stable localization model is tied to the entire native source. -/
structure SpectrumInfinitySource where
  category : StableInfinityCategory.{1}
  source : nerve SymmetricSpectrum ⟶ category.toSSet
  source_objects : Function.Bijective (source.app (op ⦋0⦌))
  invert : ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), StableGenerator f →
    IsEquivalenceEdge category.toSSet
      (source.app (op ⦋1⦌) (nerve.edgeMk f).edge)
  universal : ∀ (Z : SSet.{1}) [SSet.Quasicategory Z],
    ∃ f : mapping category.toSSet Z ⟶
      ((mapping (nerve SymmetricSpectrum) Z).fullEnhancedSubcategory
        (InvertsStableGenerators Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition source Z ∧ CategoricalWeakEquivalence f

/-- An actual point-set spectrum is sent to its original source vertex. -/
def SpectrumInfinitySource.vertex (S : SpectrumInfinitySource) (E : SymmetricSpectrum) :
    S.category.toSSet _⦋0⦌ := S.source.app (op ⦋0⦌) (ComposableArrows.mk₀ E)

/-- Native spectrum maps give those same actual one-simplex edges. -/
def SpectrumInfinitySource.edge (S : SpectrumInfinitySource) {E F : SymmetricSpectrum}
    (f : E ⟶ F) : S.category.toSSet _⦋1⦌ :=
  S.source.app (op ⦋1⦌) (nerve.edgeMk f).edge

/-- The sphere unit is the actual regular sphere module, before localization. -/
abbrev sphereSpectrum : SymmetricSpectrum := Mod.regular SymmetricSequence.sphere

/-- The BGT sphere source is this actual source-localized sphere, not Perf of a field. -/
def sphereVertex (S : SpectrumInfinitySource) : S.category.toSSet _⦋0⦌ := S.vertex sphereSpectrum

end MathlibExt.AlgebraicTopology.StableSpectraInfinitySource

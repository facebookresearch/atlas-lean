/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.Stabilization
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Closed
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The stable infinity category of the actual native symmetric spectra

The source category is Tau Ceti's sphere-module category of symmetric
spectra. Level weak maps use the actual pointed simplicial levels and
geometric weak homotopy equivalence. Cofibrancy uses the native free-zero
initial map and levelwise boundary lifting; Omega-fibrancy uses the level
Kan conditions and the adjoint sphere structure maps. Stabilization uses the
completed native free stabilization maps F_(1+n)(S1 smash K) to F_n(K).

The stable source is a full infinity-categorical localization of that
entire category at the stable equivalences of Hovey--Shipley--Smith,
tested on mapping spaces into Omega-fibrant spectra. The level
equivalences and free stabilization maps generate them only under
homotopy colimits: localizing at the generators alone does not invert the
wedge of a free stabilization map with an identity. Its universal condition
uses full functor categories, retaining every higher natural transformation. No K spectrum,
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

/-- The level equivalences and the free stabilization maps, which generate the stable
equivalences under homotopy colimits. Localizing at these maps alone does not invert all stable
equivalences: the wedge of a free stabilization map with an identity is not inverted. -/
def StableGenerator {E F : SymmetricSpectrum} (f : E ⟶ F) : Prop :=
  IsLevelWeak f ∨ ∃ (n : ℕ) (K : PointedSSet.{0}),
    HEq f (SymmetricSpectrum.freeStabilizationMap n K)

/-- The native pointed zero object is the identity pointing of Delta[0]. -/
abbrev pointedZero : PointedSSet.{0} := Under.mk (𝟙 (Δ[0] : SSet.{0}))

/-- Its actual free-zero spectrum is the source initial spectrum. -/
abbrev zeroSpectrum : SymmetricSpectrum := (SymmetricSpectrum.free 0).obj pointedZero

/-- The unique based map from the actual pointed zero object. -/
def pointedZeroMap (X : PointedSSet.{0}) : pointedZero ⟶ X :=
  Under.homMk X.hom (by simp)

/-- The native free-spectrum adjunction supplies the actual initial map. -/
def initialSpectrumMap (E : SymmetricSpectrum) : zeroSpectrum ⟶ E :=
  SymmetricSpectrum.freeDesc E (pointedZeroMap (level E 0))

/-- The native free-spectrum left adjoint preserves the actual pointed initial object. -/
def zeroSpectrumIsInitial : IsInitial zeroSpectrum := by
  letI : (SymmetricSpectrum.free 0).IsLeftAdjoint :=
    (SymmetricSpectrum.freeEvaluationAdjunction 0).isLeftAdjoint
  exact (Under.mkIdInitial (X := (Δ[0] : SSet.{0}))).isInitialObj
    (SymmetricSpectrum.free 0) _

/-- Every actual level boundary has the right lifting property for a trivial level fibration. -/
def IsLevelTrivialFibration {E F : SymmetricSpectrum} (f : E ⟶ F) : Prop :=
  ∀ (n m : ℕ), HasLiftingProperty (SSet.boundary m).ι
    (((SymmetricSpectrum.evaluation n).map f).right)

/-- The source projective cofibration test uses the native initial free-spectrum map. -/
def IsCofibrant (E : SymmetricSpectrum) : Prop :=
  ∀ (X Y : SymmetricSpectrum) (f : X ⟶ Y), IsLevelTrivialFibration f →
    HasLiftingProperty (initialSpectrumMap E) f

/-- Omega-fibrancy uses actual level Kan complexes and actual adjoint sphere maps. -/
def IsOmegaFibrant (E : SymmetricSpectrum) : Prop :=
  (∀ n : ℕ, SSet.KanComplex (level E n).right) ∧
    ∀ n : ℕ, WeakEquivalence (E.smashPowAdjointStructureMap n).right

/-- A cofibrant replacement square of `f`: maps `p : X' ⟶ X` and `q : Y' ⟶ Y` from cofibrant
spectra that are level trivial fibrations, with `f' : X' ⟶ Y'` lying over `f`. -/
def IsCofibrantReplacementSquare {X Y X' Y' : SymmetricSpectrum} (f : X ⟶ Y) (p : X' ⟶ X)
    (q : Y' ⟶ Y) (f' : X' ⟶ Y') : Prop :=
  IsCofibrant X' ∧ IsCofibrant Y' ∧ IsLevelTrivialFibration p ∧ IsLevelTrivialFibration q ∧
    f' ≫ q = p ≫ f

/-- The stable equivalences of symmetric spectra (Hovey–Shipley–Smith, Def. 3.1.3, in the
projective form): `f` has a cofibrant replacement square, and for every such square the map `f'`
induces weak equivalences of the mapping spaces `Map(-, E)` (level zero of the function spectra)
into every Omega-fibrant spectrum `E`. Replacement squares always exist (projective cofibrant
replacement); requiring one keeps the test from holding vacuously. -/
def IsStableEquivalence {X Y : SymmetricSpectrum} (f : X ⟶ Y) : Prop :=
  (∃ (X' Y' : SymmetricSpectrum) (p : X' ⟶ X) (q : Y' ⟶ Y) (f' : X' ⟶ Y'),
    IsCofibrantReplacementSquare f p q f') ∧
  ∀ (X' Y' : SymmetricSpectrum) (p : X' ⟶ X) (q : Y' ⟶ Y) (f' : X' ⟶ Y'),
    IsCofibrantReplacementSquare f p q f' → ∀ E : SymmetricSpectrum, IsOmegaFibrant E →
      WeakEquivalence
        ((SymmetricSpectrum.evaluation 0).map ((MonoidalClosed.pre f').app E)).right

/-- A functor vertex inverts every stable equivalence. -/
def InvertsStableEquivalences (Z : SSet.{1})
    (a : (mapping (nerve SymmetricSpectrum) Z) _⦋0⦌) : Prop :=
  ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), IsStableEquivalence f →
    IsEquivalenceEdge Z
      (((mappingZero (nerve SymmetricSpectrum) Z).symm a).app (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- The full stable localization model is tied to the entire native source. -/
structure SpectrumInfinitySource where
  category : StableInfinityCategory.{1}
  source : nerve SymmetricSpectrum ⟶ category.toSSet
  source_objects : Function.Bijective (source.app (op ⦋0⦌))
  invert : ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), IsStableEquivalence f →
    IsEquivalenceEdge category.toSSet
      (source.app (op ⦋1⦌) (nerve.edgeMk f).edge)
  universal : ∀ (Z : SSet.{1}) [SSet.Quasicategory Z],
    ∃ f : mapping category.toSSet Z ⟶
      ((mapping (nerve SymmetricSpectrum) Z).fullEnhancedSubcategory
        (InvertsStableEquivalences Z)).toSSet,
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

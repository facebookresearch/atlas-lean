/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityIntervalInsertion
public import MathlibExt.AlgebraicTopology.StableSpectraInfinitySource

/-!
# Native symmetric-spectrum assembly of the iterated S-construction

The carrier is Tau Ceti's actual sphere-module symmetric spectrum. Its
levels compare to the fixed all-coordinate multi-S diagonal, its finite
permutation actions are those on the original interval coordinates, and
every single sphere action is normalized to the full circle insertion.
The comparison allows a point-set rectification, using genuine weak
equivalences on all levels rather than an opaque spectrum or strict
set-theoretic recognition of stable equivalence.

The global construction contract also fixes every exact-functor map on
the original diagonal spaces. Additivity, localization, K0 identification
and motive corepresentability are separate theorem requests.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Definition 7.5
and Section 7.1, pages 44--45. The native Tau Ceti source ports retain
their Apache 2.0 copyright, authors and exact revision attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityKSpectra

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels
open StableInfinityMultiSConstruction StableInfinitySFunctorMaps
open StableInfinityIntervalInsertion StableSpectraInfinitySource
open MathlibExt.SpectraSource
open scoped Simplicial

universe u

/-- The native level-index transport from q+1 to the sphere-action index 1+q. -/
def nextLevelCast (E : SymmetricSpectrum) (q : ℕ) :
    level E (q + 1) ⟶ level E (1 + q) :=
  eqToHom (congrArg (level E) (Nat.add_comm q 1))

/-- A native sphere-module assembly tied to every original S-diagonal. -/
structure KAssembly (C : StableInfinityCategory.{0})
    (I : CircleInsertion C) where
  spectrum : SymmetricSpectrum
  comparison : ∀ q : ℕ, pointedDiagonal I.pointing q ⟶ level spectrum q
  comparison_weak : ∀ q : ℕ, WeakEquivalence (comparison q).right
  sphere_action : ∀ q : ℕ,
    PointedSSet.circle ◁ comparison q ≫ spectrum.smashPowStructureMap q =
      I.map q ≫ comparison (q + 1) ≫ nextLevelCast spectrum q
  permutation : ∀ (q : ℕ)
    (g : FiniteBijection.mk q ⟶ FiniteBijection.mk q)
    (k : SimplexCategoryᵒᵖ) (x : (multiSDiagonal C q).obj k),
    (spectrum.X.functor.map g).right.app k
      ((comparison q).right.app k x) =
      (comparison q).right.app k
        ((coreMap (multiPermutationMap q k.unop.len
          g.toEquiv)).app k x)

/-- A sphere-module map is normalized to the actual exact-functor diagonal map. -/
def IsSourceKMap {C D : StableInfinityCategory.{0}}
    {I : CircleInsertion C} {J : CircleInsertion D}
    (K : KAssembly C I) (L : KAssembly D J) (f : ExactFunctor C D)
    (g : K.spectrum ⟶ L.spectrum) : Prop :=
  ∀ q : ℕ, (K.comparison q).right ≫
    ((SymmetricSpectrum.evaluation q).map g).right =
      multiSDiagonalMap f q ≫ (L.comparison q).right

/-- The entire connective K construction, including every canonical exact map. -/
structure ConnectiveKConstruction where
  insertion : ∀ C : StableInfinityCategory.{0}, CircleInsertion C
  assembly : ∀ C : StableInfinityCategory.{0}, KAssembly C (insertion C)
  map : ∀ {C D : StableInfinityCategory.{0}}, ExactFunctor C D →
    ((assembly C).spectrum ⟶ (assembly D).spectrum)
  map_source : ∀ {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D),
    IsSourceKMap (assembly C) (assembly D) f (map f)
  map_id : ∀ C : StableInfinityCategory.{0},
    map (ExactFunctor.id C) = 𝟙 (assembly C).spectrum
  map_comp : ∀ {C D E : StableInfinityCategory.{0}}
    (f : ExactFunctor C D) (g : ExactFunctor D E),
    map (f.comp g) = map f ≫ map g

/-- K uses the source-normalized S-assembly, independent of BGT equivalences. -/
def connectiveK (K : ConnectiveKConstruction)
    (C : StableInfinityCategory.{0}) : SymmetricSpectrum :=
  (K.assembly C).spectrum

/-- Its canonical map is the normalized map on the original full S-diagrams. -/
def connectiveKMap (K : ConnectiveKConstruction)
    {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D) :
    connectiveK K C ⟶ connectiveK K D := K.map f

/-- The actual stable-localization vertex of the constructed K spectrum. -/
def connectiveKVertex (K : ConnectiveKConstruction)
    (S : SpectrumInfinitySource) (C : StableInfinityCategory.{0}) :
    S.category.toSSet _⦋0⦌ := S.vertex (connectiveK K C)

/-- A small presentation is tied to the entire original infinity category. -/
structure StableSmallPresentation (C : StableInfinityCategory.{u}) where
  small : StableInfinityCategory.{0}
  comparison : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{u}).obj
    small.toSSet ⟶ C.toSSet
  weak : CategoricalWeakEquivalence comparison

/-- A large enhanced source is evaluated through its genuine small presentation. -/
def presentedConnectiveK (K : ConnectiveKConstruction)
    {C : StableInfinityCategory.{u}} (P : StableSmallPresentation C) :
    SymmetricSpectrum := connectiveK K P.small

end MathlibExt.AlgebraicTopology.StableInfinityKSpectra

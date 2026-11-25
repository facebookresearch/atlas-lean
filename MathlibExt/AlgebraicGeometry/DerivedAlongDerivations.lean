/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels

/-!
# Actual based deformation maps along a prestack morphism

All coefficients and affine simplices remain those of X. The Y-lift
diagram is literally Map(Δ[j],Y(E[j])), based at f(x[j]). The map of
lift diagrams is actual postcomposition with f. Compatible path,
replacement and covariant comparisons are on this whole joint diagram.
Their maps are fixed by the actual projections and augmentations.

These constructions specify the deformation map whose Yoneda
transpose is the cotangent differential. No cotangent or tangent
comparison is assumed here.

Reference: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV1111.3209v4 §2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedAlongDerivations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.HomotopicalAlgebra
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    {X Y : Prestack k} (K : KernelSystem N X)

/-- Native Hom-diagram functor on the full coefficient/family product. -/
def jointMappingFunctor :
    (CoefficientTest M R K × Families X ⥤ SSet.{u + 1}) ⥤
      (CoefficientTest M R K × Families X ⥤ SSet.{u + 1}) :=
  (((Functor.const (CoefficientTest M R K × Families X ⥤ SSet.{u + 1})).obj
      ((opOpEquivalence (CoefficientTest M R K × Families X)).inverse ⋙
        (jointSimplexes M R K).op)).prod' (𝟭 _)) ⋙
    CategoryTheory.prodFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.diag (CoefficientTest M R K × Families X)) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (Functor.uncurry.obj (SimplicialCategory.sHomFunctor SSet.{u + 1}))

/-- The actual lift diagram Y(E), with all X coefficient/family parameters. -/
def alongLifts (Y : Prestack k) : CoefficientTest M R K × Families X ⥤ SSet.{u + 1} :=
  (jointMappingFunctor M R K).obj (jointAlgebras M R K ⋙ Y)

/-- The actual base diagram Y(A), with the same X-family parameters. -/
def alongBase (Y : Prestack k) : CoefficientTest M R K × Families X ⥤ SSet.{u + 1} :=
  (jointMappingFunctor M R K).obj (CategoryTheory.Prod.snd _ _ ⋙ algebraProjection X ⋙ Y)

/-- The source diagram is the existing joint X-lift diagram. -/
theorem alongLifts_self : alongLifts M R K X = jointLifts M R K := rfl

/-- The source base diagram is the existing joint X-base diagram. -/
theorem alongBase_self : alongBase M R K X = jointBase M R K := rfl

/-- The lift map is literal postcomposition with f at every joint simplex. -/
def alongLiftMap (f : X ⟶ Y) : jointLifts M R K ⟶ alongLifts M R K Y :=
  (jointMappingFunctor M R K).map (Functor.whiskerLeft (jointAlgebras M R K) f)

/-- The base map is literal postcomposition with the same f. -/
def alongBaseMap (f : X ⟶ Y) : jointBase M R K ⟶ alongBase M R K Y :=
  (jointMappingFunctor M R K).map
    (Functor.whiskerLeft (CategoryTheory.Prod.snd _ _ ⋙ algebraProjection X) f)

/-- The actual Y-projection is fixed by each split coefficient projection. -/
structure AlongLiftProjection (f : X ⟶ Y) (P : JointLiftProjection M R K) where
  map : alongLifts M R K Y ⟶ alongBase M R K Y
  projection : ∀ (t : CoefficientTest M R K) (j : Families X),
    HEq (map.app (t,j))
      ((mappingFamiliesMap X
        (Functor.whiskerRight ((testInclusion M R K).obj t).projection Y)).app j)
  square : alongLiftMap M R K f ≫ map = P.map ≫ alongBaseMap M R K f

/-- The target point is f(x), rather than an independent point of Y(A). -/
def alongPoint (f : X ⟶ Y) (P : JointLiftProjection M R K) :=
  P.point ≫ alongBaseMap M R K f

/-- A path model of that exact based Y-diagram. -/
structure AlongPath (Y : Prestack k) extends PrepathObject (alongBase M R K Y) where
  diagonal_weak : ∀ j, WeakEquivalence (ι.app j)
  endpoints_fibration : ∀ j,
    SSet.modelCategoryQuillen.J.rlp (prod.lift (p₀.app j) (p₁.app j))

/-- Postcomposition of path data retains both endpoints and the actual diagonal. -/
structure AlongPathMap (f : X ⟶ Y) (B : JointPath M R K) (C : AlongPath M R K Y) where
  map : B.P ⟶ C.P
  diagonal : B.ι ≫ map = alongBaseMap M R K f ≫ C.ι
  first : map ≫ C.p₀ = B.p₀ ≫ alongBaseMap M R K f
  second : map ≫ C.p₁ = B.p₁ ≫ alongBaseMap M R K f

/-- The actual based Y-deformation diagram, indexed by all X coefficients. -/
def alongDerivations (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (B : AlongPath M R K Y) :=
  pullback (prod.map A.map (alongPoint M R K f P)) (prod.lift B.p₀ B.p₁)

/-- Assembly of the actual map of native based pullbacks.
Both projections fix every joint test/family simplex of its map. -/
structure AlongRawMap (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (B : JointPath M R K)
    (C : AlongPath M R K Y) (T : AlongPathMap M R K f B C) where
  map : jointDerivations M R K P B ⟶ alongDerivations M R K f P A C
  first : map ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ prod.map (alongLiftMap M R K f) (𝟙 _)
  second : map ≫ pullback.snd _ _ = pullback.snd _ _ ≫ T.map

/-- Replacement is on the entire actual Y-deformation diagram. -/
structure AlongDerivationModel (f : X ⟶ Y) (P : JointLiftProjection M R K)
    (A : AlongLiftProjection M R K f P) (B : AlongPath M R K Y) where
  replacement : SpaceDiagramReplacement.{u, u + 1, u + 1} (alongDerivations M R K f P A B)

/-- Source and target replacements are related by the same actual whole-diagram map. -/
structure AlongReplacementMap {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : JointPath M R K}
    {C : AlongPath M R K Y} {T : AlongPathMap M R K f B C}
    (a : AlongRawMap M R K f P A B C T) (D : JointDerivationModel M R K P B)
    (E : AlongDerivationModel M R K f P A C) where
  map : D.replacement.diagram ⟶ E.replacement.diagram
  normalized : D.replacement.map ≫ map = a.map ≫ E.replacement.map

/-- Native family limits retain the whole coefficient-test naturality. -/
def alongFunctor {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : AlongPath M R K Y}
    (D : AlongDerivationModel M R K f P A B) : CoefficientTest M R K ⥤ SSet.{u + 1} :=
  Functor.curry.obj D.replacement.diagram ⋙ lim

/-- The actual total and projection of the along-deformation functor. -/
def alongTotal {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : AlongPath M R K Y}
    (D : AlongDerivationModel M R K f P A B) : SSet.{u + 1} :=
  nerve ((Functor.uncurry.obj (alongFunctor M R K D)).Elements)

/-- The actual covariant base of all along-deformations. -/
def alongProjection {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : AlongPath M R K Y}
    (D : AlongDerivationModel M R K f P A B) :
    alongTotal M R K D ⟶ nerve (CoefficientTest M R K) :=
  nerveMap (Functor.Elements.π (Functor.uncurry.obj (alongFunctor M R K D)) ⋙
    CategoryTheory.Prod.fst _ _)

/-- Along-deformations have the same actual covariant replacement convention. -/
abbrev AlongFibration {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : AlongPath M R K Y}
    (D : AlongDerivationModel M R K f P A B) :=
  CovariantReplacement (alongProjection M R K D)

/-- The actual transformation between native family-limit deformation functors. -/
def alongFunctorMap {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : JointPath M R K}
    {C : AlongPath M R K Y} {T : AlongPathMap M R K f B C}
    {a : AlongRawMap M R K f P A B C T} {D : JointDerivationModel M R K P B}
    {E : AlongDerivationModel M R K f P A C} (r : AlongReplacementMap M R K a D E) :
    derivationFunctor M R K D ⟶ alongFunctor M R K E :=
  Functor.whiskerRight (Functor.curry.map r.map) lim

/-- Native element-category functoriality fixes the entire raw deformation total map. -/
def alongTotalMap {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : JointPath M R K}
    {C : AlongPath M R K Y} {T : AlongPathMap M R K f B C}
    {a : AlongRawMap M R K f P A B C T} {D : JointDerivationModel M R K P B}
    {E : AlongDerivationModel M R K f P A C} (r : AlongReplacementMap M R K a D E) :
    rawDerivationTotal M R K D ⟶ alongTotal M R K E :=
  nerveMap (Functor.uncurry.map (alongFunctorMap M R K r)).mapElements

/-- The derived deformation map is fixed by this raw source comparison and its augmentations. -/
structure AlongFibrationMap {f : X ⟶ Y} {P : JointLiftProjection M R K}
    {A : AlongLiftProjection M R K f P} {B : JointPath M R K}
    {C : AlongPath M R K Y} {T : AlongPathMap M R K f B C}
    {a : AlongRawMap M R K f P A B C T} {D : JointDerivationModel M R K P B}
    {E : AlongDerivationModel M R K f P A C} (r : AlongReplacementMap M R K a D E)
    (DF : DerivationFibration M R K D) (EF : AlongFibration M R K E) where
  map : DF.total ⟶ EF.total
  over : map ≫ EF.projection = DF.projection
  normalized : DF.map ≫ map = alongTotalMap M R K r ≫ EF.map

end MathlibExt.AlgebraicGeometry.DerivedAlongDerivations

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralEtaleCoherentFamilies
public import MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements
public import MathlibExt.CategoryTheory.NativeDGNerveModels

/-!
# Native ordinary and DG sources of the same étale coefficient family

The ordinary DG enrichment is the exact original full sheaf-cochain
enrichment. Its unit comparison sends every ring scalar to that scalar
times the actual degree-zero cochain of the original map. The source
simplicial morphism is the native lax unit followed by the actual
cochain-to-Dold--Kan map.

The fibre entry into the original coefficient Grothendieck category is
fixed on every object and map by the original category equality and
pseudofunctor identity. Its whole source can therefore be compared to
the full K-injective enhancement without dropping homogeneous Hom data.

Sources: Keller, *Deriving DG categories*, Section2; HTT Section1.3.1;
Bhatt--Mathew1807.04725v4, Notation5.8. Native sheaf-cochain, good
truncation, Dold--Kan and Grothendieck source revisions are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeEtaleCoefficientSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Limits
open _root_.Opposite _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open GeneralEtaleCoherentFamilies GeneralEtaleDerivedEnhancements
open MathlibExt.DGSource MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open CochainComplex.HomComplex
open scoped Simplicial

variable (Λ : Type) [Ring Λ] (X : Scheme.{0})

/-- This source is the same complete native cochain DG enrichment and its actual ordinary Hom. -/
structure CoefficientDGOrdinarySource where
  ordinary : EnrichedOrdinaryCategory (Cochains LargeInt) (CoefficientComplexes Λ X)
  enrichment_normalization : ordinary.toEnrichedCategory = coefficientDG Λ X
  unit_zero : (𝟙_ (Cochains LargeInt)).X 0 ≅ ModuleCat.of LargeInt LargeInt
  unit_normalization :
    letI := coefficientLinear Λ X
    letI := ordinary
    ∀ (F G : CoefficientComplexes Λ X) (f : F ⟶ G) (r : LargeInt),
      (((eHomEquiv (Cochains LargeInt) f ≫
        eqToHom (congrArg (fun E => E.Hom F G) enrichment_normalization)).f 0).hom)
        (unit_zero.inv.hom r) = r • Cochain.ofHom f

variable (N : CoefficientDGOrdinarySource Λ X)

/-- The actual simplicial category of these same original coefficient complexes. -/
def sourceSimplicialCategory : Type 2 :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X) := N.ordinary.toEnrichedCategory
  letI : EnrichedCategory SSet.{1} (DGSimplicialCategory LargeInt (CoefficientComplexes Λ X)) :=
    MathlibExt.DGSource.instEnrichedCategorySSetDGSimplicialCategory LargeInt
  ForgetEnrichment SSet.{1} (DGSimplicialCategory LargeInt (CoefficientComplexes Λ X))

instance sourceCategory : Category.{1} (sourceSimplicialCategory Λ X N) :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X) := N.ordinary.toEnrichedCategory
  letI : EnrichedCategory SSet.{1} (DGSimplicialCategory LargeInt (CoefficientComplexes Λ X)) :=
    MathlibExt.DGSource.instEnrichedCategorySSetDGSimplicialCategory LargeInt
  _root_.CategoryTheory.categoryForgetEnrichment (W := SSet.{1})
    (C := DGSimplicialCategory LargeInt (CoefficientComplexes Λ X))

/-- The ordinary Hom is the unit-shaped Hom of the exact native simplicial enrichment. -/
instance sourceSimplicial : SimplicialCategory (sourceSimplicialCategory Λ X N) :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X) := N.ordinary.toEnrichedCategory
  letI : EnrichedCategory SSet.{1} (DGSimplicialCategory LargeInt (CoefficientComplexes Λ X)) :=
    MathlibExt.DGSource.instEnrichedCategorySSetDGSimplicialCategory LargeInt
  ForgetEnrichment.enrichedOrdinaryCategory (V := SSet.{1})

/-- The original coefficient complex becomes its native double-opposite simplicial object. -/
def sourceObject (F : CoefficientComplexes Λ X) : sourceSimplicialCategory Λ X N :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X) := N.ordinary.toEnrichedCategory
  letI : EnrichedCategory SSet.{1} (DGSimplicialCategory LargeInt (CoefficientComplexes Λ X)) :=
    MathlibExt.DGSource.instEnrichedCategorySSetDGSimplicialCategory LargeInt
  ForgetEnrichment.of SSet.{1} (DGSimplicialCategory.of LargeInt F)

/-- The original cochain map is sent through the exact native lax unit and good-truncation/Dold--Kan map. -/
def sourceMorphism {F G : CoefficientComplexes Λ X} (f : F ⟶ G) :
    sourceObject Λ X N F ⟶ sourceObject Λ X N G := by
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X) := N.ordinary.toEnrichedCategory
  letI : EnrichedCategory SSet.{1} (DGSimplicialCategory LargeInt (CoefficientComplexes Λ X)) :=
    MathlibExt.DGSource.instEnrichedCategorySSetDGSimplicialCategory LargeInt
  let h : 𝟙_ SSet.{1} ⟶ (cochainToSSet LargeInt).obj (dgHomComplex LargeInt F G) :=
    Functor.LaxMonoidal.ε (cochainToSSet LargeInt) ≫
      (cochainToSSet LargeInt).map (eHomEquiv (Cochains LargeInt) f)
  apply ForgetEnrichment.homOf SSet.{1}
  simpa only [DGSimplicialCategory.hom_eq, DGSimplicialCategory.underlying_of] using h

/-- A functor from cochain complexes of sheaves of $\Lambda$-modules on the small étale site of $X$
($\Lambda$ a ring) to the simplicial category `sourceSimplicialCategory` obtained from their cochain
DG enrichment $N$ through the Dold–Kan correspondence, with prescribed values: through the given
equalities of objects, it sends each complex $F$ to `sourceObject F` and each cochain map $f$ to
`sourceMorphism f`, the vertex given by $f$ through the lax unit and the Dold–Kan map. -/
structure CoefficientSimplicialFunctorSource where
  functor : CoefficientComplexes Λ X ⥤ sourceSimplicialCategory Λ X N
  objects : ∀ F : CoefficientComplexes Λ X, functor.obj F = sourceObject Λ X N F
  maps : ∀ {F G : CoefficientComplexes Λ X} (f : F ⟶ G),
    eqToHom (objects F).symm ≫ functor.map f ≫ eqToHom (objects G) = sourceMorphism Λ X N f

variable [∀ Y : Scheme.{0}, HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
  (U : ∀ Y : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
  (C : CoefficientPseudofunctorSource Λ S U) (Y : QcqsScheme)

/-- The actual source object in the original coefficient Grothendieck family. -/
def entryObject (F : CoefficientComplexes Λ Y.scheme) : CoefficientFamilies Λ S U C where
  base := op Y
  fiber := (eqToHom (C.object (op Y)).symm).toFunctor.obj F

/-- The original source map uses the actual pseudofunctor unit and transported cochain map. -/
def entryMorphism {F G : CoefficientComplexes Λ Y.scheme} (f : F ⟶ G) :
    entryObject Λ S U C Y F ⟶ entryObject Λ S U C Y G where
  base := 𝟙 (op Y)
  fiber := (C.functor.mapId ⟨op Y⟩).hom.toNatTrans.app (entryObject Λ S U C Y F).fiber ≫
    (eqToHom (C.object (op Y)).symm).toFunctor.map f

/-- The whole source fibre entry has every object and map fixed by the native dictionary. -/
structure CoefficientFibreEntrySource where
  functor : CoefficientComplexes Λ Y.scheme ⥤ CoefficientFamilies Λ S U C
  objects : ∀ F : CoefficientComplexes Λ Y.scheme, functor.obj F = entryObject Λ S U C Y F
  maps : ∀ {F G : CoefficientComplexes Λ Y.scheme} (f : F ⟶ G),
    eqToHom (objects F).symm ≫ functor.map f ≫ eqToHom (objects G) = entryMorphism Λ S U C Y f
  projection : functor ⋙ familyProjection Λ S U C =
    (_root_.CategoryTheory.Functor.const (CoefficientComplexes Λ Y.scheme)).obj (op Y)

end MathlibExt.AlgebraicGeometry.NativeEtaleCoefficientSourceModels

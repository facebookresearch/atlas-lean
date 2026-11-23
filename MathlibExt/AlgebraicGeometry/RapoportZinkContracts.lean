/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicConstructibleContracts
public import MathlibExt.AlgebraicGeometry.SemistableWeilDeligne
public import MathlibExt.AlgebraicGeometry.AdicTateCoefficients
public import MathlibExt.CategoryTheory.MonodromyFiltration
public import MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Actual nearby monodromy and the Rapoport--Zink filtered-resolution contract

The nearby object is the actual i*Rj* of continuous Q_ell coefficients on
the actual geometric trait. Its inertia map is the actual adjunction mate
of the fixed scheme-action squares. The perverse object is exactly
RΨ(Q_ell)[d], once its characterized middle-heart membership is supplied.
Its monodromy is the finite logarithm at the actual tame-coordinate-one
element, and its filtration is the actual kernel-image convolution.

A filtered resolution must identify every level naturally with
RΓ(M_(-p)[-d]), including its maps into the actual unshifted nearby object.
Its spectral sequence is then constructed from that complex by Mathlib;
there is no separate chosen spectral sequence or abutment map.

The finite-support, geometric membership/monodromy and proper-comparison
providers are explicit proof obligations. Generic derived-functor,
tame-coordinate and spectral-convergence toolbox remains separate.

Source: Illusie, Astérisque 223 (1994), Exposé I, sections 3.6--3.8,
pp.38--41; Rapoport--Zink, Satz 2.10. The filtration is on the nearby
perverse object, not an assumed monodromy-weight filtration on generic H.
https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RapoportZinkContracts

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open AdicDerivedContracts AdicConstructibleContracts
open GeometricSemistableTraits GeometricAdicGaloisOperators
open SemistableWeilDeligne
open MathlibExt.HomologicalAlgebra

attribute [local instance] HasDerivedCategory.standard

variable (ell : ℕ) [Fact ell.Prime]
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsAlgClosure K L] (π : R) (T : GeometricTrait R K L π)
  (X : Over (Spec (.of R))) [IsProper X.hom]
  [DerivedFunctorTheory ℚ_[ell]]
  [IsIso (ProEtaleCohomologyFunctoriality.coefficientPullback ℚ_[ell]
    (RationalCoefficients.{0} ell) (specialArrow π T X))]
  [∀ σ : Galois K L, IsIso (ProEtaleCohomologyFunctoriality.coefficientPullback ℚ_[ell]
    (RationalCoefficients.{0} ell) (genericGalois (K := K) X σ))]
  [InertiaSchemeCompatibility π T X]

/-- The actual special fibre, with its actual residue-field structure. -/
abbrev specialModel : Over (Spec (.of (Residue π T))) :=
  Over.mk (pullback.snd X.hom (specialBaseMap π T))

instance specialModel_proper : IsProper (specialModel R K L π T X).hom := by
  change IsProper (pullback.snd X.hom (specialBaseMap π T))
  infer_instance

/-- The actual nearby object with continuous rational adic coefficients. -/
abbrev nearby :=
  nearbyObject ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericArrow (L := L) X) (specialArrow π T X)

/-- The actual geometric specialization map. -/
def specialization :
    continuousComplex ℚ_[ell] (RationalCoefficients.{0} ell)
      (SpecialFibre π T X) ⟶ nearby ell R K L π T X :=
  AdicDerivedContracts.specialization ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericArrow (L := L) X) (specialArrow π T X)

/-- The actual inertia monodromy is the fixed geometric adjunction mate. -/
def inertiaOperator (σ : Inertia π T) : End (nearby ell R K L π T X) :=
  AdicDerivedContracts.nearbyMonodromy ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericArrow (L := L) X) (specialArrow π T X)
    (normalGalois (K := K) X σ.1.1) (genericGalois (K := K) X σ.1.1)
    (InertiaSchemeCompatibility.genericSquare (π := π) (T := T) (X := X) σ)
    (InertiaSchemeCompatibility.specialSquare (π := π) (T := T) (X := X) σ)

/-- The literal logarithm with the geometric nearby nilpotence bound. -/
def nearbyLog (d : ℕ) (B : TameCoordinate ell R K L π T) :
    End (nearby ell R K L π T X) :=
  ∑ i ∈ (Finset.range (d + 1)).filter (fun i ↦ 0 < i),
    (((-1 : ℚ_[ell]) ^ (i + 1)) * (i : ℚ_[ell])⁻¹) •
      (inertiaOperator ell R K L π T X B.generator - 1) ^ i

variable
  [CoefficientPresentation ell (Residue π T) (specialModel R K L π T X)]
  [PerverseTheory ell (Residue π T) (specialModel R K L π T X)]

/-- The provider states membership of the actual shifted nearby object. -/
class NearbyPerverseMembership (d : ℕ) : Prop where
  constructible : boundedConstructible ell (Residue π T) (specialModel R K L
    π T X)
    ((nearby ell R K L π T X)⟦(d : ℤ)⟧)
  heart : (PerverseTheory.t (ell := ell) (k := Residue π T)
      (X := specialModel R K L π T X)).heart
    ⟨((nearby ell R K L π T X)⟦(d : ℤ)⟧), constructible⟩

variable (d : ℕ) [NearbyPerverseMembership ell R K L π T X d]
  [Abelian (PerverseHeart ell (Residue π T) (specialModel R K L π T X))]

/-- The heart object is the actual RΨ(Q_ell)[d], without a chosen substitute. -/
def nearbyPerverse : PerverseHeart ell (Residue π T) (specialModel R K L π T
  X) :=
  ⟨⟨((nearby ell R K L π T X)⟦(d : ℤ)⟧),
    NearbyPerverseMembership.constructible⟩, NearbyPerverseMembership.heart⟩

/-- The actual logarithm viewed in that fully faithful perverse heart. -/
def perverseLog (B : TameCoordinate ell R K L π T) :
    End (nearbyPerverse ell R K L π T X d) :=
  End.of ((heartInclusion ell (Residue π T) (specialModel R K L π T X)).preimage
    ((shiftFunctor (Derived ℚ_[ell] (SpecialFibre π T X)) (d : ℤ)).map
      (nearbyLog ell R K L π T X d B).asHom))

/-- The actual decreasing weight index p corresponds to M_(-p). -/
def negativeOpposite : ℤᵒᵖ ⥤ ℤ where
  obj p := -p.unop
  map f := homOfLE (neg_le_neg (leOfHom f.unop))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The fixed realized perverse-monodromy filtration after RΓ and [-d]. -/
def realizedWeightDiagram (B : TameCoordinate ell R K L π T) :
    ℤᵒᵖ ⥤ DerivedCategory (ModuleCat.{1} ℚ_[ell]) :=
  negativeOpposite ⋙
    MathlibExt.CategoryTheory.MonodromyFiltration.diagram
      (perverseLog ell R K L π T X d B) d ⋙
    heartInclusion ell (Residue π T) (specialModel R K L π T X) ⋙
    shiftFunctor (Derived ℚ_[ell] (SpecialFibre π T X)) (-(d : ℤ)) ⋙
    derivedSections ℚ_[ell] (SpecialFibre π T X) ⋙ DerivedCategory.Plus.ι

/-- The fixed weight diagram before taking derived global sections. -/
def weightSheafDiagram (B : TameCoordinate ell R K L π T) :
    ℤᵒᵖ ⥤ Derived ℚ_[ell] (SpecialFibre π T X) :=
  negativeOpposite ⋙
    MathlibExt.CategoryTheory.MonodromyFiltration.diagram
      (perverseLog ell R K L π T X d B) d ⋙
    heartInclusion ell (Residue π T) (specialModel R K L π T X) ⋙
    shiftFunctor (Derived ℚ_[ell] (SpecialFibre π T X)) (-(d : ℤ))

/-- The actual cancellation of the normalization shift. -/
def unshiftNearby :
    ((heartInclusion ell (Residue π T) (specialModel R K L π T X)).obj
      (nearbyPerverse ell R K L π T X d))⟦-(d : ℤ)⟧ ≅
    nearby ell R K L π T X :=
  (shiftFunctorAdd' (Derived ℚ_[ell] (SpecialFibre π T X))
    (d : ℤ) (-(d : ℤ)) 0 (add_neg_cancel _)).symm.app _ ≪≫
      (shiftFunctorZero (Derived ℚ_[ell] (SpecialFibre π T X)) ℤ).app _

/-- The actual unbounded global nearby complex. -/
abbrev globalNearby := DerivedCategory.Plus.ι.obj
  ((derivedSections ℚ_[ell] (SpecialFibre π T X)).obj
    (nearby ell R K L π T X))

/-- The actual weight-step inclusion before taking global sections. -/
def sheafStepInclusion (B : TameCoordinate ell R K L π T) (p : ℤᵒᵖ) :
    (weightSheafDiagram ell R K L π T X d B).obj p ⟶
      nearby ell R K L π T X :=
  (shiftFunctor (Derived ℚ_[ell] (SpecialFibre π T X)) (-(d : ℤ))).map
    ((heartInclusion ell (Residue π T) (specialModel R K L π T X)).map
      ((MathlibExt.CategoryTheory.MonodromyFiltration.inclusion
        (perverseLog ell R K L π T X d B) d).app (-p.unop))) ≫
    (unshiftNearby ell R K L π T X d).hom

/-- The actual inclusion of each realized weight step into RΓ RΨ. -/
def realizedStepInclusion (B : TameCoordinate ell R K L π T) (p : ℤᵒᵖ) :
    (realizedWeightDiagram ell R K L π T X d B).obj p ⟶
      globalNearby ell R K L π T X :=
  DerivedCategory.Plus.ι.map
    ((derivedSections ℚ_[ell] (SpecialFibre π T X)).map
      ((shiftFunctor (Derived ℚ_[ell] (SpecialFibre π T X)) (-(d : ℤ))).map
          ((heartInclusion ell (Residue π T) (specialModel R K L π T X)).map
            ((MathlibExt.CategoryTheory.MonodromyFiltration.inclusion
              (perverseLog ell R K L π T X d B) d).app (-p.unop))) ≫
        (unshiftNearby ell R K L π T X d).hom))

/-- An actual filtered cochain resolution of the fixed geometric weight
diagram, including its maps into the actual global nearby complex. -/
structure FilteredNearbyResolution (B : TameCoordinate ell R K L π T) where
  complex : FilteredObject (CochainComplex (ModuleCat.{1} ℚ_[ell]) ℤ) ℤᵒᵖ
  underlying : DerivedCategory.Q.obj complex.X ≅ globalNearby ell R K L π T X
  levels : complex.filtration.diagram ⋙ DerivedCategory.Q ≅
    realizedWeightDiagram ell R K L π T X d B
  normalized : ∀ p : ℤᵒᵖ,
    DerivedCategory.Q.map (complex.filtration.ι.app p) ≫ underlying.hom =
      levels.hom.app p ≫ realizedStepInclusion ell R K L π T X d B p
  degreewiseFinite : ∀ n : ℤ, ∃ lo hi : ℤ,
    (∀ p : ℤ, p ≤ lo → IsIso ((complex.filtration.ι.app (op p)).f n)) ∧
    ∀ p : ℤ, hi ≤ p → IsZero ((complex.filtration.obj (op p)).X n)
  source : FilteredObject (Cochains ℚ_[ell] (SpecialFibre π T X)) ℤᵒᵖ
  sourceUnderlying : DerivedCategory.Plus.Q.obj source.X ≅
    nearby ell R K L π T X
  sourceLevels : source.filtration.diagram ⋙ DerivedCategory.Plus.Q ≅
    weightSheafDiagram ell R K L π T X d B
  sourceNormalized : ∀ p : ℤᵒᵖ,
    DerivedCategory.Plus.Q.map (source.filtration.ι.app p) ≫
        sourceUnderlying.hom =
      sourceLevels.hom.app p ≫ sheafStepInclusion ell R K L π T X d B p
  sourceInjective : source.X.obj.IsKInjective ∧
    ∀ p : ℤᵒᵖ, (source.filtration.obj p).obj.IsKInjective
  globalSourceBase : complex.X =
    ((sections ℚ_[ell] (SpecialFibre π T X)).mapCochainComplexPlus.obj
      source.X).obj
  globalSourceLevels : complex.filtration.diagram =
    source.filtration.diagram ⋙
      (sections ℚ_[ell] (SpecialFibre π T X)).mapCochainComplexPlus ⋙
        CochainComplex.Plus.ι (ModuleCat.{1} ℚ_[ell])
  globalSourceInclusion : ∀ p : ℤᵒᵖ,
    complex.filtration.ι.app p ≫ eqToHom globalSourceBase =
      eqToHom (congrArg (fun F ↦ F.obj p) globalSourceLevels) ≫
        ((sections ℚ_[ell] (SpecialFibre π T X)).mapCochainComplexPlus.map
          (source.filtration.ι.app p)).hom
  globalUnitNormalization : underlying.hom =
    DerivedCategory.Q.map (eqToHom globalSourceBase) ≫
      DerivedCategory.Plus.ι.map
        ((sections ℚ_[ell] (SpecialFibre π T
          X)).rightDerivedFunctorPlusUnit.app source.X ≫
          (derivedSections ℚ_[ell] (SpecialFibre π T X)).map
            sourceUnderlying.hom)
  globalLevelUnitNormalization : ∀ p : ℤᵒᵖ,
    levels.hom.app p =
      DerivedCategory.Q.map
          (eqToHom (congrArg (fun F ↦ F.obj p) globalSourceLevels)) ≫
        DerivedCategory.Plus.ι.map
          ((sections ℚ_[ell] (SpecialFibre π T
            X)).rightDerivedFunctorPlusUnit.app
              (source.filtration.obj p) ≫
            (derivedSections ℚ_[ell] (SpecialFibre π T X)).map
              (sourceLevels.hom.app p))

namespace FilteredNearbyResolution

variable {ell R K L π T X d} {B : TameCoordinate ell R K L π T}
  (E : FilteredNearbyResolution ell R K L π T X d B)

/-- The spectral sequence is the native constructor applied to this complex. -/
def spectralSequence : CohomologicalSpectralSequence (ModuleCat.{1} ℚ_[ell])
  1 :=
  FilteredCochainSpectralSequence.spectralSequence E.complex

/-- The page object is the actual native consecutive-step cone cohomology. -/
def firstPageIso (p q : ℤ) :=
  FilteredCochainSpectralSequence.firstPageIso
    E.complex p q

/-- The actual geometric generic-fibre global complex. -/
abbrev genericGlobal := DerivedCategory.Plus.ι.obj
  ((derivedSections ℚ_[ell] (GenericFibre (L := L) X)).obj
    (continuousComplex ℚ_[ell] (RationalCoefficients.{0} ell)
      (GenericFibre (L := L) X)))

/-- The actual normalized proper global comparison, never an arbitrary map. -/
def properComparison := nearbyGlobalComparison ℚ_[ell]
  (genericArrow (L := L) X) (specialArrow π T X)
  (continuousComplex ℚ_[ell] (RationalCoefficients.{0} ell)
    (GenericFibre (L := L) X))

/-- Once the canonical proper comparison is invertible, the generic-fibre
identification is produced from that exact map and the resolution's model. -/
def genericAbutment [IsIso (properComparison (ell := ell) (π := π) (T := T)
  (X := X))] :
    DerivedCategory.Q.obj E.complex.X ≅ genericGlobal (ell := ell) (L := L)
      (X := X) :=
  E.underlying ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso (properComparison (ell := ell) (π := π) (T := T) (X := X))).symm

end FilteredNearbyResolution

namespace StratumTerms

variable [Fintype (irreducibleComponents ((SemistableModels.specialFunctor
  R).obj X).left)]
  [HasFiniteBiproducts (CochainComplex (ModuleCat.{1} ℚ_[ell]) ℤ)]

/-- Actual component subsets and the exact Rapoport--Zink column bounds. -/
def TermIndex (p : ℤ) :=
  {ks : Fin (d + 1) × Finset
      (irreducibleComponents ((SemistableModels.specialFunctor R).obj
        X).left) //
    max 0 p ≤ (ks.1.val : ℤ) ∧ (ks.2.card : ℤ) = 2 * ks.1.val - p + 1}

instance termIndex_fintype (p : ℤ) : Fintype (TermIndex R X d p) := by
  classical
  unfold TermIndex
  exact Fintype.ofFinite _

/-- The actual geometric base change of the scheme-theoretic intersection. -/
def geometricStratum
    (s : Finset (irreducibleComponents ((SemistableModels.specialFunctor
      R).obj X).left)) :
    Over (Spec (.of (Residue π T))) :=
  (Over.pullback (residueBaseMap π T)).obj
    (Over.mk (SemistableModels.stratumToBase R X s))

/-- The actual cochain representative of stratum cohomology, tensored
with the actual underlying Tate coefficient and shifted by p-2k. -/
def termComplex (ellInvertible : (ell : L) ≠ 0) (p : ℤ)
    (ks : TermIndex R X d p) : CochainComplex (ModuleCat.{1} ℚ_[ell]) ℤ :=
  let S := geometricStratum R K L π T X ks.1.2
  let G := DerivedCategory.Plus.ι.obj
    ((derivedSections ℚ_[ell] S.left).obj
      (continuousComplex ℚ_[ell] (RationalCoefficients.{0} ell) S.left))
  let C := DerivedCategory.Q.objPreimage G
  let C' := ((AdicTateCoefficients.tensorLine ell R K L π T ellInvertible
    (p - ks.1.1.val)).mapHomologicalComplex (.up ℤ)).obj C
  C'⟦p - 2 * (ks.1.1.val : ℤ)⟧

/-- The actual finite RZ derived stratum sum. Its Tate arithmetic action
is carried by the actual `tateLine`; this object is its explicit forgetful
  image. -/
def gradedStratumObject (ellInvertible : (ell : L) ≠ 0) (p : ℤ) :
    DerivedCategory (ModuleCat.{1} ℚ_[ell]) := by
  classical
  exact DerivedCategory.Q.obj (biproduct
    (fun i : Fin (Fintype.card (TermIndex R X d p)) ↦
      termComplex ell R K L π T X d ellInvertible p
        ((Fintype.equivFin (TermIndex R X d p)).symm i)))

end StratumTerms

variable [Fintype (irreducibleComponents ((SemistableModels.specialFunctor
  R).obj X).left)]
  [HasFiniteBiproducts (CochainComplex (ModuleCat.{1} ℚ_[ell]) ℤ)]

/-- The actual RZ graded identification attached to the normalized
geometric resolution. The first differential remains the native one.
Canonical restriction/Gysin and arithmetic-equivariance refinements need
the corresponding shared normalized cohomology/purity providers. -/
structure RapoportZinkData (B : TameCoordinate ell R K L π T)
    (ellInvertible : (ell : L) ≠ 0) where
  resolution : FilteredNearbyResolution ell R K L π T X d B
  grades : ∀ p : ℤ,
    DerivedCategory.Q.obj (CochainComplex.mappingCone
      (resolution.complex.filtration.diagram.map
        ((homOfLE (show p ≤ p + 1 by omega)).op))) ≅
      StratumTerms.gradedStratumObject ell R K L π T X d ellInvertible p

/-- The named general provider input for paper tasks. Every category,
object, filtration, coefficient, page and map in its data is fixed above. -/
class RapoportZinkTheory (B : TameCoordinate ell R K L π T)
    (ellInvertible : (ell : L) ≠ 0) where
  data : RapoportZinkData ell R K L π T X d B ellInvertible

end MathlibExt.AlgebraicGeometry.RapoportZinkContracts

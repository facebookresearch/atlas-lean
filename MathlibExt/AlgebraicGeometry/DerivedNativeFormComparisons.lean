/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedClosedFormContractionClasses
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence

/-!
# Native cotangent exterior maps and generator-normalized affine forms

Exterior(df) is inclusion, the actual enriched tensor of df with itself,
and projection. The resolved affine comparison uses the Moore-normalized
Kahler one-forms and the literal signed shuffle of their exterior product.
The coefficient module action uses the same scalar shuffle. Its balanced
tensor quotient and rational skew projector are the native ones.

The affine weight comparison below is computed from the original QA
weight isomorphism and the native shifts. No arbitrary affine cotangent
identification or de Rham map is introduced. The constructors and the
quasi-isomorphism of these computed comparisons remain direct Wanted work.

Sources: PTVV arXiv:1111.3209v4, Section 1.1 and Proposition 1.14;
HAG II arXiv:math/0404373v7, Section 1.4.1. Native exterior-algebra,
DG tensor, normalization, Koszul and public-source notices remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.Opposite _root_.AlgebraicTopology
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open CochainComplex.HomComplex
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The actual closed enriched tensor of a cotangent arrow with itself. -/
def tensorDifferential {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    {G : QCohEnhancement M U X} (H : CoherentMonoidalEnhancement G)
    {LX LY : G.category} (d : DGHom (LargeScalar k) 0 LY LX) :
    DGHom (LargeScalar k) 0 (H.monoidal.tensor.obj (LY, LY))
      (H.monoidal.tensor.obj (LX, LX)) :=
  H.monoidal.tensor.dgMap 0 (dgTensorHom (LargeScalar k)
    (X := (LY, LY)) (Y := (LX, LX)) (p := 0) (q := 0) (n := 0) d d (by omega))

/-- Tensor(df,df) is closed by the native tensor differential and enriched functor law. -/
theorem tensorDifferential_closed {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    {G : QCohEnhancement M U X} (H : CoherentMonoidalEnhancement G)
    {LX LY : G.category} (d : DGHom (LargeScalar k) 0 LY LX)
    (hd : d ∈ dgCycles (LargeScalar k) LY LX) :
    tensorDifferential H d ∈ dgCycles (LargeScalar k) _ _ := by
  rw [mem_dgCycles, tensorDifferential, ← H.monoidal.tensor.dgMap_dgDifferential]
  rw [dgDifferential_dgTensorHom, (mem_dgCycles (LargeScalar k)).mp hd]
  simp only [zero_dgTensorHom, dgTensorHom_zero, smul_zero, add_zero]
  exact (H.monoidal.tensor.dgMap 1).map_zero

/-- The exterior differential is the actual inclusion/tensor/projection composite. -/
def exteriorDifferential [Algebra ℚ k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    {G : QCohEnhancement M U X} (H : CoherentMonoidalEnhancement G)
    {LX LY : G.category} (d : DGHom (LargeScalar k) 0 LY LX)
    (EY : ExteriorSquare H LY) (EX : ExteriorSquare H LX) :
    DGHom (LargeScalar k) 0 EY.object EX.object :=
  dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      EY.inclusion (tensorDifferential H d) (by omega))
    EX.projection (by omega)

/-- This computed exterior differential is closed, with no separate differential proof input. -/
theorem exteriorDifferential_closed [Algebra ℚ k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    {G : QCohEnhancement M U X} (H : CoherentMonoidalEnhancement G)
    {LX LY : G.category} (d : DGHom (LargeScalar k) 0 LY LX)
    (hd : d ∈ dgCycles (LargeScalar k) LY LX)
    (EY : ExteriorSquare H LY) (EX : ExteriorSquare H LX) :
    exteriorDifferential H d EY EX ∈ dgCycles (LargeScalar k) _ _ := by
  rw [mem_dgCycles, exteriorDifferential, dgDifferential_dgComp, dgDifferential_dgComp,
    (mem_dgCycles (LargeScalar k)).mp EY.inclusion_closed,
    (mem_dgCycles (LargeScalar k)).mp EX.projection_closed,
    (mem_dgCycles (LargeScalar k)).mp (tensorDifferential_closed H d hd)]
  simp

/-- The native normalized coefficient is read through the actual Moore inclusion and term isomorphism. -/
def formCoefficient {A : SAlg k} (M : SimplicialDRModel A) (p n : ℕ)
    (z : (normalizedForms M p).X (-(n : ℤ))) : formTerm A p (op ⦋n⦌) :=
  (M.termIso p (op ⦋n⦌)).hom
    (((inclusionOfMooreComplexMap (M.forms p)).f n)
      ((((normalizedMooreComplex (ModuleCat.{u} k)).obj (M.forms p)).extendXIso
        (ComplexShape.embeddingUpIntLE 0) (by simp)).hom z))

/-- Pulling a native one-form to a shuffle degree uses the actual source simplicial form map. -/
def formPull {A : SAlg k} (M : SimplicialDRModel A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (z : formTerm A 1 n) : formTerm A 1 m :=
  (M.termIso 1 m).hom ((M.forms 1).map f ((M.termIso 1 n).inv z))

/-- The literal signed scalar shuffle on the actual normalized Kahler one-forms. -/
def formScalarShuffle {A : SAlg k} (M : SimplicialDRModel A) (p q : ℕ)
    (a : A.obj (op ⦋p⦌)) (z : formTerm A 1 (op ⦋q⦌)) : formTerm A 1 (op ⦋p + q⦌) :=
  ∑ s : Shuffle p q, (-1 : k) ^ inversions s •
    ((A.map (leftProjection s).op a) •
      (show ⋀[A.obj (op ⦋p + q⦌)]^1 (Ω[A.obj (op ⦋p + q⦌)⁄k]) from
        formPull M (rightProjection s).op z))

/-- The literal signed shuffle of the ordinary exterior product, in form degree two. -/
def formWedgeShuffle {A : SAlg k} (M : SimplicialDRModel A) (p q : ℕ)
    (z : formTerm A 1 (op ⦋p⦌)) (w : formTerm A 1 (op ⦋q⦌)) :
    formTerm A 2 (op ⦋p + q⦌) :=
  ∑ s : Shuffle p q, (-1 : k) ^ inversions s •
    MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels.wedge k (A.obj (op ⦋p + q⦌)) 1 1
      (formPull M (leftProjection s).op z) (formPull M (rightProjection s).op w)

/-- A normalized wedge map is fixed on every actual homogeneous tensor generator. -/
structure NormalizedFormWedge {A : SAlg k} (M : SimplicialDRModel A) where
  map : normalizedForms M 1 ⊗ normalizedForms M 1 ⟶ normalizedForms M 2
  normalized : ∀ (p q : ℕ) (z : (normalizedForms M 1).X (-(p : ℤ)))
    (w : (normalizedForms M 1).X (-(q : ℤ))),
    formCoefficient M 2 (p + q)
      (((HomologicalComplex.ιTensorObj (normalizedForms M 1) (normalizedForms M 1)
        (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)) ≫
          map.f (-((p + q : ℕ) : ℤ))).hom (TensorProduct.tmul k z w)) =
      formWedgeShuffle M p q (formCoefficient M 1 p z) (formCoefficient M 1 q w)

/-- The actual normalized cotangent on QA, with every scalar coefficient action fixed. -/
structure ResolvedCotangentModule (N : ShuffleAlgebraFunctor k) {Q : AlgebraReplacementFunctor k}
    (D : AffineDRSystem Q) (A : SAlg k) where
  module : DGDerivedModules k (coefficientCategory N (Q.functor.obj A))
  value : DerivedCoefficientTensorModels.value (coefficientCategory N (Q.functor.obj A))
    PUnit.unit module.obj ≅ normalizedForms (D.forms A) 1
  action : ∀ (p q : ℕ)
    (a : (N.functor.obj (Q.functor.obj A)).X.X (-(p : ℤ)))
    (z : (DerivedCoefficientTensorModels.value (coefficientCategory N (Q.functor.obj A))
      PUnit.unit module.obj).X (-(q : ℤ))),
    formCoefficient (D.forms A) 1 (p + q)
      ((value.hom.f (-((p + q : ℕ) : ℤ))).hom
        (DerivedCotangentModels.moduleAction module.obj (op PUnit.unit) a (by omega) z)) =
      formScalarShuffle (D.forms A) p q
        (MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle.coefficient (Q.functor.obj A) p
          (((N.model (Q.functor.obj A)).complexIso.hom.f (-(p : ℤ))).hom a))
        (formCoefficient (D.forms A) 1 q ((value.hom.f (-(q : ℤ))).hom z))

/-- The native rational skew projector of the actual balanced module tensor. -/
def moduleSkewProjector [Algebra ℚ k] (C : DGCat k) (o : C)
    (T : DerivedTensorModel C o) (unit : DGDerivedModules k C)
    (unit_eq : unit.obj = regularModule C o) (B : CoherenceModel C o T unit unit_eq)
    (P : DGDerivedModules k C) : DGHom k 0 (T.functor.obj (P, P)).obj (T.functor.obj (P, P)).obj :=
  algebraMap ℚ k (1 / 2 : ℚ) •
    (dgId k (T.functor.obj (P, P)).obj -
      ((DGFunctor.homEquivDGCycles k _ _) (B.symmetry P P).hom).val)

/-- The actual exterior module splits that fixed native skew projector up to DG homotopy. -/
structure ModuleExteriorSquare [Algebra ℚ k] (C : DGCat k) (o : C)
    (T : DerivedTensorModel C o) (unit : DGDerivedModules k C)
    (unit_eq : unit.obj = regularModule C o) (B : CoherenceModel C o T unit unit_eq)
    (P : DGDerivedModules k C) where
  module : DGDerivedModules k C
  inclusion : DGHom k 0 module.obj (T.functor.obj (P, P)).obj
  inclusion_closed : inclusion ∈ dgCycles k _ _
  projection : DGHom k 0 (T.functor.obj (P, P)).obj module.obj
  projection_closed : projection ∈ dgCycles k _ _
  section_homotopy : DGHom k (-1) module.obj module.obj
  section_identity : dgDifferential k (-1) section_homotopy =
    dgComp k (p := 0) (q := 0) (n := 0) inclusion projection (by omega) - dgId k module.obj
  projector_homotopy : DGHom k (-1) (T.functor.obj (P, P)).obj (T.functor.obj (P, P)).obj
  projector_identity : dgDifferential k (-1) projector_homotopy =
    dgComp k (p := 0) (q := 0) (n := 0) projection inclusion (by omega) -
      moduleSkewProjector C o T unit unit_eq B P

/-- The resolution exterior comparison is fixed on the entire native balanced tensor quotient. -/
structure ResolvedExteriorFormComparison [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) {Q : AlgebraReplacementFunctor k}
    (D : AffineDRSystem Q) (A : SAlg k) (P : ResolvedCotangentModule N D A)
    (T : DerivedTensorModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit)
    (unit : DGDerivedModules k (coefficientCategory N (Q.functor.obj A)))
    (unit_eq : unit.obj = regularModule (coefficientCategory N (Q.functor.obj A)) PUnit.unit)
    (B : CoherenceModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit T unit unit_eq)
    (E : ModuleExteriorSquare (coefficientCategory N (Q.functor.obj A)) PUnit.unit
      T unit unit_eq B P.module) (W : NormalizedFormWedge (D.forms A)) where
  map : DerivedCoefficientTensorModels.value (coefficientCategory N (Q.functor.obj A))
    PUnit.unit E.module.obj ⟶ normalizedForms (D.forms A) 2
  normalized : quotientMap (coefficientCategory N (Q.functor.obj A)) PUnit.unit
      (T.action P.module.obj) (T.action P.module.obj) ≫
    (T.value P.module P.module).comparison.inv ≫
    moduleComponent ((DGFunctor.homEquivDGCycles k _ _).symm
      ⟨E.projection, E.projection_closed⟩) (op PUnit.unit) ≫ map =
      (P.value.hom ⊗ₘ P.value.hom) ≫ W.map

/-- Unshifting the original QA weight isomorphism computes the affine form comparison. -/
def affineFormWeightMap {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q) (A : SAlg k) :
    normalizedForms (D.forms A) 2 ⟶ ((D.functor.obj A).weight 2)⟦-2⟧ :=
  (shiftFunctorZero (Cochains k) ℤ).inv.app (normalizedForms (D.forms A) 2) ≫
    (shiftFunctorAdd' (Cochains k) (2 : ℤ) (-2) 0 (by omega)).hom.app
      (normalizedForms (D.forms A) 2) ≫
    (shiftFunctor (Cochains k) (-2)).map
      ((D.model A).weightIso 2).inv ≫
    (shiftFunctor (Cochains k) (-2)).map
      (eqToHom (congrArg (fun E => E.weight (2 : ℤ)) (D.object_eq A)))

/-- The larger native coefficient comparison keeps exactly the same shifts and coefficients. -/
def affineCoefficientFormMap {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q) (A : SAlg k) :
    (largeCochainLift k).obj (normalizedForms (D.forms A) 2) ⟶
      ((globalToCoefficients k).obj ((liftComplex k).obj ((D.functor.obj A).weight 2)))⟦-2⟧ :=
  (globalToCoefficients k).map ((liftComplex k).map (affineFormWeightMap D A))

end MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons

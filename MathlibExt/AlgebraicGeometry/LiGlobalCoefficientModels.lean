/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalStackCotangentModels
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
public import MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Native global coefficient and cotangent binding for Li sources

The classical source is the full DG category of actual K-injective,
derived-cartesian module-presheaf complexes on ALL affine stack points.
Its Hom is the native full cochain Hom complex. Every scalar action is
the actual base-k action in the section ring. The enriched realization
preserves all Hom complexes by quasi-isomorphisms; an H0 equivalence or
independent objectwise isomorphisms does not replace it.

The source coefficient image is the exact PR4048 native
DerivedCoefficientCech/DerivedSourcedCech/DerivedCoefficientImage model,
with its whole-functor geometric comparison, all envelope actions and
actual injective diagram replacement before limits. The coherent target
uses the native complete joint square-zero test/family diagram and its
left mapping fibration. It is bound to the genuine global relative
cotangent normalization by ONE global cochain resolution.

All model/bridge data are construction outputs in the Li virtual factory.
The Scheme.Hom cotangent provider itself is implemented public Axiom
source, not a newly asserted existence theorem.

Source pins: native coefficient modules from Atlas PR4048
e6e3c8d7c02b1baedace4e3044e622070b5217d0; AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b, SchemeCotangentComplex.lean
and ResolutionCotangentAny.lean (Apache 2.0); Jun Li math/0110113v1
Sections 1--2. All imported source/license headers are preserved.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGlobalCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry GeneralStackGeometry StackCycleGeometry StackAffineModules
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open DerivedPrestackMapping DerivedQCohEnhancementModels DerivedQCohModuleFamilies
open DerivedSquareZeroFamilies
open DerivedFamilyCoefficientCategories DerivedCoefficientCechModels DerivedSourcedCechModels
open DerivedCoefficientImageModels DerivedGlobalCotangentModels DerivedCoherentCotangentModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] (X : Stack (Spec (.of k)))

abbrev Complex := CochainComplex (ModulePresheaf X) ℤ

def pointScalar (p : AffinePoint X) : k →+* (rings X).obj (op p) :=
  p.obj.base.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- Nonflat scalar extension is computed from a native cofibrant global source. -/
structure CartesianResolution (K : Complex X) where
  source : Complex X
  map : source ⟶ K
  [quasi : QuasiIso map]
  cofibrant : ∀ p : AffinePoint X, GlobalStackCotangentModels.IsCofibrant
    (GlobalStackCotangentModels.evaluate source p)
  baseChange : ∀ {p q : AffinePoint X} (f : p ⟶ q),
    GlobalStackCotangentModels.DerivedBaseChange source f
attribute [instance] CartesianResolution.quasi

/-- Native complexes, not freely chosen DG Hom carriers. -/
structure ClassicalComplex where
  complex : Complex X
  [injective : complex.IsKInjective]
  cartesian : CartesianResolution X complex
attribute [instance] ClassicalComplex.injective

instance classicalEnrichment [Linear (LargeScalar k) (ModulePresheaf X)] :
    DGCategory (LargeScalar k) (ClassicalComplex X) where
  Hom A B := CochainComplex.linearHomComplex (LargeScalar k) A.complex B.complex
  id A := eId (Cochains (LargeScalar k)) A.complex
  comp A B C := eComp (Cochains (LargeScalar k)) A.complex B.complex C.complex
  id_comp A B := EnrichedCategory.id_comp (V := Cochains (LargeScalar k)) A.complex B.complex
  comp_id A B := EnrichedCategory.comp_id (V := Cochains (LargeScalar k)) A.complex B.complex
  assoc A B C D := EnrichedCategory.assoc (V := Cochains (LargeScalar k))
    A.complex B.complex C.complex D.complex

def unitComplex : Complex X :=
  (CochainComplex.singleFunctor (ModulePresheaf X) 0).obj
    (PresheafOfModules.unit (rings X ⋙ forget₂ CommRingCat RingCat))

/-- The entire source model is constructed together with the native coefficient context. -/
structure Context where
  lift : CochainLiftModel k
  shuffle : ShuffleAlgebraFunctor k
  scalars : AffineScalarSystem shuffle
  modules : AffineModuleFibration shuffle scalars
  unit : RegularUnitSystem modules
  prestack : Prestack k
  category : FamilyCoefficientCategory lift shuffle prestack
  raw : RawModuleRealization modules
  qcoh : QCohEnhancement modules unit prestack
  diagram : CoefficientDiagramSystem category qcoh
  unitDiagram : UnitCoefficientDiagram category qcoh diagram
  image : SourcedCoefficientImageModel category raw qcoh diagram unitDiagram
  replacement : EnrichedDiagramReplacement category qcoh diagram
  limits : CoefficientLimitFunctor category qcoh replacement
  unitLift : UnitCoefficientLift category qcoh replacement unitDiagram
  unitCone : CoherentUnitCone category qcoh unitLift
  globalSections : GlobalSectionComparison category qcoh limits unitCone
  classicalLinear : Linear (LargeScalar k) (ModulePresheaf X)
  scalar_normalized : letI := classicalLinear;
    ∀ (M N : ModulePresheaf X) (a : LargeScalar k) (f : M ⟶ N)
      (p : AffinePoint X) (x : M.obj (op p)),
      (a • f).app (op p) x = pointScalar X p a.down • f.app (op p) x
  realization : letI := classicalLinear;
    EnrichedFunctor (Cochains (LargeScalar k)) (ClassicalComplex X) qcoh.category
  hom_quasi : letI := classicalLinear;
    ∀ A B : ClassicalComplex X, QuasiIso (realization.map A B)
  actual : letI := classicalLinear;
    ∀ A : ClassicalComplex X,
      ActualCoefficientSection category qcoh raw diagram (realization.obj A)
  classicalUnit : ClassicalComplex X
  unitResolution : unitComplex X ⟶ classicalUnit.complex
  [unitQuasi : QuasiIso unitResolution]
  unit_normalized : letI := classicalLinear; qcoh.unit = realization.obj classicalUnit
  kernels : KernelSystem shuffle prestack
  kernelSections : KernelSectionFunctor modules raw kernels
  kernelDG : KernelDGFunctor modules raw kernels qcoh kernelSections
  liftProjection : JointLiftProjection modules raw kernels
  path : JointPath modules raw kernels
  derivations : JointDerivationModel modules raw kernels liftProjection path
  derivationFibration : DerivationFibration modules raw kernels derivations
  coherentCotangent : CoherentGlobalCotangent kernelDG derivations derivationFibration
attribute [instance] Context.unitQuasi

variable {X} {Y : Stack (Spec (.of k))} (f : StackHom X Y) (C : Context X)

/-- For the structural morphism to the native point, the full coherent cotangent
is fixed by ONE global resolution of the implemented relative cotangent model. -/
structure CotangentBinding where
  native : GlobalStackCotangentModels.Normalization f
  object : ClassicalComplex X
  map : native.complex ⟶ object.complex
  [quasi : QuasiIso map]
  normalized : letI := C.classicalLinear;
    C.coherentCotangent.object = C.realization.obj object
attribute [instance] CotangentBinding.quasi

variable (B : CotangentBinding f C)

/-- The global obstruction source and its map use one actual cochain square,
so every overlap, coefficient action and homogeneous map is retained. -/
structure SourceBinding where
  complex : Complex X
  object : ClassicalComplex X
  resolution : complex ⟶ object.complex
  [quasi : QuasiIso resolution]
  map : complex ⟶ B.native.complex
  injectiveMap : object.complex ⟶ B.object.complex
  square : resolution ≫ injectiveMap = map ≫ B.map
  coefficientMap : letI := C.classicalLinear;
    DGHom (LargeScalar k) 0 (C.realization.obj object) C.coherentCotangent.object
  closed : letI := C.classicalLinear;
    coefficientMap ∈ dgCycles (LargeScalar k) (C.realization.obj object) C.coherentCotangent.object
  normalized : letI := C.classicalLinear; HEq coefficientMap
    (C.realization.dgMap 0 (show DGHom (LargeScalar k) 0 object B.object from
      CochainComplex.HomComplex.Cochain.ofHom injectiveMap))
attribute [instance] SourceBinding.quasi

end MathlibExt.AlgebraicGeometry.LiGlobalCoefficientModels

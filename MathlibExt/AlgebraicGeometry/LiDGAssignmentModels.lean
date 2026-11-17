/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiSourceQualifiedVirtualModels
public import MathlibExt.AlgebraicGeometry.LiCentralSourceModels
public import MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
import all MathlibExt.CategoryTheory.DGSource.DGFullSubcategory
import all MathlibExt.CategoryTheory.DGSource.DGNaturalTransformation
import all MathlibExt.CategoryTheory.DGSource.DGRepresentables

/-!
# The full DG Li assignment and the particular global cotangent map

The coefficient category, Hom complexes, sourced coefficient image and
coherent cotangent are the existing native PR4048 objects. Precomposition
below is computed from the SAME global injective cochain map used in the
POT. The eventual comparison is an equality of whole DG natural
transformations, including every homogeneous coefficient map.

Source: Jun Li math/0110113v1, (1.15)--(1.25), Proposition1.18,
Theorems2.3/2.5 and Proposition2.4; Atlas PR4048
e6e3c8d7c02b1baedace4e3044e622070b5217d0. The native polynomial
extension classes retain AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache2.0), especially
Deformation/RingThickening/CotangentObstructionCocycle.lean.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiDGAssignmentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackAffineModules
open MathlibExt.DGSource MathlibExt.CategoryTheory.DGModelContracts
open DerivedQCohEnhancementModels LiGlobalCoefficientModels
open DerivedPrestackMapping DerivedAffineFamilies DerivedQCohModuleFamilies
open DerivedFamilyCoefficientCategories DerivedCoefficientCechModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels DerivedCoefficientTensorModels
open CochainComplex.HomComplex

universe u v w z

section DG

variable {r : Type u} [CommRing r] {A : Type v} {B : Type w} {E : Type z}
  [DGCategory r A] [DGCategory r B] [DGCategory r E]

/-- Restriction of the actual DG natural transformation along an actual DG functor. -/
def restrictTransformation (T : EnrichedFunctor (Cochains r) A B)
    {F H : EnrichedFunctor (Cochains r) B E} (a : DGNatTrans F H) :
    DGNatTrans (T.comp (Cochains r) F) (T.comp (Cochains r) H) :=
  DGNatTrans.ofDGApp (fun x => a.dgApp (T.obj x))
    (fun x => a.dgApp_mem_dgCycles (T.obj x))
    (fun n f => by
      simpa only [EnrichedFunctor.comp_dgMap] using a.dgComp_dgMap_dgApp (T.dgMap n f))

@[simp] theorem restrictTransformation_dgApp (T : EnrichedFunctor (Cochains r) A B)
    {F H : EnrichedFunctor (Cochains r) B E} (a : DGNatTrans F H) (x : A) :
    (restrictTransformation T a).dgApp x = a.dgApp (T.obj x) := by
  simp only [restrictTransformation, DGNatTrans.dgApp_ofDGApp]

/-- The covariant full DG Hom functor is the existing representable on the opposite. -/
def homFunctor (p : A) : EnrichedFunctor (Cochains r) A (Cochains r) :=
  (DerivedCoefficientDualModels.doubleOpposite (R := r) A).comp (Cochains r)
    (dgRepresentable (C := Aᵒᵖ) r (op p))

@[simp] theorem homFunctor_obj (p x : A) :
    (homFunctor (r := r) p).obj x = dgHomComplex r p x := rfl

theorem homFunctor_dgMap (p : A) {x y : A} {n : ℤ} (g : DGHom r n x y) :
    (homFunctor (r := r) p).dgMap n g = dgPostcomp r (op p) n g := by
  unfold homFunctor
  rw [EnrichedFunctor.comp_dgMap]
  have h : (DerivedCoefficientDualModels.doubleOpposite (R := r) A).dgMap n g = g := by
    rw [EnrichedFunctor.dgMap_apply]
    rfl
  rw [h]
  unfold dgPostcomp
  exact dgRepresentable_dgMap (C := Aᵒᵖ) r (op p) g

/-- The native covariant Yoneda rule retains EVERY homogeneous cochain, without a cycle assumption. -/
theorem homTransformation_apply (p : A)
    {F : EnrichedFunctor (Cochains r) A (Cochains r)}
    (a : DGNatTrans (homFunctor (r := r) p) F) (x : A) (n : ℤ) (g : DGHom r n p x) :
    ((a.dgApp x : Cochain (dgHomComplex r p x) (F.obj x) 0).v n n (add_zero n)).hom g =
      ((F.dgMap n g : Cochain (F.obj p) (F.obj x) n).v 0 n (zero_add n)).hom
        (((a.dgApp p : Cochain (dgHomComplex r p p) (F.obj p) 0).v 0 0 (add_zero 0)).hom
          (dgId r p)) := by
  have h := a.dgComp_dgMap_dgApp g
  have q := congrArg (fun z : Cochain (dgHomComplex r p p) (F.obj x) n =>
    (z.v 0 n (zero_add n)).hom (dgId r p)) h
  rw [dgComp_v r _ _ (add_zero n) 0 n n (zero_add n) (add_zero n),
    dgComp_v r _ _ (zero_add n) 0 0 n (add_zero 0) (zero_add n)] at q
  simp only [mul_zero, zero_mul, Int.negOnePow_zero, one_smul,
    ModuleCat.hom_comp, LinearMap.comp_apply, homFunctor_dgMap] at q
  have hg := dgPostcomp_v r p g 0 n (zero_add n) (dgId r p)
  simp only [zero_mul, Int.negOnePow_zero, one_smul, dgId_dgComp] at hg
  exact (congrArg (fun z : DGHom r n p x =>
    ((a.dgApp x : Cochain (dgHomComplex r p x) (F.obj x) 0).v n n (add_zero n)).hom z) hg).symm.trans q

/-- Actual precomposition, retaining the full cochain complex in every coefficient. -/
def precompose {p l : A} (f : DGHom r 0 p l) (hf : f ∈ dgCycles r p l) :
    DGNatTrans (homFunctor (r := r) l) (homFunctor (r := r) p) :=
  restrictTransformation (DerivedCoefficientDualModels.doubleOpposite (R := r) A)
    ((dgRepresentableNatTransEquiv (C := Aᵒᵖ) r (op l) (op p)).symm ⟨f, by
      rw [mem_dgCycles]
      exact (mem_dgCycles (C := A) r).1 hf⟩)

/-- Every homogeneous cotangent class is sent to composition with that same map. -/
theorem precompose_apply {p l : A} (f : DGHom r 0 p l) (hf : f ∈ dgCycles r p l)
    (x : A) (n : ℤ) (g : DGHom r n l x) :
    (((precompose f hf).dgApp x :
      Cochain (dgHomComplex r l x) (dgHomComplex r p x) 0).v n n (add_zero n)).hom g =
      dgComp r f g (zero_add n) := by
  rw [precompose, restrictTransformation_dgApp]
  have h := dgApp_dgRepresentableNatTransEquiv_symm_v (C := Aᵒᵖ)
    (R := r) (op l) (op p) ⟨f, by
      rw [mem_dgCycles]
      exact (mem_dgCycles (C := A) r).1 hf⟩ (Y := op x) g
  simpa only [homFunctor, EnrichedFunctor.comp, DerivedCoefficientDualModels.doubleOpposite,
    dgRepresentable_obj, dgComp_op,
    mul_zero, Int.negOnePow_zero, one_smul] using h

end DG

section CoefficientModules

variable {r : Type u} [CommRing r] {A : Type u} [DGCategory r A]

/-- Native component evaluation is enriched on the full cochain Hom complexes. -/
def moduleEvaluation (x : Aᵒᵖ) :
    EnrichedFunctor (Cochains r) (RightModule r A) (Cochains r) :=
  EnrichedFunctor.ofDGMap (fun M => M.toEnrichedFunctor.obj x)
    (fun n => DGFunctor.dgApp r n x)
    (fun _ f => DGFunctor.dgApp_dgDifferential r f x)
    (fun M => DGFunctor.dgApp_dgId r M x)
    (fun f g h => DGFunctor.dgApp_dgComp r f g h x)

/-- Cofibrant modules retain that same native evaluation. -/
def derivedModuleEvaluation (x : Aᵒᵖ) :
    EnrichedFunctor (Cochains r) (DGDerivedModules r A) (Cochains r) where
  obj M := M.obj.toEnrichedFunctor.obj x
  map M N := (moduleEvaluation x).map M.obj N.obj
  map_id M := (moduleEvaluation x).map_id M.obj
  map_comp M N P := (moduleEvaluation x).map_comp M.obj N.obj P.obj

end CoefficientModules

section Components

variable {r : Type u} [CommRing r] {A : Type v} [DGCategory r A]

/-- The actual closed cochain component of a native DG natural transformation. -/
def component {F H : EnrichedFunctor (Cochains r) A (Cochains r)}
    (a : DGNatTrans F H) (x : A) : F.obj x ⟶ H.obj x :=
  Cocycle.homOf (Cocycle.mk (a.dgApp x) 1 rfl (by
    have h := a.dgApp_mem_dgCycles x
    rw [mem_dgCycles] at h
    simpa only [dgDifferential_linearHomComplex, zero_add] using! h))

end Components

section SmallTensor

variable {k : Type} [Field k] (X : Stack (Spec (.of k)))

instance smallTensorLeftAdditive (M : ModulePresheaf X) :
    ((curriedTensor (ModulePresheaf X)).obj M).Additive where
  map_add := by
    intro N P f g
    ext1 p
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp

instance smallTensorFunctorAdditive : (curriedTensor (ModulePresheaf X)).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext P
    ext1 p
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp

/- This preservation proof uses Mathlib Presheaf/Monoidal.lean at
56a005855ea17e0b0958f73ec801ae140b0a1679, Copyright (c) 2024
Dagur Asgeirsson, Jack McKoen and Joël Riou, Apache2.0. -/
instance smallTensorLeftPreserves (M : ModulePresheaf X) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) where
  preservesColimitsOfShape := ⟨⟨fun h =>
    ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _
      (fun p => isColimitOfPreserves
        (tensorLeft (show ModuleCat ((rings X).obj p) from M.obj p))
        (isColimitOfPreserves (PresheafOfModules.evaluation _ p) h))⟩⟩⟩

instance smallTensorRightPreserves (M : ModulePresheaf X) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

instance smallTensorComplexStruct : MonoidalCategoryStruct (Complex X) :=
  HomologicalComplex.monoidalCategoryStruct (ModulePresheaf X) (ComplexShape.up ℤ)

instance smallTensorComplexMonoidal : MonoidalCategory (Complex X) :=
  HomologicalComplex.monoidalCategory (ModulePresheaf X) (ComplexShape.up ℤ)

end SmallTensor

variable {k : Type} [Field k] {X Y : Stack (Spec (.of k))}
  {f : StackHom X Y} (C : Context X) (B : CotangentBinding f C)
  (P : SourceBinding f C B)

/-- Realization of the literal native injectiveMap; the target is the canonical cotangent. -/
def injectiveDGMap : letI := C.classicalLinear;
    DGHom (LargeScalar k) 0 (C.realization.obj P.object) C.coherentCotangent.object := by
  letI := C.classicalLinear
  exact cast (congrArg (fun l => DGHom (LargeScalar k) 0 (C.realization.obj P.object) l)
    B.normalized.symm)
    (C.realization.dgMap 0 (show DGHom (LargeScalar k) 0 P.object B.object from
      Cochain.ofHom P.injectiveMap))

theorem injectiveDGMap_heq : letI := C.classicalLinear;
    HEq (injectiveDGMap C B P)
      (C.realization.dgMap 0 (show DGHom (LargeScalar k) 0 P.object B.object from
        Cochain.ofHom P.injectiveMap)) := by
  letI := C.classicalLinear
  unfold injectiveDGMap
  exact cast_heq _ _

theorem coefficientMap_eq_injectiveDGMap : letI := C.classicalLinear;
    P.coefficientMap = injectiveDGMap C B P := by
  letI := C.classicalLinear
  exact eq_of_heq (P.normalized.trans (injectiveDGMap_heq C B P).symm)

theorem injectiveDGMap_closed : letI := C.classicalLinear;
    injectiveDGMap C B P ∈ dgCycles (LargeScalar k)
      (C.realization.obj P.object) C.coherentCotangent.object := by
  letI := C.classicalLinear
  rw [← coefficientMap_eq_injectiveDGMap C B P]
  exact P.closed

/-- Precomposition by the same native global P → L, on the entire coefficient DG category. -/
def nativePrecomposition : letI := C.classicalLinear;
    DGNatTrans (homFunctor (r := LargeScalar k) C.coherentCotangent.object)
      (homFunctor (r := LargeScalar k) (C.realization.obj P.object)) := by
  letI := C.classicalLinear
  exact precompose (injectiveDGMap C B P) (injectiveDGMap_closed C B P)

section Tensor

abbrev coefficientCategoryAt (j : Families C.prestack) :=
  coefficientLarge C.lift C.shuffle ((algebraProjection C.prestack).obj j)

def coefficientUnitAt (j : Families C.prestack) : coefficientCategoryAt C j :=
  coefficientObject C.lift C.shuffle ((algebraProjection C.prestack).obj j)

/-- One enriched cofibrant coefficient realization, with actual source actions. -/
structure CoefficientModules where
  functor : ∀ j : Families C.prestack,
    EnrichedFunctor (Cochains (LargeScalar k)) C.qcoh.category
      (DGDerivedModules (LargeScalar k) (coefficientCategoryAt C j))
  augmentation : ∀ j : Families C.prestack,
    DGNatTrans
      ((functor j).comp (Cochains (LargeScalar k))
        (derivedModuleEvaluation (op (coefficientUnitAt C j))))
      (C.diagram.diagram.obj j).toEnrichedFunctor
  quasi : ∀ (E : C.qcoh.category) (j : Families C.prestack),
    QuasiIso (component (augmentation j) E)
  diagram : Families C.prestack ⥤
    DGFunctor (LargeScalar k) C.qcoh.category (Cochains (LargeScalar k))
  diagramObjects : ∀ j : Families C.prestack,
    (diagram.obj j).toEnrichedFunctor = (functor j).comp (Cochains (LargeScalar k))
      (derivedModuleEvaluation (op (coefficientUnitAt C j)))
  familyAugmentation : diagram ⟶ C.diagram.diagram
  familyComponents : ∀ j : Families C.prestack,
    HEq (familyAugmentation.app j) (augmentation j)
  action : letI := C.category.enrichment;
    ∀ (E : C.qcoh.category) (j : Families C.prestack) (p q n : ℤ) (h : q + p = n)
      (a : (affineCoefficient C.lift C.shuffle ((algebraProjection C.prestack).obj j)).X p)
      (x : (((functor j).obj E).obj.toEnrichedFunctor.obj (op (coefficientUnitAt C j))).X q),
    HEq
      ((component (augmentation j) E).f n
        ((((functor j).obj E).obj.toEnrichedFunctor.dgMap p
          (X := op (coefficientUnitAt C j)) (Y := op (coefficientUnitAt C j)) a :
          Cochain _ _ p).v q n h x))
      (((C.diagram.sections.obj E).toEnrichedFunctor.dgMap p
          (generator C.category (𝟙 j) p a) : Cochain _ _ p).v q n h
        ((eqToHom (C.diagram.value E j)).f q
          ((component (augmentation j) E).f q x)))

variable {C}

def CoefficientModules.value (M : CoefficientModules C) (E : C.qcoh.category)
    (j : Families C.prestack) :
    (M.diagram.obj j).toEnrichedFunctor.obj E ≅
      ((M.functor j).obj E).obj.toEnrichedFunctor.obj (op (coefficientUnitAt C j)) :=
  eqToIso (congrArg (fun F => F.obj E) (M.diagramObjects j))

/-- Family transport is the actual cochain arrow of the ONE coefficient diagram. -/
def CoefficientModules.transport (M : CoefficientModules C) (E : C.qcoh.category)
    {j l : Families C.prestack} (f : j ⟶ l) :
    ((M.functor j).obj E).obj.toEnrichedFunctor.obj (op (coefficientUnitAt C j)) ⟶
      ((M.functor l).obj E).obj.toEnrichedFunctor.obj (op (coefficientUnitAt C l)) :=
  (M.value E j).inv ≫ component (M.diagram.map f) E ≫ (M.value E l).hom

/-- Every nonidentity family generator has its literal transported coefficient action. -/
structure CoefficientFamilyActions (M : CoefficientModules C) : Prop where
  normalized : letI := C.category.enrichment;
    ∀ (E : C.qcoh.category) (j l : Families C.prestack) (f : j ⟶ l)
      (p q n : ℤ) (h : q + p = n)
      (a : (affineCoefficient C.lift C.shuffle ((algebraProjection C.prestack).obj l)).X p)
      (x : (((M.functor j).obj E).obj.toEnrichedFunctor.obj (op (coefficientUnitAt C j))).X q),
    HEq
      ((component (M.augmentation l) E).f n
        ((((M.functor l).obj E).obj.toEnrichedFunctor.dgMap p
          (X := op (coefficientUnitAt C l)) (Y := op (coefficientUnitAt C l)) a :
          Cochain _ _ p).v q n h ((M.transport E f).f q x)))
      (((C.diagram.sections.obj E).toEnrichedFunctor.dgMap p
          (generator C.category f p a) : Cochain _ _ p).v q n h
        ((eqToHom (C.diagram.value E j)).f q
          ((component (M.augmentation j) E).f q x)))

/-- Restrict every object and every DG transformation of an ordinary diagram. -/
def restrictDiagram {J : Type w} [Category.{z} J]
    (T : EnrichedFunctor (Cochains (LargeScalar k)) C.qcoh.category C.qcoh.category)
    (D : J ⥤ DGFunctor (LargeScalar k) C.qcoh.category (Cochains (LargeScalar k))) :
    J ⥤ DGFunctor (LargeScalar k) C.qcoh.category (Cochains (LargeScalar k)) where
  obj j := ⟨T.comp (Cochains (LargeScalar k)) (D.obj j).toEnrichedFunctor⟩
  map f := restrictTransformation T (D.map f)
  map_id j := by
    apply DGNatTrans.ext_dgApp
    intro E
    change (restrictTransformation T (D.map (𝟙 j))).dgApp E =
      (DGNatTrans.id (T.comp (Cochains (LargeScalar k)) (D.obj j).toEnrichedFunctor)).dgApp E
    rw [D.map_id, restrictTransformation_dgApp]
    change (DGNatTrans.id (D.obj j).toEnrichedFunctor).dgApp (T.obj E) = _
    simp only [DGNatTrans.dgApp_id, EnrichedFunctor.comp]
  map_comp f g := by
    apply DGNatTrans.ext_dgApp
    intro E
    change (restrictTransformation T (D.map (f ≫ g))).dgApp E =
      (DGNatTrans.comp (restrictTransformation T (D.map f))
        (restrictTransformation T (D.map g))).dgApp E
    rw [D.map_comp, restrictTransformation_dgApp]
    change (DGNatTrans.comp (D.map f) (D.map g)).dgApp (T.obj E) = _
    simp only [DGNatTrans.dgApp_comp, restrictTransformation_dgApp]

variable (C) {L : LiGlobalDualSourceModels.LargeComplex X}
  (D : LiGlobalDualSourceModels.Duality X P.complex L)

/-- The actual sourced tensor functor. Its local values use the native balanced
coequalizer, all module actions, and all homogeneous coefficient maps. -/
structure SourceTensor where
  source : ClassicalComplex X
  roof : LiGlobalDualSourceModels.TensorComplex X
  toDualSource : roof ⟶ D.sourceModel
  [dualSourceQuasi : QuasiIso toDualSource]
  toSource : roof ⟶ LiGlobalDualSourceModels.raisedTransported X source.complex
  [sourceQuasi : QuasiIso toSource]
  sourceFlat : LiGlobalDualSourceModels.IsTensorFlat X
    (LiGlobalDualSourceModels.raisedTransported X source.cartesian.source)
  coefficients : CoefficientModules C
  nativeTensor : ∀ j : Families C.prestack,
    DerivedTensorModel (coefficientCategoryAt C j) (coefficientUnitAt C j)
  tensor : EnrichedFunctor (Cochains (LargeScalar k)) C.qcoh.category C.qcoh.category
  localTensor : ∀ j : Families C.prestack,
    EnrichedFunctor (Cochains (LargeScalar k)) C.qcoh.category
      (DGDerivedModules (LargeScalar k) (coefficientCategoryAt C j))
  objects : letI := C.classicalLinear;
    ∀ (E : C.qcoh.category) (j : Families C.prestack),
      (localTensor j).obj E = (nativeTensor j).functor.obj
        ((coefficients.functor j).obj (C.realization.obj source), (coefficients.functor j).obj E)
  homogeneous : letI := C.classicalLinear;
    ∀ (E F : C.qcoh.category) (j : Families C.prestack) (n : ℤ)
      (g : DGHom (LargeScalar k) n E F),
    HEq ((localTensor j).dgMap n g)
      ((nativeTensor j).functor.dgMap n
        (dgTensorHom (LargeScalar k)
          (X := ((coefficients.functor j).obj (C.realization.obj source),
            (coefficients.functor j).obj E))
          (Y := ((coefficients.functor j).obj (C.realization.obj source),
            (coefficients.functor j).obj F))
          (dgId (LargeScalar k) ((coefficients.functor j).obj (C.realization.obj source)))
          ((coefficients.functor j).dgMap n g) (zero_add n)))
  diagram : Families C.prestack ⥤
    DGFunctor (LargeScalar k) C.qcoh.category (Cochains (LargeScalar k))
  diagramObjects : ∀ j : Families C.prestack,
    (diagram.obj j).toEnrichedFunctor = (localTensor j).comp (Cochains (LargeScalar k))
      (derivedModuleEvaluation (op (coefficientUnitAt C j)))
  comparison : restrictDiagram tensor C.diagram.diagram ⟶ diagram
  comparisonQuasi : ∀ (E : C.qcoh.category) (j : Families C.prestack),
    QuasiIso (component (comparison.app j) E)

attribute [instance] SourceTensor.dualSourceQuasi SourceTensor.sourceQuasi

variable {C B P D}

/-- The Li assignment is the native coefficient limit of the SAME sourced tensor.
The existing whole-diagram injective replacement precedes this limit. -/
def SourceTensor.functor (T : SourceTensor C B P D) :
    EnrichedFunctor (Cochains (LargeScalar k)) C.qcoh.category (Cochains (LargeScalar k)) :=
  T.tensor.comp (Cochains (LargeScalar k)) C.limits.functor

/-- The actual local tensor value iso, computed from the native balanced module model. -/
def SourceTensor.localValue (T : SourceTensor C B P D) (E : C.qcoh.category)
    (j : Families C.prestack) : letI := C.classicalLinear;
    (T.diagram.obj j).toEnrichedFunctor.obj E ≅
      balancedTensor (coefficientCategoryAt C j) (coefficientUnitAt C j)
        ((T.nativeTensor j).action
          ((T.coefficients.functor j).obj (C.realization.obj T.source)).obj)
        ((T.nativeTensor j).action ((T.coefficients.functor j).obj E).obj) := by
  letI := C.classicalLinear
  exact eqToIso (congrArg (fun F => F.obj E) (T.diagramObjects j)) ≪≫
    eqToIso (congrArg (fun M : DGDerivedModules (LargeScalar k) (coefficientCategoryAt C j) =>
      M.obj.toEnrichedFunctor.obj (op (coefficientUnitAt C j))) (T.objects E j)) ≪≫
    ((T.nativeTensor j).value
      ((T.coefficients.functor j).obj (C.realization.obj T.source))
      ((T.coefficients.functor j).obj E)).comparison

/-- The entire sourced tensor diagram uses the same two actual family transports
on EVERY balanced generator, including every homogeneous source/coefficient degree. -/
structure SourceTensorFamilies (T : SourceTensor C B P D) : Prop where
  coefficientActions : CoefficientFamilyActions T.coefficients
  transport : letI := C.classicalLinear;
    ∀ (E : C.qcoh.category) (j l : Families C.prestack) (f : j ⟶ l)
      (p q n : ℤ) (h : p + q = n)
      (x : (((T.coefficients.functor j).obj (C.realization.obj T.source)).obj.toEnrichedFunctor.obj
        (op (coefficientUnitAt C j))).X p)
      (y : (((T.coefficients.functor j).obj E).obj.toEnrichedFunctor.obj
        (op (coefficientUnitAt C j))).X q),
    ((T.localValue E l).hom.f n)
      ((component (T.diagram.map f) E).f n ((T.localValue E j).inv.f n
        (DerivedCoefficientTensorModels.generator (coefficientCategoryAt C j) (coefficientUnitAt C j)
          ((T.nativeTensor j).action
            ((T.coefficients.functor j).obj (C.realization.obj T.source)).obj)
          ((T.nativeTensor j).action ((T.coefficients.functor j).obj E).obj) h x y))) =
      DerivedCoefficientTensorModels.generator (coefficientCategoryAt C l) (coefficientUnitAt C l)
        ((T.nativeTensor l).action
          ((T.coefficients.functor l).obj (C.realization.obj T.source)).obj)
        ((T.nativeTensor l).action ((T.coefficients.functor l).obj E).obj) h
        ((T.coefficients.transport (C.realization.obj T.source) f).f p x)
        ((T.coefficients.transport E f).f q y)

end Tensor

section Coevaluation

/-- The native whole-presheaf map, transported by the same two implemented functors. -/
def raisedTransportedMap {A H : Complex X} (g : A ⟶ H) :
    LiGlobalDualSourceModels.raisedTransported X A ⟶
      LiGlobalDualSourceModels.raisedTransported X H :=
  ((LiGlobalDualSourceModels.transport X).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift.functor
      (rings X ⋙ forget₂ CommRingCat RingCat)).mapHomologicalComplex (ComplexShape.up ℤ)).map g)

variable {C B P} {L : LiGlobalDualSourceModels.LargeComplex X}
  {D : LiGlobalDualSourceModels.Duality X P.complex L} (T : SourceTensor C B P D)

/-- One whole cochain roof fixes the DG comparison to the SAME native coevaluation.
Both tensor factors use the actual cofibrant Cartesian models, without a global free frame. -/
structure NativeCoevaluation where
  sourceRoof : LiGlobalDualSourceModels.TensorComplex X
  toSourceRoof : sourceRoof ⟶ T.roof
  [sourceRoofQuasi : QuasiIso toSourceRoof]
  toSourceCofibrant : sourceRoof ⟶
    LiGlobalDualSourceModels.raisedTransported X T.source.cartesian.source
  [sourceCofibrantQuasi : QuasiIso toSourceCofibrant]
  source_square : toSourceCofibrant ≫ raisedTransportedMap T.source.cartesian.map =
    toSourceRoof ≫ T.toSource
  dualRoof : LiGlobalDualSourceModels.TensorComplex X
  toDual : dualRoof ⟶ D.dualModel
  [dualQuasi : QuasiIso toDual]
  toPotCofibrant : dualRoof ⟶ LiGlobalDualSourceModels.raisedTransported X P.object.cartesian.source
  [potCofibrantQuasi : QuasiIso toPotCofibrant]
  potFlat : LiGlobalDualSourceModels.IsTensorFlat X
    (LiGlobalDualSourceModels.raisedTransported X P.object.cartesian.source)
  pot_square : toPotCofibrant ≫ raisedTransportedMap P.object.cartesian.map =
    toDual ≫ D.dualResolution ≫ raisedTransportedMap P.resolution
  pair : ClassicalComplex X
  pairResolution : T.source.cartesian.source ⊗ P.object.cartesian.source ⟶ pair.complex
  [pairQuasi : QuasiIso pairResolution]
  pair_normalized : letI := C.classicalLinear;
    C.realization.obj pair = T.tensor.obj (C.realization.obj P.object)
  tensorLift : LiGlobalDualSourceModels.raisedTransported X T.source.cartesian.source ⊗
    LiGlobalDualSourceModels.raisedTransported X P.object.cartesian.source ⟶
      LiGlobalDualSourceModels.raisedTransported X
        (T.source.cartesian.source ⊗ P.object.cartesian.source)
  tensor_pure : ∀ (p : (AffinePoint X)ᵒᵖ) (i j n : ℤ) (h : i + j = n)
    (x : (T.source.cartesian.source.X i).obj p) (y : (P.object.cartesian.source.X j).obj p),
    ((HomologicalComplex.ιTensorObj
      (LiGlobalDualSourceModels.raisedTransported X T.source.cartesian.source)
      (LiGlobalDualSourceModels.raisedTransported X P.object.cartesian.source) i j n h ≫
        tensorLift.f n).app p)
        (ULift.up.{2} x ⊗ₜ[(LiGlobalDualSourceModels.tensorRings X).obj p] ULift.up.{2} y) =
      ULift.up.{2}
        ((HomologicalComplex.ιTensorObj T.source.cartesian.source P.object.cartesian.source
          i j n h).app p (x ⊗ₜ[(rings X).obj p] y))
  unitLift : LiGlobalDualSourceModels.raisedTransported X (unitComplex X) ≅
    𝟙_ (LiGlobalDualSourceModels.TensorComplex X)
  unit_pure : ∀ (p : (AffinePoint X)ᵒᵖ) (r : (rings X).obj p),
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (LiGlobalDualSourceModels.TensorModules X))).hom.app p
      ((unitLift.hom.f 0).app p
        (ULift.up.{2} ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (PresheafOfModules.unit (rings X ⋙ forget₂ CommRingCat RingCat))).inv.app p r))) =
        ULift.up.{2} r
  unitRoof : LiGlobalDualSourceModels.TensorComplex X
  toUnit : unitRoof ⟶ D.unitModel
  [unitQuasi : QuasiIso toUnit]
  toClassicalUnit : unitRoof ⟶ LiGlobalDualSourceModels.raisedTransported X C.classicalUnit.complex
  [classicalUnitQuasi : QuasiIso toClassicalUnit]
  unit_square : toClassicalUnit =
    toUnit ≫ D.unitResolution ≫ unitLift.inv ≫ raisedTransportedMap C.unitResolution
  map : C.classicalUnit.complex ⟶ pair.complex
  lift : unitRoof ⟶ sourceRoof ⊗ dualRoof
  native : lift ≫ ((toSourceRoof ≫ T.toDualSource) ⊗ₘ toDual) = toUnit ≫ D.coevaluation
  classical : lift ≫ (toSourceCofibrant ⊗ₘ toPotCofibrant) ≫ tensorLift ≫
    raisedTransportedMap pairResolution = toClassicalUnit ≫ raisedTransportedMap map

attribute [instance] NativeCoevaluation.sourceRoofQuasi NativeCoevaluation.sourceCofibrantQuasi
  NativeCoevaluation.dualQuasi NativeCoevaluation.potCofibrantQuasi NativeCoevaluation.pairQuasi
  NativeCoevaluation.unitQuasi NativeCoevaluation.classicalUnitQuasi

variable {T} (N : NativeCoevaluation T)

/-- The coefficient coevaluation is the actual realization of that global cochain map. -/
def NativeCoevaluation.dgMap : letI := C.classicalLinear;
    DGHom (LargeScalar k) 0 C.qcoh.unit (T.tensor.obj (C.realization.obj P.object)) := by
  letI := C.classicalLinear
  exact cast (congrArg₂ (fun a b => DGHom (LargeScalar k) 0 a b)
    C.unit_normalized.symm N.pair_normalized)
    (C.realization.dgMap 0 (show DGHom (LargeScalar k) 0 C.classicalUnit N.pair from
      Cochain.ofHom N.map))

/-- The global unit class is computed by the already normalized native limit comparison. -/
def NativeCoevaluation.class : letI := C.classicalLinear;
    (T.functor.obj (C.realization.obj P.object)).X 0 := by
  letI := C.classicalLinear
  exact (C.globalSections.map (T.tensor.obj (C.realization.obj P.object))).f 0 (N.dgMap)

end Coevaluation

section Assignment

variable {C B P} {L : LiGlobalDualSourceModels.LargeComplex X}
  (D : LiGlobalDualSourceModels.Duality X P.complex L)

/-- Construction output of the full source DG assignment and the particular POT morphism. -/
structure Assignment where
  tensor : SourceTensor C B P D
  families : SourceTensorFamilies tensor
  coevaluation : NativeCoevaluation tensor
  li : DGNatTrans (homFunctor (r := LargeScalar k) C.coherentCotangent.object) tensor.functor
  dualComparison : letI := C.classicalLinear;
    DGNatTrans (homFunctor (r := LargeScalar k) (C.realization.obj P.object)) tensor.functor
  dualQuasi : letI := C.classicalLinear; ∀ E : C.qcoh.category,
    QuasiIso (component dualComparison E)
  dual_identity : letI := C.classicalLinear;
    ((dualComparison.dgApp (C.realization.obj P.object) : Cochain _ _ 0).v 0 0 (add_zero 0)).hom
      (dgId (LargeScalar k) (C.realization.obj P.object)) = coevaluation.class
  normalized : letI := C.classicalLinear;
    li = DGNatTrans.comp (nativePrecomposition C B P) dualComparison

variable {D} (A : Assignment (C := C) (B := B) (P := P) D)

/-- The entire dual/source comparison is fixed by the SAME native coevaluation, on all degrees. -/
theorem Assignment.dual_apply : letI := C.classicalLinear;
    ∀ (E : C.qcoh.category) (n : ℤ)
      (g : DGHom (LargeScalar k) n (C.realization.obj P.object) E),
      ((A.dualComparison.dgApp E : Cochain _ _ 0).v n n (add_zero n)).hom g =
        ((A.tensor.functor.dgMap n g : Cochain _ _ n).v 0 n (zero_add n)).hom A.coevaluation.class := by
  letI := C.classicalLinear
  intro E n g
  rw [homTransformation_apply, A.dual_identity]

/-- The actual Li assignment is precomposition by the SAME native global map, on all cochains. -/
theorem Assignment.apply : letI := C.classicalLinear;
    ∀ (E : C.qcoh.category) (n : ℤ)
      (g : DGHom (LargeScalar k) n C.coherentCotangent.object E),
      ((A.li.dgApp E : Cochain _ _ 0).v n n (add_zero n)).hom g =
        ((A.dualComparison.dgApp E : Cochain _ _ 0).v n n (add_zero n)).hom
          (dgComp (C := C.qcoh.category) (LargeScalar k) (injectiveDGMap C B P) g (zero_add n)) := by
  letI := C.classicalLinear
  intro E n g
  rw [A.normalized, DGNatTrans.dgApp_comp, dgCompZero_def, dgComp_linearHomComplex]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact congrArg _ (precompose_apply (A := C.qcoh.category)
    (injectiveDGMap C B P) (injectiveDGMap_closed C B P) E n g)

end Assignment

end MathlibExt.AlgebraicGeometry.LiDGAssignmentModels

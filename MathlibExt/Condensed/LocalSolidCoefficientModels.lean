/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import MathlibExt.Condensed.GeometricTopologicalRestriction
public import MathlibExt.Condensed.PerfectoidSolidCoefficientModels
public import MathlibExt.CategoryTheory.DGScalarNerveMaps
public import MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
public import MathlibExt.AlgebraicGeometry.PerfectoidGeometricBounds
public import Mathlib.Tactic.FunProp

/-!
# Actual local solid almost coefficients and normalized pullbacks

Local coefficients use the actual untilt plus ring, its actual
pseudouniformizer ideal, analytic reflection, adic completion and
completed compact DG dictionary. Almost locality retains the actual
topologically nilpotent ideal and every module-component Hom complex.

Pullback changes coefficients by the actual continuous plus-ring map.
Its compact dictionary map is fixed against native derived geometric
extension, analytic reflection and completion, on objects and all
homogeneous cohomology classes. Its module extension is the full
scalar-changing Hom adjunction against the prescribed raw restriction.
The resulting nerve maps retain every actual coherent simplex.

Source: Anschuetz--Mann, arXiv:2403.01951v2, Theorem 1.1,
Definitions 2.3--2.4 and 4.2. Local affine identification uses the
explicit finite dim.trg qualification, supplied separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.LocalSolidCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarNerveMaps
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.RingTheory.CompleteHuberPairModels
open GeometricScalarRestriction SolidAnalyticModules AdicSolidGenerators
open GeometricDGModules PerfectoidSolidCoefficientModels
open CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]

/-- The actual lifted plus ring of the original untilt. -/
abbrev Coefficient (P : AffineUntilting p) := ULift.{1} P.pair.plus

/-- A real plus-ring pseudouniformizer, with its unit and topological normalization. -/
structure Pseudouniformizer (P : AffineUntilting p) where
  element : P.pair.plus
  unit : IsUnit (element : P.pair.ring)
  nilpotent : IsTopologicallyNilpotent (element : P.pair.ring)

/-- Its actual adic ideal, not an independently selected completion ideal. -/
def adicIdeal {P : AffineUntilting p} (π : Pseudouniformizer p P) : Ideal (Coefficient p P) :=
  Ideal.span {ULift.up π.element}

/-- The actual local modified solid almost data. -/
structure LocalModel (P : AffineUntilting p) where
  parameter : Pseudouniformizer p P
  restriction : RestrictionInput (Coefficient p P) ⊤
  analytic : AnalyticReflection (Coefficient p P) ⊤ restriction
  completion : CompletionModel (Coefficient p P) (adicIdeal p parameter)
  compact : IntegralCompactModel p P.pair restriction analytic (adicIdeal p parameter) completion
  almost : AlmostIdealData p P.pair
  /-- The almost localization of modified modules onto the almost-local ones. -/
  localization : AlmostLocalization (Coefficient p P) compact almost.ideal
  [analyticShift : analytic.functor.CommShift ℤ]
  [analyticUnitShift : NatTrans.CommShift analytic.unit ℤ]
  [completionShift : completion.functor.CommShift ℤ]
  [completionUnitShift : NatTrans.CommShift completion.unit ℤ]

attribute [instance] LocalModel.analyticShift LocalModel.analyticUnitShift
  LocalModel.completionShift LocalModel.completionUnitShift

/-- The actual enhanced modified solid almost coefficient category. -/
abbrev LocalCategory {P : AffineUntilting p} (M : LocalModel p P) :=
  IntegralAlmostModules p P.pair M.restriction M.analytic
    (adicIdeal p M.parameter) M.completion M.compact M.almost

/-- Its coherent nerve uses the retained original DG module actions and Hom complexes. -/
def localNerve {P : AffineUntilting p} (M : LocalModel p P) : SSet.{2} :=
  integerNerve (R := Coefficient p P) (LocalCategory p M)

/-- The actual continuous plus-ring restriction, before analytic or adic reflection. -/
def coefficientMap {P Q : AffineUntilting p} (f : P ⟶ Q) :
    Coefficient p Q →+* Coefficient p P where
  toFun a := ULift.up ⟨f.original.hom a.down, f.original.plus _ a.down.2⟩
  map_zero' := ULift.ext (Subtype.ext (map_zero _))
  map_one' := ULift.ext (Subtype.ext (map_one _))
  map_add' _ _ := ULift.ext (Subtype.ext (map_add _ _ _))
  map_mul' _ _ := ULift.ext (Subtype.ext (map_mul _ _ _))

/-- Continuity is inherited from the original untilt ring map. -/
theorem continuous_coefficientMap {P Q : AffineUntilting p} (f : P ⟶ Q) :
    Continuous (coefficientMap p f) := by
  have h := f.original.continuous
  change Continuous (fun a : Coefficient p Q ↦
    ULift.up (⟨f.original.hom a.down, f.original.plus _ a.down.2⟩ : P.pair.plus))
  fun_prop

/-- Native scalar-extension inputs, including the source-normalized derived shift: the shifted
geometric extension package along the actual plus-ring map. -/
abbrev ExtensionInput {P Q : AffineUntilting p} (f : P ⟶ Q) :=
  GeometricTopologicalRestriction.ShiftedExtensionModel (coefficientMap p f)
    (continuous_coefficientMap p f)

/-- Actual geometric extension, followed by the displayed analytic and adic reflectors. -/
def completedGeometricExtension {P Q : AffineUntilting p} (f : P ⟶ Q)
    (E : ExtensionInput p f) (M : LocalModel p P) :
    GeometricDerived (Coefficient p Q) ⥤ GeometricDerived (Coefficient p P) :=
  letI := E.adjoint
  letI := E.derived
  GeometricTopologicalRestriction.derivedExtension (coefficientMap p f)
    (continuous_coefficientMap p f) ⋙ M.analytic.functor ⋙ M.completion.functor

instance completedGeometricExtension_shift {P Q : AffineUntilting p} (f : P ⟶ Q)
    (E : ExtensionInput p f) (M : LocalModel p P) :
    (completedGeometricExtension p f E M).CommShift ℤ := by
  letI := E.adjoint
  letI := E.derived
  letI := E.shift
  exact inferInstanceAs ((GeometricTopologicalRestriction.derivedExtension
    (coefficientMap p f) (continuous_coefficientMap p f) ⋙
      M.analytic.functor ⋙ M.completion.functor).CommShift ℤ)

/-- The original actual K-injective cochain realizing one compact object. -/
abbrev compactComplex {P : AffineUntilting p} (M : LocalModel p P) (x : M.compact.objects) :=
  (M.compact.realization.obj x).obj

/-- A homogeneous geometric cohomology class uses the native cocycle shift and quotient. -/
def cochainClass {A : Type 1} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {X Y : CochainComplex (GeometricModules A) ℤ} {n : ℤ} (a : Cocycle X Y n) :
    DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj (Y⟦n⟧) :=
  DerivedCategory.Q.map (Cocycle.homOf (a.rightShift n 0 (by omega)))

/-- A shifted object comparison is forced by the native Q and functor shift maps. -/
def shiftedComparison {A B : Type 1} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (G : GeometricDerived A ⥤ GeometricDerived B) [G.CommShift ℤ]
    (X : CochainComplex (GeometricModules A) ℤ)
    (Y : CochainComplex (GeometricModules B) ℤ)
    (e : G.obj (DerivedCategory.Q.obj X) ≅ DerivedCategory.Q.obj Y) (n : ℤ) :
    G.obj (DerivedCategory.Q.obj (X⟦n⟧)) ≅ DerivedCategory.Q.obj (Y⟦n⟧) :=
  G.mapIso ((DerivedCategory.Q.commShiftIso n).app X) ≪≫
    (G.commShiftIso n).app (DerivedCategory.Q.obj X) ≪≫
      (shiftFunctor (GeometricDerived B) n).mapIso e ≪≫
        ((DerivedCategory.Q.commShiftIso n).app Y).symm

/-- A coefficient pullback retains actual compact geometry and the complete module adjunction.
The raw DG-module extension along the strict pullback of dictionaries need not preserve almost-local
modules; the enhanced pullback (`PullbackModel.localExtension`) is the target almost localization
after the raw extension (Mann, proof of Lemma 2.2.22(ii)). -/
structure PullbackModel {P Q : AffineUntilting p} (f : P ⟶ Q)
    (MP : LocalModel p P) (MQ : LocalModel p Q) where
  input : ExtensionInput p f
  compactFunctor : SemilinearFunctor (coefficientMap p f)
    MQ.compact.objectsᵒᵖ MP.compact.objectsᵒᵖ
  restriction : RestrictionModel (coefficientMap p f) compactFunctor
  extension : ExtensionModel (coefficientMap p f) restriction
  geometry : ∀ x : MQ.compact.objects,
    (completedGeometricExtension p f input MP).obj
      (DerivedCategory.Q.obj (compactComplex p MQ x)) ≅
        DerivedCategory.Q.obj (compactComplex p MP (compactFunctor.obj (op x)).unop)
  geometric_classes : ∀ (x y : MQ.compact.objects) (n : ℤ)
    (a : DGHom (Coefficient p Q) n x y) (_ha : dgDifferential (Coefficient p Q) n a = 0)
    (b : Cocycle (compactComplex p MQ x) (compactComplex p MQ y) n)
    (c : Cocycle (compactComplex p MP (compactFunctor.obj (op x)).unop)
      (compactComplex p MP (compactFunctor.obj (op y)).unop) n),
    (b : Cochain _ _ n) = MQ.compact.realization.dgMap n a →
    (c : Cochain _ _ n) = MP.compact.realization.dgMap n
      (((compactFunctor.map (op y) (op x)).f n) a) →
    (completedGeometricExtension p f input MP).map (cochainClass b) ≫
      (shiftedComparison (completedGeometricExtension p f input MP)
        (compactComplex p MQ y) (compactComplex p MP (compactFunctor.obj (op y)).unop)
        (geometry y) n).hom = (geometry x).hom ≫ cochainClass c

/-- The actual local enhanced pullback, on cofibrant almost-local modules and all Hom degrees:
the raw extension followed by the target almost localization. -/
def PullbackModel.localExtension {P Q : AffineUntilting p} {f : P ⟶ Q}
    {MP : LocalModel p P} {MQ : LocalModel p Q} (B : PullbackModel p f MP MQ) :
    SemilinearFunctor (coefficientMap p f) (LocalCategory p MQ) (LocalCategory p MP) where
  obj N := MP.localization.functor.obj (B.extension.functor.obj ⟨N.obj, N.property.1⟩)
  map M N := B.extension.functor.map ⟨M.obj, M.property.1⟩ ⟨N.obj, N.property.1⟩ ≫
    (restrictCochains (coefficientMap p f)).map
      (MP.localization.functor.map (B.extension.functor.obj ⟨M.obj, M.property.1⟩)
        (B.extension.functor.obj ⟨N.obj, N.property.1⟩))
  identity M := by
    have h1 := B.extension.functor.identity ⟨M.obj, M.property.1⟩
    have h2 := MP.localization.functor.dgMap_dgId
      (B.extension.functor.obj ⟨M.obj, M.property.1⟩)
    rw [EnrichedFunctor.dgMap_apply] at h2
    simp only [DGFullSubcategory.dgId_eq] at h1 h2 ⊢
    exact (congrArg (fun z ↦ ((MP.localization.functor.map
      (B.extension.functor.obj ⟨M.obj, M.property.1⟩)
      (B.extension.functor.obj ⟨M.obj, M.property.1⟩)).f 0).hom z) h1).trans h2
  composition M N P i j k a b h := by
    have h1 := B.extension.functor.composition ⟨M.obj, M.property.1⟩
      ⟨N.obj, N.property.1⟩ ⟨P.obj, P.property.1⟩ i j k a b h
    have h2 := MP.localization.functor.dgMap_dgComp
      (((B.extension.functor.map ⟨M.obj, M.property.1⟩ ⟨N.obj, N.property.1⟩).f i).hom a)
      (((B.extension.functor.map ⟨N.obj, N.property.1⟩ ⟨P.obj, P.property.1⟩).f j).hom b) h
    simp only [EnrichedFunctor.dgMap_apply] at h2
    simp only [DGFullSubcategory.dgComp_eq] at h1 h2 ⊢
    exact (congrArg (fun z ↦ ((MP.localization.functor.map
      (B.extension.functor.obj ⟨M.obj, M.property.1⟩)
      (B.extension.functor.obj ⟨P.obj, P.property.1⟩)).f k).hom z) h1).trans h2

/-- Native postcomposition gives the actual local coefficient nerve map. -/
def PullbackModel.nerveMap {P Q : AffineUntilting p} {f : P ⟶ Q}
    {MP : LocalModel p P} {MQ : LocalModel p Q} (B : PullbackModel p f MP MQ) :
    localNerve p MQ ⟶ localNerve p MP := scalarNerveMap (coefficientMap p f) (B.localExtension p)

end MathlibExt.Condensed.LocalSolidCoefficientModels

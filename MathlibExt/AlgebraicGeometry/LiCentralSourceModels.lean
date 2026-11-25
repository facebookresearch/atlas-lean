/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiRelativeSourceModels
public import MathlibExt.AlgebraicGeometry.LiExpandedCentralModels
public import MathlibExt.AlgebraicGeometry.GlobalStackCotangentModels

/-!
# The actual central Li source and original-parameter derivative

The total lifted-map source is restricted to the actual central family.
Its target parameter is the one shared full base-Cech system. The original
curve derivative is the derivative of the literal product of expanded
parameters, normalized by the etale coordinate of the given pointed curve.

The central source is the native homotopy fibre cone(derivative)[-1].
Its whole coefficient diagram receives an actual K-injective replacement
before the right-adjoint Kan assembly. The bundle/POT/virtual construction
uses this central fibre, rather than the unrestricted total source.

Source: Jun Li math/0110113v1, printed pp24--25, (2.3), Proposition2.4
and Theorem2.5; full source definitions (1.15)--(1.25).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiCentralSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry StackAffineModules ExpandedTargetChainGeometry
open ExpandedTargetGluingModels LiExpandedDegenerationModels LiGenericSourceIndex
open LiGenericSourceAssemblyModels
open scoped BigOperators Simplicial
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] {P Q : RelativePair (k := k)} {W0 : SingularTarget P Q}
  (W : OneParameter P Q W0) (S : LiExpandedDegenerationModels.StandardSystem W)
  {n g : ℕ} [LocallyOfFiniteType W0.scheme.hom] [IsNoetherian W0.scheme.left]
  (beta : StableMapNumericalClasses.NumericalClass W0.scheme.left)
  (M : LiExpandedCentralModels.ModuliModel W S n g beta)

def actualFamily (C : SourceChart M.stack) : LiExpandedCentralModels.Family W S n g C.spec :=
  ((M.family C.spec).obj C.point).obj

structure Frame (C : SourceChart M.stack) where
  gauge : LiGenericGaugeSourceModels.Source C
  target : Over.mk C.family.structural ≅ (S.chart gauge.gauge.rank).scheme
  parameter : Over.mk C.family.parameterStructural ≅ base W gauge.gauge.rank
  projection : C.family.projection ≫ parameter.hom.left =
    target.hom.left ≫ (S.chart gauge.gauge.rank).projection.left
  parameterMap : C.spec ⟶ base W gauge.gauge.rank
  parameter_square : C.family.parameter ≫ parameter.hom.left = parameterMap.left
  central : parameterMap ≫ baseToCurve W gauge.gauge.rank = LiExpandedCentralModels.centralBase W C.spec
  identification : (actualFamily W S beta M C).target.scheme ≅
    pullback (S.chart gauge.gauge.rank).projection parameterMap
  identified_projection : identification.hom ≫ pullback.snd
    (S.chart gauge.gauge.rank).projection parameterMap = (actualFamily W S beta M C).target.projection
  identified_contraction : identification.hom ≫ pullback.fst
    (S.chart gauge.gauge.rank).projection parameterMap ≫ (S.chart gauge.gauge.rank).contraction =
      (actualFamily W S beta M C).target.contraction
  relativeTarget : pullback C.family.projection C.family.parameter ≅
    (actualFamily W S beta M C).target.scheme.left
  relative_projection : relativeTarget.hom ≫ (actualFamily W S beta M C).target.projection.left =
    pullback.snd C.family.projection C.family.parameter
  relative_template : relativeTarget.hom ≫ identification.hom.left ≫
    (pullback.fst (S.chart gauge.gauge.rank).projection parameterMap).left =
      pullback.fst C.family.projection C.family.parameter ≫ target.hom.left
  vertex : Fin 1 ≃ Fin C.family.components
  marking : Fin n ≃ Fin (C.family.markings (vertex 0))
  genus : C.family.genus (vertex 0) = g
  curve : (C.family.curve (vertex 0)).X ≅ (actualFamily W S beta M C).curve.X
  curve_projection : curve.hom ≫ (actualFamily W S beta M C).curve.π = (C.family.curve (vertex 0)).π
  curve_marking : ∀ i, (C.family.curve (vertex 0)).marking (marking i) ≫ curve.hom =
    (actualFamily W S beta M C).curve.marking i
  map : C.family.relative (vertex 0) ≫ relativeTarget.hom = curve.hom ≫ (actualFamily W S beta M C).map
  boundary : Fin C.family.boundaryCount ≃ Fin 0
  ordinary_marking : ∀ i, C.family.root (vertex 0) (marking i) = none
  parameterLabels : Fin (gauge.gauge.rank + 1) ≃ Fin C.family.parameterCount
  parameter_normalized : ∀ i, C.family.parameterBaseFunction (parameterLabels i) =
    (parameter.hom ≫ baseToParameters W gauge.gauge.rank).left.appTop.hom
      (parameterSection gauge.gauge.rank i)
  scaling : ScalingData (S.chart gauge.gauge.rank) gauge.gauge.torus
  scaling_normalized : letI := gauge.gauge.torus.group;
    letI := gauge.gauge.action; letI := scaling.standard;
    γ[ExpansionParameterModels.torusScheme k gauge.gauge.rank,Over.mk C.family.structural] ≫ target.hom =
      (ExpansionParameterModels.torusScheme k gauge.gauge.rank ◁ target.hom) ≫
        γ[ExpansionParameterModels.torusScheme k gauge.gauge.rank,(S.chart gauge.gauge.rank).scheme]

abbrev QualifiedFrame (C : SourceChart M.stack) := ULift.{2} (Frame W S beta M C)
def gauge (C : SourceChart M.stack) (h : QualifiedFrame W S beta M C) := h.down.gauge

def actualSourceArrow {C E : SourceChart M.stack}
    (h : Frame W S beta M C) (j : Frame W S beta M E) (f : E.native ⟶ C.native) :
    (E.family.curve (j.vertex 0)).X ⟶ (C.family.curve (h.vertex 0)).X :=
  j.curve.hom ≫ ((M.family E.spec).map f.hom.fiber).hom.source.hom ≫
    (M.reindex f.hom.base C.point).source ≫ h.curve.inv

def actualTargetArrow {C E : SourceChart M.stack}
    (h : Frame W S beta M C) (j : Frame W S beta M E) (f : E.native ⟶ C.native) :
    pullback E.family.projection E.family.parameter ⟶ pullback C.family.projection C.family.parameter :=
  j.relativeTarget.hom ≫ ((M.family E.spec).map f.hom.fiber).hom.target.iso.hom.left ≫
    (M.reindex f.hom.base C.point).target.left ≫ h.relativeTarget.inv

structure ArrowNormalization {C E : SourceChart M.stack}
    (h : Frame W S beta M C) (j : Frame W S beta M E) (f : E.native ⟶ C.native)
    (F : LiGenericSourceRefinementModels.FamilyMap C E f) : Prop where
  vertex : F.vertex = j.vertex.symm.trans h.vertex
  source : HEq (F.source (j.vertex 0)) (actualSourceArrow W S beta M h j f)
  target : F.target = actualTargetArrow W S beta M h j f

def parameterValue {C : SourceChart M.stack} (h : Frame W S beta M C)
    (i : Fin (h.gauge.gauge.rank + 1)) : C.ring :=
  (Scheme.ΓSpecIso (.of C.ring)).hom.hom
    ((h.parameterMap ≫ baseToParameters W h.gauge.gauge.rank).left.appTop.hom
      (parameterSection h.gauge.gauge.rank i))

def originalDerivativeValue {C : SourceChart M.stack} (h : Frame W S beta M C)
    (x : (C.source.data (LiGenericGaugeSourceModels.coefficient C)).logCochains.obj ⦋0⦌) : C.ring :=
  ∑ i : Fin (h.gauge.gauge.rank + 1),
    (∏ j ∈ Finset.univ.erase i, parameterValue W S beta M h j) *
      C.source.globalParameter (LiGenericGaugeSourceModels.coefficient C) x (h.parameterLabels i)

def pointBaseComplex (C : SourceChart M.stack) :=
  (CochainComplex.singleFunctor (ModuleCat.{0} C.ring) 1).obj (ModuleCat.of C.ring C.ring)

structure ChartDerivative (C : SourceChart M.stack) (h : Frame W S beta M C) where
  raw : LiGenericGaugeSourceModels.rawComplex C ⟶ pointBaseComplex W S beta M C
  normalized : ∀ x, (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
    (ModuleCat.of C.ring C.ring)).hom (raw.f 1 x) =
      originalDerivativeValue W S beta M h (((C.source.termIso (LiGenericGaugeSourceModels.coefficient C) 1).hom x).2)
  gauge : h.gauge.map ≫ raw = 0
  quotient : LiGenericGaugeSourceModels.quotientComplex C h.gauge ⟶ pointBaseComplex W S beta M C
  cone : CochainComplex.mappingCone.inr h.gauge.map ≫ quotient = raw

def baseComplex : SmallParentComplex M.stack :=
  (CochainComplex.singleFunctor (ModulePresheaf M.stack) 1).obj
    (PresheafOfModules.unit (rings M.stack ⋙ forget₂ CommRingCat RingCat))

def pointEvaluation (C : SourceChart M.stack) : ModulePresheaf M.stack ⥤ ModuleCat.{0} C.ring :=
  PresheafOfModules.evaluation (rings M.stack ⋙ forget₂ CommRingCat RingCat) (op C.native) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of C.ring)).inv.hom

instance (C : SourceChart M.stack) : (pointEvaluation W S beta M C).Additive where
  map_add := by intros; rfl

def evaluate (L : SmallParentComplex M.stack) (C : SourceChart M.stack) :
    CochainComplex (ModuleCat.{0} C.ring) ℤ :=
  ((pointEvaluation W S beta M C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

def evaluateMap {L N : SmallParentComplex M.stack} (u : L ⟶ N) (C : SourceChart M.stack) :=
  ((pointEvaluation W S beta M C).mapHomologicalComplex (ComplexShape.up ℤ)).map u

def baseDegreeIso (C : SourceChart M.stack) :=
  (pointEvaluation W S beta M C).mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
    (PresheafOfModules.unit (rings M.stack ⋙ forget₂ CommRingCat RingCat)))

structure BaseFrame (C : SourceChart M.stack) where
  comparison : evaluate W S beta M (baseComplex W S beta M) C ≅ pointBaseComplex W S beta M C
  pure : ∀ r : C.ring, (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
    (ModuleCat.of C.ring C.ring)).hom (comparison.hom.f 1
      ((baseDegreeIso W S beta M C).inv ((Scheme.ΓSpecIso (.of C.ring)).inv.hom r))) = r

/-- One global original-base derivative; every chart reads its actual shared parameter. -/
structure Derivative
    (A : LiGenericSourceAssemblyModels.Assembly M.stack (QualifiedFrame W S beta M) (gauge W S beta M)) where
  map : A.native.global ⟶ baseComplex W S beta M
  chart : ∀ C (h : QualifiedFrame W S beta M C), ChartDerivative W S beta M C h.down
  frame : ∀ C, BaseFrame W S beta M C
  coefficientSquare : ∀ C (h : QualifiedFrame W S beta M C),
    (evaluateMap W S beta M map C) ≫ (frame C).comparison.hom =
      (((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of C.ring)).inv.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((PresheafOfModules.evaluation
            ((includeLift M.stack (QualifiedFrame W S beta M)).op ⋙ coefficientRings M.stack (QualifiedFrame W S beta M))
            (op (show LiftIndex M.stack (QualifiedFrame W S beta M) from .chart C h))).mapHomologicalComplex
              (ComplexShape.up ℤ)).map A.native.localMap)) ≫
        A.native.comparison C h ≫ (chart C h).quotient

def centralComplex
    {A : LiGenericSourceAssemblyModels.Assembly M.stack (QualifiedFrame W S beta M) (gauge W S beta M)}
    (B : Derivative W S beta M A) : SmallParentComplex M.stack :=
  (CochainComplex.mappingCone B.map)⟦(-1 : ℤ)⟧

def localCentral
    {A : LiGenericSourceAssemblyModels.Assembly M.stack (QualifiedFrame W S beta M) (gauge W S beta M)}
    (B : Derivative W S beta M A) : SmallLiftComplex M.stack (QualifiedFrame W S beta M) :=
  ((smallFromParents M.stack (QualifiedFrame W S beta M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (centralComplex W S beta M B)

def centralAssemblyMap
    {A : LiGenericSourceAssemblyModels.Assembly M.stack (QualifiedFrame W S beta M) (gauge W S beta M)}
    (B : Derivative W S beta M A) (K : RightKan M.stack (QualifiedFrame W S beta M))
    (I : LiftComplex M.stack (QualifiedFrame W S beta M))
    (q : raiseLocal M.stack (QualifiedFrame W S beta M) (localCentral W S beta M B) ⟶ I) :=
  RightKan.unit M.stack (QualifiedFrame W S beta M) K
    (spreadComplex M.stack (QualifiedFrame W S beta M) (raiseParent M.stack (centralComplex W S beta M B))) ≫
      K.complex.map q

structure Source where
  total : LiGenericSourceAssemblyModels.Assembly M.stack (QualifiedFrame W S beta M) (gauge W S beta M)
  left : ∀ (C E : SourceChart M.stack) (h : QualifiedFrame W S beta M C)
    (j : QualifiedFrame W S beta M E) (f : E.native ⟶ C.native),
    ArrowNormalization W S beta M h.down
      (total.native.refinement C E h j f).qualification.down
      (total.native.refinement C E h j f).left (total.native.leftSource C E h j f).family
  right : ∀ (C E : SourceChart M.stack) (h : QualifiedFrame W S beta M C)
    (j : QualifiedFrame W S beta M E) (f : E.native ⟶ C.native),
    ArrowNormalization W S beta M j.down
      (total.native.refinement C E h j f).qualification.down
      (total.native.refinement C E h j f).right (total.native.rightSource C E h j f).family
  derivative : Derivative W S beta M total
  kan : RightKan M.stack (QualifiedFrame W S beta M)
  replacement : LiftComplex M.stack (QualifiedFrame W S beta M)
  resolution : raiseLocal M.stack (QualifiedFrame W S beta M) (localCentral W S beta M derivative) ⟶ replacement
  [quasi : QuasiIso resolution]
  [injective : replacement.IsKInjective]
  [assembled : QuasiIso (centralAssemblyMap W S beta M derivative kan replacement resolution)]
  parentModel : ParentComplex M.stack
  normalization : raiseParent M.stack (centralComplex W S beta M derivative) ⟶ parentModel
  [normalized : QuasiIso normalization]
  toKan : parentModel ⟶ parentComplex M.stack (QualifiedFrame W S beta M) kan replacement
  [kanQuasi : QuasiIso toKan]
  square : normalization ≫ toKan =
    ((parentRestriction M.stack (QualifiedFrame W S beta M)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (centralAssemblyMap W S beta M derivative kan replacement resolution)
  cofibrant : ∀ p, IsCofibrant (evaluateParent M.stack parentModel p)
  baseChange : ∀ {p q : AffinePoint M.stack} (f : p ⟶ q), BaseChange M.stack parentModel f
attribute [instance] Source.quasi Source.injective Source.assembled Source.normalized Source.kanQuasi

end MathlibExt.AlgebraicGeometry.LiCentralSourceModels

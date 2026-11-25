/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiDGAssignmentModels
public import MathlibExt.AlgebraicGeometry.LiNonsplitSourceModels
import all MathlibExt.AlgebraicGeometry.LiGenericSourceAssemblyModels

/-!
# Li assignment normalization on all affine tests and shifted coefficients

The local DG functor is the actual native source tensor with an arbitrary
cochain coefficient. Its homogeneous action is fixed on every pure total
tensor, with the native Koszul sign. The full global assignment is read
on these source charts through actual cochain maps, on all Hom degrees.

Canonical local classes are computed from the SAME global cotangent
normalization, through actual polynomial-resolution maps. Ordinary
classes retain every actual lifted polynomial function; nonsplit classes
retain every pure lifted-face difference. Their source values are the
computed native curve/lift/Cech/gauge cocycles. Comparison uses actual
cochain homotopies when choices change. It does not replace the whole DG
transformation equality by an H0 or obstruction-sheaf comparison.

Source: Jun Li math/0110113v1, (1.15)--(1.25), Proposition1.18,
Theorems2.3/2.5 and Proposition2.4. Cotangent polynomial maps and extension
classes are native AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b
(Apache2.0), especially 08QI,08RB and08SP. Native DG source notices remain
in their original completed source ports.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiSourceDGNormalizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackAffineModules StackBundleCones
open MathlibExt.DGSource MathlibExt.CategoryTheory.DGModelContracts
open DerivedQCohEnhancementModels LiGlobalCoefficientModels LiDGAssignmentModels
open LiGenericSourceIndex LiGenericSourceAssemblyModels GeometricCotangentComplex
open CochainComplex.HomComplex
open scoped Simplicial TensorProduct

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm LiMarkedCurveExtensions.oppositeTower

variable {k : Type} [Field k] {X Y : Stack (Spec (.of k))}

def pointEvaluation (S : SourceChart X) : ModulePresheaf X ⥤ ModuleCat.{0} S.ring :=
  PresheafOfModules.evaluation (rings X ⋙ forget₂ CommRingCat RingCat) (op S.native) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of S.ring)).inv.hom

instance pointEvaluationAdditive (S : SourceChart X) : (pointEvaluation S).Additive where
  map_add := by intros; rfl

def evaluatePoint (M : LiGlobalCoefficientModels.Complex X) (S : SourceChart X) :
    Cochains S.ring := ((pointEvaluation S).mapHomologicalComplex (ComplexShape.up ℤ)).obj M

def evaluateCochain {M N : LiGlobalCoefficientModels.Complex X} {n : ℤ}
    (g : Cochain M N n) (S : SourceChart X) : Cochain (evaluatePoint M S) (evaluatePoint N S) n :=
  Cochain.mk fun i j h => (pointEvaluation S).map (g.v i j h)

def largeLocalModules (S : SourceChart X) : ModuleCat.{0} S.ring ⥤ ModuleCat.{1} (LargeScalar k) :=
  ModuleCat.restrictScalars (algebraMap k S.ring) ⋙ DerivedClosedFormComplexes.liftModules k ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : LargeScalar k ≃+* k).toRingHom

instance largeLocalModulesAdditive (S : SourceChart X) : (largeLocalModules S).Additive where
  map_add := by intros; rfl

def largeLocal (S : SourceChart X) : Cochains S.ring ⥤ Cochains (LargeScalar k) :=
  (largeLocalModules S).mapHomologicalComplex (ComplexShape.up ℤ)

def largeLocalCochain {S : SourceChart X} {M N : Cochains S.ring} {n : ℤ}
    (g : Cochain M N n) : Cochain ((largeLocal S).obj M) ((largeLocal S).obj N) n :=
  Cochain.mk fun i j h => (largeLocalModules S).map (g.v i j h)

/-- The native chart comparison is computed from the actual global-to-local source map. -/
def nativeChartMap {Frame : SourceChart X → Type 2}
    {gauge : ∀ S : SourceChart X, Frame S → LiGenericGaugeSourceModels.Source S}
    (N : NativeSource X Frame gauge) (S : SourceChart X) (h : Frame S) :
    evaluatePoint N.global S ⟶ chartComplex X Frame gauge S h :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of S.ring)).inv.hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (((PresheafOfModules.evaluation
      ((includeLift X Frame).op ⋙ coefficientRings X Frame)
      (op (show LiftIndex X Frame from .chart S h))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map N.localMap) ≫ N.comparison S h

def unitCoefficient (S : SourceChart X) (I : ModuleCat.{0} S.ring) (m : ℤ) : Cochains S.ring :=
  (CochainComplex.singleFunctor (ModuleCat.{0} S.ring) m).obj I

def unitGenerator (S : SourceChart X) : (𝟙_ (Cochains S.ring)).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{0} S.ring))).inv 1

/-- A closed cotangent cochain has its actual native point in the Hom complex. -/
def classPoint {a : Type} [CommRing a] {M : Cochains a}
    {F : EnrichedFunctor (Cochains a) (Cochains a) (Cochains a)}
    (A : DGNatTrans (homFunctor (r := a) M) F) {J : Cochains a} (g : M ⟶ J) :
    𝟙_ (Cochains a) ⟶ F.obj J := linearHomComplexOfHom a g ≫ component A J

variable (N : LiGlobalCoefficientModels.Complex X) (S : SourceChart X)

def pointSource : Cochains S.ring := (evaluatePoint N S)⟦(1 : ℤ)⟧

/-- The coefficient assignment is the literal native tensor, on all homogeneous maps. -/
structure LocalSourceFunctor where
  functor : EnrichedFunctor (Cochains S.ring) (Cochains S.ring) (Cochains S.ring)
  objects : ∀ J : Cochains S.ring, functor.obj J = pointSource N S ⊗ J
  flat : ∀ (J H : Cochains S.ring) (u : J ⟶ H), QuasiIso u → QuasiIso (pointSource N S ◁ u)
  homogeneous : ∀ (J H : Cochains S.ring) (r i j n : ℤ) (h : i + j = n)
    (g : DGHom S.ring r J H) (x : (pointSource N S).X i) (y : J.X j),
    (eqToHom (objects H)).f (n + r)
      ((functor.dgMap r g : Cochain _ _ r).v n (n + r) rfl
        ((eqToHom (objects J).symm).f n
          (HomologicalComplex.ιTensorObj (pointSource N S) J i j n h (x ⊗ₜ[S.ring] y)))) =
      (r * i).negOnePow •
        (HomologicalComplex.ιTensorObj (pointSource N S) H i (j + r) (n + r) (by omega)
          (x ⊗ₜ[S.ring] ((g : Cochain J H r).v j (j + r) rfl y)))

variable {N S}

/-- Reading the source uses the actual native chart cochain map, tensoring that same map. -/
def LocalSourceFunctor.read (F : LocalSourceFunctor N S)
    {G : LiGenericGaugeSourceModels.Source S}
    (u : evaluatePoint N S ⟶ LiGenericGaugeSourceModels.quotientComplex S G) (J : Cochains S.ring) :
    F.functor.obj J ⟶ (LiGenericGaugeSourceModels.quotientComplex S G)⟦(1 : ℤ)⟧ ⊗ J :=
  eqToHom (F.objects J) ≫ u⟦(1 : ℤ)⟧' ▷ J

def liePointMap (S : SourceChart X) (G : LiGenericGaugeSourceModels.Source S)
    (I : ModuleCat.{0} S.ring) (y : I) :
    LiGenericGaugeSourceModels.lieComplex S G.gauge ⟶
      LiGenericGaugeSourceModels.lieCoefficient S G.gauge I :=
  (CochainComplex.singleFunctor (ModuleCat.{0} S.ring) 1).map
    (ModuleCat.ofHom
      { toFun := fun x i => x i • y
        map_add' := by intro x z; funext i; exact add_smul (x i) (z i) y
        map_smul' := by intro a x; funext i; exact mul_smul a (x i) y })

variable (S : SourceChart X) (G : LiGenericGaugeSourceModels.Source S)

abbrev rawUnit := LiGenericGaugeSourceModels.quotientComplex S G
abbrev rawCoefficient (I : ModuleCat.{0} S.ring) :=
  LiGenericGaugeSourceModels.quotientCoefficientComplex S G I

/-- The raw tensor coefficient bridge is fixed on every cone block and every total tensor. -/
structure RawCoefficients where
  point : ∀ (I : ModuleCat.{0} S.ring) (y : I), rawUnit S G ⟶ rawCoefficient S G I
  source : ∀ (I : ModuleCat.{0} S.ring) (y : I) (j : ℤ) (x : (rawUnit S G).X j),
    (CochainComplex.mappingCone.snd (G.coefficientMap I)).v j j (add_zero j)
      ((point I y).f j x) =
      (S.coefficients.map (LiGenericGaugeSourceModels.coefficientPoint S I y)).f j
        ((CochainComplex.mappingCone.snd G.map).v j j (add_zero j) x)
  lie : ∀ (I : ModuleCat.{0} S.ring) (y : I) (j : ℤ) (x : (rawUnit S G).X j),
    (CochainComplex.mappingCone.fst (G.coefficientMap I)).val.v j (j + 1) rfl
      ((point I y).f j x) =
      (liePointMap S G I y).f (j + 1)
        ((CochainComplex.mappingCone.fst G.map).val.v j (j + 1) rfl x)
  comparison : ∀ (I : ModuleCat.{0} S.ring) (m : ℤ),
    (rawUnit S G)⟦(1 : ℤ)⟧ ⊗ unitCoefficient S I m ≅ (rawCoefficient S G I)⟦(1 - m : ℤ)⟧
  pure : ∀ (I : ModuleCat.{0} S.ring) (m r : ℤ) (x : ((rawUnit S G)⟦(1 : ℤ)⟧).X r) (y : I),
    ((rawCoefficient S G I).shiftFunctorObjXIso (1 - m) (r + m) (r + 1) (by omega)).hom
      ((comparison I m).hom.f (r + m)
        (HomologicalComplex.ιTensorObj ((rawUnit S G)⟦(1 : ℤ)⟧) (unitCoefficient S I m) r m (r + m) rfl
          (x ⊗ₜ[S.ring]
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m I).inv y))) =
      (m * r).negOnePow • (point I y).f (r + 1)
        (((rawUnit S G).shiftFunctorObjXIso 1 r (r + 1) rfl).hom x)

def rawDeformationValue (I : ModuleCat.{0} S.ring) (E : LiGenericSourceModels.MapExtension S.family I) :
    (rawCoefficient S G I).X 1 :=
  (CochainComplex.mappingCone.inr (G.coefficientMap I)).f 1
    ((S.source.termIso I 1).inv (((S.deformations.functor I).obj E).value.val))

section Polynomial

variable {S G} {f : StackHom X Y} (C : Context X) (B : CotangentBinding f C)

def chartBaseScalar (c : IntrinsicConeChart f) : k →+* GlobalStackCotangentModels.baseRing c :=
  c.geometry.target.U.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

instance chartBaseAlgebra (c : IntrinsicConeChart f) :
    Algebra k (GlobalStackCotangentModels.baseRing c) := (chartBaseScalar c).toAlgebra

def pointRingMap (S : SourceChart X) (c : IntrinsicConeChart f)
    (u : S.native ⟶ GlobalStackCotangentModels.chartPoint c) :
    GlobalStackCotangentModels.sourceRing c →+* S.ring :=
  (Scheme.ΓSpecIso (.of S.ring)).hom.hom.comp u.hom.base.left.appTop.hom

/-- The point derivative is fixed on every native polynomial cochain, through the
actual stack arrow and SAME global cotangent resolution. There is no arbitrary local L. -/
structure PolynomialTest (S : SourceChart X) where
  chart : IntrinsicConeChart f
  arrow : S.native ⟶ GlobalStackCotangentModels.chartPoint chart
  [algebra : Algebra (GlobalStackCotangentModels.baseRing chart) S.ring]
  algebra_normalized : ∀ a : GlobalStackCotangentModels.baseRing chart,
    algebraMap (GlobalStackCotangentModels.baseRing chart) S.ring a =
      pointRingMap S chart arrow (algebraMap (GlobalStackCotangentModels.baseRing chart)
        (GlobalStackCotangentModels.sourceRing chart) a)
  k_normalized : ∀ a : k,
    algebraMap (GlobalStackCotangentModels.baseRing chart) S.ring
      (algebraMap k (GlobalStackCotangentModels.baseRing chart) a) = algebraMap k S.ring a
  resolution : PolynomialResolution (GlobalStackCotangentModels.baseRing chart) S.ring
  model : GlobalStackCotangentModels.ResolutionMap
    (RingHom.id (GlobalStackCotangentModels.baseRing chart)) (pointRingMap S chart arrow)
    (B.native.resolution chart) resolution
  comparison : affineComplex (B.native.resolution chart) ⟶
    ((ModuleCat.restrictScalars (pointRingMap S chart arrow)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (evaluatePoint B.object.complex S)
  comparison_pure : ∀ (n : ℤ) (x : (affineComplex (B.native.resolution chart)).X n),
    HEq (comparison.f n x)
      ((B.map.f n).app (op S.native)
        ((B.native.complex.X n).map arrow.op ((B.native.comparison chart).f n x)))
  derivative : evaluatePoint B.object.complex S ⟶ affineComplex resolution
  square : comparison ≫
    ((ModuleCat.restrictScalars (pointRingMap S chart arrow)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map derivative = model.map

attribute [instance] PolynomialTest.algebra

variable {C B} (T : PolynomialTest C B S)

/-- Forgetting the actual target-atlas algebra does not split the extension or change its kernel. -/
def PolynomialTest.extension
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) S.ring) :
    AffineSquareZeroCotangentClasses.Extension k S.ring := by
  letI : Algebra k E.ring := ((algebraMap (GlobalStackCotangentModels.baseRing T.chart) E.ring).comp
    (algebraMap k (GlobalStackCotangentModels.baseRing T.chart))).toAlgebra
  exact
    { ring := E.ring
      commRing := E.commRing
      algebra := inferInstance
      projection :=
        { toRingHom := E.projection.toRingHom
          commutes' a := by
            change E.projection
              (algebraMap (GlobalStackCotangentModels.baseRing T.chart) E.ring
                (algebraMap k (GlobalStackCotangentModels.baseRing T.chart) a)) = algebraMap k S.ring a
            rw [E.projection.commutes]
            exact T.k_normalized a }
      surjective := E.surjective
      squareZero := E.squareZero
      coefficient := E.coefficient
      kernel := E.kernel
      action := E.action }

/-- The actual canonical nonsplit class is the native pure-face cochain composed with that derivative. -/
def PolynomialTest.class
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) S.ring)
    {L : AffineSquareZeroCotangentClasses.PolynomialLift T.resolution E}
    (N : AffineSquareZeroCotangentClasses.NormalizedCochain T.resolution E L) :
    evaluatePoint B.object.complex S ⟶ AffineSquareZeroCotangentClasses.coefficientComplex E :=
  T.derivative ≫ N.map

def squareAlgebra (I : ModuleCat.{0} S.ring) :
    Algebra (GlobalStackCotangentModels.baseRing T.chart) (TrivSqZeroExt S.ring I) :=
  ((TrivSqZeroExt.inlHom S.ring I).comp
    (algebraMap (GlobalStackCotangentModels.baseRing T.chart) S.ring)).toAlgebra

/-- An actual first-order affine motion, with its specified target-atlas algebra fixed. -/
structure FirstOrderMap (I : ModuleCat.{0} S.ring) where
  lift : letI := squareAlgebra T I;
    S.ring →ₐ[GlobalStackCotangentModels.baseRing T.chart] TrivSqZeroExt S.ring I
  reduction : ∀ x : S.ring, (lift x).fst = x

/-- Every pure degree-zero polynomial differential has its actual lifted function derivative. -/
structure DerivationCochain {I : ModuleCat.{0} S.ring} (D : FirstOrderMap T I) where
  map : affineComplex T.resolution ⟶ unitCoefficient S I 0
  pure : ∀ x : T.resolution.algebra.obj (op ⦋0⦌),
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).hom
      (map.f 0 ((affineDegreeIso T.resolution 0).inv
        (CommAlgCat.resolutionCotangentTermDifferential (GlobalStackCotangentModels.baseRing T.chart)
          (CommAlgCat.of (GlobalStackCotangentModels.baseRing T.chart) S.ring)
          T.resolution.algebra T.resolution.augmentation (op ⦋0⦌) x))) =
        (D.lift (T.resolution.augmentation.app (op ⦋0⦌) x)).snd

def firstOrderBase {I : ModuleCat.{0} S.ring} (D : FirstOrderMap T I) :
    Spec (.of (TrivSqZeroExt S.ring I)) ⟶ Spec (.of S.ring) := by
  letI := squareAlgebra T I
  exact Spec.map (CommRingCat.ofHom D.lift.toRingHom)

/-- The lifted family is the literal pullback along that affine motion, with all source maps. -/
structure FirstOrderGeometry {I : ModuleCat.{0} S.ring} (D : FirstOrderMap T I)
    (E : LiGenericSourceModels.MapExtension S.family I) where
  curve : ∀ v, (E.curve.component v).curve.X ≅ pullback (S.family.curve v).π (firstOrderBase T D)
  curve_projection : ∀ v, (curve v).hom ≫ pullback.snd (S.family.curve v).π (firstOrderBase T D) =
    (E.curve.component v).curve.π
  curve_reduction : ∀ v, (E.curve.component v).reduction ≫ (curve v).hom ≫
    pullback.fst (S.family.curve v).π (firstOrderBase T D) = 𝟙 _
  curve_marking : ∀ v i, (E.curve.component v).curve.marking i ≫ (curve v).hom ≫
    pullback.fst (S.family.curve v).π (firstOrderBase T D) = firstOrderBase T D ≫ (S.family.curve v).marking i
  parameter : E.parameter.map = firstOrderBase T D ≫ S.family.parameter
  map : ∀ v, E.map v = (curve v).hom ≫ pullback.fst (S.family.curve v).π (firstOrderBase T D) ≫ S.family.map v

end Polynomial

section Normalization

variable {f : StackHom X Y} {C : Context X} {B : CotangentBinding f C}
  {P : SourceBinding f C B} {L : LiGlobalDualSourceModels.LargeComplex X}
  {D : LiGlobalDualSourceModels.Duality X P.complex L}
  (A : LiDGAssignmentModels.Assignment (C := C) (B := B) (P := P) D)
  (N : LiGlobalCoefficientModels.Complex X) (S : SourceChart X)
  (G : LiGenericGaugeSourceModels.Source S)
  (u : evaluatePoint N S ⟶ rawUnit S G)

/-- Both ordinary and nonsplit classes use actual source-produced cocycles.
The quantifier over ALL nonsplit lift systems includes the universal curve,
its d-dual trivialization, and every change of local lifts or cover. -/
structure LocalNormalization where
  localSource : LocalSourceFunctor N S
  li : DGNatTrans (homFunctor (r := S.ring) (evaluatePoint B.object.complex S)) localSource.functor
  coefficients : RawCoefficients S G
  ordinary : ∀ (T : PolynomialTest C B S) (I : ModuleCat.{0} S.ring) (d : FirstOrderMap T I),
    DerivationCochain T d
  extension : ∀ (T : PolynomialTest C B S) (I : ModuleCat.{0} S.ring) (d : FirstOrderMap T I),
    LiGenericSourceModels.MapExtension S.family I
  extensionGeometry : ∀ T I d, FirstOrderGeometry T d (extension T I d)
  ordinaryPoint : ∀ (T : PolynomialTest C B S) (I : ModuleCat.{0} S.ring) (d : FirstOrderMap T I),
    𝟙_ (Cochains S.ring) ⟶ (rawCoefficient S G I)⟦(1 : ℤ)⟧
  ordinary_value : ∀ T I d,
    ((rawCoefficient S G I).shiftFunctorObjXIso 1 0 1 rfl).hom
      ((ordinaryPoint T I d).f 0 (unitGenerator S)) = rawDeformationValue S G I (extension T I d)
  ordinary_homotopy : ∀ T I d,
    Homotopy
      (classPoint li (T.derivative ≫ (ordinary T I d).map) ≫
        localSource.read u (unitCoefficient S I 0) ≫ (coefficients.comparison I 0).hom)
      (ordinaryPoint T I d)
  nonsplit_system : ∀ (T : PolynomialTest C B S)
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) S.ring),
    LiNonsplitSourceModels.System S (T.extension E)
  nonsplitPoint : ∀ (T : PolynomialTest C B S)
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) S.ring)
    (Q : LiNonsplitSourceModels.System S (T.extension E)),
    𝟙_ (Cochains S.ring) ⟶ localSource.functor.obj (unitCoefficient S E.coefficient (-1))
  nonsplit_homotopy : ∀ (T : PolynomialTest C B S)
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) S.ring)
    (V : AffineSquareZeroCotangentClasses.PolynomialLift T.resolution E)
    (K : AffineSquareZeroCotangentClasses.NormalizedCochain T.resolution E V)
    (Q : LiNonsplitSourceModels.System S (T.extension E)),
    Homotopy (classPoint li (T.class E K)) (nonsplitPoint T E Q)
  nonsplitRawPoint : ∀ (T : PolynomialTest C B S)
    (E : AffineSquareZeroCotangentClasses.Extension (GlobalStackCotangentModels.baseRing T.chart) S.ring)
    (Q : LiNonsplitSourceModels.System S (T.extension E)),
    𝟙_ (Cochains S.ring) ⟶ (rawCoefficient S G E.coefficient)⟦(2 : ℤ)⟧
  nonsplit_raw : ∀ T E Q,
    nonsplitPoint T E Q ≫ localSource.read u (unitCoefficient S E.coefficient (-1)) ≫
      (coefficients.comparison E.coefficient (-1)).hom = nonsplitRawPoint T E Q
  nonsplit_value : ∀ T E Q,
    ((rawCoefficient S G E.coefficient).shiftFunctorObjXIso 2 0 2 rfl).hom
      ((nonsplitRawPoint T E Q).f 0 (unitGenerator S)) = Q.quotientCocycle S (T.extension E) G
  globalEvaluation : letI := C.classicalLinear;
    ∀ J : ClassicalComplex X,
      A.tensor.functor.obj (C.realization.obj J) ⟶
        (largeLocal S).obj (localSource.functor.obj (evaluatePoint J.complex S))
  homogeneous : letI := C.classicalLinear;
    ∀ (J H : ClassicalComplex X) (n i : ℤ) (g : Cochain J.complex H.complex n)
      (x : (A.tensor.functor.obj (C.realization.obj J)).X i),
    (globalEvaluation H).f (i + n)
      ((A.tensor.functor.dgMap n (show DGHom (LargeScalar k) n (C.realization.obj J) (C.realization.obj H)
        from C.realization.dgMap n (show DGHom (LargeScalar k) n J H from g)) : Cochain _ _ n).v i (i + n) rfl x) =
      (largeLocalCochain (S := S)
        (localSource.functor.dgMap n (show DGHom S.ring n (evaluatePoint J.complex S) (evaluatePoint H.complex S)
          from evaluateCochain g S))).v i (i + n) rfl ((globalEvaluation J).f i x)

variable {N S G u}

/-- The same global canonical cotangent is read on every source point; this is the actual DG image. -/
def realizedCotangent (J : ClassicalComplex X) (n : ℤ) (g : Cochain B.object.complex J.complex n) :
    letI := C.classicalLinear;
    DGHom (LargeScalar k) n C.coherentCotangent.object (C.realization.obj J) := by
  letI := C.classicalLinear
  exact cast (congrArg (fun a => DGHom (LargeScalar k) n a (C.realization.obj J)) B.normalized.symm)
    (C.realization.dgMap n (show DGHom (LargeScalar k) n B.object J from g))

/-- Equality is on EVERY cochain degree and arbitrary complex coefficient, before passing to homology. -/
structure GlobalLocalSquare (Q : LocalNormalization A N S G u) : Prop where
  square : letI := C.classicalLinear;
    ∀ (J : ClassicalComplex X) (n : ℤ) (g : Cochain B.object.complex J.complex n),
    (Q.globalEvaluation J).f n
      ((A.li.dgApp (C.realization.obj J) : Cochain _ _ 0).v n n (add_zero n)
        (realizedCotangent (B := B) J n g)) =
      ULift.up.{1}
        ((Q.li.dgApp (evaluatePoint J.complex S) : Cochain _ _ 0).v n n (add_zero n)
          (show DGHom S.ring n (evaluatePoint B.object.complex S) (evaluatePoint J.complex S)
            from evaluateCochain g S))

variable {A} (Frame : SourceChart X → Type 2)
  (gauge : ∀ S : SourceChart X, Frame S → LiGenericGaugeSourceModels.Source S)
  (N : LiGlobalCoefficientModels.Complex X)
  (u : ∀ S (h : Frame S), evaluatePoint N S ⟶ rawUnit S (gauge S h))

/-- A single source-qualified DG port, over all chart choices and all actual affine arrows. -/
structure SourcePort where
  chart : ∀ S (h : Frame S), LocalNormalization A N S (gauge S h) (u S h)
  square : ∀ S h, GlobalLocalSquare A (chart S h)
  tests : ∀ c : IntrinsicConeChart f,
    ∃ (S : SourceChart X) (h : Frame S) (T : PolynomialTest C B S),
      T.chart = c ∧ Etale T.arrow.hom.base.left ∧ Function.Surjective T.arrow.hom.base.left
  family : letI := C.classicalLinear;
    ∀ (S E : SourceChart X) (h : Frame S) (j : Frame E) (v : E.native ⟶ S.native)
      (J : ClassicalComplex X),
    (largeLocal S).obj ((chart S h).localSource.functor.obj (evaluatePoint J.complex S)) ⟶
      (largeLocal E).obj ((chart E j).localSource.functor.obj (evaluatePoint J.complex E))
  family_pure : letI := C.classicalLinear;
    ∀ (S E : SourceChart X) (h : Frame S) (j : Frame E) (v : E.native ⟶ S.native)
      (J : ClassicalComplex X) (a b n : ℤ) (w : a + b = n)
      (x : (pointSource N S).X a) (y : (evaluatePoint J.complex S).X b),
    (family S E h j v J).f n
      (ULift.up.{1} ((eqToHom ((chart S h).localSource.objects (evaluatePoint J.complex S)).symm).f n
        (HomologicalComplex.ιTensorObj (pointSource N S) (evaluatePoint J.complex S) a b n w
          (x ⊗ₜ[S.ring] y)))) =
      ULift.up.{1} ((eqToHom ((chart E j).localSource.objects (evaluatePoint J.complex E)).symm).f n
        (HomologicalComplex.ιTensorObj (pointSource N E) (evaluatePoint J.complex E) a b n w
          ((show (pointSource N E).X a from (N.X (a + 1)).map v.op x) ⊗ₜ[E.ring]
            (show (evaluatePoint J.complex E).X b from (J.complex.X b).map v.op y))))
  family_square : letI := C.classicalLinear;
    ∀ (S E : SourceChart X) (h : Frame S) (j : Frame E) (v : E.native ⟶ S.native)
      (J : ClassicalComplex X),
    (chart S h).globalEvaluation J ≫ family S E h j v J = (chart E j).globalEvaluation J

end Normalization

end MathlibExt.AlgebraicGeometry.LiSourceDGNormalizationModels

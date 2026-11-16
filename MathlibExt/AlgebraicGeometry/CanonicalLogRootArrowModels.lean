/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricFiniteRootArrowModels
public import MathlibExt.AlgebraicGeometry.NativeRootFamilyLineMaps
public import MathlibExt.AlgebraicGeometry.RelativeStackImageModels

/-!
# The canonical root arrow through its original finite family diagrams

On every parameter T and every positive n, the fibre map is the actual
finite-root restriction along the source-normalized DF image. Its source
and target coefficient dictionaries are the original finite stack fibres.
The infinite arrow is compared on every finite projection, preserving
all original root objects and coefficient arrows through natural isomorphisms.

Source: Talpo--Vistoli1410.1164v2, Sections3--5 and Theorem5.24.
Topos equivalence and root-preserving reconstruction are separate conclusions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CanonicalLogRootArrowModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootFamilies DenominatorRootStacks
open FiniteRootTowers InfiniteDenominatorRoots KatoChartCoefficientModels
open LogRootSourceModels LogRootMorphismModels GeometricFiniteRootArrowModels
open InfiniteRootPreservationModels

local instance modificationCategory {S : Scheme.{0}} (A B : Stack S) :
    Category (StackHom A B) :=
  Pseudofunctor.StrongTrans.homCategory (F := A.toPseudofunctor) (G := B.toPseudofunctor)

variable [InverseImageTheory.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
  (RX : RootRealization X D I) (RY : RootRealization Y D I)

/-- Native inverse image preserves the power map; this identifies the
actual original root-extension categories before forgetting any data. -/
structure PowerLanding (Z : LogScheme.{0}) (RZ : RootRealization Z D I) where
  source : ∀ (T : Over Z.scheme) (n : Exponent),
    (RZ.finite n).stack.Fibre T ≌
      FiniteLogRootArrowModels.FiniteFibre (sourceDF I D RZ.dictionary T) n
  roots : ∀ (T : Over Z.scheme) (n : Exponent) (r : (RZ.finite n).stack.Fibre T),
    ((source T n).functor.obj r).of.extended =
      (((RZ.finite n).fibre T).functor.obj r).of.extended
  restriction : ∀ (T : Over Z.scheme) (n : Exponent) (r : (RZ.finite n).stack.Fibre T)
      (U : T.left.Etale) (a : (sourceMonoid D RZ.dictionary T).obj.obj (op U)),
    HEq ((((source T n).functor.obj r).of.restriction.comparison U a).hom)
      (((((RZ.finite n).fibre T).functor.obj r).of.restriction.comparison U a).hom)
  arrows : ∀ (T : Over Z.scheme) (n : Exponent)
      {r s : (RZ.finite n).stack.Fibre T} (a : r ⟶ s),
    HEq (((source T n).functor.map a).iso.hom.hom)
      ((((RZ.finite n).fibre T).functor.map a).iso.hom.hom)

/-- The full family functor is determined at each finite root level. -/
structure FiniteArrow where
  sourceLanding : PowerLanding I D X RX
  targetLanding : PowerLanding I D Y RY
  df : DFImage I D f RX.dictionary RY.dictionary
  parameter : ∀ T : Over X.scheme,
    ParameterImage I D f RX.dictionary RY.dictionary df T
  restriction : ∀ (T : Over X.scheme) (n : Exponent),
    FiniteLogRootArrowModels.Restriction (targetDF I D f RY.dictionary T)
      (sourceDF I D RX.dictionary T) (parameter T).characteristic (parameter T).comparison n
  functor : ∀ (T : Over X.scheme) (n : Exponent),
    (RX.finite n).stack.Fibre T ⥤ (RY.finite n).stack.Fibre ((Over.map f.map).obj T)
  functor_eq : ∀ (T : Over X.scheme) (n : Exponent), functor T n =
    (sourceLanding.source T n).functor ⋙
      finiteFunctor I D f RX.dictionary RY.dictionary df T (parameter T) n (restriction T n) ⋙
        (targetLanding.source ((Over.map f.map).obj T) n).inverse
  normalization : ∀ (T : Over X.scheme) (n : Exponent),
    functor T n ⋙ (targetLanding.source ((Over.map f.map).obj T) n).functor ≅
      (sourceLanding.source T n).functor ⋙
        finiteFunctor I D f RX.dictionary RY.dictionary df T (parameter T) n (restriction T n)
  normalization_eq : ∀ (T : Over X.scheme) (n : Exponent)
      (r : (RX.finite n).stack.Fibre T),
    HEq ((normalization T n).hom.app r)
      ((targetLanding.source ((Over.map f.map).obj T) n).counitIso.hom.app
        ((finiteFunctor I D f RX.dictionary RY.dictionary df T (parameter T) n
          (restriction T n)).obj ((sourceLanding.source T n).functor.obj r)))
  family : ∀ {T U : Over X.scheme} (a : T ⟶ U) (n : Exponent),
    ((RX.finite n).stack.toPseudofunctor.map a.op.toLoc).toFunctor ⋙ functor T n ≅
      functor U n ⋙ ((RY.finite n).stack.toPseudofunctor.map
        ((Over.map f.map).map a).op.toLoc).toFunctor
  tower : ∀ (T : Over X.scheme) (m n : Exponent) (h : m.val ∣ n.val),
    functor T n ⋙ StackCycleGeometry.component (RY.tower.transition m n h)
      ((Over.map f.map).obj T) ≅
      StackCycleGeometry.component (RX.tower.transition m n h) T ⋙ functor T m
  tower_identity : ∀ (T : Over X.scheme) (n : Exponent) (r : (RX.finite n).stack.Fibre T),
    (tower T n n (dvd_refl _)).hom.app r ≫
      (functor T n).map
        ((InfiniteDenominatorRoots.componentIso (RX.tower.identity n) T).hom.app r) =
    (InfiniteDenominatorRoots.componentIso (RY.tower.identity n) ((Over.map f.map).obj T)).hom.app
      ((functor T n).obj r)
  tower_composition : ∀ (T : Over X.scheme) (l m n : Exponent)
      (hlm : l.val ∣ m.val) (hmn : m.val ∣ n.val) (r : (RX.finite n).stack.Fibre T),
    (InfiniteDenominatorRoots.componentIso (RY.tower.composition l m n hlm hmn)
      ((Over.map f.map).obj T)).hom.app ((functor T n).obj r) ≫
      (tower T l n (dvd_trans hlm hmn)).hom.app r =
    (StackCycleGeometry.component (RY.tower.transition l m hlm) ((Over.map f.map).obj T)).map
      ((tower T m n hmn).hom.app r) ≫
      (tower T l m hlm).hom.app
        ((StackCycleGeometry.component (RX.tower.transition m n hmn) T).obj r) ≫
      (functor T l).map
        ((InfiniteDenominatorRoots.componentIso (RX.tower.composition l m n hlm hmn) T).hom.app r)

/-- The actual finite-root line arrow, computed from the native source
counit normalization and original DF root restriction on every coefficient. -/
def finiteRootLineMap (F : FiniteArrow I D f RX RY) (T : Over X.scheme) (n : Exponent)
    (r : (RX.finite n).stack.Fibre T) (U : T.left.Etale)
    (a : (targetMonoid D f RY.dictionary T).obj.obj (op U)) :=
  (((F.normalization T n).hom.app r).iso.hom.hom.comparison U a).hom ≫
    (((F.restriction T n).lines ((F.sourceLanding.source T n).functor.obj r)).comparison U a).hom

/-- The finite arrow on the original native root-line dictionaries. -/
def nativeFiniteLineMap (F : FiniteArrow I D f RX RY) (T : Over X.scheme) (n : Exponent)
    (r : (RX.finite n).stack.Fibre T) (V : T.left.Etale)
    (b : (targetMonoid D f RY.dictionary T).obj.obj (op V)) :=
  eqToHom (congrArg (fun E => (E.chart V).module b)
    (F.targetLanding.roots ((Over.map f.map).obj T) n ((F.functor T n).obj r)).symm) ≫
    finiteRootLineMap I D f RX RY F T n r V b ≫
    eqToHom (congrArg (fun E => (E.chart V).module
      ((F.parameter T).characteristic.hom.app (op V) b)) (F.sourceLanding.roots T n r))

/-- The actual source tower line comparison: original finite-fibre
normalization followed by the literal quotient-exponent root restriction. -/
def towerLineMap (Z : LogScheme.{0}) (RZ : RootRealization Z D I)
    (T : Over Z.scheme) (m n : Exponent) (h : m.val ∣ n.val)
    (r : (RZ.finite n).stack.Fibre T) (U : (InfiniteDenominatorRoots.fibreBase T).left.Etale)
    (a : (DenominatorRootStacks.pulledMonoids (InfiniteDenominatorRoots.fibreBase T)
      RZ.dictionary.characteristic).obj.obj (op U)) :=
  (((RZ.tower.normalization m n h T).hom.app r).iso.hom.hom.comparison U a).hom ≫
    ((((RZ.tower.tower T).transition m n h).comparison
      (((RZ.finite n).fibre T).functor.obj r)).comparison U a).hom

/-- Every Weyl-free root tower cell is fixed by the original line maps
and actual quotient-exponent transition, including zero sections. -/
structure TowerLineNormalization (F : FiniteArrow I D f RX RY) : Prop where
  sourcePower : ∀ (T : Over X.scheme) (q : ℕ),
    (EtaleMonoidInverseImage.monoidPullback (InfiniteDenominatorRoots.fibreBase T).hom).map
      (powerMap RX.dictionary.characteristic q) = powerMap (sourceMonoid D RX.dictionary T) q
  targetPower : ∀ (T : Over X.scheme) (q : ℕ),
    (EtaleMonoidInverseImage.monoidPullback
      (InfiniteDenominatorRoots.fibreBase ((Over.map f.map).obj T)).hom).map
      (powerMap RY.dictionary.characteristic q) = powerMap (targetMonoid D f RY.dictionary T) q
  line : ∀ (T : Over X.scheme) (m n : Exponent) (h : m.val ∣ n.val)
      (r : (RX.finite n).stack.Fibre T) (U : T.left.Etale)
      (a : (targetMonoid D f RY.dictionary T).obj.obj (op U)),
    ((((RY.finite m).fibre ((Over.map f.map).obj T)).functor.map
      ((F.tower T m n h).hom.app r)).iso.hom.hom.comparison U a).hom ≫
      eqToHom (congrArg (fun E => (E.chart U).module a)
        (F.targetLanding.roots ((Over.map f.map).obj T) m
          ((F.functor T m).obj ((StackCycleGeometry.component (RX.tower.transition m n h) T).obj r))).symm) ≫
      finiteRootLineMap I D f RX RY F T m
        ((StackCycleGeometry.component (RX.tower.transition m n h) T).obj r) U a ≫
      eqToHom (congrArg (fun E => (E.chart U).module
        ((F.parameter T).characteristic.hom.app (op U) a))
        (F.sourceLanding.roots T m ((StackCycleGeometry.component (RX.tower.transition m n h) T).obj r))) ≫
      towerLineMap I D X RX T m n h r U ((F.parameter T).characteristic.hom.app (op U) a) =
    towerLineMap I D Y RY ((Over.map f.map).obj T) m n h ((F.functor T n).obj r) U a ≫
      eqToHom (congrArg
        ((((RY.finite n).fibre ((Over.map f.map).obj T)).functor.obj
          ((F.functor T n).obj r)).of.extended.chart U).module
        (ConcreteCategory.congr_hom (congrArg (fun j => j.hom.app (op U))
          (targetPower T (n.val / m.val))) a)) ≫
      eqToHom (congrArg (fun E => (E.chart U).module (a ^ (n.val / m.val)))
        (F.targetLanding.roots ((Over.map f.map).obj T) n ((F.functor T n).obj r)).symm) ≫
      finiteRootLineMap I D f RX RY F T n r U (a ^ (n.val / m.val)) ≫
      eqToHom (congrArg (fun E => (E.chart U).module
        ((F.parameter T).characteristic.hom.app (op U) (a ^ (n.val / m.val))))
        (F.sourceLanding.roots T n r)) ≫
      eqToHom (congrArg ((((RX.finite n).fibre T).functor.obj r).of.extended.chart U).module
        ((map_pow ((F.parameter T).characteristic.hom.app (op U)).hom a (n.val / m.val)).trans
          (ConcreteCategory.congr_hom (congrArg (fun j => j.hom.app (op U))
            (sourcePower T (n.val / m.val))) ((F.parameter T).characteristic.hom.app (op U) a)).symm))

/-- The native parameter coefficient, transported through the original monoid compositor. -/
def transportedCoefficient (Z : LogScheme.{0}) (RZ : RootRealization Z D I)
    {T U : Over Z.scheme} (a : T ⟶ U) (V : U.left.Etale)
    (b : (pulledMonoids ((Over.map (𝟙 Z.scheme)).obj U)
      RZ.dictionary.characteristic).obj.obj (op V)) :=
  let a' := (Over.map (𝟙 Z.scheme)).map a
  let M := pulledMonoids ((Over.map (𝟙 Z.scheme)).obj U) RZ.dictionary.characteristic
  (monoidOverComparison RZ.dictionary.characteristic a').hom.hom.app
    (op ((SmallEtaleGeometry.etaleBaseChange a'.left).obj V))
    (EtaleMonoidInverseImage.generator a'.left M V b)
/-- The original characteristic map commutes with actual family coefficients. -/
def familyCoefficientCondition (F : FiniteArrow I D f RX RY) {T U : Over X.scheme} (a : T ⟶ U)
    (V : U.left.Etale) (b : (targetMonoid D f RY.dictionary U).obj.obj (op V)) : Prop :=
  (F.parameter T).characteristic.hom.app
    (op ((SmallEtaleGeometry.etaleBaseChange a.left).obj V))
    (transportedCoefficient I D Y RY ((Over.map f.map).map a) V b) =
      transportedCoefficient I D X RX a V ((F.parameter U).characteristic.hom.app (op V) b)
/-- The native family comparison along the source side of the actual coefficient square. -/
def familyLeftLine (F : FiniteArrow I D f RX RY) {T U : Over X.scheme}
    (a : T ⟶ U) (n : Exponent) (r : (RX.finite n).stack.Fibre U) (V : U.left.Etale)
    (b : (targetMonoid D f RY.dictionary U).obj.obj (op V)) :=
  (Scheme.Modules.pullback (SmallEtaleGeometry.projection a.left V)).map
    (nativeFiniteLineMap I D f RX RY F U n r V b) ≫
  NativeRootFamilyLineMaps.familyLineMap I RX.dictionary.df
    (powerMap RX.dictionary.characteristic n.val) (RX.finite n) a r V
      ((F.parameter U).characteristic.hom.app (op V) b)

-- The target path contains the native coefficient equality and finite-fibre conversions.
set_option maxHeartbeats 2000000 in
/-- The target side uses the original family cell and the literal native finite-line map. -/
def familyRightLine (F : FiniteArrow I D f RX RY) {T U : Over X.scheme}
    (a : T ⟶ U) (n : Exponent) (r : (RX.finite n).stack.Fibre U) (V : U.left.Etale)
    (b : (targetMonoid D f RY.dictionary U).obj.obj (op V))
    (hc : familyCoefficientCondition I D f RX RY F a V b) :=
  let W := (SmallEtaleGeometry.etaleBaseChange a.left).obj V
  let rT := ((RX.finite n).stack.toPseudofunctor.map a.op.toLoc).toFunctor.obj r
  let bT := transportedCoefficient I D Y RY ((Over.map f.map).map a) V b
  NativeRootFamilyLineMaps.familyLineMap I RY.dictionary.df
    (powerMap RY.dictionary.characteristic n.val) (RY.finite n) ((Over.map f.map).map a)
    ((F.functor U n).obj r) V b ≫
  (((((RY.finite n).fibre ((Over.map f.map).obj T)).functor.map
    ((F.family a n).inv.app r)).iso.hom.hom.comparison W bT).hom) ≫
  nativeFiniteLineMap I D f RX RY F T n rT W bT ≫
  eqToHom (congrArg ((((RX.finite n).fibre T).functor.obj rT).of.extended.chart W).module hc)

-- The two paths retain native dependent source and target root coefficients.
set_option maxHeartbeats 2000000 in
/-- The two actual native line paths agree on every original finite-root coefficient. -/
def familyLineCondition (F : FiniteArrow I D f RX RY) {T U : Over X.scheme}
    (a : T ⟶ U) (n : Exponent) (r : (RX.finite n).stack.Fibre U) (V : U.left.Etale)
    (b : (targetMonoid D f RY.dictionary U).obj.obj (op V))
    (hc : familyCoefficientCondition I D f RX RY F a V b) : Prop :=
  HEq (familyLeftLine I D f RX RY F a n r V b) (familyRightLine I D f RX RY F a n r V b hc)

/-- All finite family cells use the native coefficient square and line diagram. -/
structure FamilyLineNormalization (F : FiniteArrow I D f RX RY) : Prop where
  coefficient : ∀ {T U : Over X.scheme} (a : T ⟶ U) (V : U.left.Etale)
    (b : (targetMonoid D f RY.dictionary U).obj.obj (op V)),
    familyCoefficientCondition I D f RX RY F a V b
  line : ∀ {T U : Over X.scheme} (a : T ⟶ U) (n : Exponent)
    (r : (RX.finite n).stack.Fibre U) (V : U.left.Etale)
    (b : (targetMonoid D f RY.dictionary U).obj.obj (op V)),
    familyLineCondition I D f RX RY F a n r V b (coefficient a V b)

variable [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]

/-- The native infinite arrow is fixed by all original finite family functors. -/
structure InfiniteArrow (F : FiniteArrow I D f RX RY) where
  towerLineNormalization : TowerLineNormalization I D f RX RY F
  familyLineNormalization : FamilyLineNormalization I D f RX RY F
  morphism : StackHom RX.infinite.stack (baseChanged RY.infinite.stack f.map)
  projectionMaps : ∀ n : Exponent,
    BaseChangedMap (RY.infinite.projection n) f.map
  finiteGlobal : ∀ n : Exponent,
    StackHom (RX.finite n).stack (baseChanged (RY.finite n).stack f.map)
  finiteGlobalComponents : ∀ (T : Over X.scheme) (n : Exponent),
    StackCycleGeometry.component (finiteGlobal n) T = F.functor T n
  family_normalization : ∀ {T U : Over X.scheme} (a : T ⟶ U) (n : Exponent)
      (r : (RX.finite n).stack.Fibre U),
    HEq ((F.family a n).hom.app r)
      ((Cat.Hom.toNatIso ((finiteGlobal n).naturality a.op.toLoc)).hom.app r)
  finiteModification : ∀ n : Exponent,
    Pseudofunctor.StrongTrans.vcomp morphism (projectionMaps n).morphism ≅
      Pseudofunctor.StrongTrans.vcomp (RX.infinite.projection n) (finiteGlobal n)
  finite : ∀ (T : Over X.scheme) (n : Exponent),
    StackCycleGeometry.component morphism T ⋙
      StackCycleGeometry.component (RY.infinite.projection n) ((Over.map f.map).obj T) ≅
    StackCycleGeometry.component (RX.infinite.projection n) T ⋙ F.functor T n
  finite_normalization : ∀ (T : Over X.scheme) (n : Exponent)
      (r : RX.infinite.stack.Fibre T),
    HEq ((finite T n).hom.app r)
      ((InfiniteDenominatorRoots.componentIso (finiteModification n) T).hom.app r)
  tower_modification : ∀ (T : Over X.scheme) (m n : Exponent) (h : m.val ∣ n.val)
      (r : RX.infinite.stack.Fibre T),
    (InfiniteDenominatorRoots.componentIso (RY.infinite.projectionCompatibility m n h)
      ((Over.map f.map).obj T)).hom.app ((StackCycleGeometry.component morphism T).obj r) ≫
      (StackCycleGeometry.component (RY.tower.transition m n h) ((Over.map f.map).obj T)).map
        ((finite T n).hom.app r) ≫
      (F.tower T m n h).hom.app ((StackCycleGeometry.component (RX.infinite.projection n) T).obj r) ≫
      (F.functor T m).map
        ((InfiniteDenominatorRoots.componentIso (RX.infinite.projectionCompatibility m n h) T).inv.app r) =
    (finite T m).hom.app r

end MathlibExt.AlgebraicGeometry.CanonicalLogRootArrowModels

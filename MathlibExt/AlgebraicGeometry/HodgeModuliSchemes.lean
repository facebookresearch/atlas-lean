/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FramedLambdaFamilyFunctor
public import MathlibExt.AlgebraicGeometry.GeneralLinearFrameSchemes
public import MathlibExt.AlgebraicGeometry.LinearizedLineBundles
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Actual relative Hodge representation and quotient schemes

The framed scheme represents the actual locally descended admissible
family functor on every complex parameter scheme. Its parameter section,
frame action and scaling action are normalized on the actual family
operators, frames and native coefficient sections. The group schemes are
the actual determinant-localized matrix Specs.

The coarse target is a native scheme quotient after every base change
to the quotient scheme and, separately, to A1. Source, target,
action/projection diagrams and the quotient map are
literal native fibre products; their universal property does not use an
unrelated quotient carrier. Fibres and local product comparisons are also
actual scheme fibre products, with native etale morphisms.

Source: Simpson, alg-geom/9604005v1, Proposition 4.1 and Theorem 9.1.
These are construction/statement interfaces. The source theorem and native
frame/limit/GIT providers remain direct Wanted dependencies, rather than
proved or assumed representability/quotient conclusions.
Imported ordinary module, Spec, quotient and frame definitions retain
their pinned Mathlib/Stacks source, author and Apache license attribution.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HodgeModuliSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open RelativeFramedLambdaFamilies RelativeLambdaPullbackSystems AdmissibleRelativeLambdaFamilies
open FramedLambdaFamilyFunctor GeneralLinearFrameSchemes ProjectiveLineSystems
open LinearizedLineBundles LineBundleTaskContracts

abbrev parameterLine := GeometricChow.affineLine

def parameterCoordinate : Γ(parameterLine.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv.hom Polynomial.X

section UniversalQuotient

variable {G Y Z : ComplexScheme} [MonObj G] [ModObj G Y]

/-- Pull back the actual quotient map along an arbitrary map to its target. -/
def quotientPullback (q : Y ⟶ Z) {S : ComplexScheme} (c : S ⟶ Z) : Over S.left :=
  Over.mk (pullback.snd q.left c.left)

def quotientActionPullback (q : Y ⟶ Z) {S : ComplexScheme} (c : S ⟶ Z) : Over S.left :=
  Over.mk (pullback.snd ((CartesianMonoidalCategory.snd G Y).left ≫ q.left) c.left)

def quotientPullbackAction (q : Y ⟶ Z)
    (h : γ[G,Y] ≫ q = CartesianMonoidalCategory.snd G Y ≫ q)
    {S : ComplexScheme} (c : S ⟶ Z) :
    quotientActionPullback (G := G) q c ⟶ quotientPullback q c :=
  Over.homMk (pullback.lift
    (pullback.fst ((CartesianMonoidalCategory.snd G Y).left ≫ q.left) c.left ≫ γ[G,Y].left)
    (pullback.snd _ _) (by
      have hh := congrArg Over.Hom.left h
      rw [Over.comp_left, Over.comp_left] at hh
      rw [Category.assoc, hh, ← Category.assoc]
      exact pullback.condition
        (f := (CartesianMonoidalCategory.snd G Y).left ≫ q.left) (g := c.left)))
    (by simp only [quotientActionPullback, quotientPullback, Over.mk_hom, pullback.lift_snd])

def quotientPullbackFrameProjection (q : Y ⟶ Z) {S : ComplexScheme} (c : S ⟶ Z) :
    quotientActionPullback (G := G) q c ⟶ quotientPullback q c :=
  Over.homMk (pullback.lift
    (pullback.fst ((CartesianMonoidalCategory.snd G Y).left ≫ q.left) c.left ≫
      (CartesianMonoidalCategory.snd G Y).left)
    (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition))
    (by simp only [quotientActionPullback, quotientPullback, Over.mk_hom, pullback.lift_snd])

def quotientPullbackProjection (q : Y ⟶ Z) {S : ComplexScheme} (c : S ⟶ Z) :
    quotientPullback q c ⟶ Over.mk (𝟙 S.left) :=
  Over.homMk (pullback.snd q.left c.left) (by simp [quotientPullback])

/-- Universality after arbitrary base change to the actual quotient target.
The source and action are literal native scheme pullbacks. -/
structure UniversalCategoricalQuotient (q : Y ⟶ Z) : Prop where
  invariant : γ[G,Y] ≫ q = CartesianMonoidalCategory.snd G Y ≫ q
  universal : ∀ (S : ComplexScheme) (c : S ⟶ Z) (W : Over S.left)
      (f : quotientPullback q c ⟶ W),
    quotientPullbackAction q invariant c ≫ f =
      quotientPullbackFrameProjection (G := G) q c ≫ f →
        ∃! g : Over.mk (𝟙 S.left) ⟶ W, quotientPullbackProjection q c ≫ g = f

end UniversalQuotient

variable [FrameTheory 1]

/-- The actual GL1 parameter is normalized to units of the native global
coefficient ring and the literal multiplication on the affine parameter. -/
class ScalingParameterTheory where
  units : ∀ S : ComplexScheme, (S ⟶ frameScheme 1) ≃ Γ(S.left, ⊤)ˣ
  coordinate : ∀ (S : ComplexScheme) (g : S ⟶ frameScheme 1),
    g.left.appTop.hom (GeneralLinearFrameSchemes.coordinate 1 0 0) = (units S g : Γ(S.left, ⊤))
  naturality : ∀ {S T : ComplexScheme} (f : S ⟶ T) (g : T ⟶ frameScheme 1),
    units S (f ≫ g) = Units.map f.left.appTop.hom (units T g)
  [action : ModObj (frameScheme 1) parameterLine]
  multiply : ∀ (S : ComplexScheme) (g : S ⟶ frameScheme 1) (t : S ⟶ parameterLine),
    (CartesianMonoidalCategory.lift g t ≫ γ[frameScheme 1,parameterLine]).left.appTop.hom
        parameterCoordinate = (units S g : Γ(S.left, ⊤)) * t.left.appTop.hom parameterCoordinate

attribute [instance_reducible, instance] ScalingParameterTheory.action

variable (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ) (P : PullbackSystem X x n)
  (V : UnitFibreComparison X x n P) (d : ℕ) (H : LineBundle X.left)
  (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
  (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
    (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
  (T : BettiCharacteristicClasses.ProjectiveBundleTheory D Q)
  [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
  (F : FibreTests X x n P V d H)
  (RP : ReindexingProofs X x n P V d H D Q T F) (PC : PullbackCoherence X x n P)

structure ActionAdmissibility : Prop where
  frame : ∀ (S : ComplexScheme) (E : AdmissibleFamily X x n P V d H D Q T F S)
      (g : Aut (CurveVectorBundles.trivialBundle S.left n)),
    IsAdmissible X x n P V d H D Q T F (Family.changeFrame E.val g)
  scale : ∀ (S : ComplexScheme) (E : AdmissibleFamily X x n P V d H D Q T F S)
      (a : Γ(S.left, ⊤)ˣ), IsAdmissible X x n P V d H D Q T F (Family.scale E.val a.val)

variable [FrameTheory n] [ScalingParameterTheory]
  (AP : ActionAdmissibility X x n P V d H D Q T F)

structure HodgeRepresentation where
  scheme : ComplexScheme
  [finiteType : LocallyOfFiniteType scheme.hom]
  [quasiCompact : QuasiCompact scheme.hom]
  parameter : scheme ⟶ parameterLine
  points : ∀ S : ComplexScheme, (S ⟶ scheme) ≃ FamilyClasses X x n P V d H D Q T F S
  naturality : ∀ {S U : ComplexScheme} (f : S ⟶ U) (g : U ⟶ scheme),
    points S (f ≫ g) = classesMap X x n P V d H D Q T F RP f (points U g)
  parameter_value : ∀ (S : ComplexScheme) (E : AdmissibleFamily X x n P V d H D Q T F S),
    ((points S).symm (classOf X x n P V d H D Q T F E) ≫ parameter).left.appTop.hom
      parameterCoordinate = E.val.parameter
  [frameAction : ModObj (frameScheme n) scheme]
  frame_normalization : ∀ (S : ComplexScheme) (E : AdmissibleFamily X x n P V d H D Q T F S)
      (g : S ⟶ frameScheme n),
    points S (CartesianMonoidalCategory.lift g
        ((points S).symm (classOf X x n P V d H D Q T F E)) ≫ γ[frameScheme n,scheme]) =
      classOf X x n P V d H D Q T F
        ⟨Family.changeFrame E.val (FrameTheory.points S g), AP.frame S E _⟩
  frame_parameter : γ[frameScheme n,scheme] ≫ parameter =
    CartesianMonoidalCategory.snd (frameScheme n) scheme ≫ parameter
  line : LineBundle scheme.left
  [noetherian : IsNoetherian scheme.left]
  ample : IsAmpleLine line
  linearization : Linearization (frameScheme n) scheme line.val
  actionPowers : PullbackPowers (LinearizedLineBundles.action (frameScheme n) scheme)
  projectionPowers : PullbackPowers (LinearizedLineBundles.projection (frameScheme n) scheme)
  allSemistable : ∀ (Omega : Type) [Field Omega] (s : Spec (CommRingCat.of Omega) ⟶ scheme.left),
    HasInvariantNonvanishingPower (frameScheme n) scheme linearization actionPowers
      projectionPowers s
  [scalingAction : ModObj (frameScheme 1) scheme]
  scaling_normalization : ∀ (S : ComplexScheme) (E : AdmissibleFamily X x n P V d H D Q T F S)
      (g : S ⟶ frameScheme 1),
    points S (CartesianMonoidalCategory.lift g
        ((points S).symm (classOf X x n P V d H D Q T F E)) ≫ γ[frameScheme 1,scheme]) =
      classOf X x n P V d H D Q T F
        ⟨Family.scale E.val (ScalingParameterTheory.units S g).val, AP.scale S E _⟩
  scaling_parameter : γ[frameScheme 1,scheme] ≫ parameter =
    (frameScheme 1 ◁ parameter) ≫ γ[frameScheme 1,parameterLine]

attribute [instance] HodgeRepresentation.finiteType HodgeRepresentation.quasiCompact

def frameActionMap (R : HodgeRepresentation X x n P V d H D Q T F RP AP) :
    (frameScheme n ⊗ R.scheme).left ⟶ R.scheme.left := by
  letI := R.frameAction
  exact γ[frameScheme n,R.scheme].left

def frameProjectionMap (R : HodgeRepresentation X x n P V d H D Q T F RP AP) :
    (frameScheme n ⊗ R.scheme).left ⟶ R.scheme.left :=
  (CartesianMonoidalCategory.snd (frameScheme n) R.scheme).left

def baseObject (Y : ComplexScheme) (p : Y ⟶ parameterLine) (S : ComplexScheme)
    (c : S ⟶ parameterLine) : Over S.left := Over.mk (pullback.snd p.left c.left)

def baseMap {Y Z : ComplexScheme} (p : Y ⟶ parameterLine) (q : Z ⟶ parameterLine)
    (f : Y ⟶ Z) (hf : f ≫ q = p) (S : ComplexScheme) (c : S ⟶ parameterLine) :
    baseObject Y p S c ⟶ baseObject Z q S c :=
  Over.homMk (pullback.lift (pullback.fst p.left c.left ≫ f.left)
    (pullback.snd p.left c.left) (by
      rw [Category.assoc, ← Over.comp_left, hf]
      exact pullback.condition)) (by simp only [baseObject, Over.mk_hom, pullback.lift_snd])

def frameBaseObject (R : HodgeRepresentation X x n P V d H D Q T F RP AP)
    (S : ComplexScheme) (c : S ⟶ parameterLine) : Over S.left :=
  Over.mk (pullback.snd (frameProjectionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left)
    c.left)

def baseFrameAction (R : HodgeRepresentation X x n P V d H D Q T F RP AP)
    (S : ComplexScheme) (c : S ⟶ parameterLine) :
    frameBaseObject X x n P V d H D Q T F RP AP R S c ⟶ baseObject R.scheme R.parameter S c :=
  Over.homMk (pullback.lift
    (pullback.fst (frameProjectionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left) c.left ≫
      frameActionMap X x n P V d H D Q T F RP AP R)
    (pullback.snd (frameProjectionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left) c.left) (by
      have h := congrArg Over.Hom.left R.frame_parameter
      rw [Over.comp_left, Over.comp_left] at h
      change frameActionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left =
        frameProjectionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left at h
      rw [Category.assoc, h, ← Category.assoc]
      exact pullback.condition
        (f := frameProjectionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left)
        (g := c.left)))
      (by simp only [frameBaseObject, baseObject, Over.mk_hom, pullback.lift_snd])

def baseFrameProjection (R : HodgeRepresentation X x n P V d H D Q T F RP AP)
    (S : ComplexScheme) (c : S ⟶ parameterLine) :
    frameBaseObject X x n P V d H D Q T F RP AP R S c ⟶ baseObject R.scheme R.parameter S c :=
  Over.homMk (pullback.lift
    (pullback.fst (frameProjectionMap X x n P V d H D Q T F RP AP R ≫ R.parameter.left) c.left ≫
      frameProjectionMap X x n P V d H D Q T F RP AP R)
    (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition))
      (by simp only [frameBaseObject, baseObject, Over.mk_hom, pullback.lift_snd])

structure HodgeQuotient (R : HodgeRepresentation X x n P V d H D Q T F RP AP) where
  scheme : ComplexScheme
  [finiteType : LocallyOfFiniteType scheme.hom]
  [quasiCompact : QuasiCompact scheme.hom]
  parameter : scheme ⟶ parameterLine
  quotient : R.scheme ⟶ scheme
  commutes : quotient ≫ parameter = R.parameter
  invariant : frameActionMap X x n P V d H D Q T F RP AP R ≫ quotient.left =
    frameProjectionMap X x n P V d H D Q T F RP AP R ≫ quotient.left
  targetUniversal : letI := R.frameAction;
    UniversalCategoricalQuotient (G := frameScheme n) quotient
  universal : ∀ (S : ComplexScheme) (c : S ⟶ parameterLine) (Y : Over S.left)
      (f : baseObject R.scheme R.parameter S c ⟶ Y),
    baseFrameAction X x n P V d H D Q T F RP AP R S c ≫ f =
      baseFrameProjection X x n P V d H D Q T F RP AP R S c ≫ f →
        ∃! g : baseObject scheme parameter S c ⟶ Y,
          baseMap R.parameter parameter quotient commutes S c ≫ g = f

def fibre (Y : ComplexScheme) (p : Y ⟶ parameterLine) (c : scalarBase ⟶ parameterLine) :
    ComplexScheme := Over.mk (pullback.snd p.left c.left ≫ scalarBase.hom)

structure EtaleLocalProduct (Y : ComplexScheme) (p : Y ⟶ parameterLine) (y : scalarBase ⟶ Y) where
  neighborhood : ComplexScheme
  point : scalarBase ⟶ neighborhood
  map : neighborhood ⟶ Y
  point_eq : point ≫ map = y
  [etaleMap : Etale map.left]
  comparison : neighborhood ⟶ fibre Y p (y ≫ p) ⊗ parameterLine
  [etaleComparison : Etale comparison.left]
  parameter : comparison ≫ CartesianMonoidalCategory.snd (fibre Y p (y ≫ p)) parameterLine = map ≫ p

end MathlibExt.AlgebraicGeometry.HodgeModuliSchemes

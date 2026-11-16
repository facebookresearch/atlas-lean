/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HodgeModuliSchemes

/-!
# Independent fixed-parameter Higgs and de Rham moduli endpoints

Fixed-parameter families are defined directly by actual bundle/connection/
frame data and the constant coefficient section. Their representing schemes
and categorical quotients are independent construction targets, rather than
aliases for a fibre of the total Hodge scheme. The fibre comparison has
actual scheme isomorphisms, an all-test-scheme family-class normalization,
and the native quotient-map square.

At zero, the endpoint carries a genuine relative integrable Higgs morphism,
with its bundle/frame and literal operator normalization. At one, it carries
the actual lambda-one flat connection, with both connection operators and
frame normalized. These objects can be used before any provider proof is
completed.

Source: Simpson, alg-geom/9604005v1, section 4 and Proposition 4.1.
Native source/target tensor, module, class quotient and fibre constructions
retain their Mathlib/Stacks license, revision and adaptation credits in the
imported modules.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FixedParameterLambdaModuli

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open RelativeFramedLambdaFamilies RelativeLambdaPullbackSystems AdmissibleRelativeLambdaFamilies
open FramedLambdaFamilyFunctor HodgeModuliSchemes GeneralLinearFrameSchemes
open RelativeDifferentialForms RelativeDeRhamDifferential AlgebraicLambdaConnections
open ProjectiveLineSystems AlgebraicLineBundleFamilies LineBundleTaskContracts CurveVectorBundles

def scalarParameter (S : ComplexScheme) (lambda : ℂ) : Γ(S.left, ⊤) :=
  CoherentCurveLinearSeries.globalScalarMap S.hom lambda

variable (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ) (P : PullbackSystem X x n)
  (V : UnitFibreComparison X x n P) (d : ℕ) (H : LineBundle X.left)
  (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
  (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
    (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
  (T : BettiCharacteristicClasses.ProjectiveBundleTheory D Q)
  [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
  (F : FibreTests X x n P V d H)

abbrev FixedFamily (lambda : ℂ) (S : ComplexScheme) :=
  {E : Family X x S (P.differential S) n //
    IsAdmissible X x n P V d H D Q T F E ∧ E.parameter = scalarParameter S lambda}

def fixedRelation (lambda : ℂ) (S : ComplexScheme)
    (E G : FixedFamily X x n P V d H D Q T F lambda S) : Prop := Nonempty (Family.Iso E.val G.val)

@[instance_reducible] def fixedSetoid (lambda : ℂ) (S : ComplexScheme) :=
  Relation.EqvGen.setoid (fixedRelation X x n P V d H D Q T F lambda S)

abbrev FixedClasses (lambda : ℂ) (S : ComplexScheme) :=
  Quotient (fixedSetoid X x n P V d H D Q T F lambda S)

def fixedClass {lambda : ℂ} {S : ComplexScheme}
    (E : FixedFamily X x n P V d H D Q T F lambda S) : FixedClasses X x n P V d H D Q T F
      lambda S :=
  Quotient.mk _ E

def forgetFixed {lambda : ℂ} {S : ComplexScheme} :
    FixedClasses X x n P V d H D Q T F lambda S → FamilyClasses X x n P V d H D Q T F S :=
  Quotient.map (fun E ↦ (⟨E.val, E.property.1⟩ : AdmissibleFamily X x n P V d H D Q T F S)) (by
    intro E G h
    induction h with
    | rel E G h => exact Relation.EqvGen.rel _ _ h
    | refl E => exact Relation.EqvGen.refl _
    | symm E G h ih => exact Relation.EqvGen.symm _ _ ih
    | trans E G K hEG hGK ihEG ihGK => exact Relation.EqvGen.trans _ _ _ ihEG ihGK)

structure RelativeHiggsFamily (S : ComplexScheme) where
  object : (prod X S).left.Modules
  bundle : IsVectorBundle object n
  theta : object ⟶ moduleTensor (prod X S).left object (forms (projection X S) 1)
  integrable : relativeHiggsSquare theta = 0
  frame : (Scheme.Modules.pullback (framingSection X S x).left).obj object ≅ trivialBundle S.left n

structure ZeroHiggsRealization {S : ComplexScheme}
    (E : FixedFamily X x n P V d H D Q T F 0 S) where
  higgs : RelativeHiggsFamily X x n S
  bundle : E.val.connection.object ≅ higgs.object
  operator : ∀ (U : (prod X S).left.Opens) (s : E.val.connection.object.val.obj (op U)),
    ((tensorMap bundle.hom (𝟙 (forms (projection X S) 1))).val.app (op U)).hom
        (E.val.connection.nabla0 U s) =
      (higgs.theta.val.app (op U)).hom ((bundle.hom.val.app (op U)).hom s)
  frame : (Scheme.Modules.pullback (framingSection X S x).left).map bundle.hom ≫
    higgs.frame.hom = E.val.frame.hom

structure FlatFamily (S : ComplexScheme) where
  connection : LambdaConnection (projection X S) 1 (P.differential S)
  rank_eq : connection.rank = n
  frame : (Scheme.Modules.pullback (framingSection X S x).left).obj connection.object ≅
    trivialBundle S.left n

structure OneFlatRealization {S : ComplexScheme}
    (E : FixedFamily X x n P V d H D Q T F 1 S) where
  flat : FlatFamily X x n P S
  bundle : E.val.connection.object ≅ flat.connection.object
  operator0 : ∀ (U : (prod X S).left.Opens) (s : E.val.connection.object.val.obj (op U)),
    ((tensorMap bundle.hom (𝟙 (forms (projection X S) 1))).val.app (op U)).hom
        (E.val.connection.nabla0 U s) =
      flat.connection.nabla0 U ((bundle.hom.val.app (op U)).hom s)
  operator1 : ∀ (U : (prod X S).left.Opens)
      (s : (moduleTensor (prod X S).left E.val.connection.object (forms (projection X S) 1)).val.obj
        (op U)),
    ((tensorMap bundle.hom (𝟙 (forms (projection X S) 2))).val.app (op U)).hom
        (E.val.connection.nabla1 U s) = flat.connection.nabla1 U
      (((tensorMap bundle.hom (𝟙 (forms (projection X S) 1))).val.app (op U)).hom s)
  frame : (Scheme.Modules.pullback (framingSection X S x).left).map bundle.hom ≫
    flat.frame.hom = E.val.frame.hom

variable (RP : ReindexingProofs X x n P V d H D Q T F)
  (AP : ActionAdmissibility X x n P V d H D Q T F) [FrameTheory n]

structure FixedRepresentation (lambda : ℂ) where
  scheme : ComplexScheme
  [finiteType : LocallyOfFiniteType scheme.hom]
  [quasiCompact : QuasiCompact scheme.hom]
  points : ∀ S : ComplexScheme, (S ⟶ scheme) ≃ FixedClasses X x n P V d H D Q T F lambda S
  naturality : ∀ {S U : ComplexScheme} (f : S ⟶ U) (g : U ⟶ scheme),
    forgetFixed X x n P V d H D Q T F (points S (f ≫ g)) =
      classesMap X x n P V d H D Q T F RP f (forgetFixed X x n P V d H D Q T F (points U g))
  [frameAction : ModObj (frameScheme n) scheme]
  frame_normalization : ∀ (S : ComplexScheme)
      (E : FixedFamily X x n P V d H D Q T F lambda S) (g : S ⟶ frameScheme n),
    points S (CartesianMonoidalCategory.lift g
        ((points S).symm (fixedClass X x n P V d H D Q T F E)) ≫ γ[frameScheme n,scheme]) =
      fixedClass X x n P V d H D Q T F
        ⟨Family.changeFrame E.val (FrameTheory.points S g),
          AP.frame S ⟨E.val, E.property.1⟩ _, by
            simpa only [Family.changeFrame_parameter] using E.property.2⟩

structure FixedQuotient {lambda : ℂ}
    (R : FixedRepresentation X x n P V d H D Q T F RP AP lambda) where
  scheme : ComplexScheme
  [finiteType : LocallyOfFiniteType scheme.hom]
  [quasiCompact : QuasiCompact scheme.hom]
  categorical : letI := R.frameAction;
    LinearizedLineBundles.CategoricalQuotient (frameScheme n) R.scheme scheme
  universal : letI := R.frameAction;
    UniversalCategoricalQuotient (G := frameScheme n) categorical.quotient

def FixedQuotient.quotient {lambda : ℂ}
    {R : FixedRepresentation X x n P V d H D Q T F RP AP lambda}
    (C : FixedQuotient X x n P V d H D Q T F RP AP R) : R.scheme ⟶ C.scheme := by
  letI := R.frameAction
  exact C.categorical.quotient

def complexParameterPoint (a : ℂ) : scalarBase ⟶ parameterLine :=
  Over.homMk (scalarBase.hom ≫ GeometricChow.affinePoint a) (by
    have hr : CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 (CommRingCat.of ℂ) := by ext z; simp
    have h : GeometricChow.affinePoint a ≫ parameterLine.hom = 𝟙 _ := by
      change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))) = 𝟙 _
      rw [← Spec.map_comp, hr, Spec.map_id]
    rw [Category.assoc, h, Category.comp_id])

def fibreInclusion (Y : ComplexScheme) (p : Y ⟶ parameterLine) (c : scalarBase ⟶ parameterLine) :
    fibre Y p c ⟶ Y :=
  Over.homMk (pullback.fst p.left c.left) (by
    change pullback.fst p.left c.left ≫ Y.hom = pullback.snd p.left c.left ≫ scalarBase.hom
    rw [← Over.w p, ← Category.assoc, pullback.condition, Category.assoc, Over.w c])

variable [FrameTheory 1] [ScalingParameterTheory]

def fibreQuotientMap
    {R : HodgeRepresentation X x n P V d H D Q T F RP AP}
    (C : HodgeQuotient X x n P V d H D Q T F RP AP R) (lambda : ℂ) :
    fibre R.scheme R.parameter (complexParameterPoint lambda) ⟶
      fibre C.scheme C.parameter (complexParameterPoint lambda) :=
  Over.homMk (baseMap R.parameter C.parameter C.quotient C.commutes scalarBase
    (complexParameterPoint lambda)).left (by
      change (baseMap R.parameter C.parameter C.quotient C.commutes scalarBase
        (complexParameterPoint lambda)).left ≫
          (baseObject C.scheme C.parameter scalarBase (complexParameterPoint lambda)).hom ≫
            scalarBase.hom =
          (baseObject R.scheme R.parameter scalarBase (complexParameterPoint lambda)).hom ≫
            scalarBase.hom
      rw [← Category.assoc, Over.w])

structure FibreIdentification (lambda : ℂ)
    (R : HodgeRepresentation X x n P V d H D Q T F RP AP)
    (C : HodgeQuotient X x n P V d H D Q T F RP AP R)
    (Rfix : FixedRepresentation X x n P V d H D Q T F RP AP lambda)
    (Cfix : FixedQuotient X x n P V d H D Q T F RP AP Rfix) where
  framed : fibre R.scheme R.parameter (complexParameterPoint lambda) ≅ Rfix.scheme
  coarse : fibre C.scheme C.parameter (complexParameterPoint lambda) ≅ Cfix.scheme
  class_normalization : ∀ (S : ComplexScheme)
      (f : S ⟶ fibre R.scheme R.parameter (complexParameterPoint lambda)),
    forgetFixed X x n P V d H D Q T F (Rfix.points S (f ≫ framed.hom)) =
      R.points S (f ≫ fibreInclusion R.scheme R.parameter (complexParameterPoint lambda))
  quotient_square : fibreQuotientMap X x n P V d H D Q T F RP AP C lambda ≫ coarse.hom =
    framed.hom ≫ Cfix.quotient X x n P V d H D Q T F RP AP

end MathlibExt.AlgebraicGeometry.FixedParameterLambdaModuli

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
public import MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
/-!
# Actual affine perfect obstruction theories and normalized extension cocycles

The source is a finite-free complex in degrees −1 and 0, and its morphism
lands in the actual full cotangent complex computed from genuine polynomial
resolution data. The conditions are the actual isomorphism on H⁰ and
surjection on H⁻¹, not supplied deformation conclusions.

For a lift of the degree-zero polynomial algebra across a square-zero
extension, the obstruction cocycle is characterized on each pure differential
by the difference of the two lifted faces. Its target is the actual conormal
module of the extension in degree −1. The normalization determines the
cochain map uniquely, as proved here. The class for a perfect obstruction
theory is literal composition with that normalized map in Mathlib's derived
category; no arbitrary obstruction carrier or class is supplied.

Construction and lifting comparison are requested separately. Generic
polynomial resolutions, cotangent comparison and square-zero deformation
infrastructure are already implemented in AxiomMath/Stacks, e.g.
StacksFrontier/Cotangent/ResolutionCotangentAny.lean and
StacksFrontier/Deformation/ToposThickening/LiftingMorphismDerivedCriterion.lean,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, and are not re-requested
as missing. Primary reference: Behrend--Fantechi, *The intrinsic normal cone*,
§4, https://arxiv.org/abs/alg-geom/9601010.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial
open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
attribute [local instance] HasDerivedCategory.standard
variable {k B : Type} [Field k] [CommRing B] [Algebra k B]

structure PerfectObstructionTheory (R : PolynomialResolution k B) where
  model : FreeTwoTerm B
  morphism : derived B model ⟶ affineDerived R
  [h0 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{0} B) 0).map morphism)]
  [hNegative : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{0} B) (-1)).map morphism)]

attribute [instance] PerfectObstructionTheory.h0 PerfectObstructionTheory.hNegative

structure PolynomialLift (R : PolynomialResolution k B) (Q : _root_.Algebra.Extension.{0} k B) where
  hom : R.algebra.obj (op ⦋0⦌) →ₐ[k] Q.Ring
  over : (IsScalarTower.toAlgHom k Q.Ring B).comp hom = (R.augmentation.app (op ⦋0⦌)).hom

theorem augmentation_face (R : PolynomialResolution k B) (i : Fin 2)
    (p : R.algebra.obj (op ⦋1⦌)) :
    (R.augmentation.app (op ⦋0⦌)).hom (R.algebra.δ i p) =
      (R.augmentation.app (op ⦋1⦌)).hom p := by
  have h := R.augmentation.naturality (SimplexCategory.δ i).op
  exact congrArg (fun f : R.algebra.obj (op ⦋1⦌) ⟶ CommAlgCat.of k B => f p) h

def liftError (R : PolynomialResolution k B) (Q : _root_.Algebra.Extension.{0} k B)
    (L : PolynomialLift R Q) (p : R.algebra.obj (op ⦋1⦌)) : Q.Cotangent :=
  _root_.Algebra.Extension.Cotangent.mk ⟨L.hom (R.algebra.δ (0 : Fin 2) p) -
    L.hom (R.algebra.δ (1 : Fin 2) p), by
    change algebraMap Q.Ring B _ = 0
    have hov (t : R.algebra.obj (op ⦋0⦌)) : algebraMap Q.Ring B (L.hom t) =
        (R.augmentation.app (op ⦋0⦌)).hom t :=
      congrArg (fun f : R.algebra.obj (op ⦋0⦌) →ₐ[k] B => f t) L.over
    rw [map_sub, hov, hov, augmentation_face, augmentation_face, sub_self]⟩

abbrev coefficientComplex (Q : _root_.Algebra.Extension.{0} k B) :
    CochainComplex (ModuleCat.{0} B) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{0} B) (-1)).obj (ModuleCat.of B Q.Cotangent)

structure CotangentExtensionCocycle (R : PolynomialResolution k B)
    (Q : _root_.Algebra.Extension.{0} k B)
    (L : PolynomialLift R Q) where
  morphism : affineComplex R ⟶ coefficientComplex Q
  normalization : ∀ p : R.algebra.obj (op ⦋1⦌),
    ((affineDegreeIso R 1).inv ≫ morphism.f (-1) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) (ModuleCat.of B Q.Cotangent)).hom)
      (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k B) R.algebra
        R.augmentation (op ⦋1⦌) p) = liftError R Q L p

def obstructionClass {R : PolynomialResolution k B} (T : PerfectObstructionTheory R)
    {Q : _root_.Algebra.Extension.{0} k B} {L : PolynomialLift R Q}
    (C : CotangentExtensionCocycle R Q L) :
    derived B T.model ⟶ (DerivedCategory.singleFunctor (ModuleCat.{0} B) (-1)).obj
      (ModuleCat.of B Q.Cotangent) :=
  T.morphism ≫ DerivedCategory.Q.map C.morphism

abbrev Liftings (Q : _root_.Algebra.Extension.{0} k B) :=
  {f : B →ₐ[k] Q.Ring | (IsScalarTower.toAlgHom k Q.Ring B).comp f = AlgHom.id k B}


@[ext] theorem cocycle_ext {R : PolynomialResolution k B} {Q : _root_.Algebra.Extension.{0} k B}
    {L : PolynomialLift R Q} {C C' : CotangentExtensionCocycle R Q L}
    (h : C.morphism = C'.morphism) : C = C' := by
  cases C
  cases C'
  cases h
  rfl

theorem cocycle_unique {R : PolynomialResolution k B} {Q : _root_.Algebra.Extension.{0} k B}
    {L : PolynomialLift R Q} (C C' : CotangentExtensionCocycle R Q L) : C = C' := by
  apply cocycle_ext
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = -1
  · subst i
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) (ModuleCat.of B Q.Cotangent)
    apply (cancel_mono e.hom).mp
    apply (cancel_epi (affineDegreeIso R 1).inv).mp
    apply CommAlgCat.resolutionCotangentTerm_hom_ext k (CommAlgCat.of k B)
      R.algebra R.augmentation (op ⦋1⦌)
    intro p
    exact (C.normalization p).trans (C'.normalization p).symm
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
      (ModuleCat.of B Q.Cotangent) i hi).eq_of_tgt _ _

end MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeStackTensorDictionaries
public import MathlibExt.AlgebraicGeometry.ParabolicBilinearTensorModels
public import MathlibExt.AlgebraicGeometry.UniversalRootWeightLines
public import MathlibExt.AlgebraicGeometry.RootStackProjectionModules

/-!
# Root tensor and base-line comparisons on all actual generators

Root line multiplication and the tensor unit are fixed on all pure
tensors and every actual affine root family. The base comparison on a
positive A generator is the literal scheme pullback, native inverse-DF
comparison, identity-étale diagonal restriction and the root object's
actual restriction isomorphism. Group-period comparisons preserve this
recipe, units and multiplication.

Source: Borne–Vistoli arXiv:1001.0466v2, Corollary5.4 and the
projection-formula construction in Theorem6.1.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootWeightTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackAffineModules _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.CartesianStackTensorProducts _root_.AlgebraicGeometry.SchemeStackModuleModels
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootFamilies DenominatorRootStacks
open EtaleMonoidInverseImage ParabolicSheafCategories RootWeightEvaluations UniversalRootWeightLines
open AlgebraicLineBundleFamilies CoherentCurveLinearSeries LineBundleTaskContracts NativeTensorComparisons
open ModuleTensorPullbackSections SchemeStackTensorDictionaries ParabolicBilinearTensorModels
open scoped TensorProduct

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A) (j : A ⟶ B)

theorem generator_map {Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Etale) (a : A.obj.obj (op U)) :
    ((monoidPullback f).map j).hom.app (op ((etaleBaseChange f).obj U)) (generator f A U a) =
      generator f B U (j.hom.app (op U) a) := by
  have h := (adjunction f).unit.naturality j
  exact (congrArg (fun k ↦ k.hom.app (op U) (a)) h).symm

theorem localGenerator_map (U : X.Etale) (T : Over U.left) (a : A.obj.obj (op U)) :
    ((monoidPullback (T.hom ≫ U.hom)).map j).hom.app (op (identityEtale T.left))
      (localGenerators A U T a) = localGenerators B U T (j.hom.app (op U) a) := by
  let m := generator (T.hom ≫ U.hom) A U a
  have h := NatTrans.naturality_apply ((monoidPullback (T.hom ≫ U.hom)).map j).hom
    (localDiagonal U T).op m
  change _ = _ at h
  simpa [localGenerators, m, generator_map] using h

theorem diagonal_projection (U : X.Etale) (T : Over U.left) :
    (localDiagonal U T).left ≫ projection (T.hom ≫ U.hom) U = T.hom := by
  change pullback.lift T.hom (𝟙 T.left) _ ≫ pullback.fst U.hom (T.hom ≫ U.hom) = T.hom
  simp

def diagonalCoefficient (U : X.Etale) (T : Over U.left) (L : U.left.Modules) :
    (Scheme.Modules.pullback T.hom).obj L ≅
      (Scheme.Modules.pullback (localDiagonal U T).left).obj
        ((Scheme.Modules.pullback (projection (T.hom ≫ U.hom) U)).obj L) :=
  eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj L) (diagonal_projection U T).symm) ≪≫
    (Scheme.Modules.pullbackComp (localDiagonal U T).left (projection (T.hom ≫ U.hom) U)).symm.app L

def positiveBaseLine (U : X.Etale) (T : Over U.left)
    (E : rootsAt I D j ((Over.map U.hom).obj T)) (a : A.obj.obj (op U)) :
    (Scheme.Modules.pullback T.hom).obj ((D.chart U).module a) ≅
      (E.of.extended.chart (identityEtale T.left)).module (localGenerators B U T (j.hom.app (op U) a)) :=
  diagonalCoefficient U T ((D.chart U).module a) ≪≫
    (Scheme.Modules.pullback (localDiagonal U T).left).mapIso
      (((I T.left X (T.hom ≫ U.hom) A).object D).comparison U a) ≪≫
    (pulledStructure I D ((Over.map U.hom).obj T)).reindex (localDiagonal U T)
      (generator (T.hom ≫ U.hom) A U a) ≪≫
    E.of.restriction.comparison (identityEtale T.left) (localGenerators A U T a) ≪≫
      eqToIso (congrArg (E.of.extended.chart (identityEtale T.left)).module (localGenerator_map j U T a))

variable (U : X.Etale) (R : DenominatorRootStacks.Model I D j U.hom)
  (W : StackWeights I D j U R) (T : TensorLanding R.stack)

abbrev value (a : AffinePoint R.stack) := values I D j U R a (W.groupified a) (W.laws a)

def baseWeight (p : Groupification (A.obj.obj (op U))) : Weight (B.obj.obj (op U)) :=
  ⟨groupMap (j.hom.app (op U)).hom p⟩

/-- The root tensor operations are native cartesian morphisms fixed by
the whole affine-family sections and native groupified DF multiplication. -/
structure WeightTensor where
  unit : CartesianStackModules.structureModule R.stack ≅ W.line.obj (oneWeight (B := B) U)
  multiplication : ∀ v w : Weight (B.obj.obj (op U)),
    ((CartesianStackTensorProducts.tensor R.stack T).obj (W.line.obj v)).obj (W.line.obj w) ≅
      W.line.obj (weightProduct v w)
  unit_normalized : ∀ (a : AffinePoint R.stack) (r : Γ(a.obj.base.left,⊤)),
    W.sections (oneWeight (B := B) U) a (unit.hom.hom.app (op a) r) =
      (((unitIso I D j U R a (W.groupified a) (W.laws a)).inv.val.app (op ⊤)).hom r)
  multiplication_normalized : ∀ (v w : Weight (B.obj.obj (op U))) (a : AffinePoint R.stack)
    (x : (W.line.obj v).obj.obj (op a)) (y : (W.line.obj w).obj.obj (op a)),
    W.sections (weightProduct v w) a ((multiplication v w).hom.hom.app (op a) (x ⊗ₜ y)) =
      (((multiplicationIso I D j U R a (W.groupified a) (W.laws a) v w).hom.val.app (op ⊤)).hom
        (tensorSections a.obj.base.left ((value I D j U R W a).obj v) ((value I D j U R W a).obj w)
          (W.sections v a x) (W.sections w a y)))

end MathlibExt.AlgebraicGeometry.RootWeightTensorModels

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootWeightTensorModels

/-!
# Native source recipes for the parabolic group periods

Positive base-line comparison is the actual root restriction on every
DF generator. Unit and multiplication extend that comparison to all
group weights. Its cartesian module map is fixed on every affine test.
The period is then the native root tensor rearrangement followed by the
inverse of the actual adjunction projection-formula map and the fixed
represented-scheme tensor dictionary.

Source: Borne–Vistoli arXiv:1001.0466v2, Theorem6.1, the displayed
projection-formula sequence for rho_(u,v).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootParabolicPeriodModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackAffineModules _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.CartesianStackTensorProducts _root_.AlgebraicGeometry.SchemeStackModuleModels
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootFamilies DenominatorRootStacks
open EtaleMonoidInverseImage ParabolicSheafCategories RootWeightEvaluations UniversalRootWeightLines
open AlgebraicLineBundleFamilies CoherentCurveLinearSeries LineBundleTaskContracts NativeTensorComparisons
open ModuleTensorPullbackSections SchemeStackTensorDictionaries ParabolicBilinearTensorModels
open RootWeightTensorModels

def sheafTensorIso {Y : Scheme.{0}} {L L' M M' : Y.Modules}
    (a : L ≅ L') (b : M ≅ M') : moduleTensor Y L M ≅ moduleTensor Y L' M' where
  hom := tensorMap a.hom b.hom
  inv := tensorMap a.inv b.inv
  hom_inv_id := by rw [← tensorMap_comp]; simp
  inv_hom_id := by rw [← tensorMap_comp]; simp

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (U : X.Etale) (R : DenominatorRootStacks.Model I D j U.hom)
  (W : StackWeights I D j U R) (T : TensorLanding R.stack)

def positiveValue (a : AffinePoint R.stack) (m : A.obj.obj (op U)) :
    (value I D j U R W a).obj (baseWeight j U (Algebra.GrothendieckGroup.of m)) ≅
      ((rootObject I D j U R a).of.extended.chart (identityEtale a.obj.base.left)).module
        (localGenerators B U a.obj.base (j.hom.app (op U) m)) :=
  eqToIso (congrArg (value I D j U R W a).obj (by
    apply Weight.ext
    exact groupMap_of (j.hom.app (op U)).hom m)) ≪≫
      positiveIso I D j U R a (W.groupified a) (W.laws a) (j.hom.app (op U) m)

def baseUnitValue (a : AffinePoint R.stack) :
    (value I D j U R W a).obj (baseWeight j U 1) ≅ structureModule a.obj.base.left :=
  eqToIso (congrArg (value I D j U R W a).obj (by
    apply Weight.ext; exact map_one (groupMap (j.hom.app (op U)).hom))) ≪≫
      unitIso I D j U R a (W.groupified a) (W.laws a)

def baseProductValue (a : AffinePoint R.stack) (p q : Groupification (A.obj.obj (op U))) :
    moduleTensor a.obj.base.left ((value I D j U R W a).obj (baseWeight j U p))
      ((value I D j U R W a).obj (baseWeight j U q)) ≅
        (value I D j U R W a).obj (baseWeight j U (p*q)) :=
  multiplicationIso I D j U R a (W.groupified a) (W.laws a) (baseWeight j U p) (baseWeight j U q) ≪≫
    eqToIso (congrArg (value I D j U R W a).obj (by
      apply Weight.ext; exact (map_mul (groupMap (j.hom.app (op U)).hom) p q).symm))

/-- The actual groupified root restriction, with every positive generator,
unit and multiplication fixed as scheme-module maps. -/
structure BaseFamilyComparison where
  comparison : ∀ (p : Groupification (A.obj.obj (op U))) (a : AffinePoint R.stack),
    (Scheme.Modules.pullback a.obj.base.hom).obj ((G.chart U).line p) ≅
      (value I D j U R W a).obj (baseWeight j U p)
  pullbackTensor : ∀ a : AffinePoint R.stack, PullbackTensorData a.obj.base.hom
  positive : ∀ (a : AffinePoint R.stack) (m : A.obj.obj (op U)),
    (comparison (Algebra.GrothendieckGroup.of m) a).hom =
      (Scheme.Modules.pullback a.obj.base.hom).map ((G.chart U).positive m).hom ≫
      (positiveBaseLine I D j U a.obj.base (rootObject I D j U R a) m).hom ≫
        (positiveValue I D j U R W a m).inv
  unit : ∀ a : AffinePoint R.stack,
    (comparison 1 a).hom ≫ (baseUnitValue I D j U R W a).hom =
      (Scheme.Modules.pullback a.obj.base.hom).map (G.chart U).unit.hom ≫
        SheafOfModules.pullbackObjUnitToUnit a.obj.base.hom.toRingCatSheafHom
  multiplication : ∀ (a : AffinePoint R.stack) (p q : Groupification (A.obj.obj (op U))),
    (Scheme.Modules.pullback a.obj.base.hom).map ((G.chart U).multiplication p q).hom ≫
      (comparison (p*q) a).hom =
    ((pullbackTensor a).comparison ((G.chart U).line p) ((G.chart U).line q)).hom ≫
      tensorMap (comparison p a).hom (comparison q a).hom ≫ (baseProductValue I D j U R W a p q).hom

structure BaseLift where
  quasicoherent : ∀ p : Groupification (A.obj.obj (op U)),
    SheafOfModules.IsQuasicoherent (R := U.left.ringCatSheaf) ((G.chart U).line p)
  family : BaseFamilyComparison I D j G U R W

namespace BaseLift

variable {I D j G U R W} (L : BaseLift I D j G U R W)
  {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
  (K : ModuleDictionary S)

def object (p : Groupification (A.obj.obj (op U))) : QCoh S.stack :=
  K.equivalence.inverse.obj ⟨(G.chart U).line p, L.quasicoherent p⟩

def moduleIso (p : Groupification (A.obj.obj (op U))) :
    K.toModules.obj (L.object K p) ≅ (G.chart U).line p :=
  (schemeQCohForget U.left).mapIso (K.equivalence.counitIso.app ⟨(G.chart U).line p,L.quasicoherent p⟩)

def sections (P : RootStackProjectionModules.Projection I D j U R S)
    (p : Groupification (A.obj.obj (op U))) (a : AffinePoint R.stack)
    (x : ((pullback P.morphism).obj (L.object K p)).obj.obj (op a)) :
    Γ((Scheme.Modules.pullback a.obj.base.hom).obj ((G.chart U).line p),⊤) :=
  ((((Scheme.Modules.pullback a.obj.base.hom).map (L.moduleIso K p).hom).val.app (op ⊤)).hom)
    ((((eqToHom (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj (K.toModules.obj (L.object K p)))
      (P.test_normalization a))).val.app (op ⊤)).hom)
        (K.sections (L.object K p) ((affineMap P.morphism).obj a) x))

end BaseLift

variable {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
  (P : RootStackProjectionModules.Projection I D j U R S) (Q : DirectImage P.morphism)
  (K : ModuleDictionary S) (TS : TensorLanding S.stack)
  (DK : TensorDictionary S K TS) (WT : WeightTensor I D j U R W T)
  (L : BaseLift I D j G U R W)

/-- The source base-line and projection-formula certificate on their
fixed native maps. No Phi equivalence or tensor-preservation theorem is input. -/
structure PeriodData where
  base : ∀ p : Groupification (A.obj.obj (op U)),
    (pullback P.morphism).obj (L.object K p) ≅ W.line.obj (baseWeight j U p)
  base_normalized : ∀ (p : Groupification (A.obj.obj (op U))) (a : AffinePoint R.stack)
    (x : ((pullback P.morphism).obj (L.object K p)).obj.obj (op a)),
    W.sections (baseWeight j U p) a ((base p).hom.hom.app (op a) x) =
      (((L.family.comparison p a).hom.val.app (op ⊤)).hom (L.sections K P p a x))
  projection : ∀ (p : Groupification (A.obj.obj (op U))) (F : QCoh R.stack),
    IsIso (CartesianStackTensorComparisons.projectionFormula T P.morphism TS Q (L.object K p) F)

namespace PeriodData

variable {I D j G U R W T P Q K TS DK WT L}
  (H : PeriodData I D j G U R W T P Q K TS L)

def rootPeriod (F : QCoh R.stack) (p : Groupification (A.obj.obj (op U)))
    (w : Weight (B.obj.obj (op U))) :
    ((CartesianStackTensorProducts.tensor R.stack T).obj F).obj
        (W.line.obj (shift (j.hom.app (op U)).hom p w)) ≅
      ((CartesianStackTensorProducts.tensor R.stack T).obj ((pullback P.morphism).obj (L.object K p))).obj
        (((CartesianStackTensorProducts.tensor R.stack T).obj F).obj (W.line.obj w)) := by
  letI := CartesianStackTensorComparisons.monoidal R.stack T
  exact whiskerLeftIso F (WT.multiplication (baseWeight j U p) w).symm ≪≫
    (α_ F (W.line.obj (baseWeight j U p)) (W.line.obj w)).symm ≪≫
    whiskerRightIso (β_ F (W.line.obj (baseWeight j U p))) (W.line.obj w) ≪≫
    (α_ (W.line.obj (baseWeight j U p)) F (W.line.obj w)) ≪≫
    whiskerRightIso (H.base p).symm (F ⊗ W.line.obj w)

def recipe (F : QCoh R.stack) (p : Groupification (A.obj.obj (op U)))
    (w : Weight (B.obj.obj (op U))) :
    (RootStackProjectionModules.directImageToModules I D j U R P Q K).obj
      (((CartesianStackTensorProducts.tensor R.stack T).obj F).obj
        (W.line.obj (shift (j.hom.app (op U)).hom p w))) ≅
    moduleTensor U.left ((G.chart U).line p)
      ((RootStackProjectionModules.directImageToModules I D j U R P Q K).obj
        (((CartesianStackTensorProducts.tensor R.stack T).obj F).obj (W.line.obj w))) := by
  letI := H.projection p (((CartesianStackTensorProducts.tensor R.stack T).obj F).obj (W.line.obj w))
  exact (RootStackProjectionModules.directImageToModules I D j U R P Q K).mapIso (H.rootPeriod (WT := WT) F p w) ≪≫
    K.toModules.mapIso (asIso (CartesianStackTensorComparisons.projectionFormula T P.morphism TS Q
      (L.object K p) (((CartesianStackTensorProducts.tensor R.stack T).obj F).obj (W.line.obj w)))).symm ≪≫
    DK.tensor (L.object K p) (Q.functor.obj (((CartesianStackTensorProducts.tensor R.stack T).obj F).obj (W.line.obj w))) ≪≫
    sheafTensorIso (L.moduleIso K p) (Iso.refl _)

end PeriodData

end MathlibExt.AlgebraicGeometry.RootParabolicPeriodModels

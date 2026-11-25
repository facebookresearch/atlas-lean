/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
public import MathlibExt.AlgebraicGeometry.DenominatorRootFamilies

/-!
# Deligne--Faltings inverse-image contracts on native small sites

The monoid inverse image is the native site adjoint. Every comparison of
pulled lines is fixed on its actual adjunction-unit generators, including
sections, multiplication, units and cartesian arrows. The generators locally
present the inverse image; no independently assigned monoid or line operation
stands in for pullback. The geometric construction is Proposition3.9 of
Borne--Vistoli, arXiv:1001.0466v2, with its adjunction in Remark3.11.
The ordinary tensor-pullback comparisons are source-covered in AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b, ModulePullbackTensor.lean (Apache2.0).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImages
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
universe u

lemma generator_naturality {X T : Scheme.{u}} (f : T ⟶ X) [HasInverseImage f]
    (A : DeligneFaltingsSheaves.MonoidSheaf X) {U V : X.Etale} (a : V ⟶ U) (p : A.obj.obj (op U)) :
    ((monoidPullback f).obj A).obj.map ((etaleBaseChange f).map a).op
      (generator f A U p) = generator f A V (A.obj.map a.op p) := by
  exact (ConcreteCategory.congr_hom
    (((adjunction f).unit.app A).hom.naturality a.op) p).symm

lemma projection_naturality {X T : Scheme.{u}} (f : T ⟶ X)
    {U V : X.Etale} (a : V ⟶ U) :
    ((etaleBaseChange f).map a).left ≫ projection f U = projection f V ≫ a.left := by
  exact SmallEtaleGeometry.projection_naturality f a

/-- Source-normalized inverse images of actual DF structures. The module
comparison is tested on every generator and every source etale arrow. -/
structure PullbackData {X T : Scheme.{u}} {A : DeligneFaltingsSheaves.MonoidSheaf X}
    (D : Structure A) (f : T ⟶ X) [HasInverseImage f] where
  pulled : Structure ((monoidPullback f).obj A)
  tensorPullback : ∀ U : X.Etale, PullbackTensorData (projection f U)
  comparison : ∀ (U : X.Etale) (a : A.obj.obj (op U)),
    (Scheme.Modules.pullback (projection f U)).obj ((D.chart U).module a) ≅
      (pulled.chart ((etaleBaseChange f).obj U)).module (generator f A U a)
  section_eq : ∀ U a,
    pullbackSection (projection f U) ((D.chart U).sectionMap a) ≫ (comparison U a).hom =
      (pulled.chart ((etaleBaseChange f).obj U)).sectionMap (generator f A U a)
  unit : ∀ U,
    (comparison U 1).hom ≫ eqToHom (congrArg
      (pulled.chart ((etaleBaseChange f).obj U)).module (map_one (generator f A U))) ≫
      (pulled.chart ((etaleBaseChange f).obj U)).unit.hom =
    (Scheme.Modules.pullback (projection f U)).map (D.chart U).unit.hom ≫
      SheafOfModules.pullbackObjUnitToUnit (projection f U).toRingCatSheafHom
  multiplication : ∀ U a b,
    (Scheme.Modules.pullback (projection f U)).map ((D.chart U).multiplication a b).hom ≫
      (comparison U (a*b)).hom =
    ((tensorPullback U).comparison ((D.chart U).module a) ((D.chart U).module b)).hom ≫
      tensorMap (comparison U a).hom (comparison U b).hom ≫
      ((pulled.chart ((etaleBaseChange f).obj U)).multiplication
        (generator f A U a) (generator f A U b)).hom ≫
      eqToHom (congrArg (pulled.chart ((etaleBaseChange f).obj U)).module
        (map_mul (generator f A U) a b).symm)
  cartesian : ∀ {U V : X.Etale} (a : V ⟶ U) (p : A.obj.obj (op U)),
    (Scheme.Modules.pullback (projection f V)).map (D.reindex a p).hom ≫
      (comparison V (A.obj.map a.op p)).hom =
    (Scheme.Modules.pullbackComp (projection f V) a.left).hom.app ((D.chart U).module p) ≫
      eqToHom (congrArg (fun h => (Scheme.Modules.pullback h).obj ((D.chart U).module p))
        (projection_naturality f a).symm) ≫
      (Scheme.Modules.pullbackComp ((etaleBaseChange f).map a).left (projection f U)).inv.app
        ((D.chart U).module p) ≫
      (Scheme.Modules.pullback ((etaleBaseChange f).map a).left).map (comparison U p).hom ≫
      (pulled.reindex ((etaleBaseChange f).map a) (generator f A U p)).hom ≫
      eqToHom (congrArg (pulled.chart ((etaleBaseChange f).obj V)).module
        (generator_naturality f A a p))

end MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImages

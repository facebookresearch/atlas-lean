/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralCoverDescentModels

/-!
# The actual Cartan quotient and K-valued cameral value

The Cartan morphism is the G descent of the literal universal Borel
quotient on the incidence cover. It is a module morphism; no invertible
comparison with the centralizer bundle is imposed on ramified fibres.
The value section is computed from the native c tensor K section. Its
scheme-valued realization represents actual pulled module sections on
every test scheme and is fixed by the pulled tautological section.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Proposition 12.5 and
Sections 17.3--17.8. The section total space is V(M dual), with the
section convention of the native module-sheaf representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralCartanValueModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralIncidenceModels CameralRamificationReindexing
open CameralRegularizedHiggsModels CameralCoverDescentModels CameralRamificationTensorModels
open GroupTorsorGeometry ExpansionParameterModels CoherentCurveLinearSeries
open LineBundleTaskContracts AlgebraicLineBundleFamilies RelativeLambdaReindexing

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

abbrev cartanModule (X : Over (Spec (.of ℂ))) := scalarModule X (.of ℂ (Fin F.rank → ℂ))

def scalarPullback {Y Y' : Over (Spec (.of ℂ))} (f : Y' ⟶ Y) (M : ModuleCat ℂ) :
    (Scheme.Modules.pullback f.left).obj (scalarModule Y M) ≅ scalarModule Y' M :=
  (Scheme.Modules.pullbackComp f.left Y.hom).app ((tilde.functor (.of ℂ)).obj M) ≪≫
    (Scheme.Modules.pullbackCongr f.w).app ((tilde.functor (.of ℂ)).obj M)

variable (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} {K : TwistLine X}
  (H : RegularizedBundle F X K) (D : CoverDescent F I H.regularizer)

theorem incidenceMap_parameter : incidenceMap F I H.regularizer D ≫ universalProjection F I =
    pullback.snd (projection F D.cameral) H.regularizer.torsor.projection ≫ H.regularizer.map := by
  rw [incidenceMap, Category.assoc, pullback.condition, ← Category.assoc, D.over_torsor]

def universalCentralizerComparison :
    (Scheme.Modules.pullback (incidenceMap F I H.regularizer D).left).obj
      (centralizerModule I.incidence) ≅
    (Scheme.Modules.pullback
      (pullback.fst (projection F D.cameral) H.regularizer.torsor.projection).left).obj
      ((Scheme.Modules.pullback (projection F D.cameral).left).obj H.centralizer.module) :=
  (Scheme.Modules.pullbackComp (incidenceMap F I H.regularizer D).left
    (universalProjection F I).left).app _ ≪≫
  (Scheme.Modules.pullbackCongr
    (congrArg (fun f : pullback (projection F D.cameral) H.regularizer.torsor.projection ⟶
      F.centralizers.scheme => f.left) (incidenceMap_parameter F I H D))).app _ ≪≫
  (Scheme.Modules.pullbackComp
    (pullback.snd (projection F D.cameral) H.regularizer.torsor.projection).left
    H.regularizer.map.left).symm.app _ ≪≫
  (Scheme.Modules.pullback
    (pullback.snd (projection F D.cameral) H.regularizer.torsor.projection).left).mapIso
      H.centralizer.trivialization.symm ≪≫
  (Scheme.Modules.pullbackComp
    (pullback.snd (projection F D.cameral) H.regularizer.torsor.projection).left
    H.regularizer.torsor.projection.left).app _ ≪≫
  (Scheme.Modules.pullbackCongr
    (congrArg (fun f : pullback (projection F D.cameral)
      H.regularizer.torsor.projection ⟶ X => f.left)
      (pullback.condition (f := projection F D.cameral)
        (g := H.regularizer.torsor.projection)).symm)).app _ ≪≫
  (Scheme.Modules.pullbackComp
    (pullback.fst (projection F D.cameral) H.regularizer.torsor.projection).left
    (projection F D.cameral).left).symm.app _

structure CartanDescent where
  quotient : (Scheme.Modules.pullback (projection F D.cameral).left).obj H.centralizer.module ⟶
    cartanModule F (total F D.cameral)
  normalized :
    (Scheme.Modules.pullback
      (pullback.fst (projection F D.cameral) H.regularizer.torsor.projection).left).map quotient ≫
      (scalarPullback
        (pullback.fst (projection F D.cameral) H.regularizer.torsor.projection)
        (.of ℂ (Fin F.rank → ℂ))).hom =
    (universalCentralizerComparison F I H D).inv ≫
      (Scheme.Modules.pullback (incidenceMap F I H.regularizer D).left).map I.value.quotient ≫
      (scalarPullback (incidenceMap F I H.regularizer D) (.of ℂ (Fin F.rank → ℂ))).hom

abbrev cartanKModule (Y : Over (Spec (.of ℂ))) (L : TwistLine Y) :=
  moduleTensor Y.left (cartanModule F Y) L.module

def cartanAction (Y : Over (Spec (.of ℂ))) (w : F.Weyl) :
    cartanModule F Y ≅ cartanModule F Y :=
  (Scheme.Modules.pullback Y.hom).mapIso
    ((tilde.functor (.of ℂ)).mapIso (F.action.linear w).toModuleIso)

def cartanKAction (Y : Over (Spec (.of ℂ))) (L : TwistLine Y) (w : F.Weyl) :
    cartanKModule F Y L ≅ cartanKModule F Y L where
  hom := tensorMap (cartanAction F Y w).hom (𝟙 L.module)
  inv := tensorMap (cartanAction F Y w).inv (𝟙 L.module)
  hom_inv_id := by
    rw [← tensorMap_comp, Iso.hom_inv_id, Category.id_comp, tensorMap_id]
  inv_hom_id := by
    rw [← tensorMap_comp, Iso.inv_hom_id, Category.id_comp, tensorMap_id]

structure SectionSpace (Y : Over (Spec (.of ℂ))) (M : Y.left.Modules) where
  total : Over Y.left
  points : ∀ U : Over Y.left, (U ⟶ total) ≃ Section ((Scheme.Modules.pullback U.hom).obj M)
  naturality : ∀ {U V : Over Y.left} (f : V ⟶ U) (g : U ⟶ total),
    points V (f ≫ g) =
      pullbackSection f.left (points U g) ≫
        (Scheme.Modules.pullbackComp f.left U.hom).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Over.w f)).hom.app M

def tautological {Y : Over (Spec (.of ℂ))} {M : Y.left.Modules} (S : SectionSpace Y M) :
    Section ((Scheme.Modules.pullback S.total.hom).obj M) := S.points S.total (𝟙 S.total)

def sectionTotal {Y : Over (Spec (.of ℂ))} {M : Y.left.Modules} (S : SectionSpace Y M) :
    Over (Spec (.of ℂ)) := (Over.map Y.hom).obj S.total

def sectionProjection {Y : Over (Spec (.of ℂ))} {M : Y.left.Modules} (S : SectionSpace Y M) :
    sectionTotal S ⟶ Y := Over.homMk S.total.hom rfl

variable (Q : CartanDescent F I H D) (T : TensorPullbackComparison (projection F D.cameral).left)

def valueSection : Section
    (moduleTensor (total F D.cameral).left (cartanModule F (total F D.cameral))
      ((Scheme.Modules.pullback (projection F D.cameral).left).obj K.module)) :=
  pullbackSection (projection F D.cameral).left H.sectionMap ≫
    (T.iso H.centralizer.module K.module).hom ≫ tensorMap Q.quotient (𝟙 _)

def cartanKPullback : (Scheme.Modules.pullback (projection F D.cameral).left).obj
    (cartanKModule F X K) ≅
    moduleTensor (total F D.cameral).left (cartanModule F (total F D.cameral))
      ((Scheme.Modules.pullback (projection F D.cameral).left).obj K.module) :=
  T.iso (cartanModule F X) K.module ≪≫
    { hom := tensorMap (scalarPullback (projection F D.cameral) (.of ℂ (Fin F.rank → ℂ))).hom (𝟙 _)
      inv := tensorMap (scalarPullback (projection F D.cameral) (.of ℂ (Fin F.rank → ℂ))).inv (𝟙 _)
      hom_inv_id := by
        rw [← tensorMap_comp, Iso.hom_inv_id, Category.id_comp, tensorMap_id]
      inv_hom_id := by
        rw [← tensorMap_comp, Iso.inv_hom_id, Category.id_comp, tensorMap_id] }

def valueMap (S : SectionSpace X (cartanKModule F X K)) :
    total F D.cameral ⟶ sectionTotal S :=
  (Over.map X.hom).map
    ((S.points (Over.mk (projection F D.cameral).left)).symm
      (valueSection F I H D Q T ≫ (cartanKPullback F I H D T).inv))

def valueSectionOf (s : Section (moduleTensor X.left H.centralizer.module K.module)) : Section
    (moduleTensor (total F D.cameral).left (cartanModule F (total F D.cameral))
      ((Scheme.Modules.pullback (projection F D.cameral).left).obj K.module)) :=
  pullbackSection (projection F D.cameral).left s ≫
    (T.iso H.centralizer.module K.module).hom ≫ tensorMap Q.quotient (𝟙 _)

def valueMapOf (S : SectionSpace X (cartanKModule F X K))
    (s : Section (moduleTensor X.left H.centralizer.module K.module)) :
    total F D.cameral ⟶ sectionTotal S :=
  (Over.map X.hom).map ((S.points (Over.mk (projection F D.cameral).left)).symm
    (valueSectionOf F I H D Q T s ≫ (cartanKPullback F I H D T).inv))

theorem valueMapOf_over (S : SectionSpace X (cartanKModule F X K))
    (s : Section (moduleTensor X.left H.centralizer.module K.module)) :
    valueMapOf F I H D Q T S s ≫ sectionProjection S = projection F D.cameral := by
  apply Over.OverMorphism.ext
  exact ((S.points (Over.mk (projection F D.cameral).left)).symm
    (valueSectionOf F I H D Q T s ≫ (cartanKPullback F I H D T).inv)).w

def schemeWeylMap (Y : Over (Spec (.of ℂ))) (L : TwistLine Y)
    (S : SectionSpace Y (cartanKModule F Y L)) (w : F.Weyl) : sectionTotal S ⟶ sectionTotal S :=
  (Over.map Y.hom).map ((S.points S.total).symm
    (tautological S ≫ (Scheme.Modules.pullback S.total.hom).map (cartanKAction F Y L w).hom))

structure CartanWeylAction (Y : Over (Spec (.of ℂ))) (L : TwistLine Y)
    (S : SectionSpace Y (cartanKModule F Y L)) where
  action : F.Weyl →* Aut (sectionTotal S)
  normalized : ∀ w : F.Weyl, (action w).asIso.hom = schemeWeylMap F Y L S w

structure EquivariantValue (S : SectionSpace X (cartanKModule F X K))
    (W : CartanWeylAction F X K S) where
  map : total F D.cameral ⟶ sectionTotal S
  over : map ≫ sectionProjection S = projection F D.cameral
  equivariant : ∀ w : F.Weyl,
    (coverIso F D.cameral w).hom ≫ map = map ≫ (W.action w).asIso.hom

structure ValueCorrespondence (S : SectionSpace X (cartanKModule F X K))
    (W : CartanWeylAction F X K S) where
  sections : Section (moduleTensor X.left H.centralizer.module K.module) ≃
    EquivariantValue F I H D S W
  normalized : ∀ s : Section (moduleTensor X.left H.centralizer.module K.module),
    (sections s).map = valueMapOf F I H D Q T S s

end MathlibExt.AlgebraicGeometry.CameralCartanValueModels

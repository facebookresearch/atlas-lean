/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRegularizedHiggsModels
public import MathlibExt.AlgebraicGeometry.CameralMarkedRegularizers

/-!
# Arrows and pullbacks of regularized Higgs families

The arrows below are the actual G-torsor and module isomorphisms. Both
trivializations, the centralizer inclusion and the K-valued section are
preserved. Pullback comparisons retain the actual original torsor map
and the entire pulled section, including nonreduced coefficient tests.
Source: Donagi--Gaitsgory math/0005132v3, Sections17.1--17.7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralHiggsCategoryModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralRamificationReindexing
open GroupTorsorGeometry ExpansionParameterModels
open CoherentCurveLinearSeries LineBundleTaskContracts
open AlgebraicLineBundleFamilies RelativeLambdaReindexing

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  {X : Over (Spec (.of ℂ))} {K : TwistLine X}

attribute [local instance] centralizerGroupAction

@[ext] theorem hom_ext {H H' : RegularizedBundle F X K}
    (a b : CameralRegularizedHiggsModels.Hom F H H')
    (hR : a.regularizer = b.regularizer) (hA : a.adjoint = b.adjoint)
    (hC : a.centralizer = b.centralizer) : a = b := by
  cases a
  cases b
  cases hR
  cases hA
  cases hC
  rfl

structure ArrowMaps (H H' : RegularizedBundle F X K) where
  regularizer : H.regularizer ⟶ H'.regularizer
  adjoint : H.adjoint.module ≅ H'.adjoint.module
  centralizer : H.centralizer.module ≅ H'.centralizer.module
  inclusion : centralizer.hom ≫ H'.centralizer.inclusion =
    H.centralizer.inclusion ≫ adjoint.hom
  sectionMap : H.sectionMap ≫ tensorMap centralizer.hom (𝟙 K.module) = H'.sectionMap

structure IsNormalized {H H' : RegularizedBundle F X K}
    (a : ArrowMaps F H H') : Prop where
  adjoint :
    (Scheme.Modules.pullback H.regularizer.torsor.projection.left).map a.adjoint.hom ≫
      (baseComparison F a.regularizer H'.adjoint.module).hom ≫
      (Scheme.Modules.pullback a.regularizer.iso.hom.left).map H'.adjoint.trivialization.hom =
    H.adjoint.trivialization.hom ≫
      (targetComparison F a.regularizer
        (RegularCentralizerAffineModels.lieModule F.lie.carrier F.centralizers.scheme)).hom
  centralizer :
    (Scheme.Modules.pullback H.regularizer.torsor.projection.left).map a.centralizer.hom ≫
      (baseComparison F a.regularizer H'.centralizer.module).hom ≫
      (Scheme.Modules.pullback a.regularizer.iso.hom.left).map
        H'.centralizer.trivialization.hom =
    H.centralizer.trivialization.hom ≫
      (targetComparison F a.regularizer F.centralizers.universal).hom

def arrowMaps {H H' : RegularizedBundle F X K}
    (a : CameralRegularizedHiggsModels.Hom F H H') : ArrowMaps F H H' where
  regularizer := a.regularizer
  adjoint := a.adjoint
  centralizer := a.centralizer
  inclusion := a.inclusion
  sectionMap := a.sectionMap

def normalizedHom {H H' : RegularizedBundle F X K} (a : ArrowMaps F H H')
    (h : IsNormalized F a) : CameralRegularizedHiggsModels.Hom F H H' where
  regularizer := a.regularizer
  adjoint := a.adjoint
  centralizer := a.centralizer
  adjoint_normalized := h.adjoint
  centralizer_normalized := h.centralizer
  inclusion := a.inclusion
  sectionMap := a.sectionMap

def identityMaps (H : RegularizedBundle F X K) : ArrowMaps F H H where
  regularizer := 𝟙 H.regularizer
  adjoint := Iso.refl _
  centralizer := Iso.refl _
  inclusion := by simp
  sectionMap := by rw [Iso.refl_hom, tensorMap_id, Category.comp_id]

def compositionMaps {H H' H'' : RegularizedBundle F X K}
    (a : ArrowMaps F H H') (b : ArrowMaps F H' H'') : ArrowMaps F H H'' where
  regularizer := a.regularizer ≫ b.regularizer
  adjoint := a.adjoint ≪≫ b.adjoint
  centralizer := a.centralizer ≪≫ b.centralizer
  inclusion := by
    simp only [Iso.trans_hom, Category.assoc, b.inclusion]
    rw [← Category.assoc, a.inclusion, Category.assoc]
  sectionMap := by
    rw [Iso.trans_hom, ← Category.comp_id (𝟙 K.module), tensorMap_comp,
      ← Category.assoc, a.sectionMap, b.sectionMap]

/-- The condition that identity and composite arrows of regularized Higgs bundles on $X$ twisted by
the line bundle $K$ are normalized: for every bundle $H$, the identity arrow data of $H$ (identity
map of regularizers and identity module isomorphisms) is normalized, and for all arrows
$a : H \to H'$ and $b : H' \to H''$, the composite arrow data of $a$ and $b$ is normalized. Arrow
data is normalized when its isomorphisms of adjoint modules and of centralizer modules, pulled back
to the torsors, are compatible with the trivializations of those modules. -/
structure CategoryCoherence : Prop where
  identity : ∀ H : RegularizedBundle F X K, IsNormalized F (identityMaps F H)
  composition : ∀ {H H' H'' : RegularizedBundle F X K}
    (a : CameralRegularizedHiggsModels.Hom F H H')
    (b : CameralRegularizedHiggsModels.Hom F H' H''),
    IsNormalized F (compositionMaps F (arrowMaps F a) (arrowMaps F b))

variable (L : CategoryCoherence F (X := X) (K := K))

def idHom (H : RegularizedBundle F X K) :
    CameralRegularizedHiggsModels.Hom F H H :=
  normalizedHom F (identityMaps F H) (L.identity H)

def compHom {H H' H'' : RegularizedBundle F X K}
    (a : CameralRegularizedHiggsModels.Hom F H H')
    (b : CameralRegularizedHiggsModels.Hom F H' H'') :
    CameralRegularizedHiggsModels.Hom F H H'' :=
  normalizedHom F (compositionMaps F (arrowMaps F a) (arrowMaps F b))
    (L.composition a b)

@[instance_reducible] def category : Category (RegularizedBundle F X K) where
  Hom := CameralRegularizedHiggsModels.Hom F
  id := idHom F L
  comp := compHom F L
  id_comp a := by
    apply hom_ext
    · exact Category.id_comp a.regularizer
    · exact Iso.refl_trans a.adjoint
    · exact Iso.refl_trans a.centralizer
  comp_id a := by
    apply hom_ext
    · exact Category.comp_id a.regularizer
    · exact Iso.trans_refl a.adjoint
    · exact Iso.trans_refl a.centralizer
  assoc a b c := by
    apply hom_ext
    · exact Category.assoc a.regularizer b.regularizer c.regularizer
    · exact Iso.trans_assoc a.adjoint b.adjoint c.adjoint
    · exact Iso.trans_assoc a.centralizer b.centralizer c.centralizer

/-- The line in a reindexed family is the literal pulled module. -/
def pulledTwist {Y : Over (Spec (.of ℂ))} (f : Y ⟶ X)
    (h : IsLineBundle ((Scheme.Modules.pullback f.left).obj K.module)) : TwistLine Y where
  module := (Scheme.Modules.pullback f.left).obj K.module
  line := h

def originalModuleComparison {Y : Over (Spec (.of ℂ))} (f : Y ⟶ X)
    {P : Regularizer F X} (r : Reindex G P.torsor f) (M : X.left.Modules) :
    (Scheme.Modules.pullback r.torsor.projection.left).obj
      ((Scheme.Modules.pullback f.left).obj M) ≅
    (Scheme.Modules.pullback (r.original G).left).obj
      ((Scheme.Modules.pullback P.torsor.projection.left).obj M) :=
  (Scheme.Modules.pullbackComp r.torsor.projection.left f.left).app M ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left r.square.symm)).app M ≪≫
    (Scheme.Modules.pullbackComp (r.original G).left P.torsor.projection.left).symm.app M

structure PullbackBundle {Y : Over (Spec (.of ℂ))} (f : Y ⟶ X)
    (hK : IsLineBundle ((Scheme.Modules.pullback f.left).obj K.module))
    (H : RegularizedBundle F X K) (r : Reindex G H.regularizer.torsor f)
    (T : TensorPullbackComparison f.left) where
  adjointBundle : AdjointBundle F (reindexObject G F.centralizers.scheme H.regularizer f r)
  centralizerBundle : CentralizerBundle F
    (reindexObject G F.centralizers.scheme H.regularizer f r) adjointBundle
  sectionData : Section (moduleTensor Y.left centralizerBundle.module
    ((Scheme.Modules.pullback f.left).obj K.module))
  adjoint : adjointBundle.module ≅ (Scheme.Modules.pullback f.left).obj H.adjoint.module
  centralizer : centralizerBundle.module ≅
    (Scheme.Modules.pullback f.left).obj H.centralizer.module
  inclusion : centralizerBundle.inclusion ≫ adjoint.hom =
    centralizer.hom ≫ (Scheme.Modules.pullback f.left).map H.centralizer.inclusion
  section_normalized : sectionData ≫ tensorMap centralizer.hom (𝟙 _) =
    pullbackSection f.left H.sectionMap ≫ (T.iso H.centralizer.module K.module).hom
  adjoint_trivialization :
    (Scheme.Modules.pullback r.torsor.projection.left).map adjoint.hom ≫
      (originalModuleComparison F f r H.adjoint.module).hom ≫
      (Scheme.Modules.pullback (r.original G).left).map H.adjoint.trivialization.hom =
    adjointBundle.trivialization.hom ≫
      (Scheme.Modules.pullbackComp (r.original G).left H.regularizer.map.left).inv.app
        (RegularCentralizerAffineModels.lieModule F.lie.carrier F.centralizers.scheme)
  centralizer_trivialization :
    (Scheme.Modules.pullback r.torsor.projection.left).map centralizer.hom ≫
      (originalModuleComparison F f r H.centralizer.module).hom ≫
      (Scheme.Modules.pullback (r.original G).left).map H.centralizer.trivialization.hom =
    centralizerBundle.trivialization.hom ≫
      (Scheme.Modules.pullbackComp (r.original G).left H.regularizer.map.left).inv.app
        F.centralizers.universal

def PullbackBundle.bundle {Y : Over (Spec (.of ℂ))} {f : Y ⟶ X}
    {hK : IsLineBundle ((Scheme.Modules.pullback f.left).obj K.module)}
    {H : RegularizedBundle F X K} {r : Reindex G H.regularizer.torsor f}
    {T : TensorPullbackComparison f.left} (P : PullbackBundle F f hK H r T) :
    RegularizedBundle F Y (pulledTwist f hK) where
  regularizer := reindexObject G F.centralizers.scheme H.regularizer f r
  adjoint := P.adjointBundle
  centralizer := P.centralizerBundle
  sectionMap := P.sectionData

end MathlibExt.AlgebraicGeometry.CameralHiggsCategoryModels

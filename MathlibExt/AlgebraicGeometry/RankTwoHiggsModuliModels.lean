/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoHiggsCurveFamilies
public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

/-!
# Actual coarse rank-two degree-one Higgs moduli

Class maps act on the actual stable-family groupoids and commute with
their actual reindexing. Their universal property tests all compatible
maps to actual schemes. The universal Higgs family is an actual family;
every family is its literal pullback tensored with a line from its base.
This retains scalar automorphisms and the unavoidable base-line twist.
No identification with a discrete family groupoid is assumed.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.2; the coprime rank/degree universal-family
construction for stable Higgs bundles.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RankTwoHiggsModuliModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open RankTwoHiggsCurveFamilies GeometricHiggsFamilies
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies LineBundleTaskContracts
open NativeTensorComparisons SheafTensorSections

variable (C : ComplexScheme) (B : BaseChanges C)

structure ClassMaps (Y : ComplexScheme) where
  map : ∀ T : ComplexScheme, StableFamily C T → (T ⟶ Y)
  arrows : ∀ (T : ComplexScheme) {E E' : StableFamily C T} (_a : E ⟶ E'), map T E = map T E'
  naturality : ∀ {S T : ComplexScheme} (f : S ⟶ T) (E : StableFamily C T),
    map S ((B.change f).obj E) = f ≫ map T E

def baseLine (T : ComplexScheme) (L : T.left.Modules) : (prod C T).left.Modules :=
  (Scheme.Modules.pullback (prod.snd : prod C T ⟶ T).left).obj L

def baseLineField {T : ComplexScheme} (E : Family C T) (L : T.left.Modules) :
    moduleTensor (prod C T).left E.module (baseLine C T L) ⟶
      moduleTensor (prod C T).left
        (moduleTensor (prod C T).left E.module (baseLine C T L))
        ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C)) :=
  tensorMap E.field (𝟙 (baseLine C T L)) ≫
    (tensorAssociator (prod C T).left E.module
      ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C))
      (baseLine C T L)).hom ≫
    tensorMap (𝟙 E.module)
      (tensorCommutor (prod C T).left
        ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C))
        (baseLine C T L)).hom ≫
    (tensorAssociator (prod C T).left E.module (baseLine C T L)
      ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C))).inv

structure BaseLineComparison {T : ComplexScheme} (E E' : Family C T) (L : T.left.Modules) where
  line : IsLineBundle L
  comparison : E.module ≅ moduleTensor (prod C T).left E'.module (baseLine C T L)
  field : comparison.hom ≫ baseLineField C E' L = E.field ≫ tensorMap comparison.hom
    (𝟙 ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C)))

structure ModuliModel where
  scheme : ComplexScheme
  variety : PerverseSheaves.IsComplexVariety scheme
  smooth : Smooth scheme.hom
  quasiProjective : ∃ n : ℕ, ∃ j : scheme ⟶ ProjectiveSpace.projectiveSpace ℂ n,
    IsImmersion j.left
  classes : ClassMaps C B scheme
  universalFamily : StableFamily C scheme
  universal_class : classes.map scheme universalFamily = 𝟙 scheme
  family_normalization : ∀ (T : ComplexScheme) (E : StableFamily C T),
    ∃ L : T.left.Modules,
      Nonempty (BaseLineComparison C E.obj
        ((B.change (classes.map T E)).obj universalFamily).obj L)
  universal : ∀ (Y : ComplexScheme) (F : ClassMaps C B Y),
    ∃! h : scheme ⟶ Y, ∀ (T : ComplexScheme) (E : StableFamily C T),
      classes.map T E ≫ h = F.map T E

end MathlibExt.AlgebraicGeometry.RankTwoHiggsModuliModels

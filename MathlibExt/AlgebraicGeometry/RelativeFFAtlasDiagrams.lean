/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies
public import MathlibExt.AlgebraicGeometry.RelativePerfectoidBases
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# The actual affine-overlap gluing diagram of a global FF curve

Overlap tests are actual residue-linear affine maps into two original
perfectoid atlas charts whose maps to the source space agree. Their
curve maps are the displayed relative FF base-change maps. The native
multispan and multicofork therefore impose exactly these geometric
identifications. A colimiting model cannot identify additional chart
components merely because an overlap condition is vacuous.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and II.1;
the generic multispan/colimit construction is native Mathlib.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeFFAtlasDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open LocalWittCoefficientFields LocalCoefficientScalarFrames RelativeFarguesFontaineRings
open RelativeFarguesFontaineMaps RelativeFFCurveFamilies RelativePerfectoidBases
open PerfectoidDiamondModels AnalyticGroupTorsorSites

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (I : IntegerPresentation p C) (A : RelativeFFCurveFamilies.Family p C I)
  {S : RelativePerfectoidBases.Space p C} (L : LabelledAtlas p C S)

structure Overlap where
  left : S.perfectoid.atlas.index
  right : S.perfectoid.atlas.index
  base : Base p C
  first : base ⟶ L.base left
  second : base ⟶ L.base right
  square : affineMap p first.val ≫ L.chart p C left =
    affineMap p second.val ≫ L.chart p C right

def shape : MultispanShape where
  L := Overlap p C L
  R := S.perfectoid.atlas.index
  fst o := o.left
  snd o := o.right

def diagram : MultispanIndex (shape p C L) (ESpace p E.field) where
  left o := (A.frame o.base).object p C I
  right i := (A.frame (L.base i)).object p C I
  fst o := (A.change o.first).map
  snd o := (A.change o.second).map

def cocone (X : ESpace p E.field) (f : ∀ i, (A.frame (L.base i)).object p C I ⟶ X)
    (h : ∀ o : Overlap p C L,
      (A.change o.first).map ≫ f o.left = (A.change o.second).map ≫ f o.right) :
    Multicofork (diagram p C I A L) :=
  Multicofork.ofπ _ X f h

end MathlibExt.AlgebraicGeometry.RelativeFFAtlasDiagrams

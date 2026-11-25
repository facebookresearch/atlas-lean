/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.OneColorAssociativity

/-!
# Focused O7E one-color associativity public-contract packet

Pins the stable downstream-facing contracts comparing ordinary
and one-colored associativity routes: colorize compatibilities
and the uncolor grouping comparisons with route compatibilities.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v

variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Colorize factor compatibilities.
example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData PUnit) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (ColoredOperadObj.OneColor.colorizeGroupingAHom O d) ≫
        AssocInsertion.groupingAToFactorsHom O γ
          (ColoredOperadObj.OneColor.uncolorAssocData d) =
      ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
          (ColoredOperadObj.OneColor.colorizeCollection O)
          (ColoredOperadObj.OneColor.colorizeSubst O γ) d ≫
        ColoredOperadObj.OneColor.colorizeFactorHom O
          d.outerAfterInnerData :=
  ColoredOperadObj.OneColor.colorizeGroupingAToFactors_compat O γ d

example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData PUnit) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (ColoredOperadObj.OneColor.colorizeGroupingBHom O d) ≫
        AssocInsertion.groupingBToFactorsHom O γ
          (ColoredOperadObj.OneColor.uncolorAssocData d) =
      ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
          (ColoredOperadObj.OneColor.colorizeCollection O)
          (ColoredOperadObj.OneColor.colorizeSubst O γ) d ≫
        ColoredOperadObj.OneColor.colorizeFactorHom O d.innerData :=
  ColoredOperadObj.OneColor.colorizeGroupingBToFactors_compat O γ d

example (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.colorizeFlattenedGroupingAIso O d).hom ≫
        AssocInsertion.flattenAToFlattenBHom O
          (ColoredOperadObj.OneColor.uncolorAssocData d) =
      ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom
          (ColoredOperadObj.OneColor.colorizeCollection O) d ≫
        (ColoredOperadObj.OneColor.colorizeFlattenedGroupingBIso O d).hom :=
  ColoredOperadObj.OneColor.colorizeFlattenAToFlattenB_compat O d

example (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.colorizeAssocSourceIso O d).hom =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map
          (ColoredOperadObj.OneColor.colorizeGroupingAHom O d)) :=
  ColoredOperadObj.OneColor.colorizeAssocSourceIso_hom O d

-- Colorize route compatibilities.
example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.colorizeAssocSourceIso O d).hom ≫
        associativityRouteA O γ
          (ColoredOperadObj.OneColor.uncolorAssocData d) =
      ColoredOperadObj.associativityRouteA
        (ColoredOperadObj.OneColor.colorizeCollection O)
        (ColoredOperadObj.OneColor.colorizeSubst O γ) d :=
  ColoredOperadObj.OneColor.colorizeAssociativityRouteA_compat O γ d

example (O : SymmetricCollection V) (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.colorizeCollection O).map d.totalHom =
      O.relabelIso
        (ColoredOperadObj.OneColor.uncolorAssocData d).totalIso :=
  ColoredOperadObj.OneColor.colorizeCollection_map_totalHom O d

example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData PUnit) :
    (ColoredOperadObj.OneColor.colorizeAssocSourceIso O d).hom ≫
        associativityRouteB O γ
          (ColoredOperadObj.OneColor.uncolorAssocData d) =
      ColoredOperadObj.associativityRouteB
        (ColoredOperadObj.OneColor.colorizeCollection O)
        (ColoredOperadObj.OneColor.colorizeSubst O γ) d :=
  ColoredOperadObj.OneColor.colorizeAssociativityRouteB_compat O γ d

-- Uncolor grouping comparisons.
noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    AssocInsertion.groupingA
          (ColoredOperadObj.OneColor.uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.groupingA O
        (ColoredOperadObj.OneColor.colorizeAssocData d) :=
  ColoredOperadObj.OneColor.uncolorGroupingAIso O d

noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    AssocInsertion.groupingB
          (ColoredOperadObj.OneColor.uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.groupingB O
        (ColoredOperadObj.OneColor.colorizeAssocData d) :=
  ColoredOperadObj.OneColor.uncolorGroupingBIso O d

noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    AssocInsertion.flattenedGroupingA
          (ColoredOperadObj.OneColor.uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.flattenedGroupingA O
        (ColoredOperadObj.OneColor.colorizeAssocData d) :=
  ColoredOperadObj.OneColor.uncolorFlattenedGroupingAIso O d

noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    AssocInsertion.flattenedGroupingB
          (ColoredOperadObj.OneColor.uncolorCollection O) d ≅
      ColoredOperadObj.AssocInsertion.flattenedGroupingB O
        (ColoredOperadObj.OneColor.colorizeAssocData d) :=
  ColoredOperadObj.OneColor.uncolorFlattenedGroupingBIso O d

noncomputable example (O : ColoredSymmetricCollection PUnit V)
    (d : AssocData) :
    associativityCommonSource
          (ColoredOperadObj.OneColor.uncolorCollection O) d ≅
      ColoredOperadObj.associativityCommonSource O
        (ColoredOperadObj.OneColor.colorizeAssocData d) :=
  ColoredOperadObj.OneColor.uncolorAssocSourceIso O d

example (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    (ColoredOperadObj.OneColor.uncolorAssocSourceIso O d).hom =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map
          (ColoredOperadObj.OneColor.uncolorGroupingAHom O d)) :=
  ColoredOperadObj.OneColor.uncolorAssocSourceIso_hom O d

-- Uncolor factor compatibilities.
example (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (ColoredOperadObj.OneColor.uncolorGroupingAHom O d) ≫
        ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ
          (ColoredOperadObj.OneColor.colorizeAssocData d) =
      AssocInsertion.groupingAToFactorsHom
          (ColoredOperadObj.OneColor.uncolorCollection O)
          (ColoredOperadObj.OneColor.uncolorSubst O γ) d ≫
        ColoredOperadObj.OneColor.uncolorFactorHom O
          d.outerAfterInnerData :=
  ColoredOperadObj.OneColor.uncolorGroupingAToFactors_compat O γ d

example (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (ColoredOperadObj.OneColor.uncolorGroupingBHom O d) ≫
        ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O γ
          (ColoredOperadObj.OneColor.colorizeAssocData d) =
      AssocInsertion.groupingBToFactorsHom
          (ColoredOperadObj.OneColor.uncolorCollection O)
          (ColoredOperadObj.OneColor.uncolorSubst O γ) d ≫
        ColoredOperadObj.OneColor.uncolorFactorHom O d.innerData :=
  ColoredOperadObj.OneColor.uncolorGroupingBToFactors_compat O γ d

example (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    (ColoredOperadObj.OneColor.uncolorFlattenedGroupingAIso O d).hom ≫
        ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O
          (ColoredOperadObj.OneColor.colorizeAssocData d) =
      AssocInsertion.flattenAToFlattenBHom
          (ColoredOperadObj.OneColor.uncolorCollection O) d ≫
        (ColoredOperadObj.OneColor.uncolorFlattenedGroupingBIso O d).hom :=
  ColoredOperadObj.OneColor.uncolorFlattenAToFlattenB_compat O d

-- Uncolor route compatibilities.
example (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (ColoredOperadObj.OneColor.uncolorAssocSourceIso O d).hom ≫
        ColoredOperadObj.associativityRouteA O γ
          (ColoredOperadObj.OneColor.colorizeAssocData d) =
      associativityRouteA
        (ColoredOperadObj.OneColor.uncolorCollection O)
        (ColoredOperadObj.OneColor.uncolorSubst O γ) d :=
  ColoredOperadObj.OneColor.uncolorAssociativityRouteA_compat O γ d

example (O : ColoredSymmetricCollection PUnit V) (d : AssocData) :
    (ColoredOperadObj.OneColor.uncolorCollection O).relabelIso
        d.totalIso =
      O.map (ColoredOperadObj.OneColor.colorizeAssocData d).totalHom :=
  ColoredOperadObj.OneColor.uncolorCollection_relabelIso_totalIso O d

example (O : ColoredSymmetricCollection PUnit V)
    (γ : ColoredOperadSubstitution O) (d : AssocData) :
    (ColoredOperadObj.OneColor.uncolorAssocSourceIso O d).hom ≫
        ColoredOperadObj.associativityRouteB O γ
          (ColoredOperadObj.OneColor.colorizeAssocData d) =
      associativityRouteB
        (ColoredOperadObj.OneColor.uncolorCollection O)
        (ColoredOperadObj.OneColor.uncolorSubst O γ) d :=
  ColoredOperadObj.OneColor.uncolorAssociativityRouteB_compat O γ d

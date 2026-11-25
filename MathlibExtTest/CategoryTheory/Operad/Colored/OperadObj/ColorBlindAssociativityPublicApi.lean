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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlindAssociativity

/-!
# Focused O7E color-blind associativity public-contract packet

Pins the stable downstream-facing contracts comparing
color-blind and ordinary associativity routes: grouping
comparisons, factor compatibilities, and route compatibilities.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v w

variable (Color : Type u)
variable {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Grouping comparisons.
noncomputable example (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.groupingA
          (ColoredOperadObj.ColorBlind.collection Color O) d ≅
      AssocInsertion.groupingA O
        (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) :=
  ColoredOperadObj.ColorBlind.groupingAIso Color O d

noncomputable example (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.groupingB
          (ColoredOperadObj.ColorBlind.collection Color O) d ≅
      AssocInsertion.groupingB O
        (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) :=
  ColoredOperadObj.ColorBlind.groupingBIso Color O d

noncomputable example (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.flattenedGroupingA
          (ColoredOperadObj.ColorBlind.collection Color O) d ≅
      AssocInsertion.flattenedGroupingA O
        (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) :=
  ColoredOperadObj.ColorBlind.flattenedGroupingAIso Color O d

noncomputable example (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.flattenedGroupingB
          (ColoredOperadObj.ColorBlind.collection Color O) d ≅
      AssocInsertion.flattenedGroupingB O
        (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) :=
  ColoredOperadObj.ColorBlind.flattenedGroupingBIso Color O d

noncomputable example (O : SymmetricCollection V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.associativityCommonSource
          (ColoredOperadObj.ColorBlind.collection Color O) d ≅
      associativityCommonSource O
        (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) :=
  ColoredOperadObj.ColorBlind.assocSourceIso Color O d

-- Factor compatibilities.
example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (ColoredOperadObj.ColorBlind.groupingAHom Color O d) ≫
        AssocInsertion.groupingAToFactorsHom O γ
          (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) =
      ColoredOperadObj.AssocInsertion.groupingAToFactorsHom
          (ColoredOperadObj.ColorBlind.collection Color O)
          (ColoredOperadObj.ColorBlind.substitutionData Color O γ) d ≫
        ColoredOperadObj.ColorBlind.factorHom Color O
          d.outerAfterInnerData :=
  ColoredOperadObj.ColorBlind.groupingAToFactors_compat Color O γ d

example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).map
          (ColoredOperadObj.ColorBlind.groupingBHom Color O d) ≫
        AssocInsertion.groupingBToFactorsHom O γ
          (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) =
      ColoredOperadObj.AssocInsertion.groupingBToFactorsHom
          (ColoredOperadObj.ColorBlind.collection Color O)
          (ColoredOperadObj.ColorBlind.substitutionData Color O γ) d ≫
        ColoredOperadObj.ColorBlind.factorHom Color O d.innerData :=
  ColoredOperadObj.ColorBlind.groupingBToFactors_compat Color O γ d

example (O : SymmetricCollection V) (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.flattenedGroupingAIso Color O d).hom ≫
        AssocInsertion.flattenAToFlattenBHom O
          (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) =
      ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom
          (ColoredOperadObj.ColorBlind.collection Color O) d ≫
        (ColoredOperadObj.ColorBlind.flattenedGroupingBIso Color O d).hom :=
  ColoredOperadObj.ColorBlind.flattenAToFlattenB_compat Color O d

example (O : SymmetricCollection V) (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.assocSourceIso Color O d).hom =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map
          (ColoredOperadObj.ColorBlind.groupingAHom Color O d)) :=
  ColoredOperadObj.ColorBlind.assocSourceIso_hom Color O d

-- Route compatibilities.
example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.assocSourceIso Color O d).hom ≫
        associativityRouteA O γ
          (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) =
      ColoredOperadObj.associativityRouteA
        (ColoredOperadObj.ColorBlind.collection Color O)
        (ColoredOperadObj.ColorBlind.substitutionData Color O γ) d :=
  ColoredOperadObj.ColorBlind.associativityRouteA_compat Color O γ d

example (O : SymmetricCollection V) (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.collection Color O).map d.totalHom =
      O.relabelIso
        (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color
          d).totalIso :=
  ColoredOperadObj.ColorBlind.collection_map_totalHom Color O d

example (O : SymmetricCollection V) (γ : OperadSubstitution O)
    (d : ColoredAssocData Color) :
    (ColoredOperadObj.ColorBlind.assocSourceIso Color O d).hom ≫
        associativityRouteB O γ
          (ColoredOperadObj.ColorBlind.forgetColorsAssocData Color d) =
      ColoredOperadObj.associativityRouteB
        (ColoredOperadObj.ColorBlind.collection Color O)
        (ColoredOperadObj.ColorBlind.substitutionData Color O γ) d :=
  ColoredOperadObj.ColorBlind.associativityRouteB_compat Color O γ d

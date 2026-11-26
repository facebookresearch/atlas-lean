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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Associativity

/-!
# Focused O7E colored associativity public-contract packet

Pins the stable downstream-facing contracts for colored operadic
associativity: the two route groupings, the reindexing hom, the
factor homs with the grouping-A component equations, the two routes
from the common source, and the associativity equation.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v u

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Grouping A signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : FiniteFamily (FiniteFamily V) :=
  ColoredOperadObj.AssocInsertion.groupingA O d

-- Grouping B signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : FiniteFamily (FiniteFamily V) :=
  ColoredOperadObj.AssocInsertion.groupingB O d

-- Flattened groupings.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : FiniteFamily V :=
  ColoredOperadObj.AssocInsertion.flattenedGroupingA O d

noncomputable example (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : FiniteFamily V :=
  ColoredOperadObj.AssocInsertion.flattenedGroupingB O d

-- Reindexing hom from flattened A to flattened B.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.AssocInsertion.flattenedGroupingA O d ⟶
      ColoredOperadObj.AssocInsertion.flattenedGroupingB O d :=
  ColoredOperadObj.AssocInsertion.flattenAToFlattenBHom O d

-- Route-A factor hom signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
          (ColoredOperadObj.AssocInsertion.groupingA O d) ⟶
      (ColoredOperadObj.substitutionFactors O).obj d.outerAfterInnerData :=
  ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ d

-- The grouping-A factor hom is the identity on block indices.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color) :
    (ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ
      d).equiv = Equiv.refl _ :=
  ColoredOperadObj.AssocInsertion.groupingAToFactorsHom_equiv O γ d

-- The root block collapses the singleton tensor.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color) :
    (ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ
      d).hom none =
      (FiniteTensor.singletonIso (V := V)).hom.app
        (O.obj d.middleData.outerProfile) :=
  ColoredOperadObj.AssocInsertion.groupingAToFactorsHom_hom_none O γ d

-- Each child block runs its local substitution.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (d : ColoredAssocData Color) (i : d.branches.index) :
    (ColoredOperadObj.AssocInsertion.groupingAToFactorsHom O γ
      d).hom (some i) = γ.app (d.localData i) :=
  ColoredOperadObj.AssocInsertion.groupingAToFactorsHom_hom_some O γ d i

-- Route-B factor hom signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    (FiniteFamily.map (FiniteTensor.tensor (V := V))).obj
          (ColoredOperadObj.AssocInsertion.groupingB O d) ⟶
      (ColoredOperadObj.substitutionFactors O).obj d.innerData :=
  ColoredOperadObj.AssocInsertion.groupingBToFactorsHom O γ d

-- Common source signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (d : ColoredAssocData Color) : V :=
  ColoredOperadObj.associativityCommonSource O d

-- Route A signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    ColoredOperadObj.associativityCommonSource O d ⟶
      O.obj d.outerAfterInnerData.totalProfile :=
  ColoredOperadObj.associativityRouteA O γ d

-- Route B signature.
noncomputable example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O) (d : ColoredAssocData Color) :
    ColoredOperadObj.associativityCommonSource O d ⟶
      O.obj d.outerAfterInnerData.totalProfile :=
  ColoredOperadObj.associativityRouteB O γ d

-- Associativity equation.
example (O : ColoredSymmetricCollection Color V)
    (γ : ColoredOperadSubstitution O)
    (h : ColoredOperadObj.IsAssociative O γ)
    (d : ColoredAssocData Color) :
    ColoredOperadObj.associativityRouteA O γ d =
      ColoredOperadObj.associativityRouteB O γ d :=
  h d

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Evaluation of graded objects

Evaluation of a graded object preserves limits and colimits of each
shape for which they exist in the coefficient category.
-/

@[expose] public section

namespace CategoryTheory.GradedObject

open Limits

universe u v w uK vK

variable {I : Type w} {C : Type u} [Category.{v} C]

/-- Graded-object evaluation preserves every existing shape of limits. -/
instance evaluation_preservesLimitsOfShape
    (K : Type uK) [Category.{vK} K] [HasLimitsOfShape K C] (i : I) :
    PreservesLimitsOfShape K (eval (C := C) i) := by
  change PreservesLimitsOfShape K
    ((piEquivalenceFunctorDiscrete I C).functor ⋙
      (evaluation (Discrete I) C).obj (Discrete.mk i))
  infer_instance

/-- Graded-object evaluation preserves every existing shape of colimits. -/
instance evaluation_preservesColimitsOfShape
    (K : Type uK) [Category.{vK} K] [HasColimitsOfShape K C] (i : I) :
    PreservesColimitsOfShape K (eval (C := C) i) := by
  change PreservesColimitsOfShape K
    ((piEquivalenceFunctorDiscrete I C).functor ⋙
      (evaluation (Discrete I) C).obj (Discrete.mk i))
  infer_instance

end CategoryTheory.GradedObject

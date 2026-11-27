/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Vanishing differentials in colimits of complexes

The evaluation cocone is colimit. Its inclusions jointly determine a
morphism, and each inclusion satisfies the chain-map equation.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe uC vC uJ vJ w

namespace HomologicalComplex

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}
  {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J C]

/-- A differential vanishing at every stage vanishes in the colimit complex. -/
theorem colimit_d_eq_zero (F : J ⥤ HomologicalComplex C c) (i j : ι)
    (hF : ∀ a, (F.obj a).d i j = 0) : (colimit F).d i j = 0 := by
  let hc := isColimitOfPreserves (HomologicalComplex.eval C c i) (colimit.isColimit F)
  apply hc.hom_ext
  intro a
  change (colimit.ι F a).f i ≫ (colimit F).d i j = (colimit.ι F a).f i ≫ 0
  calc
    _ = (F.obj a).d i j ≫ (colimit.ι F a).f j := (colimit.ι F a).comm i j
    _ = 0 := by rw [hF a, zero_comp]
    _ = _ := (comp_zero).symm

end HomologicalComplex

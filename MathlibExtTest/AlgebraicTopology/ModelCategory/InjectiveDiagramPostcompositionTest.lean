/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.InjectiveDiagramPostcomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uK vK uC vC uD vD

open CategoryTheory HomotopicalAlgebra

variable (K : Type uK) [Category.{vK} K]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [ModelCategory C] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C}

example (adj : L ⊣ R) [adj.IsQuillenAdjunction] :
    ((trivialCofibrations D).functorCategory K).rlp ≤
      (((trivialCofibrations C).functorCategory K).rlp).inverseImage
        ((Functor.whiskeringRight K D C).obj R) :=
  (adj.injectiveDiagram_rightClasses_le_inverseImage K).1

example (adj : L ⊣ R) [adj.IsQuillenAdjunction] :
    ((cofibrations D).functorCategory K).rlp ≤
      (((cofibrations C).functorCategory K).rlp).inverseImage
        ((Functor.whiskeringRight K D C).obj R) :=
  (adj.injectiveDiagram_rightClasses_le_inverseImage K).2

example (adj : L ⊣ R) (X : K ⥤ C) (k : K) :
    ((adj.whiskerRight K).unit.app X).app k = adj.unit.app (X.obj k) := by
  simp

example (adj : L ⊣ R) (Y : K ⥤ D) (k : K) :
    ((adj.whiskerRight K).counit.app Y).app k = adj.counit.app (Y.obj k) := by
  simp

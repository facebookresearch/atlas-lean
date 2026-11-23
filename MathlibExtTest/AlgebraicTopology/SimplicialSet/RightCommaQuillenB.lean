/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenB

/-!
# Ordinary applications of the original-transition Quillen B implication

The weak comparison retains the actual comma-projection coordinate. For
an arbitrary source and a terminal discrete target, the transition premise
is derived from the actual identity arrows.
-/

open CategoryTheory
open scoped Simplicial

universe u

namespace RightCommaQuillenBConsumer

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

example (F : C ⥤ D)
    (hF : ∀ (d d' : D) (g : d ⟶ d'),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (CostructuredArrow.map (S := F) g)))) (d : D) :
    TopCat.weakHomotopyEquivalences (SSet.rightCommaHomotopyFiberComparison F d) ∧
      SSet.rightCommaHomotopyFiberComparison F d ≫
          TopCat.homotopyFiberToTotal (SSet.toTop.map (nerveMap F))
            (SSet.realizedVertex (ComposableArrows.mk₀ d : (nerve D : SSet.{u}) _⦋0⦌)) =
        SSet.toTop.map (nerveMap (CostructuredArrow.proj F d)) :=
  ⟨SSet.rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences F hF d,
    SSet.rightCommaHomotopyFiberComparison_toTotal F d⟩

example {C : Type} [Category.{0} C] (F : C ⥤ Discrete PUnit)
    (d : Discrete PUnit) :
    TopCat.weakHomotopyEquivalences (SSet.rightCommaHomotopyFiberComparison F d) := by
  apply SSet.rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences F ?_ d
  intro x y g
  have hxy : y = x := Subsingleton.elim _ _
  subst y
  have hg : g = 𝟙 x := Subsingleton.elim _ _
  subst g
  simpa only [SSet.rightCommaNerveDiagram_obj, SSet.rightCommaNerveDiagram_map] using
    TopCat.weakHomotopyEquivalences.of_isIso
      (SSet.toTop.map ((SSet.rightCommaNerveDiagram F).map (𝟙 x)))

end RightCommaQuillenBConsumer

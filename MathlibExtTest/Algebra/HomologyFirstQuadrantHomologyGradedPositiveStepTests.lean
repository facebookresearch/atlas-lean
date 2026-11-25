/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedPositiveStep

/-! # Tests for positive total-homology filtration step comparisons -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedPositiveStepTests

variable {C : Type u} [Category.{v} C] [Abelian C]

#check horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
#check horizontalFiniteTotalHomologyFiltrationStepMap_comp_positiveComparison_inv

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)).hom.app p =
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (p + q) p hp).hom ≫
        (horizontalFiniteTotalHomologyFiltration K (p + q)).diagram.map
          (homOfLE (Nat.sub_le p 1)) :=
  horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison K p q hp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    (horizontalFiniteTotalHomologyFiltration K (p + q)).diagram.map
          (homOfLE (Nat.sub_le p 1)) ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K
          (p + q)).inv.app p =
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (p + q) p hp).inv ≫
        horizontalTotalHomologyFiltrationStepMap K p q :=
  horizontalFiniteTotalHomologyFiltrationStepMap_comp_positiveComparison_inv
    K p q hp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K 1 q ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (1 + q)).hom.app 1 =
      (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
          K (1 + q) 1 (by omega)).hom ≫
        (horizontalFiniteTotalHomologyFiltration K (1 + q)).diagram.map
          (homOfLE (Nat.sub_le 1 1)) :=
  horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
    K 1 q (by omega)

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n : ℕ) :
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
      K n 1 (by omega)).hom =
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).hom.app 0 := by
  simp

#print axioms horizontalTotalHomologyFiltrationStepMap_comp_positiveComparison
#print axioms horizontalFiniteTotalHomologyFiltrationStepMap_comp_positiveComparison_inv

end HomologicalComplex₂.FirstQuadrantHomologyGradedPositiveStepTests

end

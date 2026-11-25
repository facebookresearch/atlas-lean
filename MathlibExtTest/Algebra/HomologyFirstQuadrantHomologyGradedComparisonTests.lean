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
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedComparison

/-! # Tests for the positive predecessor filtration comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedComparisonTests

variable {C : Type u} [Category.{v} C] [Abelian C]

#check horizontalTotalHomologyPrevNatIndexEq
#check horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
#check horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_hom
#check horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_inv

example (p : ℕ) (hp : 0 < p) :
    ((((p : ℤ) - 1 : ℤ) : EInt)) =
      ((((p - 1 : ℕ) : ℤ) : EInt)) :=
  horizontalTotalHomologyPrevNatIndexEq p hp

noncomputable example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n : ℕ) :
    (horizontalTotalHomologyFiltration K n).obj ((0 : ℤ) : EInt) ≅
      (horizontalFiniteTotalHomologyFiltration K n).obj 0 :=
  horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n 1 (by omega)

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n p : ℕ) (hp : 0 < p) :
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).hom =
      eqToHom (congrArg
        (fun i : EInt => (horizontalTotalHomologyFiltration K n).obj i)
        (horizontalTotalHomologyPrevNatIndexEq p hp)) ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).hom.app (p - 1) :=
  horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_hom K n p hp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n p : ℕ) (hp : 0 < p) :
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).inv =
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).inv.app (p - 1) ≫
        eqToHom (congrArg
          (fun i : EInt => (horizontalTotalHomologyFiltration K n).obj i)
          (horizontalTotalHomologyPrevNatIndexEq p hp).symm) :=
  horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_inv K n p hp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n p : ℕ) (hp : 0 < p) :
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).hom ≫
        (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).inv =
      𝟙 _ :=
  (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).hom_inv_id

example : ¬(0 : ℕ) < 0 := by omega

#print axioms horizontalTotalHomologyPrevNatIndexEq
#print axioms horizontalPositivePrevCompleteFiniteHomologyFiltrationIso

end HomologicalComplex₂.FirstQuadrantHomologyGradedComparisonTests

end

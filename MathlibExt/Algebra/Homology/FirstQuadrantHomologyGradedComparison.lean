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

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyFilteredObjectFunctor

/-!
# Positive predecessor comparison for the total-homology filtration

At a positive natural filtration index, the preceding complete-filtration
stage has integer index `p - 1` and is canonically identified with natural
stage `p - 1` of the finite image filtration.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For positive `p`, its predecessor computed in the integers agrees with
the integer cast of its natural predecessor. -/
theorem horizontalTotalHomologyPrevNatIndexEq (p : ℕ) (hp : 0 < p) :
    ((((p : ℤ) - 1 : ℤ) : EInt)) =
      ((((p - 1 : ℕ) : ℤ) : EInt)) :=
  congrArg (@WithBotTop.coe ℤ)
    (Int.natCast_pred_of_pos hp).symm

/-- At a positive index, the preceding complete total-homology filtration
stage is canonically isomorphic to the corresponding finite stage. -/
noncomputable def horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n p : ℕ) (hp : 0 < p) :
    (horizontalTotalHomologyFiltration K n).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ≅
      (horizontalFiniteTotalHomologyFiltration K n).obj (p - 1) :=
  eqToIso (congrArg
    (fun i : EInt => (horizontalTotalHomologyFiltration K n).obj i)
    (horizontalTotalHomologyPrevNatIndexEq p hp)) ≪≫
  (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).app (p - 1)

@[simp]
theorem horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n p : ℕ) (hp : 0 < p) :
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).hom =
      eqToHom (congrArg
        (fun i : EInt => (horizontalTotalHomologyFiltration K n).obj i)
        (horizontalTotalHomologyPrevNatIndexEq p hp)) ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).hom.app (p - 1) :=
  rfl

@[simp]
theorem horizontalPositivePrevCompleteFiniteHomologyFiltrationIso_inv
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n p : ℕ) (hp : 0 < p) :
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K n p hp).inv =
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso K n).inv.app (p - 1) ≫
        eqToHom (congrArg
          (fun i : EInt => (horizontalTotalHomologyFiltration K n).obj i)
          (horizontalTotalHomologyPrevNatIndexEq p hp).symm) :=
  rfl

end HomologicalComplex₂

end

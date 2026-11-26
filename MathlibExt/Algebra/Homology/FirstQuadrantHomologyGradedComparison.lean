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
# Comparing positive predecessor stages of the homology filtration

For p ∈ ℕ with p>0, the finite integer index p−1 in EInt is the image of the natural
predecessor p−1. For a first-quadrant bicomplex in an abelian category, this identifies the
preceding complete image-filtration stage with the corresponding natural-index stage of the
finite image filtration.

The comparison first transports along the equality of indices and then applies the
complete-to-finite homology image isomorphism. Its positive-column hypothesis is needed
because the integer predecessor at p=0 is −1.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For p ∈ ℕ with 0 < p, the image of (p : ℤ)−1 in EInt equals the image of ((p−1 : ℕ) : ℤ). Thus
the predecessor computed in the integers and the natural predecessor define the same
complete-filtration index. The positivity assumption excludes p=0, whose integer predecessor
is −1 while its natural predecessor is 0. -/
theorem horizontalTotalHomologyPrevNatIndexEq (p : ℕ) (hp : 0 < p) :
    ((((p : ℤ) - 1 : ℤ) : EInt)) =
      ((((p - 1 : ℕ) : ℤ) : EInt)) :=
  congrArg (@WithBotTop.coe ℤ)
    (Int.natCast_pred_of_pos hp).symm

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), n,p ∈ ℕ, and hp : 0 < p.
The complete image stage F_{(p:ℤ)−1}H_n(Tot(K)) is canonically isomorphic to the finite image
stage F_{p−1}H_n(Tot(K)), where the latter predecessor is in ℕ. The isomorphism first
transports the complete stage along (p:ℤ)−1 = ((p−1:ℕ):ℤ) in EInt, then applies the
complete-to-finite filtration comparison at p−1. -/
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

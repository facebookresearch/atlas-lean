/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HornOpposite

/-!
# Tests for opposite horn squares
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.horn

example {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 1)) (p : X ⟶ Y) :
    (Arrow.mk (SSet.horn n i).ι ⟶ Arrow.mk p) ≃
      (Arrow.mk (SSet.horn n i.rev).ι ⟶
        Arrow.mk (SSet.opFunctor.map p)) :=
  opArrowHomEquiv n i p

example {X Y : SSet.{u}} {n : ℕ} {i : Fin (n + 1)} {p : X ⟶ Y}
    (sq : Arrow.mk (SSet.horn n i).ι ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (opArrowHomEquiv n i p sq) :=
  opLiftStructEquiv sq

example {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 1)) (p : X ⟶ Y)
    (sq : Arrow.mk (SSet.horn n i).ι ⟶ Arrow.mk p) :
    (opArrowHomEquiv n i p sq).left =
      (SSet.hornOppositeIso n i).inv ≫ SSet.opFunctor.map sq.left := by
  simp

example {X Y : SSet.{u}} (n : ℕ) (i : Fin (n + 1)) (p : X ⟶ Y)
    (sq : Arrow.mk (SSet.horn n i).ι ⟶ Arrow.mk p) :
    (opArrowHomEquiv n i p sq).right =
      (SSet.stdSimplex.opIso ⦋n⦌).inv ≫
        SSet.opFunctor.map sq.right := by
  simp

example {X Y : SSet.{u}} {n : ℕ} {i : Fin (n + 1)} {p : X ⟶ Y}
    (sq : Arrow.mk (SSet.horn n i).ι ⟶ Arrow.mk p)
    (l : Arrow.LiftStruct sq) :
    (opLiftStructEquiv sq l).l =
      (SSet.stdSimplex.opIso ⦋n⦌).inv ≫ SSet.opFunctor.map l.l := by
  simp

end SSet.horn

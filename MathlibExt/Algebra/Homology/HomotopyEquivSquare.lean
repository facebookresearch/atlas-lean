/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u w

namespace HomologicalComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type w} {c : ComplexShape ι}
variable {K L K' L' : HomologicalComplex C c}

/-- A strictly commuting square of forward maps of homotopy equivalences
induces a commuting square of inverse maps up to homotopy. -/
def invNaturality
    (e : HomotopyEquiv K L) (e' : HomotopyEquiv K' L')
    (a : K ⟶ K') (b : L ⟶ L')
    (h : e.hom ≫ b = a ≫ e'.hom) :
    Homotopy (e.inv ≫ a) (b ≫ e'.inv) := by
  let hInsertRight :=
    (e'.homotopyHomInvId.compLeftId (e.inv ≫ a)).symm
  let hSquare : Homotopy
      ((e.inv ≫ a) ≫ e'.hom ≫ e'.inv)
      ((e.inv ≫ e.hom) ≫ b ≫ e'.inv) :=
    Homotopy.ofEq (by
      simpa only [Category.assoc] using
        congrArg (fun k => e.inv ≫ k ≫ e'.inv) h.symm)
  let hRemoveLeft := e.homotopyInvHomId.compRightId (b ≫ e'.inv)
  exact hInsertRight.trans (hSquare.trans hRemoveLeft)

end HomologicalComplex.HomotopyEquiv

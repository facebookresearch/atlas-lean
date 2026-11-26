/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Inverse naturality of homotopy equivalences

For homotopy equivalences e : K ≃ L and e′ : K′ ≃ L′, let a : K → K′ and b : L → L′ make the
forward square commute strictly. The inverse square then commutes up to a constructed
homotopy: e⁻¹ followed by a is homotopic to b followed by e′⁻¹.

The complexes have an arbitrary common shape in a preadditive category, with independent
object, morphism and index universes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u w

namespace HomologicalComplex.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type w} {c : ComplexShape ι}
variable {K L K' L' : HomologicalComplex C c}

/-- The inverse square of a homotopy-equivalence square commutes up to homotopy.

From e.hom ≫ b = a ≫ e′.hom, construct a homotopy between e.inv ≫ a and b ≫ e′.inv. -/
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

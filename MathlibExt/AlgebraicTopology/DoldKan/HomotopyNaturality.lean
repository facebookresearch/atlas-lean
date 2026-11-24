/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace AlgebraicTopology.DoldKan

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
/-- The inductive Dold--Kan homotopy from `P q` to the identity is natural in
the simplicial object, on every homotopy component. -/
theorem homotopyPToId_hom_naturality (q n m : ℕ)
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (homotopyPToId X q).hom n m ≫ f.app (Opposite.op ⦋m⦌) =
      f.app (Opposite.op ⦋n⦌) ≫ (homotopyPToId Y q).hom n m := by
  induction q with
  | zero =>
      simp [homotopyPToId]
  | succ q ih =>
      simp only [homotopyPToId, Homotopy.trans_hom, Homotopy.ofEq_hom,
        Homotopy.add_hom, Homotopy.compLeft_hom, Pi.zero_apply,
        zero_add, add_zero, Preadditive.add_comp, Preadditive.comp_add]
      rw [ih]
      by_cases hmn : (ComplexShape.down ℕ).Rel m n
      · simp only [homotopyHσToZero, Homotopy.nullHomotopy'_hom, dite_eq_left hmn]
        rw [Category.assoc, ← hσ'_naturality q n m hmn f]
        rw [← Category.assoc, ← P_f_naturality q n f]
        rw [Category.assoc]
      · rw [(homotopyHσToZero (X := X) q).zero n m hmn,
          (homotopyHσToZero (X := Y) q).zero n m hmn]
        simp

/-- The eventual Dold--Kan homotopy from `PInfty` to the identity is natural
in the simplicial object, on every homotopy component. -/
theorem homotopyPInftyToId_hom_naturality (n m : ℕ)
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (homotopyPInftyToId X).hom n m ≫ f.app (Opposite.op ⦋m⦌) =
      f.app (Opposite.op ⦋n⦌) ≫ (homotopyPInftyToId Y).hom n m := by
  exact homotopyPToId_hom_naturality (m + 1) n m f

end AlgebraicTopology.DoldKan

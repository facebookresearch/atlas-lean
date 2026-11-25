/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monad.MonoidalBar

/-!
# Classifying bars and the strict universal-bundle map

For a monoid object `M` in a monoidal category, two-sided monoidal bars give
`B(*, M, *)` and `B(M, M, *)`. The point object carries specified left and right
actions satisfying their unit and associativity laws. An augmentation into the
point object induces the strict map from the total bar to the classifying bar.

The outer factor of the total bar uses multiplication as its right action.
For monoids in the cartesian category of types, the corresponding nerve uses
`SingleObj Gᵐᵒᵖ`: its composition convention `f ≫ g = g * f` matches the
interior bar multiplication in this opposite monoid.

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

open MonoidalCategory

/-- Strict classifying bar `B(*, M, *)` over a point datum.

`Pt` carries the point left `ModObj M` instance and the explicit right
action `ractPt`; both sides of the bar use it. The construction is the
existing `monoidalBar` specialization, so every simplicial identity and
computation rule is inherited from the general two-sided bar core. -/
noncomputable abbrev classifyingBar (M : C) [MonObj M] (Pt : C)
    [ModObj M Pt] (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt) :
    SimplicialObject (Discrete PUnit.{1} ⥤ C) :=
  monoidalBar Pt M Pt ractPt hPtOne hPtAssoc

/-- Pointwise degree formula for the classifying bar, inherited.

Degree `n` at the point is `Pt` tensored on the left with the `n`-fold
tensor-monad power applied to `Pt`. -/
@[simp]
theorem classifyingBar_obj_point (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt)
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((classifyingBar M Pt ractPt hPtOne hPtAssoc).obj
      (Opposite.op (SimplexCategory.mk n))).obj a =
      (tensorLeft Pt).obj ((monadPow (tensorMonad M) n).obj Pt) :=
  rfl

/-- Zeroth face of the classifying bar is the outer iterated action. -/
theorem classifyingBar_d0 (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt)
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((classifyingBar M Pt ractPt hPtOne hPtAssoc).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op).app a =
      barFaceApp
        (R := rightModuleOfRightAction Pt M ractPt hPtOne hPtAssoc)
        (L := leftPointModule M Pt) n 0 a := by
  exact monoidalBar_d0 Pt M Pt ractPt hPtOne hPtAssoc n a

/-- Last face of the classifying bar uses the point left action. -/
theorem classifyingBar_dLast (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt)
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((classifyingBar M Pt ractPt hPtOne hPtAssoc).map
      (SimplexCategory.δ (Fin.last (n + 1))).op).app a =
      barFaceApp
        (R := rightModuleOfRightAction Pt M ractPt hPtOne hPtAssoc)
        (L := leftPointModule M Pt) n (Fin.last (n + 1)) a := by
  exact monoidalBar_dLast Pt M Pt ractPt hPtOne hPtAssoc n a

/-- Interior faces of the classifying bar use monad multiplication. -/
theorem classifyingBar_dInterior (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt)
    (n : ℕ) (k : Fin n) (a : Discrete PUnit.{1}) :
    ((classifyingBar M Pt ractPt hPtOne hPtAssoc).map
      (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op).app a =
      (tensorLeft Pt).map
        (barMuAtPos (tensorMonad M) n k
          ((leftPointModule M Pt).functor.obj a)) := by
  exact monoidalBar_dInterior Pt M Pt ractPt hPtOne hPtAssoc n k a

/-- Degeneracies of the classifying bar insert the monad unit. -/
theorem classifyingBar_s (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt)
    (n : ℕ) (i : Fin (n + 1)) (a : Discrete PUnit.{1}) :
    ((classifyingBar M Pt ractPt hPtOne hPtAssoc).map
      (SimplexCategory.σ i).op).app a =
      (tensorLeft Pt).map (barEtaAtPos (tensorMonad M) n i Pt) := by
  exact monoidalBar_s Pt M Pt ractPt hPtOne hPtAssoc n i a

/-- Strict total bar `B(M, M, *)` over the same point datum.

The outer factor uses the genuine multiplication `MonObj.mul` as its
explicit right action, with unit and associativity laws supplied directly
by `MonObj.mul_one` and the symmetric form of `MonObj.mul_assoc`. The
inner factor is the same point module as in `classifyingBar`. -/
noncomputable abbrev universalBar (M : C) [MonObj M] (Pt : C)
    [ModObj M Pt] :
    SimplicialObject (Discrete PUnit.{1} ⥤ C) :=
  monoidalBar M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm)

/-- Pointwise degree formula for the total bar, inherited. -/
@[simp]
theorem universalBar_obj_point (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).obj
      (Opposite.op (SimplexCategory.mk n))).obj a =
      (tensorLeft M).obj ((monadPow (tensorMonad M) n).obj Pt) :=
  rfl

/-- Zeroth face of the total bar is the outer iterated action. -/
theorem universalBar_d0 (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).map
      (SimplexCategory.δ (0 : Fin (n + 2))).op).app a =
      barFaceApp
        (R := rightModuleOfRightAction M M MonObj.mul (MonObj.mul_one M)
          ((MonObj.mul_assoc M).symm))
        (L := leftPointModule M Pt) n 0 a := by
  exact monoidalBar_d0 M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm) n a

/-- Last face of the total bar uses the point left action. -/
theorem universalBar_dLast (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).map
      (SimplexCategory.δ (Fin.last (n + 1))).op).app a =
      barFaceApp
        (R := rightModuleOfRightAction M M MonObj.mul (MonObj.mul_one M)
          ((MonObj.mul_assoc M).symm))
        (L := leftPointModule M Pt) n (Fin.last (n + 1)) a := by
  exact monoidalBar_dLast M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm) n a

/-- Interior faces of the total bar use monad multiplication. -/
theorem universalBar_dInterior (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (k : Fin n) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).map
      (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op).app a =
      (tensorLeft M).map
        (barMuAtPos (tensorMonad M) n k
          ((leftPointModule M Pt).functor.obj a)) := by
  exact monoidalBar_dInterior M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm) n k a

/-- Degeneracies of the total bar insert the monad unit. -/
theorem universalBar_s (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (i : Fin (n + 1)) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).map
      (SimplexCategory.σ i).op).app a =
      (tensorLeft M).map (barEtaAtPos (tensorMonad M) n i Pt) := by
  exact monoidalBar_s M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm) n i a

/-- Strict universal-bundle map from the total bar to the classifying bar.

Given an augmentation datum `aug : M ⟶ Pt` compatible with the two right
actions, the map is the existing `monoidalBarHom` (hence the existing
`twoSidedBarHom`) with the identity point morphism on the inner factor.
Its components are therefore computed by the
`twoSidedBarHom` computation rules. -/
noncomputable def universalBundle (M : C) [MonObj M] (Pt : C)
    [ModObj M Pt] (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt)
    (aug : M ⟶ Pt) (hAug : (aug ▷ M) ≫ ractPt = MonObj.mul ≫ aug) :
    universalBar M Pt ⟶ classifyingBar M Pt ractPt hPtOne hPtAssoc :=
  monoidalBarHom (Y := M) (Y' := Pt) (X := Pt) (X' := Pt)
    (ract := MonObj.mul) (ract' := ractPt)
    (h_one := MonObj.mul_one M) (h_assoc := (MonObj.mul_assoc M).symm)
    (h_one' := hPtOne) (h_assoc' := hPtAssoc) aug hAug (𝟙 Pt)

end Monad
end CategoryTheory

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
# Two sided classifying bars and augmentation maps

For a monoid object `M` in a monoidal category, let `Pt` have a left `M`-action and a right
`M`-action with the stated unit and associativity laws. The two-sided classifying bar has
degree `Pt ⊗ T_M^n(Pt)`, and the regular universal bar has degree `M ⊗ T_M^n(Pt)`.

Boundary faces use the endpoint actions, interior faces use monad multiplication, and
degeneracies use the monad unit. A right-action-compatible map `M → Pt` induces the
augmentation map between these simplicial bars.

See J. P. May, The Geometry of Iterated Loop Spaces, LNM 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, https://doi.org/10.1007/BFb0067491.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

open MonoidalCategory

/-- Classifying two sided bar of an internal monoid.

Form `B(Pt,M,Pt)` from the given right action on the outer point object and left module
structure on the inner point object. -/
noncomputable abbrev classifyingBar (M : C) [MonObj M] (Pt : C)
    [ModObj M Pt] (ractPt : Pt ⊗ M ⟶ Pt)
    (hPtOne : (Pt ◁ MonObj.one) ≫ ractPt = (ρ_ Pt).hom)
    (hPtAssoc : (α_ Pt M M).hom ≫ (Pt ◁ MonObj.mul) ≫ ractPt =
      (ractPt ▷ M) ≫ ractPt) :
    SimplicialObject (Discrete PUnit.{1} ⥤ C) :=
  monoidalBar Pt M Pt ractPt hPtOne hPtAssoc

/-- Degree object of the classifying bar.

At degree `n` and the indexing point, the object is `Pt ⊗ (T_M^n.obj Pt)`. -/
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

/-- First boundary face of the classifying bar.

Its first face component is the two-sided bar boundary map at index zero for the specified
right and left point modules. -/
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

/-- Last boundary face of the classifying bar.

Its last face component is the two-sided bar boundary map at the last index for the specified
endpoint modules. -/
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

/-- Interior faces of the classifying bar multiply monad factors.

The interior face indexed by `k` is outer tensoring by `Pt` of the monad multiplication
inserted at bar position `k`. -/
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

/-- Classifying bar degeneracies insert the monad unit.

The degeneracy indexed by `i` is outer tensoring by `Pt` of the monad unit insertion at
position `i`. -/
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

/-- Regular two sided bar of an internal monoid.

Form `B(M,M,Pt)` with multiplication as the outer right action and the given left action on
`Pt`. -/
noncomputable abbrev universalBar (M : C) [MonObj M] (Pt : C)
    [ModObj M Pt] :
    SimplicialObject (Discrete PUnit.{1} ⥤ C) :=
  monoidalBar M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm)

/-- Degree object of the regular universal bar.

At degree `n`, the object is `M ⊗ (T_M^n.obj Pt)`. -/
@[simp]
theorem universalBar_obj_point (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).obj
      (Opposite.op (SimplexCategory.mk n))).obj a =
      (tensorLeft M).obj ((monadPow (tensorMonad M) n).obj Pt) :=
  rfl

/-- First boundary face of the regular universal bar.

The first face is the canonical two-sided boundary map for the regular outer module and the
point left module. -/
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

/-- Last boundary face of the regular universal bar.

The last face is the canonical last boundary map for the regular outer module and the point
left module. -/
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

/-- Interior universal bar faces multiply monad factors.

The interior face is outer tensoring by `M` of the corresponding bar multiplication insertion. -/
theorem universalBar_dInterior (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (k : Fin n) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).map
      (SimplexCategory.δ (k.succ.castSucc : Fin (n + 2))).op).app a =
      (tensorLeft M).map
        (barMuAtPos (tensorMonad M) n k
          ((leftPointModule M Pt).functor.obj a)) := by
  exact monoidalBar_dInterior M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm) n k a

/-- Universal bar degeneracies insert the monad unit.

The degeneracy is outer tensoring by `M` of the corresponding bar unit insertion. -/
theorem universalBar_s (M : C) [MonObj M] (Pt : C) [ModObj M Pt]
    (n : ℕ) (i : Fin (n + 1)) (a : Discrete PUnit.{1}) :
    ((universalBar M Pt).map
      (SimplexCategory.σ i).op).app a =
      (tensorLeft M).map (barEtaAtPos (tensorMonad M) n i Pt) := by
  exact monoidalBar_s M M Pt MonObj.mul (MonObj.mul_one M)
    ((MonObj.mul_assoc M).symm) n i a

/-- Simplicial bar map induced by a compatible augmentation.

A map `aug : M → Pt` satisfying the right-action compatibility gives a simplicial map from the
regular bar to the classifying bar, with identity inner point map. -/
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

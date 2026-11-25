/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryBar.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Category bar basic public contract

Compile-level pins for the degree-zero description, endpoint faces on `mk₁`,
degeneracies on `mk₀`, and `Data`/`SSet` computations.
-/

open CategoryTheory Opposite

universe u v uR uL

namespace MathlibExtTest.CategoryBar.BasicTests

variable {C : Type u} [Category.{v} C]
variable {R : Cᵒᵖ ⥤ Type uR} {L : C ⥤ Type uL}

example (F : ComposableArrows C 0) (l : L.obj F.left) (r : R.obj (op F.right)) :
    CategoryBar.barObjZeroEquiv.toFun ⟨F, l, r⟩ = ⟨F.obj 0, l, r⟩ :=
  rfl

example (x : C) (l : L.obj x) (r : R.obj (op x)) :
    CategoryBar.barObjZeroEquiv.invFun ⟨x, l, r⟩ =
      ⟨ComposableArrows.mk₀ x, l, r⟩ :=
  rfl

example {X₀ X₁ : C} (f : X₀ ⟶ X₁) (l : L.obj (ComposableArrows.mk₁ f).left)
    (r : R.obj (op (ComposableArrows.mk₁ f).right)) :
    CategoryBar.barδ (0 : Fin 2)
        (⟨ComposableArrows.mk₁ f, l, r⟩ : CategoryBar.barObj C R L 1) =
      ⟨(nerve C).δ 0 (ComposableArrows.mk₁ f),
        cast (congrArg L.obj (rfl : (ComposableArrows.mk₁ f).obj' 1 =
          ((nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f)).left))
          (L.map ((ComposableArrows.mk₁ f).map' 0 1) l),
        cast (congrArg (fun Z => R.obj (op Z)) (by
            change (ComposableArrows.mk₁ f).obj ⟨1, by omega⟩ =
              ((nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f)).obj (Fin.last _)
            rw [CategoryTheory.nerve.δ_obj]
            congr 1))
          r⟩ :=
  CategoryBar.barδ_zero_mk₁ f l r

example {X₀ X₁ : C} (f : X₀ ⟶ X₁) (l : L.obj (ComposableArrows.mk₁ f).left)
    (r : R.obj (op (ComposableArrows.mk₁ f).right)) :
    CategoryBar.barδ (Fin.last 1)
        (⟨ComposableArrows.mk₁ f, l, r⟩ : CategoryBar.barObj C R L 1) =
      ⟨(nerve C).δ (Fin.last 1) (ComposableArrows.mk₁ f),
        cast (congrArg L.obj (by
            change (ComposableArrows.mk₁ f).obj ⟨0, by omega⟩ =
              ((nerve C).δ (Fin.last 1) (ComposableArrows.mk₁ f)).obj (0 : Fin _)
            rw [CategoryTheory.nerve.δ_obj]
            congr 1))
          l,
        cast (congrArg (fun Z => R.obj (op Z)) (by
            have h : ((nerve C).δ (Fin.last 1) (ComposableArrows.mk₁ f)).obj
                (Fin.last _) =
                (ComposableArrows.mk₁ f).obj ⟨0, by omega⟩ := by
              rw [CategoryTheory.nerve.δ_obj]
              congr 1
            exact h.symm))
          (R.map (Quiver.Hom.op ((ComposableArrows.mk₁ f).map' 0 1)) r)⟩ :=
  CategoryBar.barδ_last_mk₁ f l r

example (X : C) (l : L.obj (ComposableArrows.mk₀ X).left)
    (r : R.obj (op (ComposableArrows.mk₀ X).right)) (i : Fin 1) :
    CategoryBar.barσ i
        (⟨ComposableArrows.mk₀ X, l, r⟩ : CategoryBar.barObj C R L 0) =
      ⟨(nerve C).σ i (ComposableArrows.mk₀ X),
        cast (congrArg L.obj (by
            change (ComposableArrows.mk₀ X).obj ⟨0, by omega⟩ =
              ((nerve C).σ i (ComposableArrows.mk₀ X)).obj (0 : Fin _)
            rw [CategoryTheory.nerve.σ_obj]
            exact congrArg _ Fin.predAbove_right_zero.symm)) l,
        cast (congrArg (fun Z => R.obj (op Z)) (by
            change (ComposableArrows.mk₀ X).obj ⟨0, by omega⟩ =
              ((nerve C).σ i (ComposableArrows.mk₀ X)).obj (Fin.last _)
            rw [CategoryTheory.nerve.σ_obj]
            congr 1
            exact Fin.predAbove_right_last.symm)) r⟩ :=
  CategoryBar.barσ_zero_mk₀ X l r i

example {n : ℕ} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barChain x = x.1 :=
  rfl

example {n : ℕ} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barCoeffL x = x.2.1 :=
  rfl

example {n : ℕ} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barCoeffR x = x.2.2 :=
  rfl

example (n : ℕ) :
    (CategoryBar.categoryBarData (C := C) (R := R) (L := L)).obj n =
      CategoryBar.barObj C R L n :=
  CategoryBar.categoryBarData_obj n

example {n : ℕ} (i : Fin (n + 2)) :
    (CategoryBar.categoryBarData (C := C) (R := R) (L := L)).δ i =
      ↾(CategoryBar.barδ (R := R) (L := L) i) :=
  CategoryBar.categoryBarData_δ i

example {n : ℕ} (i : Fin (n + 1)) :
    (CategoryBar.categoryBarData (C := C) (R := R) (L := L)).σ i =
      ↾(CategoryBar.barσ (R := R) (L := L) i) :=
  CategoryBar.categoryBarData_σ i

example (n : ℕ) :
    (CategoryBar.categoryBar (C := C) (R := R) (L := L)).obj
        (op (SimplexCategory.mk n)) =
      CategoryBar.barObj C R L n :=
  CategoryBar.categoryBar_obj n

example {n : ℕ} (i : Fin (n + 2)) :
    (CategoryBar.categoryBar (C := C) (R := R) (L := L)).map
        (SimplexCategory.δ i).op =
      ↾(CategoryBar.barδ (R := R) (L := L) i) :=
  CategoryBar.categoryBar_map_δ i

example {n : ℕ} (i : Fin (n + 1)) :
    (CategoryBar.categoryBar (C := C) (R := R) (L := L)).map
        (SimplexCategory.σ i).op =
      ↾(CategoryBar.barσ (R := R) (L := L) i) :=
  CategoryBar.categoryBar_map_σ i

example {n : ℕ} {i : Fin (n + 1)} (x : CategoryBar.barObj C R L n) :
    CategoryBar.barδ (R := R) (L := L) i.castSucc (CategoryBar.barσ i x) = x :=
  CategoryBar.BarLaws.δ_comp_σ_self x

namespace TypeEndpoint

/-- Explicit nonidentity endomorphism of `Bool` in `Type`. -/
def typeArrow : (Bool : Type) ⟶ (Bool : Type) := ↾Bool.not

/-- Covariant identity representable at `Bool`. -/
abbrev typeRepL : Type ⥤ Type := coyoneda.obj (op (Bool : Type))

/-- Contravariant identity representable at `Bool`. -/
abbrev typeRepR : Typeᵒᵖ ⥤ Type := yoneda.obj (Bool : Type)

/-- `Type` is non-thin: `not` is distinct from the identity function. -/
example : Bool.not ≠ id := by decide

example :
    CategoryBar.barCoeffL
        (CategoryBar.barδ (0 : Fin 2)
          (⟨ComposableArrows.mk₁ typeArrow, 𝟙 (Bool : Type), 𝟙 (Bool : Type)⟩ :
            CategoryBar.barObj Type typeRepR typeRepL 1)) = typeArrow ∧
      CategoryBar.barCoeffR
        (CategoryBar.barδ (Fin.last 1)
          (⟨ComposableArrows.mk₁ typeArrow, 𝟙 (Bool : Type), 𝟙 (Bool : Type)⟩ :
            CategoryBar.barObj Type typeRepR typeRepL 1)) = typeArrow := by
  constructor
  · simp only [CategoryBar.barCoeffL, typeRepL, typeArrow]
    rfl
  · simp only [CategoryBar.barCoeffR, typeRepR, typeArrow]
    rfl

end TypeEndpoint

end MathlibExtTest.CategoryBar.BasicTests

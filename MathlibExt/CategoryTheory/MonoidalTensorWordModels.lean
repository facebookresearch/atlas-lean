/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Fixed tensor words for cyclic and two-sided bar complexes

Words are right-associated native monoidal products. Contraction,
insertion and rotation use the actual associator, unitors and braiding.
They are not supplied as unrelated bar-face maps. For cochain complexes,
the source monoidal structure includes the internal differential and
Koszul signs.

References: Keller, *Deriving DG categories*, §§1--2; Loday, *Cyclic
homology*, §1.1; Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.MonoidalTensorWordModels

open _root_.CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- The fixed right-associated tensor word, ending in the native unit. -/
def word : List V → V
  | [] => 𝟙_ V
  | a :: xs => a ⊗ word xs

/-- Native reassociation of an appended word. -/
def appendIso (xs ys : List V) : word (xs ++ ys) ≅ word xs ⊗ word ys :=
  match xs with
  | [] => (λ_ (word ys)).symm
  | a :: tail =>
    (tensorIso (Iso.refl a) (appendIso tail ys)) ≪≫
      (α_ a (word tail) (word ys)).symm

/-- Contract the first two factors by the specified native multiplication
or DG composition map. -/
def contractHead {a b c : V} (f : a ⊗ b ⟶ c) (xs : List V) :
    word (a :: b :: xs) ⟶ word (c :: xs) :=
  (α_ a b (word xs)).inv ≫ (f ⊗ₘ 𝟙 (word xs))

/-- Insert a unit-shaped generator before the tail. -/
def insertBefore (a : V) {b : V} (f : 𝟙_ V ⟶ b) (xs : List V) :
    word (a :: xs) ⟶ word (a :: b :: xs) :=
  𝟙 a ⊗ₘ ((λ_ (word xs)).inv ≫ (f ⊗ₘ 𝟙 (word xs)))

/-- Rotate the last factor to the front by the actual braiding. In the
cochain category this is the Koszul-signed cyclic rotation. -/
def rotateLast [BraidedCategory V] (xs : List V) (a : V) :
    word (xs ++ [a]) ≅ word (a :: xs) :=
  appendIso xs [a] ≪≫
    tensorIso (Iso.refl (word xs)) (ρ_ a) ≪≫ β_ (word xs) a

end MathlibExt.CategoryTheory.MonoidalTensorWordModels

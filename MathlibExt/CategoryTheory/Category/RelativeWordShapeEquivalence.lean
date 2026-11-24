/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordShapes
import Mathlib.Logic.Equiv.Basic

/-!
# Whole original word-factor equivalence

Both inverse equations compare the actual finite label sequence and all
original Hom segments and new letters. The nullary segment is read through
its explicit universe lift. No endpoint labels are identified or quotiented.
-/

universe u v w
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {C : Type u} [Category.{v} C] (G : C → C → Type w)

/-- All actual finite label shapes and their original word-factor data. -/
abbrev Factors (a b : C) := Σ n : ℕ, Σ s : Shape C n, Cells G s a b

/-- Record the actual length, label sequence and factors of the whole original word. -/
def encodeFactors {a b : C} (p : Word G a b) : Factors G a b := ⟨p.length, encode G p⟩

/-- Decode the supplied actual length, label sequence and factors. -/
def decodeFactors {a b : C} (p : Factors G a b) : Word G a b := decode G p.2.1 p.2.2

/-- Prepend the same individually supplied original segment and new letter to actual factors. -/
def prependFactors {a x y b : C} (f : a ⟶ x) (g : G x y) (p : Factors G y b) : Factors G a b :=
  ⟨p.1 + 1, Shape.cons x y p.2.1, (f, g, p.2.2)⟩

/-- Encoding after decoding retains every original label and factor, including the nullary case. -/
theorem encodeFactors_decode {n : ℕ} (s : Shape C n) {a b : C} (p : Cells G s a b) :
    encodeFactors G (decode G s p) = ⟨n, s, p⟩ := by
  induction s generalizing a b with
  | nil => cases p; rfl
  | cons x y s ih =>
      rcases p with ⟨f, g, p⟩
      change prependFactors G f g (encodeFactors G (decode G s p)) = _
      rw [ih]
      rfl

/-- Decoding after encoding returns the entire supplied original word. -/
theorem decodeFactors_encode {a b : C} (p : Word G a b) :
    decodeFactors G (encodeFactors G p) = p := decode_encode G p

/-- The genuine whole original word-factor equivalence with both inverse equations. -/
def factorsEquiv (a b : C) : Factors G a b ≃ Word G a b where
  toFun := decodeFactors G
  invFun := encodeFactors G
  left_inv p := encodeFactors_decode G p.2.1 p.2.2
  right_inv := decodeFactors_encode G

/-- The decoded length is the supplied exact finite shape length. -/
theorem length_decodeFactors {a b : C} (p : Factors G a b) :
    (decodeFactors G p).length = p.1 := length_decode G p.2.1 p.2.2

/-- The actual finite label-product sum is equivalent to precisely that original word-length
stratum. -/
def fixedLengthFactorsEquiv (n : ℕ) (a b : C) :
    (Σ s : Shape C n, Cells G s a b) ≃ {p : Word G a b // p.length = n} := by
  let e : {p : Factors G a b // p.1 = n} ≃ (Σ s : Shape C n, Cells G s a b) :=
    Equiv.sigmaSubtype n
  exact e.symm.trans ((factorsEquiv G a b).subtypeEquiv (by
    intro p
    change p.1 = n ↔ (decodeFactors G p).length = n
    rw [length_decodeFactors]))

/-- The fixed-length equivalence decodes exactly the supplied original factors. -/
theorem fixedLengthFactorsEquiv_apply (n : ℕ) (a b : C) (p : Σ s : Shape C n, Cells G s a b) :
    (fixedLengthFactorsEquiv G n a b p).val = decode G p.1 p.2 := rfl

end CategoryTheory.RelativeWords

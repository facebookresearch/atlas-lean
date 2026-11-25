/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordPositive
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Actual original relative-word length-layer maps

The old layer consists of normalized words of length at most n. Raw
words of length n+1 normalize into the next layer, and those whose actual
new-letter count is at most n normalize into the previous layer. Every
map retains the same original word source and target, including loops
and the original length-zero Hom stage.
-/

noncomputable section
universe u v wA wB
open CategoryTheory Limits

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))

/-- The actual normalized original words of length at most n at the same two supplied labels. -/
abbrev Layer (a b : C) (n : ℕ) := {p : Word (newGenerators (A := A) (B :=
  B) (@i)) a b // p.length ≤ n}

/-- The actual raw original words containing exactly n+1 target letters. -/
abbrev RawLayer (a b : C) (n : ℕ) := {p : Word B a b // p.length = n + 1}

/-- The actual raw attaching boundary: length n+1 and normalized new-letter count at most n. -/
abbrev BoundaryLayer (a b : C) (n : ℕ) :=
  {p : Word B a b // p.length = n + 1 ∧ count (A := A) (B := B) (@i) p ≤ n}

/-- Include the same original normalized word in the next length layer. -/
def layerInclude (a b : C) (n : ℕ) : Layer (A := A) (B := B) (@i) a b n ⟶ Layer (A :=
  A) (B := B) (@i) a b (n + 1) :=
  ↾fun p => ⟨p.val, p.property.trans (Nat.le_succ n)⟩

/-- The original raw boundary is included as the same original raw word. -/
def boundaryInclude (a b : C) (n : ℕ) : BoundaryLayer (A := A) (B :=
  B) (@i) a b n ⟶ RawLayer (B := B) a b n :=
  ↾fun p => ⟨p.val, p.property.1⟩

/-- Normalize the actual raw boundary into the same previous original word layer. -/
def boundaryNormalize (a b : C) (n : ℕ) : BoundaryLayer (A := A) (B :=
  B) (@i) a b n ⟶ Layer (A := A) (B :=
    B) (@i) a b n :=
  ↾fun p => ⟨normalize (A := A) (B := B) (@i) (@φ) p.val, by
    rw [length_normalize_eq_count]
    exact p.property.2⟩

/-- Normalize every actual raw word of length n+1 into the same next original layer. -/
def rawNormalize (a b : C) (n : ℕ) : RawLayer (B := B) a b n ⟶ Layer (A := A) (B :=
  B) (@i) a b (n + 1) :=
  ↾fun p => ⟨normalize (A := A) (B := B) (@i) (@φ) p.val,
    (length_normalize_le (A := A) (B := B) (@i) (@φ) p.val).trans_eq p.property⟩

/-- The actual raw attaching-boundary and next-layer maps commute on the same entire
original normalized word. -/
theorem layer_square (a b : C) (n : ℕ) :
    boundaryNormalize (A := A) (B := B) (@i) (@φ) a b n ≫ layerInclude (A := A) (B :=
      B) (@i) a b n =
      boundaryInclude (A := A) (B := B) (@i) a b n ≫ rawNormalize (A := A) (B :=
        B) (@i) (@φ) a b n := by
  ext p
  rfl

end CategoryTheory.RelativeGenerators

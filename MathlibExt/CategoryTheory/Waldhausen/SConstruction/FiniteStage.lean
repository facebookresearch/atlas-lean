/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.CategoryTheory.Waldhausen.Basic

/-!
# Finite Waldhausen stages from `Ar[n]`

Prop-valued finite stages of the S-construction on a Waldhausen structure
without gluing, using the indexing category `Ar[n] = Arrow (Fin (n + 1))`.

An object of `Ar[n]` is an interval `(i, j)` with `i ≤ j`.
A morphism is a commuting square in `Fin (n + 1)`.
The horizontal map `(i, j) ⟶ (i, k)` fixes the left endpoint and moves the
right endpoint along `j ≤ k`; the vertical map `(i, k) ⟶ (j, k)` fixes the
right endpoint and moves the left endpoint along `i ≤ j`.
Both legs use `homOfLE`, with `i ≤ k` derived uniformly as `hij.trans hjk`,
so equal-index triples (`i = j` or `j = k`) need no separate case.

Low-degree data expectation only: `S₀` is categorically contractible (terminal), `S₁` recovers the
ambient Waldhausen category, and `S₂` encodes cofiber sequences.
No low-degree equivalence is proved here.
The name `Stage` is reserved for the later bundled category; this file
provides only the `IsStage` predicate.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Finite Waldhausen indexing category `Ar[n] = Arrow (Fin (n + 1))`.

Objects are intervals `(i, j)` with `i ≤ j` in `Fin (n + 1)`; morphisms are
commuting squares. -/
abbrev Ar (n : ℕ) := Arrow (Fin (n + 1))

/-- Canonical interval object `(i, j)` in `Ar n` for `i ≤ j`. -/
def interval {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) : Ar n :=
  Arrow.mk (homOfLE h)

/-- Diagonal interval `(i, i)`. Its values are required to be zero below. -/
def diag {n : ℕ} (i : Fin (n + 1)) : Ar n :=
  interval i i le_rfl

/-- Horizontal map `(i, j) ⟶ (i, k)`: left endpoint fixed, right endpoint
moves along `j ≤ k`. Uses `Arrow.homMk'` with legs `𝟙 i` and `homOfLE hjk`;
the square commutes because `Fin (n + 1)` homs form a subsingleton. -/
def horiz {n : ℕ} {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    interval i j hij ⟶ interval i k (hij.trans hjk) :=
  Arrow.homMk' (𝟙 i) (homOfLE hjk) (Subsingleton.elim _ _)

/-- Vertical map `(i, k) ⟶ (j, k)`: right endpoint fixed, left endpoint moves
along `i ≤ j`. Uses `Arrow.homMk'` with legs `homOfLE hij` and `𝟙 k`;
the square commutes because `Fin (n + 1)` homs form a subsingleton. -/
def vert {n : ℕ} {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    interval i k (hij.trans hjk) ⟶ interval j k hjk :=
  Arrow.homMk' (homOfLE hij) (𝟙 k) (Subsingleton.elim _ _)

/-- Map `(i, j) ⟶ diag j`: left endpoint moves along `i ≤ j`, right fixed.
Uses `Arrow.homMk'` with legs `homOfLE hij` and `𝟙 j`;
commutes by subsingleton. Uniform in the equal-index case. -/
def toDiag {n : ℕ} {i j : Fin (n + 1)} (hij : i ≤ j) :
    interval i j hij ⟶ diag j :=
  Arrow.homMk' (homOfLE hij) (𝟙 j) (Subsingleton.elim _ _)

/-- Map `diag j ⟶ (j, k)`: left fixed, right endpoint moves along `j ≤ k`.
Uses `Arrow.homMk'` with legs `𝟙 j` and `homOfLE hjk`;
commutes by subsingleton. Uniform in the equal-index case. -/
def fromDiag {n : ℕ} {j k : Fin (n + 1)} (hjk : j ≤ k) :
    diag j ⟶ interval j k hjk :=
  Arrow.homMk' (𝟙 j) (homOfLE hjk) (Subsingleton.elim _ _)

/-- Finite-stage predicate on a diagram `A : Ar n ⥤ C`.

* `diag_isZero`: every diagonal value `A (i, i)` is zero. No equality with
  the chosen zero object is required.
* `cofiber_triple`: for every non-strict triple `i ≤ j ≤ k` (equal indices
  allowed uniformly), the canonical maps
  `A (i, j) ⟶ A (i, k) ⟶ A (j, k)` form an `IsCofibrationSequence`.
  The cofibration requirement is the first conjunct of
  `IsCofibrationSequence`; no separate cofibration field is stored. -/
structure IsStage (n : ℕ) (A : Ar n ⥤ C) : Prop where
  /-- Every diagonal value of the diagram is a zero object; it need not
  equal the chosen zero object. -/
  diag_isZero : ∀ i, IsZero (A.obj (diag i))
  /-- For every non-strict triple `i ≤ j ≤ k`, the horizontal and
  vertical maps form a cofibration sequence. -/
  cofiber_triple : ∀ {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k),
    IsCofibrationSequence (A.map (horiz hij hjk)) (A.map (vert hij hjk))

/-- The actual four-map square through the diagonal is a pushout.

Top is `A.map (horiz hij hjk)`, left is `A.map (toDiag hij)` into the
diagonal, right is `A.map (vert hij hjk)`, bottom is `A.map (fromDiag hjk)`
out of the diagonal. Unpack the chosen-zero pushout from
`hA.cofiber_triple`, flip to the wanted orientation, and transport along
the `IsZero` diagonal via `IsPushout.of_iso` and zero-object uniqueness.
Equal-index triples remain uniform. -/
theorem isPushout_actualSquare {n : ℕ} {A : Ar n ⥤ C} (hA : IsStage n A)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout (A.map (horiz hij hjk)) (A.map (toDiag hij))
      (A.map (vert hij hjk)) (A.map (fromDiag hjk)) := by
  obtain ⟨_, h, q, hpush⟩ := hA.cofiber_triple hij hjk
  have hflip := hpush.flip
  let e : (0 : C) ≅ A.obj (diag j) := (isZero_zero _).iso (hA.diag_isZero j)
  apply hflip.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp
  · simpa using (hA.diag_isZero j).eq_of_tgt _ _
  · simp
  · simpa using (isZero_zero _).eq_of_src _ _

end CategoryTheory.Waldhausen.SConstruction

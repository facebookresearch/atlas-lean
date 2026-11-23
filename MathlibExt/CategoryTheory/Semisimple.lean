/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Andres Barei Bueno
-/
module

public import Mathlib.CategoryTheory.Simple

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Algebra 470, Algebra 476

/-!
# Semisimple object in a category; (Object) Semisimple category

## References

* This is Definition 1.1 in nLab's Semisimple Object page (dated Oct 3, 2026):
  https://ncatlab.org/nlab/show/semisimple+object, This is probably the best reference in general
  because of how simple and direct it is. This also appears in definition 4.15 int he notes
  Introduction to Fusion Categories by Kyle Kawagoe:
  https://categorified.net/TQFT2025/FusionCategoryNotes.pdf (for `Semisimple`)
* This appears as Definition 20 in James Bailie notes on Semisimple Categories:
  https://jameshbailie.github.io/files/papers/2017-06-26-Semisimple-categories.pdf, An alternative
  definition appears in nlab: https://ncatlab.org/nlab/show/semisimple+category, Note that nlab
  does enforce the additional restriction that every direct sum of simple objects be finite. (for
  `SemisimpleCategory`)
-/

namespace MetaMathlibExt

-- Algebra 470: Semisimple object in a category

/-- An object is semisimple if it is the (not necessarily finite) direct sum (biproduct) of simple
objects.
-/
class Semisimple.{u,v} {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C] (X : C) :
  Prop where
    decomposes_into_simples :
      ∃ (I : Type) (S : I → C) (h : CategoryTheory.Limits.HasBiproduct S),
    letI : CategoryTheory.Limits.HasBiproduct S := h;
      ((i : I) → CategoryTheory.Simple (S i)) ∧
      Nonempty (X ≅ ⨁ S)

-- Algebra 476: (Object) Semisimple category

/-- A category C is called semisimple is every object in C is isomorphic to the direct sum
(biproduct) of (not necessarily finite) simple objects.
-/
class SemisimpleCategory.{u,v} (C : Type u) [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C] : Prop where
  semisimple : ∀ (X : C), Semisimple X

end MetaMathlibExt

end

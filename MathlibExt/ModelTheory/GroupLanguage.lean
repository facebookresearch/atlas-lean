/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.ModelTheory.Semantics

/-!
# The first-order language of groups

The first-order language with one constant (the identity), one unary
function (inversion), and one binary function (multiplication),
together with its canonical structure on any group. Extracted from
the `ProPFiniteAxiomatizability` statement (Kourovka 21.120), where
it was source-local, once a second conjecture needed the same
language.
-/

@[expose] public section

namespace FirstOrder.Language

universe u

/-- Function symbols of the first-order language of groups: the
identity constant, inversion, and multiplication. -/
inductive GroupFunction : ℕ → Type
  | one : GroupFunction 0
  | inv : GroupFunction 1
  | mul : GroupFunction 2

/-- The first-order language of groups. -/
def groupLanguage : FirstOrder.Language where
  Functions := GroupFunction
  Relations := fun _ => Empty

/-- The canonical `groupLanguage`-structure on a group. -/
@[reducible]
def groupLanguageStructure (G : Type u) [Group G] : groupLanguage.Structure G where
  funMap := fun {_} f x =>
    match f with
    | .one => 1
    | .inv => (x 0)⁻¹
    | .mul => x 0 * x 1
  RelMap := fun {_} r => nomatch r

/-- The function symbols of the group language are `GroupFunction`. -/
theorem groupLanguage_functions (n : ℕ) :
    groupLanguage.Functions n = GroupFunction n := rfl

/-- The group language has no relation symbols. -/
theorem groupLanguage_relations (n : ℕ) :
    groupLanguage.Relations n = Empty := rfl

/-- Multiplication in the canonical structure is group multiplication. -/
theorem groupLanguageStructure_mul (G : Type u) [Group G] (x : Fin 2 → G) :
    (groupLanguageStructure G).funMap GroupFunction.mul x = x 0 * x 1 := rfl

/-- Inversion in the canonical structure is group inversion. -/
theorem groupLanguageStructure_inv (G : Type u) [Group G] (x : Fin 1 → G) :
    (groupLanguageStructure G).funMap GroupFunction.inv x = (x 0)⁻¹ := rfl

/-- The constant in the canonical structure is the identity. -/
theorem groupLanguageStructure_one (G : Type u) [Group G] (x : Fin 0 → G) :
    (groupLanguageStructure G).funMap GroupFunction.one x = 1 := rfl

end FirstOrder.Language

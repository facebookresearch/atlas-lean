/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Actual component values under whole short-complex transport

Equality of the two endpoint rows lets a whole heterogeneous morphism
equality be read in each original component. Canonical row equality
conjugation is a direct application; no component equality is supplied as
a separate conclusion premise.
-/

universe u v

namespace CategoryTheory.ShortComplex.Hom

variable {C : Type u} [Category.{v} C] [CategoryTheory.Limits.HasZeroMorphisms C]

/-- Whole morphism transport across the actual endpoint rows retains all three components. -/
public theorem components_heq_of_rows_eq
    {S T S' T' : ShortComplex C} (hS : S = S') (hT : T = T')
    {f : S ⟶ T} {g : S' ⟶ T'} (h : HEq f g) :
    HEq f.τ₁ g.τ₁ ∧ HEq f.τ₂ g.τ₂ ∧ HEq f.τ₃ g.τ₃ := by
  cases hS
  cases hT
  cases h
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- The canonical row-equality conjugation keeps the original three morphism values. -/
public theorem eqToHom_components_heq
    {S T S' T' : ShortComplex C} (hS : S = S') (hT : T = T') (f : S' ⟶ T') :
    HEq (eqToHom hS ≫ f ≫ eqToHom hT.symm).τ₁ f.τ₁ ∧
      HEq (eqToHom hS ≫ f ≫ eqToHom hT.symm).τ₂ f.τ₂ ∧
      HEq (eqToHom hS ≫ f ≫ eqToHom hT.symm).τ₃ f.τ₃ :=
  components_heq_of_rows_eq hS hT ((conj_eqToHom_iff_heq _ _ hS hT).1 rfl)

end CategoryTheory.ShortComplex.Hom

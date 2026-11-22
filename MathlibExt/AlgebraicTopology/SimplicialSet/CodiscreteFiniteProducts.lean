/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteNerve
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.PEmpty

/-!
# Finite products of codiscrete nerves

`W` preserves finite products: `W(PUnit)` is pointwise terminal.
-/

@[expose] public section

namespace CategoryTheory.Codiscrete

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types
open Simplicial

/-- Canonical terminal iso: `W(PUnit)` is terminal in `SSet`. -/
noncomputable def terminalIso :
    (functorToSSet : Type u ⥤ SSet.{u}).obj (PUnit : Type u) ≅ ⊤_ SSet.{u} :=
  let isPi : (n : ℕ) → IsTerminal (Fin (n + 1) → PUnit : Type u) :=
    fun n => (isTerminalEquivUnique _).symm inferInstance
  let isNerveN : (n : ℕ) → IsTerminal (nerve (Codiscrete (PUnit : Type u)) _⦋n⦌) :=
    fun n => IsTerminal.ofIso (isPi n)
      (Equiv.toIso (equivFun (X := (PUnit : Type u)) (n := n)).symm)
  let isNerveObj : (Δ : SimplexCategoryᵒᵖ) →
      IsTerminal ((nerve (Codiscrete (PUnit : Type u))).obj Δ) := fun Δ => by
    obtain ⟨⟨n⟩⟩ := Δ
    exact isNerveN n
  let isFunctorApp : (Δ : SimplexCategoryᵒᵖ) →
      IsTerminal (((functorToSSet : Type u ⥤ SSet.{u}).obj (PUnit : Type u)).obj Δ) :=
    fun Δ => by
      have h : ((functorToSSet : Type u ⥤ SSet.{u}).obj (PUnit : Type u)).obj Δ =
          (nerve (Codiscrete (PUnit : Type u))).obj Δ := rfl
      rw [h]
      exact isNerveObj Δ
  let isFunctor : IsTerminal ((functorToSSet : Type u ⥤ SSet.{u}).obj (PUnit : Type u)) :=
    Functor.isTerminal (fun Δ => isFunctorApp Δ)
  IsTerminal.uniqueUpToIso isFunctor terminalIsTerminal

instance preservesTerminal :
    PreservesLimit (Functor.empty.{0} (Type u))
      (functorToSSet : Type u ⥤ SSet.{u}) :=
  let isoTop : (functorToSSet : Type u ⥤ SSet.{u}).obj (⊤_ Type u) ≅ ⊤_ SSet.{u} :=
    ((functorToSSet : Type u ⥤ SSet.{u}).mapIso Types.terminalIso).trans terminalIso
  preservesTerminal_of_iso (f := isoTop)

instance preservesPEmpty :
    PreservesLimitsOfShape (Discrete.{0} PEmpty)
      (functorToSSet : Type u ⥤ SSet.{u}) where
  preservesLimit := by
    intro K
    have h : Functor.empty.{0} (Type u) ≅ K := Functor.emptyExt _ _
    exact preservesLimit_of_iso_diagram _ h

instance preservesFiniteProducts :
    PreservesFiniteProducts (functorToSSet : Type u ⥤ SSet.{u}) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

end CategoryTheory.Codiscrete

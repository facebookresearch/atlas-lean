/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.OfObjectFunction
public import Mathlib.CategoryTheory.Enriched.Opposite
public import Mathlib.CategoryTheory.InducedCategory

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uD vD

open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.InducedCategory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]

/-- The actual induced ordinary category retains the entire original enriched Hom data. -/
@[instance_reducible]
def enrichedOrdinaryCategory (f : A → D) : EnrichedOrdinaryCategory V (InducedCategory D f) where
  toEnrichedCategory := EnrichedCategory.ofObjectFunction f
  homEquiv := InducedCategory.homEquiv.trans (eHomEquiv V)
  homEquiv_id X := eHomEquiv_id V (f X)
  homEquiv_comp f g := eHomEquiv_comp V f.hom g.hom

/-- The induced ordinary enrichment is the original restriction on every data field. -/
theorem enrichedOrdinaryCategory_enrichment (f : A → D) :
    (enrichedOrdinaryCategory V f).toEnrichedCategory =
      EnrichedCategory.ofObjectFunction (V := V) f := by rfl

/-- The complete induced Hom equivalence uses the original ordinary arrows and point map. -/
theorem enrichedOrdinaryCategory_homEquiv_function (f : A → D)
    (a b : InducedCategory D f) :
    (enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b) =
      (InducedCategory.homEquiv (F := f)).trans (eHomEquiv V) := by rfl

/-- The entire forward point function retains the exact original induced morphism. -/
theorem enrichedOrdinaryCategory_point_function (f : A → D)
    (a b : InducedCategory D f) :
    ((enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).toFun =
      (fun g : a ⟶ b => eHomEquiv V g.hom) := by rfl

/-- The entire inverse point function recovers the original induced arrow constructor. -/
theorem enrichedOrdinaryCategory_inverse_function (f : A → D)
    (a b : InducedCategory D f) :
    ((enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).invFun =
      (fun p => InducedCategory.homMk (D := D) (F := f) (X := a) (Y := b)
        ((eHomEquiv V (C := D) (X := f a) (Y := f b)).symm p)) := by rfl

variable [BraidedCategory V]

/-- The complete induced opposite equivalence projects and reverses the original full arrow. -/
theorem enrichedOrdinaryCategory_opposite_homEquiv_function (f : A → Dᵒᵖ)
    (a b : InducedCategory Dᵒᵖ f) :
    (enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b) =
      (InducedCategory.homEquiv (F := f)).trans
        (Quiver.Hom.opEquiv.symm.trans (eHomEquiv V)) := by rfl

/-- Every induced opposite point is the point of the entire original reversed morphism. -/
theorem enrichedOrdinaryCategory_opposite_point_function (f : A → Dᵒᵖ)
    (a b : InducedCategory Dᵒᵖ f) :
    ((enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).toFun =
      (fun g : a ⟶ b => eHomEquiv V g.hom.unop) := by rfl

/-- Every inverse induced opposite point constructs the same full reversed original arrow. -/
theorem enrichedOrdinaryCategory_opposite_inverse_function (f : A → Dᵒᵖ)
    (a b : InducedCategory Dᵒᵖ f) :
    ((enrichedOrdinaryCategory V f).homEquiv (X := a) (Y := b)).invFun =
      (fun p => InducedCategory.homMk (D := Dᵒᵖ) (F := f) (X := a) (Y := b)
        (((eHomEquiv V (C := D) (X := (f b).unop) (Y := (f a).unop)).symm p).op)) := by rfl

end CategoryTheory.InducedCategory

namespace CategoryTheory.EnrichedOrdinaryCategory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]

/-- The complete opposite point equivalence uses the original arrow reversal. -/
theorem opposite_homEquiv_function (a b : Dᵒᵖ) :
    (EnrichedOrdinaryCategory.opposite V).homEquiv (X := a) (Y := b) =
      Quiver.Hom.opEquiv.symm.trans (eHomEquiv V) := by rfl

/-- Every opposite point is the original point of the same full reversed morphism. -/
theorem opposite_point_function (a b : Dᵒᵖ) :
    ((EnrichedOrdinaryCategory.opposite V).homEquiv (X := a) (Y := b)).toFun =
      (fun g : a ⟶ b => eHomEquiv V g.unop) := by rfl

/-- Every inverse opposite point reverses the original full inverse-point morphism. -/
theorem opposite_inverse_function (a b : Dᵒᵖ) :
    ((EnrichedOrdinaryCategory.opposite V).homEquiv (X := a) (Y := b)).invFun =
      (fun p => ((eHomEquiv V (C := D) (X := b.unop) (Y := a.unop)).symm p).op) := by rfl

end CategoryTheory.EnrichedOrdinaryCategory

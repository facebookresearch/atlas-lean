/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.InducedPointTransport
public import MathlibExtTest.CategoryTheory.Enriched.WholeInducedPointFunctionTests

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uD vD

open CategoryTheory MonoidalCategory Opposite

namespace InducedPointTransportTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {A : Type uA} {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]
  (f : A → Dᵒᵖ) (a b : InducedCategory Dᵒᵖ f)
  (h : (InducedCategory.enrichedOrdinaryCategory V f).toEnrichedCategory.Hom a b =
    ((f b).unop ⟶[V] (f a).unop))

example :
    (fun g : a ⟶ b => (InducedCategory.enrichedOrdinaryCategory V f).homEquiv g ≫
      (eqToIso h).hom) =
        (fun g : a ⟶ b => eHomEquiv V (C := D) g.hom.unop) :=
  InducedCategory.enrichedOrdinaryCategory_opposite_point_function_eqToIso V f a b h

example (g : a ⟶ b) :
    (InducedCategory.enrichedOrdinaryCategory V f).homEquiv g ≫ (eqToIso h).hom =
      eHomEquiv V (C := D) g.hom.unop :=
  InducedCategory.enrichedOrdinaryCategory_opposite_point_eqToIso V f a b h g

example {Z : V} (g : a ⟶ b) (r : ((f b).unop ⟶[V] (f a).unop) ⟶ Z) :
    (InducedCategory.enrichedOrdinaryCategory V f).homEquiv g ≫ (eqToIso h).hom ≫ r =
      eHomEquiv V (C := D) g.hom.unop ≫ r :=
  InducedCategory.enrichedOrdinaryCategory_opposite_point_eqToIso_assoc V f a b h g r

example :
    (fun p : 𝟙_ V ⟶ ((f b).unop ⟶[V] (f a).unop) =>
      (InducedCategory.enrichedOrdinaryCategory V f).homEquiv.symm (p ≫ (eqToIso h).inv)) =
        (fun p => InducedCategory.homMk (D := Dᵒᵖ) (F := f) (X := a) (Y := b)
          (((eHomEquiv V (C := D) (X := (f b).unop) (Y := (f a).unop)).symm p).op)) :=
  InducedCategory.enrichedOrdinaryCategory_opposite_inverse_function_eqToIso V f a b h

end InducedPointTransportTests

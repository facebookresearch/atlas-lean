/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

module

public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor

/-!
# Original scalar tensor and free identity-evaluation maps

The actual free/scalar associator commutes with the original coefficient
evaluation. The equation retains every index Hom object and scalar map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.Free

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Evaluating the original scalar image of a free map uses the same coefficient map. -/
theorem evaluate_scalarFreeIso (M : V) (a : A) (K : V)
    (X : EnrichedFunctorCat V A) (f : object a K ⟶ X) :
    evaluate a (M ⊗ K) (tensorLeftObject M X)
        ((scalarFreeIso M K a).inv ≫ tensorLeftMap M f) =
      M ◁ evaluate a K X f := by
  rw [evaluate, component_comp, scalarFreeIso_inv_component, tensorLeftMap_component]
  change (ρ_ (M ⊗ K)).inv ≫ ((M ⊗ K) ◁ eId V a) ≫
      (α_ M K (a ⟶[V] a)).hom ≫ M ◁ component f a =
    M ◁ ((ρ_ K).inv ≫ (K ◁ eId V a) ≫ component f a)
  have hn : ((M ⊗ K) ◁ eId V a) ≫ (α_ M K (a ⟶[V] a)).hom =
      (α_ M K (𝟙_ V)).hom ≫ M ◁ (K ◁ eId V a) :=
    associator_naturality_right M K (eId V a)
  have h : (ρ_ (M ⊗ K)).inv ≫ (α_ M K (𝟙_ V)).hom = M ◁ (ρ_ K).inv := by
    monoidal
  calc
    _ = (ρ_ (M ⊗ K)).inv ≫
        (α_ M K (𝟙_ V)).hom ≫ M ◁ (K ◁ eId V a) ≫ M ◁ component f a := by
      rw [← Category.assoc ((M ⊗ K) ◁ eId V a), hn]
      simp only [Category.assoc]
    _ = _ := by
      rw [← Category.assoc (ρ_ (M ⊗ K)).inv, h,
        ← whiskerLeft_comp, ← whiskerLeft_comp]

end CategoryTheory.EnrichedFunctorCat.Free

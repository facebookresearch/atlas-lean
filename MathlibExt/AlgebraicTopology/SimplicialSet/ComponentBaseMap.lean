/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents

/-!
# Actual maps between existing simplicial components

A simplicial base map restricts from each original component to the
component selected by its ACTUAL π₀ map. Its ambient inclusion square is
literal; no component compatibility or expected comparison is supplied.
-/

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- The actual base map on one existing π₀ component. -/
public def componentBaseMap (f : X ⟶ Y) (c : π₀ X) :
    (π₀.component c : SSet.{u}) ⟶ (π₀.component (mapπ₀ f c) : SSet.{u}) where
  app n := TypeCat.ofHom (fun (σ : (π₀.component c : SSet.{u}).obj n) =>
    (⟨f.app n σ.1, by
      change π₀.mk (Y.map (⦋0⦌.const n.unop 0).op (f.app n σ.1)) = mapπ₀ f c
      rw [← NatTrans.naturality_apply]
      rw [← mapπ₀_mk, σ.2]⟩ :
        (π₀.component (mapπ₀ f c) : SSet.{u}).obj n))
  naturality n m q := by
    ext σ
    apply Subtype.ext
    change f.app m (X.map q σ.1) = Y.map q (f.app n σ.1)
    exact NatTrans.naturality_apply f q σ.1

/-- The actual restricted map has the SAME original ambient base map. -/
@[reassoc]
public theorem componentBaseMap_ι (f : X ⟶ Y) (c : π₀ X) :
    componentBaseMap f c ≫ (π₀.component (mapπ₀ f c)).ι =
      (π₀.component c).ι ≫ f := by
  ext n σ
  change f.app n σ.1 = f.app n σ.1
  rfl

/-- Every component simplex retains its original image simplex. -/
public theorem componentBaseMap_app_val (f : X ⟶ Y) (c : π₀ X)
    (n : SimplexCategoryᵒᵖ) (σ : (π₀.component c : SSet.{u}).obj n) :
    ((componentBaseMap f c).app n σ).val = f.app n σ.val := by
  change f.app n σ.val = f.app n σ.val
  rfl

end SSet

end

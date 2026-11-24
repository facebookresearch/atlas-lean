/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeUniversalProperty

/-!
# Independent object universes for computads and scalar-degree functors

The generator universe is independent of the large original label type.
The target object universe is also independent of both. These clients
exercise the canonical computad API and the existing scalar-category API.
-/

noncomputable section
universe u v w
open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.SimplicialComputadUniverse

/-- Constant atoms on an independently large original object type. -/
def largeComputad (O : Type (v + 31)) : SSet.SimplicialComputad.{u, v + 31} O where
  generator _ _ _ := ULift.{u} Unit
  operator {_Δ _Δ'} _θ {_x _y} a := SSet.SimplicialComputad.single a
  operator_id _Δ {_x _y} _a := rfl
  operator_comp {_Δ _Δ' _Δ''} _θ _φ {_x _y} a :=
    (SSet.SimplicialComputad.pathMap_single
      (G := fun (_ _ : O) => ULift.{u} Unit) (H := fun (_ _ : O) => ULift.{u} Unit)
      (fun a => SSet.SimplicialComputad.single a) a).symm

example (O : Type (v + 31)) (x y : O) : SSet.{max u (v + 31)} :=
  (largeComputad.{u, v} O).hom x y

example (O : Type (v + 31)) (C : Type (w + 29))
    [EnrichedCategory SSet.{max u (v + 31)} C] :
    (EnrichedFunctor SSet.{max u (v + 31)} (largeComputad.{u, v} O).Object C) ≃
      SSet.SimplicialComputad.Assignment (largeComputad.{u, v} O) (C := C) :=
  SSet.SimplicialComputad.functorEquiv (largeComputad.{u, v} O)

example {O : Type} (A : SSet.SimplicialComputad.{u} O)
    {C : Type w} [EnrichedCategory SSet.{u} C] :
    (EnrichedFunctor SSet.{u} A.Object C) ≃ SSet.SimplicialComputad.Assignment A (C := C) :=
  SSet.SimplicialComputad.functorEquiv A

example {C : Type (v + 31)} {D : Type (w + 29)}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    (F : EnrichedFunctor SSet.{u} C D) (Δ : SimplexCategoryᵒᵖ) :
    SSet.ScalarObject C Δ ⥤ SSet.ScalarObject D Δ :=
  SSet.scalarFunctor F Δ

example {C : Type (v + 31)} {D : Type (w + 29)}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    (F : EnrichedFunctor SSet.{u} C D) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (x y : C) (a : (x ⟶[SSet.{u}] y).obj Δ) :
    (SSet.scalarFunctor F Δ').map
        ((SSet.scalarOperator (C := C) θ).map (X := ⟨x⟩) (Y := ⟨y⟩) a) =
      (SSet.scalarOperator (C := D) θ).map
        ((SSet.scalarFunctor F Δ).map (X := ⟨x⟩) (Y := ⟨y⟩) a) :=
  NatTrans.naturality_apply (F.map x y) θ a

end MathlibExtTest.SimplicialComputadUniverse

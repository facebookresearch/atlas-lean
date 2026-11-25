/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Transport
public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Naturality

/-!
# Independence of transported finite-frame comparisons

The two original frames may have different ranks. Their transported points
are the same original object, and the earned arbitrary-morphism naturality
at its identity proves equality of their genuine comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.DualFiniteFrame

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Transporting two actual finite frames to the same original object gives
the same canonical dual comparison, even when the finite ranks differ. -/
theorem transportedFrameComparison_independent
    (F : C ⥤ D) [F.Additive] (G : Cᵒᵖ ⥤ C) [G.Additive]
    (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I J : Type w) [Fintype I] [Fintype J]
    (U : C) [HasBiproduct (fun _ : I => U)] [HasBiproduct (fun _ : J => U)]
    (V : D) [HasBiproduct (fun _ : I => V)] [HasBiproduct (fun _ : J => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hG : ∀ q : U ⟶ U, G.map q.op ≫ eG.hom = eG.hom ≫ q)
    (hH : ∀ q : V ⟶ V, H.map q.op ≫ eH.hom = eH.hom ≫ q)
    (M : C) (a : Bicone (fun _ : I => U)) (ha : a.IsBilimit) (ea : a.pt ≅ M)
    (b : Bicone (fun _ : J => U)) (hb : b.IsBilimit) (eb : b.pt ≅ M) :
    (finiteFrameDualComparisonIso F G H I U V u eG eH
      (transportUnitBicone a ea) (transportUnitBiconeIsBilimit a ha ea)).hom =
    (finiteFrameDualComparisonIso F G H J U V u eG eH
      (transportUnitBicone b eb) (transportUnitBiconeIsBilimit b hb eb)).hom := by
  have h := finiteFrameDualComparisonIso_naturality F G H I J U V u eG eH hG hH
    (transportUnitBicone a ea) (transportUnitBiconeIsBilimit a ha ea)
    (transportUnitBicone b eb) (transportUnitBiconeIsBilimit b hb eb) (𝟙 M)
  dsimp only [transportUnitBicone] at h
  have hGid : G.map (𝟙 M).op = 𝟙 (G.obj (op M)) :=
    (congrArg G.map (op_id (X := M))).trans (G.map_id (op M))
  have hHid : H.map (F.map (𝟙 M)).op = 𝟙 (H.obj (op (F.obj M))) :=
    (congrArg (fun a => H.map a.op) (F.map_id M)).trans
      ((congrArg H.map (op_id (X := F.obj M))).trans (H.map_id (op (F.obj M))))
  rw [hGid, F.map_id, hHid, Category.id_comp, Category.comp_id] at h
  exact h

end CategoryTheory.DualFiniteFrame

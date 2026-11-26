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
# Independence of finite-frame contravariant comparisons

Let F : C ⥤ D be additive between preadditive categories, G,H additive contravariant
endofunctors, and U,V coefficient objects with u : F(U) ≅ V, e_G : G(U) ≅ U and e_H : H(V) ≅
V. Assume G(q.op) ≫ e_G.hom = e_G.hom ≫ q for every endomorphism q of U, and the corresponding
equation for H and endomorphisms of V.

Suppose finite bilimit bicones a and b of copies of U have points identified with the same
object M. Transport each bicone along its identification to M. Their canonical comparison maps
F(G(M)) → H(F(M)) agree, even when their finite index sets have different cardinalities.
Naturality at id_M gives this frame independence; the category worlds and indexing universe
remain independent.
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

/-- Equality of comparisons from two transported finite frames.

Let F : C ⥤ D be additive between preadditive categories, G : Cᵒᵖ ⥤ C and H : Dᵒᵖ ⥤ D
additive, with u : F(U) ≅ V, e_G : G(U) ≅ U and e_H : H(V) ≅ V. Suppose G(q.op) ≫ e_G.hom =
e_G.hom ≫ q for all q : U → U and H(q.op) ≫ e_H.hom = e_H.hom ≫ q for all q : V → V. For
finite bilimit bicones a,b of copies of U with a.pt ≅ M and b.pt ≅ M, transport both to M. The
resulting comparison homs F(G(M)) → H(F(M)) are equal; the two finite index sets may differ. -/
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

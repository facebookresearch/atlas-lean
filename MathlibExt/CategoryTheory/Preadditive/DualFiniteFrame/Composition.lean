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

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Naturality

/-!
# Composition of canonical actual finite-frame dual comparison

The original evaluation values determine comparison under successive additive
unit-preserving functors. This is the coherence used on overlaps of scheme
restriction and pullback charts.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ u₃ v₁ v₂ v₃ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]

/-- Canonical finite-frame dual comparison agrees with successive comparison
through the actual intermediate image frame. -/
theorem finiteFrameDualComparisonIso_comp (F : C ⥤ D) [F.Additive]
    (T : D ⥤ E) [T.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (K : Eᵒᵖ ⥤ E) [K.Additive]
    (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (W : E) [HasBiproduct (fun _ : I => W)]
    (u : F.obj U ≅ V) (t : T.obj V ≅ W)
    (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V) (eK : K.obj (op W) ≅ W)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    (finiteFrameDualComparisonIso (F ⋙ T) G K I U W (T.mapIso u ≪≫ t) eG eK b hb).hom =
      T.map (finiteFrameDualComparisonIso F G H I U V u eG eH b hb).hom ≫
        (finiteFrameDualComparisonIso T H K I V W t eH eK
          (mapUnitBicone F I U V u b) (mapUnitBiconeIsBilimit F I U V u b hb)).hom := by
  apply finiteFrameDualComparison_hom_ext (F ⋙ T) K I U W (T.mapIso u ≪≫ t) eK b hb
  intro i
  let A := finiteFrameDualComparisonIso F G H I U V u eG eH b hb
  let B : T.obj (H.obj (op (F.obj b.pt))) ≅ K.obj (op (T.obj (F.obj b.pt))) :=
    finiteFrameDualComparisonIso T H K I V W t eH eK
    (mapUnitBicone F I U V u b) (mapUnitBiconeIsBilimit F I U V u b hb)
  have hv : (T.mapIso u ≪≫ t).inv ≫ (F ⋙ T).map (b.ι i) =
      t.inv ≫ T.map (u.inv ≫ F.map (b.ι i)) := by
    simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.comp_map, T.map_comp, Category.assoc]
  have hleft := finiteFrameDualComparisonIso_generator (F ⋙ T) G K I U W
    (T.mapIso u ≪≫ t) eG eK b hb i
  have hright : (T.map A.hom ≫ B.hom) ≫
      (K.map ((T.mapIso u ≪≫ t).inv ≫ (F ⋙ T).map (b.ι i)).op ≫ eK.hom) =
      (F ⋙ T).map (G.map (b.ι i).op ≫ eG.hom) ≫ (T.mapIso u ≪≫ t).hom := by
    rw [hv]
    have hB : B.hom ≫ (K.map (t.inv ≫ T.map (u.inv ≫ F.map (b.ι i))).op ≫ eK.hom) =
        T.map (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom) ≫ t.hom :=
      finiteFrameDualComparisonIso_generator T H K I V W t eH eK
        (mapUnitBicone F I U V u b) (mapUnitBiconeIsBilimit F I U V u b hb) i
    have hA := finiteFrameDualComparisonIso_generator F G H I U V u eG eH b hb i
    calc
      _ = T.map A.hom ≫ (B.hom ≫
          (K.map (t.inv ≫ T.map (u.inv ≫ F.map (b.ι i))).op ≫ eK.hom)) :=
        Category.assoc _ _ _
      _ = T.map A.hom ≫ (T.map (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom) ≫ t.hom) :=
        congrArg (fun z => T.map A.hom ≫ z) hB
      _ = (T.map A.hom ≫ T.map (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom)) ≫ t.hom :=
        (Category.assoc _ _ _).symm
      _ = T.map (A.hom ≫ (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom)) ≫ t.hom :=
        congrArg (fun z => z ≫ t.hom) (T.map_comp _ _).symm
      _ = T.map (F.map (G.map (b.ι i).op ≫ eG.hom) ≫ u.hom) ≫ t.hom :=
        congrArg (fun z => T.map z ≫ t.hom) hA
      _ = _ := by
        simp only [Functor.comp_map, T.map_comp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact hleft.trans hright.symm

end CategoryTheory.DualFiniteFrame

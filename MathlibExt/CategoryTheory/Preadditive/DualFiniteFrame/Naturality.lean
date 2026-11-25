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

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Comparison

/-!
# Naturality and independence of actual finite-frame dual comparison

The coefficient transpose identity extends characteristic generator values to
every actual unit-source morphism. Those values determine the comparison and
prove naturality for arbitrary morphisms and independence of the finite frame.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- The original finite unit frame expands every actual unit-source morphism. -/
theorem biconeUnitHom_decompose (I : Type w) [Fintype I] (U : C)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (v : U ⟶ b.pt) :
    (∑ i, (v ≫ b.π i) ≫ b.ι i) = v := by
  calc
    _ = v ≫ (∑ i, b.π i ≫ b.ι i) := by
      simp only [Preadditive.comp_sum, Category.assoc]
    _ = v := by rw [IsBilimit.total hb, Category.comp_id]

/-- The genuine unit transpose law expands dual evaluation on every original
unit-source morphism through the actual finite frame. -/
theorem dualBiconeUnitHom_decompose (G : Cᵒᵖ ⥤ C) [G.Additive]
    (I : Type w) [Fintype I] (U : C) (e : G.obj (op U) ≅ U)
    (he : ∀ q : U ⟶ U, G.map q.op ≫ e.hom = e.hom ≫ q)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (v : U ⟶ b.pt) :
    G.map v.op ≫ e.hom = ∑ i, (G.map (b.ι i).op ≫ e.hom) ≫ (v ≫ b.π i) := by
  symm
  calc
    _ = ∑ i, G.map ((v ≫ b.π i) ≫ b.ι i).op ≫ e.hom := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Category.assoc, ← he (v ≫ b.π i), ← Category.assoc,
        ← G.map_comp, ← op_comp]
    _ = (∑ i, G.map ((v ≫ b.π i) ≫ b.ι i).op) ≫ e.hom :=
      (Preadditive.sum_comp _ _ _).symm
    _ = G.map (∑ i, ((v ≫ b.π i) ≫ b.ι i).op) ≫ e.hom := by
      rw [← G.map_sum]
    _ = G.map ((∑ i, (v ≫ b.π i) ≫ b.ι i).op) ≫ e.hom := by
      rw [op_sum]
    _ = _ := by rw [biconeUnitHom_decompose I U b hb v]

/-- Characteristic values extend to every actual pulled unit-source morphism,
using the genuine coefficient transpose laws on both original units. -/
theorem finiteFrameDualComparisonIso_unitHom (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hG : ∀ q : U ⟶ U, G.map q.op ≫ eG.hom = eG.hom ≫ q)
    (hH : ∀ q : V ⟶ V, H.map q.op ≫ eH.hom = eH.hom ≫ q)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (v : U ⟶ b.pt) :
    (finiteFrameDualComparisonIso F G H I U V u eG eH b hb).hom ≫
        (H.map (u.inv ≫ F.map v).op ≫ eH.hom) =
      F.map (G.map v.op ≫ eG.hom) ≫ u.hom := by
  let E := finiteFrameDualComparisonIso F G H I U V u eG eH b hb
  let B := mapUnitBicone F I U V u b
  let vb : V ⟶ B.pt := u.inv ≫ F.map v
  have ht := dualBiconeUnitHom_decompose H I V eH hH B
    (mapUnitBiconeIsBilimit F I U V u b hb) vb
  calc
    E.hom ≫ (H.map vb.op ≫ eH.hom) =
        E.hom ≫ (∑ i, (H.map (B.ι i).op ≫ eH.hom) ≫ (vb ≫ B.π i)) :=
      congrArg (fun z => E.hom ≫ z) ht
    _ = ∑ i, (E.hom ≫ (H.map (B.ι i).op ≫ eH.hom)) ≫ (vb ≫ B.π i) := by
      rw [Preadditive.comp_sum]
      simp only [Category.assoc]
    _ = ∑ i, F.map ((G.map (b.ι i).op ≫ eG.hom) ≫ (v ≫ b.π i)) ≫ u.hom := by
      apply Finset.sum_congr rfl
      intro i _
      change (E.hom ≫ (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom)) ≫
          ((u.inv ≫ F.map v) ≫ (F.map (b.π i) ≫ u.hom)) = _
      rw [finiteFrameDualComparisonIso_generator]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, F.map_comp]
    _ = F.map (∑ i, (G.map (b.ι i).op ≫ eG.hom) ≫ (v ≫ b.π i)) ≫ u.hom := by
      rw [← Preadditive.sum_comp, ← F.map_sum]
    _ = F.map (G.map v.op ≫ eG.hom) ≫ u.hom :=
      congrArg (fun z => F.map z ≫ u.hom)
        (dualBiconeUnitHom_decompose G I U eG hG b hb v).symm

/-- Actual pulled generator evaluations detect equality of maps into the
genuine dual of the actual image frame. -/
theorem finiteFrameDualComparison_hom_ext (F : C ⥤ D) [F.Additive]
    (H : Dᵒᵖ ⥤ D) [H.Additive] (I : Type w) [Fintype I]
    (U : C) (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (eH : H.obj (op V) ≅ V)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit)
    {W : D} (m n : W ⟶ H.obj (op (F.obj b.pt)))
    (h : ∀ i, m ≫ (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom) =
      n ≫ (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom)) : m = n := by
  let T := biconeDualEvaluationIso H I V eH (mapUnitBicone F I U V u b)
    (mapUnitBiconeIsBilimit F I U V u b hb)
  apply (cancel_mono T.hom).mp
  apply biproduct.hom_ext
  intro i
  have hp : T.hom ≫ biproduct.π (fun _ : I => V) i =
      H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom :=
    biconeDualEvaluationIso_hom_projection H I V eH _ _ i
  exact ((Category.assoc m T.hom _).trans (congrArg (fun z => m ≫ z) hp)).trans
    ((h i).trans ((congrArg (fun z => n ≫ z) hp).symm.trans
      (Category.assoc n T.hom _).symm))

/-- The direct finite-frame dual comparison is natural for every original
morphism, with no invertibility condition on that morphism. -/
theorem finiteFrameDualComparisonIso_naturality (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I J : Type w) [Fintype I] [Fintype J]
    (U : C) [HasBiproduct (fun _ : I => U)] [HasBiproduct (fun _ : J => U)]
    (V : D) [HasBiproduct (fun _ : I => V)] [HasBiproduct (fun _ : J => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hG : ∀ q : U ⟶ U, G.map q.op ≫ eG.hom = eG.hom ≫ q)
    (hH : ∀ q : V ⟶ V, H.map q.op ≫ eH.hom = eH.hom ≫ q)
    (a : Bicone (fun _ : I => U)) (ha : a.IsBilimit)
    (b : Bicone (fun _ : J => U)) (hb : b.IsBilimit) (φ : a.pt ⟶ b.pt) :
    F.map (G.map φ.op) ≫ (finiteFrameDualComparisonIso F G H I U V u eG eH a ha).hom =
      (finiteFrameDualComparisonIso F G H J U V u eG eH b hb).hom ≫ H.map (F.map φ).op := by
  apply finiteFrameDualComparison_hom_ext F H I U V u eH a ha
  intro i
  let A := finiteFrameDualComparisonIso F G H I U V u eG eH a ha
  let B := finiteFrameDualComparisonIso F G H J U V u eG eH b hb
  have hleft : (F.map (G.map φ.op) ≫ A.hom) ≫
      (H.map (u.inv ≫ F.map (a.ι i)).op ≫ eH.hom) =
      F.map (G.map (a.ι i ≫ φ).op ≫ eG.hom) ≫ u.hom := by
    rw [Category.assoc, finiteFrameDualComparisonIso_generator]
    simp only [F.map_comp, op_comp, G.map_comp, Category.assoc]
  have hp : H.map (F.map φ).op ≫ H.map (u.inv ≫ F.map (a.ι i)).op =
      H.map (u.inv ≫ F.map (a.ι i ≫ φ)).op := by
    rw [← H.map_comp, ← op_comp]
    simp only [F.map_comp, Category.assoc]
  have hright : (B.hom ≫ H.map (F.map φ).op) ≫
      (H.map (u.inv ≫ F.map (a.ι i)).op ≫ eH.hom) =
      F.map (G.map (a.ι i ≫ φ).op ≫ eG.hom) ≫ u.hom := by
    rw [Category.assoc, ← Category.assoc (H.map _), hp]
    exact finiteFrameDualComparisonIso_unitHom F G H J U V u eG eH hG hH b hb (a.ι i ≫ φ)
  exact hleft.trans hright.symm

/-- Any two actual finite frames on the same object define the same canonical
dual comparison; the chart index and rank may change. -/
theorem finiteFrameDualComparisonIso_frame_independent (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I J : Type w) [Fintype I] [Fintype J]
    (U : C) [HasBiproduct (fun _ : I => U)] [HasBiproduct (fun _ : J => U)]
    (V : D) [HasBiproduct (fun _ : I => V)] [HasBiproduct (fun _ : J => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (hG : ∀ q : U ⟶ U, G.map q.op ≫ eG.hom = eG.hom ≫ q)
    (hH : ∀ q : V ⟶ V, H.map q.op ≫ eH.hom = eH.hom ≫ q)
    {A : C} (a : Bicone (fun _ : I => U)) (ha : a.IsBilimit)
    (b : Bicone (fun _ : J => U)) (hb : b.IsBilimit)
    (ea : a.pt = A) (eb : b.pt = A) :
    (F.mapIso (G.mapIso (eqToIso (ea.trans eb.symm)).op)).hom ≫
        (finiteFrameDualComparisonIso F G H I U V u eG eH a ha).hom =
      (finiteFrameDualComparisonIso F G H J U V u eG eH b hb).hom ≫
        (H.mapIso ((F.mapIso (eqToIso (ea.trans eb.symm))).op)).hom :=
  finiteFrameDualComparisonIso_naturality F G H I J U V u eG eH hG hH a ha b hb
    (eqToHom (ea.trans eb.symm))

end CategoryTheory.DualFiniteFrame

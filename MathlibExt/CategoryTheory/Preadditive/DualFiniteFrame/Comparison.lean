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

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Canonical dual comparison on actual finite unit frames

An additive functor with an earned unit isomorphism carries the original finite
frame to its actual image frame. Direct genuine dual evaluation on these frames
determines the comparison, its inverse, and its projection values.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Additive preservation for the literal finite family, in its own universe. -/
theorem preservesFiniteFamily (F : C ⥤ D) [F.Additive]
    (I : Type w) [Fintype I] (f : I → C) : PreservesBiproduct f F := by
  refine ⟨fun {b} hb => ⟨isBilimitOfTotal _ ?_⟩⟩
  change (∑ i, F.map (b.π i) ≫ F.map (b.ι i)) = 𝟙 (F.obj b.pt)
  simp_rw [← F.map_comp]
  rw [← F.map_sum, ← F.map_id, IsBilimit.total hb]

/-- Direct evaluation of the genuine dual of an actual finite unit bicone. -/
def biconeDualEvaluationIso (G : Cᵒᵖ ⥤ C) [G.Additive]
    (I : Type w) [Fintype I] (U : C) [HasBiproduct (fun _ : I => U)]
    (e : G.obj (op U) ≅ U) (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    G.obj (op b.pt) ≅ ⨁ fun _ : I => U :=
  finiteFrameDualEvaluationIso G I (fun _ => U) (fun _ => U) b.ι b.π
    (bicone_ι_π_self b) (fun _ _ h => bicone_ι_π_ne b h) (IsBilimit.total hb) (fun _ => e)

/-- Evaluation on a bicone keeps each actual injection as its projection value. -/
theorem biconeDualEvaluationIso_hom_projection (G : Cᵒᵖ ⥤ C) [G.Additive]
    (I : Type w) [Fintype I] (U : C) [HasBiproduct (fun _ : I => U)]
    (e : G.obj (op U) ≅ U) (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (i : I) :
    (biconeDualEvaluationIso G I U e b hb).hom ≫ biproduct.π (fun _ : I => U) i =
      G.map (b.ι i).op ≫ e.hom := biproduct.lift_π _ _

/-- An actual unit isomorphism and additive functor transport the original
frame maps, including an empty frame. -/
def mapUnitBicone (F : C ⥤ D) [F.Additive] (I : Type w)
    (U : C) (V : D) (u : F.obj U ≅ V) (b : Bicone (fun _ : I => U)) :
    Bicone (fun _ : I => V) where
  pt := F.obj b.pt
  ι i := u.inv ≫ F.map (b.ι i)
  π i := F.map (b.π i) ≫ u.hom
  ι_π i j := by
    classical
    simp only [Category.assoc]
    rw [← Category.assoc (F.map (b.ι i)), ← F.map_comp]
    by_cases h : i = j
    · subst j
      rw [bicone_ι_π_self, F.map_id]
      simp
    · rw [bicone_ι_π_ne b h, F.map_zero]
      simp [h]

/-- The actual image frame is again a finite biproduct frame. -/
def mapUnitBiconeIsBilimit (F : C ⥤ D) [F.Additive]
    (I : Type w) [Fintype I] (U : C) (V : D) (u : F.obj U ≅ V)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    (mapUnitBicone F I U V u b).IsBilimit := by
  refine isBilimitOfTotal _ ?_
  change (∑ i, (F.map (b.π i) ≫ u.hom) ≫ (u.inv ≫ F.map (b.ι i))) = _
  calc
    _ = ∑ i, F.map (b.π i ≫ b.ι i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Category.assoc, Iso.hom_inv_id_assoc, F.map_comp]
    _ = F.map (∑ i, b.π i ≫ b.ι i) := (F.map_sum _ _).symm
    _ = 𝟙 _ := by rw [IsBilimit.total hb, F.map_id]

/-- Actual evaluation of a pulled dual frame into the target unit copower. -/
def functorBiconeDualEvaluationIso (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (e : G.obj (op U) ≅ U)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    F.obj (G.obj (op b.pt)) ≅ ⨁ fun _ : I => V := by
  have : PreservesBiproduct (fun _ : I => U) F := preservesFiniteFamily F I _
  have : HasBiproduct (fun _ : I => F.obj U) := inferInstance
  exact F.mapIso (biconeDualEvaluationIso G I U e b hb) ≪≫
    F.mapBiproduct (fun _ : I => U) ≪≫ biproduct.mapIso (fun _ : I => u)

/-- The pulled evaluation has its actual pulled generator values. -/
theorem functorBiconeDualEvaluationIso_hom_projection (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (e : G.obj (op U) ≅ U)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (i : I) :
    (functorBiconeDualEvaluationIso F G I U V u e b hb).hom ≫
        biproduct.π (fun _ : I => V) i =
      F.map (G.map (b.ι i).op ≫ e.hom) ≫ u.hom := by
  have : PreservesBiproduct (fun _ : I => U) F := preservesFiniteFamily F I _
  have : HasBiproduct (fun _ : I => F.obj U) := inferInstance
  let A := F.mapIso (biconeDualEvaluationIso G I U e b hb)
  let B := F.mapBiproduct (fun _ : I => U)
  let C : (⨁ fun _ : I => F.obj U) ≅ ⨁ fun _ : I => V :=
    biproduct.mapIso (fun _ : I => u)
  let p := biproduct.π (fun _ : I => V) i
  let q := biproduct.π (fun _ : I => F.obj U) i
  let r := F.map (biproduct.π (fun _ : I => U) i)
  have hc : C.hom ≫ p = q ≫ u.hom := by
    change biproduct.map (fun _ : I => u.hom) ≫ biproduct.π (fun _ : I => V) i = _
    exact biproduct.map_π (fun _ : I => u.hom) i
  have hb' : B.hom ≫ q = r := by
    rw [Functor.mapBiproduct_hom]
    exact biproduct.lift_π _ _
  have ha : A.hom ≫ r = F.map (G.map (b.ι i).op ≫ e.hom) := by
    exact (F.map_comp _ _).symm.trans
      (congrArg F.map (biconeDualEvaluationIso_hom_projection G I U e b hb i))
  change (A.hom ≫ (B.hom ≫ C.hom)) ≫ p = _
  calc
    _ = A.hom ≫ (B.hom ≫ (C.hom ≫ p)) := by simp only [Category.assoc]
    _ = A.hom ≫ (B.hom ≫ (q ≫ u.hom)) :=
      congrArg (fun z => A.hom ≫ (B.hom ≫ z)) hc
    _ = A.hom ≫ ((B.hom ≫ q) ≫ u.hom) :=
      congrArg (fun z => A.hom ≫ z) (Category.assoc B.hom q u.hom).symm
    _ = A.hom ≫ (r ≫ u.hom) :=
      congrArg (fun z => A.hom ≫ (z ≫ u.hom)) hb'
    _ = (A.hom ≫ r) ≫ u.hom := (Category.assoc A.hom r u.hom).symm
    _ = _ := congrArg (fun z => z ≫ u.hom) ha


/-- The canonical dual comparison on an actual finite unit frame. Both maps
are determined by the original evaluation and pulled coefficient maps. -/
def finiteFrameDualComparisonIso (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    F.obj (G.obj (op b.pt)) ≅ H.obj (op (F.obj b.pt)) :=
  functorBiconeDualEvaluationIso F G I U V u eG b hb ≪≫
    (biconeDualEvaluationIso H I V eH (mapUnitBicone F I U V u b)
      (mapUnitBiconeIsBilimit F I U V u b hb)).symm

/-- The canonical comparison retains direct evaluation on each actually
pulled original generator. -/
theorem finiteFrameDualComparisonIso_generator (F : C ⥤ D) [F.Additive]
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (u : F.obj U ≅ V) (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (i : I) :
    (finiteFrameDualComparisonIso F G H I U V u eG eH b hb).hom ≫
        (H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom) =
      F.map (G.map (b.ι i).op ≫ eG.hom) ≫ u.hom := by
  let S := functorBiconeDualEvaluationIso F G I U V u eG b hb
  let T := biconeDualEvaluationIso H I V eH (mapUnitBicone F I U V u b)
    (mapUnitBiconeIsBilimit F I U V u b hb)
  have ht : T.hom ≫ biproduct.π (fun _ : I => V) i =
      H.map (u.inv ≫ F.map (b.ι i)).op ≫ eH.hom :=
    biconeDualEvaluationIso_hom_projection H I V eH _ _ i
  change (S.hom ≫ T.inv) ≫ _ = _
  rw [← ht, Category.assoc, T.inv_hom_id_assoc]
  exact functorBiconeDualEvaluationIso_hom_projection F G I U V u eG b hb i

end CategoryTheory.DualFiniteFrame

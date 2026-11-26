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
# Finite coefficient frames and contravariant comparisons

Let C,D be preadditive, F : C ⥤ D additive, and U : C, V : D fixed objects with u : F(U) ≅ V.
A finite constant bicone b for the family i ↦ U has injections i_j, projections p_j and total
identity Σ_j p_j ≫ i_j = id_{b.pt}. Its image bicone has point F(b.pt), injections u.inv ≫
F(i_j) and projections F(p_j) ≫ u.hom. Additivity preserves the finite total identity, so this
image bicone is a bilimit when b is.

For additive contravariant functors G : Cᵒᵖ ⥤ C and H : Dᵒᵖ ⥤ D, choose e_G : G(U) ≅ U and e_H
: H(V) ≅ V. Evaluating G on the original frame, then applying F, identifies F(G(b.pt)) with
the finite biproduct of V. Evaluating H on the image frame identifies H(F(b.pt)) with that
same biproduct. Composing these comparisons gives F(G(b.pt)) ≅ H(F(b.pt)), with its values
determined by the displayed injections. The indexing, object and morphism universes are
independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Preservation of a finite biproduct family by an additive functor.

For preadditive categories C,D, an additive functor F : C ⥤ D preserves the biproduct of any
family f : I → C indexed by a finite type I. Applying F to the bicone total identity preserves
its finite sum, compositions and identity. -/
theorem preservesFiniteFamily (F : C ⥤ D) [F.Additive]
    (I : Type w) [Fintype I] (f : I → C) : PreservesBiproduct f F := by
  refine ⟨fun {b} hb => ⟨isBilimitOfTotal _ ?_⟩⟩
  change (∑ i, F.map (b.π i) ≫ F.map (b.ι i)) = 𝟙 (F.obj b.pt)
  simp_rw [← F.map_comp]
  rw [← F.map_sum, ← F.map_id, IsBilimit.total hb]

/-- Contravariant evaluation of a finite constant bicone.

Let G : Cᵒᵖ ⥤ C be additive, I finite, b a bilimit bicone of the constant family U, and e :
G(U) ≅ U. If the biproduct of I copies of U exists, evaluation on the injections gives G(b.pt)
≅ ⨁ᵢU. Its i-th projection is G((b.ι_i).op) ≫ e.hom. -/
def biconeDualEvaluationIso (G : Cᵒᵖ ⥤ C) [G.Additive]
    (I : Type w) [Fintype I] (U : C) [HasBiproduct (fun _ : I => U)]
    (e : G.obj (op U) ≅ U) (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    G.obj (op b.pt) ≅ ⨁ fun _ : I => U :=
  finiteFrameDualEvaluationIso G I (fun _ => U) (fun _ => U) b.ι b.π
    (bicone_ι_π_self b) (fun _ _ h => bicone_ι_π_ne b h) (IsBilimit.total hb) (fun _ => e)

/-- Projection formula for contravariant bicone evaluation.

For additive G, a finite bilimit bicone b of copies of U and e : G(U) ≅ U, the evaluation
isomorphism E : G(b.pt) ≅ ⨁ᵢU satisfies E.hom ≫ biproduct.π_i = G((b.ι_i).op) ≫ e.hom. -/
theorem biconeDualEvaluationIso_hom_projection (G : Cᵒᵖ ⥤ C) [G.Additive]
    (I : Type w) [Fintype I] (U : C) [HasBiproduct (fun _ : I => U)]
    (e : G.obj (op U) ≅ U) (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (i : I) :
    (biconeDualEvaluationIso G I U e b hb).hom ≫ biproduct.π (fun _ : I => U) i =
      G.map (b.ι i).op ≫ e.hom := biproduct.lift_π _ _

/-- Image bicone of a constant coefficient family.

Let F : C ⥤ D be additive between preadditive categories and u : F(U) ≅ V. For any bicone b on
the family i ↦ U, form a bicone on i ↦ V with point F(b.pt), injection u.inv ≫ F(b.ι_i) and
projection F(b.π_i) ≫ u.hom. This bicone construction allows an arbitrary index type. -/
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

/-- Bilimit of the image finite coefficient bicone.

For additive F, finite I, u : F(U) ≅ V and a bilimit bicone b of I copies of U, the image
bicone on V is again a bilimit. Its total sum reduces to F(Σ_i b.π_i ≫ b.ι_i) = id_{F(b.pt)}. -/
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

/-- Transported contravariant evaluation into a coefficient biproduct.

Let F : C ⥤ D and G : Cᵒᵖ ⥤ C be additive, b a finite bilimit bicone of copies of U, u : F(U)
≅ V and e : G(U) ≅ U. With the finite biproducts of U and V defined, applying F to the
G-evaluation and using additive biproduct preservation gives F(G(b.pt)) ≅ ⨁ᵢV. -/
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

/-- Projection formula for transported contravariant evaluation.

Under the finite bicone and additive functor hypotheses, the comparison S : F(G(b.pt)) ≅ ⨁ᵢV
satisfies S.hom ≫ biproduct.π_i = F(G((b.ι_i).op) ≫ e.hom) ≫ u.hom. Here u identifies F(U)
with V and e identifies G(U) with U. -/
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


/-- Contravariant comparison on a finite coefficient frame.

Let F,G,H be additive with F : C ⥤ D and G,H contravariant endofunctors of C,D. For a finite
bilimit frame b of copies of U and isomorphisms u : F(U) ≅ V, e_G : G(U) ≅ U and e_H : H(V) ≅
V, compare F(G(b.pt)) and H(F(b.pt)) through their evaluation isomorphisms with the same
finite biproduct of V. -/
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

/-- Injection evaluation equation for a finite-frame comparison.

For the canonical comparison χ : F(G(b.pt)) ≅ H(F(b.pt)), let i'_j = u.inv ≫ F(b.ι_j) be the
injection of the image frame. Then χ.hom ≫ H((i'_j).op) ≫ e_H.hom = F(G((b.ι_j).op) ≫ e_G.hom)
≫ u.hom for every finite frame index j. -/
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

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
# Naturality and frame independence of dual comparisons

In a preadditive category, a finite biproduct frame with inclusions ι_i and
projections π_i decomposes a map v:U → A as ∑ᵢι_i∘π_i∘v.
For an additive contravariant functor G with e:G(U) ≅ U satisfying
e∘G(qᵒᵖ)=q∘e on endomorphisms of U, this also decomposes dual evaluation.

For additive F:C → D and additive dual functors G,H with compatible
distinguished objects and their transpose laws, the finite-frame comparison
F(G(A)) ≅ H(F(A)) has the corresponding evaluation on every map U → A.
Dual generator evaluations detect equality, the comparison is natural in
arbitrary maps between framed objects, and it agrees for two finite frames
whose points are identified with the same object.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ v₁ v₂ w
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- In a preadditive category C, let b be a finite biproduct bicone of
copies of U, with inclusions ι_i and projections π_i. Every map
v:U → b.pt satisfies v=∑ᵢι_i∘π_i∘v. -/
theorem biconeUnitHom_decompose (I : Type w) [Fintype I] (U : C)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) (v : U ⟶ b.pt) :
    (∑ i, (v ≫ b.π i) ≫ b.ι i) = v := by
  calc
    _ = v ≫ (∑ i, b.π i ≫ b.ι i) := by
      simp only [Preadditive.comp_sum, Category.assoc]
    _ = v := by rw [IsBilimit.total hb, Category.comp_id]

/-- Let C be preadditive, G:Cᵒᵖ → C additive, and e:G(U) ≅ U satisfy
e∘G(qᵒᵖ)=q∘e for every endomorphism q of U.
For a finite bilimit bicone b of copies of U and v:U → b.pt,
e∘G(vᵒᵖ)=∑ᵢ(π_i∘v)∘e∘G(ι_iᵒᵖ). -/
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

/-- Let C,D be preadditive categories, F:C → D additive, and
G:Cᵒᵖ → C, H:Dᵒᵖ → D additive. Fix objects U,V and isomorphisms
u:F(U) ≅ V, e_G:G(U) ≅ U and e_H:H(V) ≅ V. Assume e_G∘G(qᵒᵖ)=q∘e_G for every endomorphism q of U,
and e_H∘H(tᵒᵖ)=t∘e_H for every endomorphism t of V.
For finite I, choose I-fold biproducts of U,V and a bilimit bicone b of
copies of U. If E_b:F(G(b.pt)) ≅ H(F(b.pt)) is the finite-frame comparison,
then every v:U → b.pt satisfies
e_H∘H((F(v)∘u⁻¹)ᵒᵖ)∘E_b=u∘F(e_G∘G(vᵒᵖ)). -/
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

/-- Let C,D be preadditive, F:C → D and H:Dᵒᵖ → D additive, with
u:F(U) ≅ V and e_H:H(V) ≅ V. For finite I, choose an I-fold biproduct
of V and a bilimit bicone b of copies of U.
Two maps m,n:W → H(F(b.pt)) are equal if all evaluations
e_H∘H((F(ι_i)∘u⁻¹)ᵒᵖ)∘m and
e_H∘H((F(ι_i)∘u⁻¹)ᵒᵖ)∘n are equal. -/
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

/-- Let C,D be preadditive categories, F:C → D additive, and
G:Cᵒᵖ → C, H:Dᵒᵖ → D additive. Fix objects U,V and isomorphisms
u:F(U) ≅ V, e_G:G(U) ≅ U and e_H:H(V) ≅ V. Assume e_G∘G(qᵒᵖ)=q∘e_G for every endomorphism q of U,
and e_H∘H(tᵒᵖ)=t∘e_H for every endomorphism t of V.
For finite index sets I,J, choose the corresponding biproducts of U and
V, and bilimit frames a,b of copies of U. For every map φ:a.pt → b.pt,
the comparisons E_a,E_b satisfy
E_a∘F(G(φᵒᵖ))=H(F(φ)ᵒᵖ)∘E_b. -/
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

/-- Let C,D be preadditive categories, F:C → D additive, and
G:Cᵒᵖ → C, H:Dᵒᵖ → D additive. Fix objects U,V and isomorphisms
u:F(U) ≅ V, e_G:G(U) ≅ U and e_H:H(V) ≅ V. Assume e_G∘G(qᵒᵖ)=q∘e_G for every endomorphism q of U,
and e_H∘H(tᵒᵖ)=t∘e_H for every endomorphism t of V.
For finite I,J and the corresponding biproducts of U,V, let a and b be
bilimit frames with points identified by equalities a.pt=A and b.pt=A.
Their finite-frame comparisons agree through the canonical source and
target identifications induced by these equalities. -/
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

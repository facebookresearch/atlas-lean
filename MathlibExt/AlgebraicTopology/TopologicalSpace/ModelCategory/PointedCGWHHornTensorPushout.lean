/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornCoproductClosed
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHFreeIntervalHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHSDRPushout
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Actual native pointed pushouts of arbitrary horn tensors

The original free-point action supplies an ordinary homotopy on the full
underlying carrier. Connected-colimit preservation maps the actual pointed
pushout, and native closed SDR cobase change proves its actual new leg weak.
For arbitrary attaching cofans, both colimit comparisons transport the
retraction and action without changing any original attaching or pushout map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC
open CategoryTheory Limits MonoidalCategory Topology
open scoped Simplicial

namespace PointedCGWH

/-- Transport of a tensor action along an isomorphism of its acted-on object. -/
def transportAction {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {I B₀ B : C} (e : B₀ ≅ B) (H : I ⊗ B₀ ⟶ B₀) : I ⊗ B ⟶ B :=
  (I ◁ e.inv) ≫ H ≫ e.hom

private theorem transportAction_endpoint
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {I B₀ B : C} (e : B₀ ≅ B) (H : I ⊗ B₀ ⟶ B₀)
    (η : 𝟙_ C ⟶ I) (f : B₀ ⟶ B₀)
    (h : (λ_ B₀).inv ≫ (η ▷ B₀) ≫ H = f) :
    (λ_ B).inv ≫ (η ▷ B) ≫ transportAction e H = e.inv ≫ f ≫ e.hom := by
  unfold transportAction
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simpa only [Category.assoc] using
    congrArg (fun q : B₀ ⟶ B₀ => e.inv ≫ q ≫ e.hom) h

private theorem transportAction_fix
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {I A₀ A B₀ B : C} (eA : A₀ ≅ A) (eB : B₀ ≅ B)
    (m₀ : A₀ ⟶ B₀) (m : A ⟶ B) (hm : eA.hom ≫ m = m₀ ≫ eB.hom)
    (H : I ⊗ B₀ ⟶ B₀) (c : I ⟶ 𝟙_ C)
    (hfix : (I ◁ m₀) ≫ H = (c ▷ A₀) ≫ (λ_ A₀).hom ≫ m₀) :
    (I ◁ m) ≫ transportAction eB H = (c ▷ A) ≫ (λ_ A).hom ≫ m := by
  have hm' : m ≫ eB.inv = eA.inv ≫ m₀ := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun q : A₀ ⟶ B => eA.inv ≫ q ≫ eB.inv) hm
  have hm'' : eA.inv ≫ m₀ ≫ eB.hom = m := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (congrArg (fun q : A ⟶ B₀ => q ≫ eB.hom) hm').symm
  unfold transportAction
  calc
    _ = (I ◁ (m ≫ eB.inv)) ≫ H ≫ eB.hom := by
      rw [← whiskerLeft_comp_assoc]
    _ = (I ◁ eA.inv) ≫ (I ◁ m₀) ≫ H ≫ eB.hom := by
      rw [hm', whiskerLeft_comp_assoc]
    _ = (I ◁ eA.inv) ≫ (c ▷ A₀) ≫ (λ_ A₀).hom ≫ m₀ ≫ eB.hom := by
      simpa only [Category.assoc] using
        congrArg (fun q : I ⊗ A₀ ⟶ B₀ => (I ◁ eA.inv) ≫ q ≫ eB.hom) hfix
    _ = (c ▷ A) ≫ (λ_ A).hom ≫ eA.inv ≫ m₀ ≫ eB.hom := by
      rw [whisker_exchange_assoc, leftUnitor_naturality_assoc]
    _ = _ := by rw [hm'']

private theorem action_cobaseChange_mem_weakHomotopyEquivalences
    {A X Y P : PointedCGWH.{u, v}} {i : A ⟶ X} {f : A ⟶ Y}
    {g : X ⟶ P} {j : Y ⟶ P} (h : IsPushout i f g j)
    (hi : IsClosedEmbedding (ConcreteCategory.hom i.right)) (r : X ⟶ A)
    (hRet : i ≫ r = 𝟙 A)
    (H : (Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval ⊗ X ⟶ X)
    (h₀ : (λ_ X).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 X) ≫ H = 𝟙 X)
    (h₁ : (λ_ X).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 X) ≫ H = r ≫ i)
    (hFix : (𝟙 _ ⊗ₘ i) ≫ H =
      (freePointIntervalCollapse ⊗ₘ 𝟙 A) ≫ (λ_ A).hom ≫ i) :
    CGWH.weakHomotopyEquivalences j.right := by
  let U := pointedToCGWH.{u, v}
  have hU : IsPushout i.right f.right g.right j.right := h.map U
  have hRetU : i.right ≫ r.right = 𝟙 A.right := by
    exact congrArg (fun q : A ⟶ A => q.right) hRet
  let hOrd := freePointIntervalActionHomotopy (𝟙 X) (r ≫ i) H h₀ h₁
  let hTop : TopCat.Homotopy
      (CGWH.cgwhToTop.map (𝟙 X.right)) (CGWH.cgwhToTop.map (r.right ≫ i.right)) :=
    hOrd
  apply CGWH.sdr_cobaseChange_mem_weakHomotopyEquivalences hU hi r.right hRetU hTop
  intro t a
  exact freePointIntervalActionHomotopy_fixed (𝟙 X) (r ≫ i) H h₀ h₁ i i hFix t a

/-- Every actual pointed pushout of one arbitrary-coefficient horn tensor has a weak new leg. -/
theorem freePointHornTensor_cobaseChange_mem_weakHomotopyEquivalences
    (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v})
    {Y P : PointedCGWH.{u, v}}
    {f : (Under.costar CGWH.point).obj
      (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i)) ⊗ K ⟶ Y}
    {g : (Under.costar CGWH.point).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) ⊗ K ⟶ P} {j : Y ⟶ P}
    (h : IsPushout
      (((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i)) ⊗ₘ 𝟙 K)
      f g j) :
    CGWH.weakHomotopyEquivalences j.right :=
  action_cobaseChange_mem_weakHomotopyEquivalences h
    (freePointHornTensorInclusion_isClosedEmbedding n i K)
    (freePointHornRetraction n i ⊗ₘ 𝟙 K)
    (freePointHornTensor_inclusion_ret n i K)
    (freePointHornTensorIntervalAction n i K)
    (freePointHornTensorIntervalAction_zero n i K)
    (freePointHornTensorIntervalAction_one n i K)
    (freePointHornTensorIntervalAction_fix n i K)

variable (J : Type v) (n : J → ℕ) (i : ∀ a, Fin (n a + 2))
  (K : J → PointedCGWH.{u, v})

/-- The arbitrary native pointed horn-tensor coproduct has a weak actual pushout leg. -/
theorem freePointHornTensorCoproduct_cobaseChange_mem_weakHomotopyEquivalences
    {Y P : PointedCGWH.{u, v}}
    {f : freePointHornTensorCoproductSource J n i K ⟶ Y}
    {g : freePointHornTensorCoproductTarget J n K ⟶ P} {j : Y ⟶ P}
    (h : IsPushout (freePointHornTensorCoproductInclusion J n i K) f g j) :
    CGWH.weakHomotopyEquivalences j.right :=
  action_cobaseChange_mem_weakHomotopyEquivalences h
    (freePointHornTensorCoproductInclusion_isClosedEmbedding J n i K)
    (freePointHornTensorCoproductRetraction J n i K)
    (freePointHornTensorCoproduct_inclusion_ret J n i K)
    (freePointHornTensorCoproductIntervalAction J n i K)
    (freePointHornTensorCoproductIntervalAction_zero J n i K)
    (freePointHornTensorCoproductIntervalAction_one J n i K)
    (freePointHornTensorCoproductIntervalAction_fix J n i K)

/-- The family of pointed horn spaces tensored with the selected scalar objects. -/
abbrev sourceFamily : J → PointedCGWH.{u, v} :=
  fun a => (Under.costar CGWH.point).obj
    (SSet.toCGWHOfFinite (SSet.horn.{v} (n a + 1) (i a))) ⊗ K a

/-- The family of pointed simplex spaces tensored with the selected scalar objects. -/
abbrev targetFamily : J → PointedCGWH.{u, v} :=
  fun a => (Under.costar CGWH.point).obj
    (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a

/-- The canonical isomorphism from the coproduct to the point of a colimiting cofan. -/
def cofanIso {F : J → PointedCGWH.{u, v}} (c : Cofan F) (hc : IsColimit c) :
    (∐ F) ≅ c.pt :=
  colimit.isoColimitCocone ⟨c, hc⟩

private theorem cofanIso_ι {F : J → PointedCGWH.{u, v}}
    (c : Cofan F) (hc : IsColimit c) (a : J) :
    Limits.Sigma.ι F a ≫ (cofanIso J c hc).hom = c.inj a :=
  colimit.isoColimitCocone_ι_hom ⟨c, hc⟩ ⟨a⟩

/-- Transport the actual coproduct retraction to both original attaching cofan points. -/
def freePointHornTensorCofanRetraction
    (cA : Cofan (sourceFamily J n i K)) (cB : Cofan (targetFamily J n K))
    (hA : IsColimit cA) (hB : IsColimit cB) : cB.pt ⟶ cA.pt :=
  (cofanIso J cB hB).inv ≫ freePointHornTensorCoproductRetraction J n i K ≫
    (cofanIso J cA hA).hom

/-- Transport the complete interval action to the actual target cofan point. -/
def freePointHornTensorCofanIntervalAction
    (cB : Cofan (targetFamily J n K)) (hB : IsColimit cB) :
    (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ cB.pt ⟶ cB.pt :=
  transportAction (cofanIso J cB hB) (freePointHornTensorCoproductIntervalAction J n i K)

private theorem cofanMap_comm
    (cA : Cofan (sourceFamily J n i K)) (cB : Cofan (targetFamily J n K))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a) :
    (cofanIso J cA hA).hom ≫ m =
      freePointHornTensorCoproductInclusion J n i K ≫ (cofanIso J cB hB).hom := by
  apply Limits.Sigma.hom_ext
  intro a
  rw [← Category.assoc, cofanIso_ι, hm]
  change _ = (Limits.Sigma.ι (sourceFamily J n i K) a ≫
    Limits.Sigma.map (fun a =>
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)))) ≫ (cofanIso J cB hB).hom
  rw [Limits.Sigma.ι_map, Category.assoc, cofanIso_ι]

/-- The original cofan attaching map retains its transported strict retraction. -/
theorem freePointHornTensorCofan_inclusion_ret
    (cA : Cofan (sourceFamily J n i K)) (cB : Cofan (targetFamily J n K))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a) :
    m ≫ freePointHornTensorCofanRetraction J n i K cA cB hA hB = 𝟙 cA.pt := by
  have hComm := cofanMap_comm J n i K cA cB hA hB m hm
  have hInv : m ≫ (cofanIso J cB hB).inv =
      (cofanIso J cA hA).inv ≫ freePointHornTensorCoproductInclusion J n i K := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun q => (cofanIso J cA hA).inv ≫ q ≫ (cofanIso J cB hB).inv) hComm
  unfold freePointHornTensorCofanRetraction
  rw [← Category.assoc, hInv]
  calc
    _ = (cofanIso J cA hA).inv ≫
        (freePointHornTensorCoproductInclusion J n i K ≫
          freePointHornTensorCoproductRetraction J n i K) ≫
            (cofanIso J cA hA).hom := by simp only [Category.assoc]
    _ = _ := by
      rw [freePointHornTensorCoproduct_inclusion_ret]
      simpa only [sourceFamily, freePointHornTensorCoproductSource,
        freePointHornTensorCoproductTarget, Category.id_comp] using
        (cofanIso J cA hA).inv_hom_id

/-- Time zero is the identity on the actual original target cofan point. -/
theorem freePointHornTensorCofanIntervalAction_zero
    (cB : Cofan (targetFamily J n K)) (hB : IsColimit cB) :
    (λ_ cB.pt).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 cB.pt) ≫
      freePointHornTensorCofanIntervalAction J n i K cB hB = 𝟙 cB.pt := by
  rw [tensorHom_id]
  unfold freePointHornTensorCofanIntervalAction
  rw [transportAction_endpoint _ _ _ (𝟙 (freePointHornTensorCoproductTarget J n K))
    (by simpa only [tensorHom_id, targetFamily, freePointHornTensorCoproductTarget] using
      freePointHornTensorCoproductIntervalAction_zero J n i K)]
  simp only [Category.id_comp, Iso.inv_hom_id]

/-- Time one is the original cofan retraction followed by the original attaching map. -/
theorem freePointHornTensorCofanIntervalAction_one
    (cA : Cofan (sourceFamily J n i K)) (cB : Cofan (targetFamily J n K))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a) :
    (λ_ cB.pt).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 cB.pt) ≫
      freePointHornTensorCofanIntervalAction J n i K cB hB =
      freePointHornTensorCofanRetraction J n i K cA cB hA hB ≫ m := by
  have hComm := cofanMap_comm J n i K cA cB hA hB m hm
  rw [tensorHom_id]
  unfold freePointHornTensorCofanIntervalAction
  rw [transportAction_endpoint _ _ _
    (freePointHornTensorCoproductRetraction J n i K ≫ freePointHornTensorCoproductInclusion J n i K)
    (by simpa only [tensorHom_id] using
      freePointHornTensorCoproductIntervalAction_one J n i K)]
  unfold freePointHornTensorCofanRetraction
  simpa only [Category.assoc] using
    congrArg (fun q => (cofanIso J cB hB).inv ≫ freePointHornTensorCoproductRetraction J n i K ≫ q)
      hComm.symm

/-- The actual transported action fixes every original source point at all times. -/
theorem freePointHornTensorCofanIntervalAction_fix
    (cA : Cofan (sourceFamily J n i K)) (cB : Cofan (targetFamily J n K))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a) :
    (𝟙 _ ⊗ₘ m) ≫ freePointHornTensorCofanIntervalAction J n i K cB hB =
      (freePointIntervalCollapse ⊗ₘ 𝟙 cA.pt) ≫ (λ_ cA.pt).hom ≫ m := by
  rw [id_tensorHom, tensorHom_id]
  exact transportAction_fix (cofanIso J cA hA) (cofanIso J cB hB)
    (freePointHornTensorCoproductInclusion J n i K) m
    (cofanMap_comm J n i K cA cB hA hB m hm)
    (freePointHornTensorCoproductIntervalAction J n i K) freePointIntervalCollapse
    (by simpa only [id_tensorHom, tensorHom_id, sourceFamily, targetFamily,
      freePointHornTensorCoproductSource, freePointHornTensorCoproductTarget] using
      freePointHornTensorCoproductIntervalAction_fix J n i K)

/-- The weak successor conclusion keeps both original attaching cofans and the actual new leg. -/
theorem freePointHornTensorCofan_cobaseChange_mem_weakHomotopyEquivalences
    (cA : Cofan (sourceFamily J n i K)) (cB : Cofan (targetFamily J n K))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a)
    {Y P : PointedCGWH.{u, v}} {f : cA.pt ⟶ Y} {g : cB.pt ⟶ P} {j : Y ⟶ P}
    (h : IsPushout m f g j) :
    CGWH.weakHomotopyEquivalences j.right :=
  action_cobaseChange_mem_weakHomotopyEquivalences h
    (freePointHornTensorCofanMap_isClosedEmbedding J n i K cA cB hA hB m hm)
    (freePointHornTensorCofanRetraction J n i K cA cB hA hB)
    (freePointHornTensorCofan_inclusion_ret J n i K cA cB hA hB m hm)
    (freePointHornTensorCofanIntervalAction J n i K cB hB)
    (freePointHornTensorCofanIntervalAction_zero J n i K cB hB)
    (freePointHornTensorCofanIntervalAction_one J n i K cA cB hA hB m hm)
    (freePointHornTensorCofanIntervalAction_fix J n i K cA cB hA hB m hm)

end PointedCGWH

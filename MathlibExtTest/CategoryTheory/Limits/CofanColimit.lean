/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.CofanColimit
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Entire contracts for original tagged cofan colimits

The original coefficient tags, stage points, final point and cocone maps
are retained. Generic contracts use independent label and Hom universes.
Native sigmaConst preservation and native cofan composition are reused
directly in the nonconstant family clients.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uI uJ vJ uL w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CofanColimitTest

section OriginalCofans

variable {C : Type uC} [Category.{vC} C] {I : Type uI} (X : I → C)
  {J : Type uJ} [Category.{vJ} J] (F : I → J ⥤ Type uL) (G : J ⥤ C)
  (ι : ∀ (j : J) (i : I), (F i).obj j → (X i ⟶ G.obj j))
  (hmap : ∀ {j k : J} (f : j ⟶ k) (i : I) (x : (F i).obj j),
    ι j i x ≫ G.map f = ι k i ((F i).map f x))
  (c : ∀ i : I, Cocone (F i)) (hc : ∀ i : I, IsColimit (c i))
  (t : Cocone G) (last : ∀ i : I, (c i).pt → (X i ⟶ t.pt))
  (hstage : ∀ j : J, IsColimit (Cofan.mk (G.obj j)
    (fun a : Σ i : I, (F i).obj j ↦ ι j a.1 a.2)))
  (hfinal : IsColimit (Cofan.mk t.pt
    (fun a : Σ i : I, (c i).pt ↦ last a.1 a.2)))
  (hleg : ∀ (j : J) (i : I) (x : (F i).obj j),
    ι j i x ≫ t.ι.app j = last i ((c i).ι.app j x))

example : IsColimit t :=
  CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg

example (s : Cocone G) (j : J) :
    t.ι.app j ≫
        (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).desc s =
      s.ι.app j :=
  (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).fac s j

example (s : Cocone G) (j : J) (i : I) (x : (F i).obj j) :
    ι j i x ≫ t.ι.app j ≫
        (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).desc s =
      ι j i x ≫ s.ι.app j := by
  rw [(CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).fac]

example (s : Cocone G) (j : J) (i : I) (x : (F i).obj j) :
    last i ((c i).ι.app j x) ≫
        (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).desc s =
      ι j i x ≫ s.ι.app j := by
  rw [← hleg, Category.assoc,
    (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).fac]

example (s : Cocone G) (m : t.pt ⟶ s.pt)
    (hm : ∀ j : J, t.ι.app j ≫ m = s.ι.app j) :
    m = (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).desc s :=
  (CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg).uniq s m hm

end OriginalCofans

section NativePreservation

variable {C : Type uC} [Category.{vC} C] [HasCoproducts.{uL} C] (X : C)

example : PreservesColimitsOfSize.{vJ, uJ} (sigmaConst.{uL}.obj X) := inferInstance

example {J : Type uJ} [Category.{vJ} J] {F : J ⥤ Type uL}
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((sigmaConst.{uL}.obj X).mapCocone c) :=
  isColimitOfPreserves _ hc

example (χ : Cardinal.{w}) [Fact χ.IsRegular] :
    (sigmaConst.{uL}.obj X).IsCardinalAccessible χ := inferInstance

end NativePreservation

section NativeFamily

variable {C : Type uC} [Category.{vC} C] {I : Type uI} [HasCoproductsOfShape I C]
  [HasCoproducts.{uL} C] (X : I → C)
  {J : Type uJ} [Category.{vJ} J] (F : I → J ⥤ Type uL)
  (c : ∀ i : I, Cocone (F i)) (hc : ∀ i : I, IsColimit (c i))

/-- The actual nested native coproduct cocone for arbitrary changing label diagrams. -/
def nativeCocone :
    Cocone (Functor.pi' (fun i : I ↦ F i ⋙ sigmaConst.obj (X i)) ⋙ Sigma.functor I) where
  pt := ∐ fun i : I ↦ (sigmaConst.obj (X i)).obj (c i).pt
  ι.app j := Sigma.map (fun i : I ↦ (sigmaConst.obj (X i)).map ((c i).ι.app j))
  ι.naturality {j k} f := by
    change
      Sigma.map (fun i : I ↦ (sigmaConst.obj (X i)).map ((F i).map f)) ≫
          Sigma.map (fun i : I ↦ (sigmaConst.obj (X i)).map ((c i).ι.app k)) =
        Sigma.map (fun i : I ↦ (sigmaConst.obj (X i)).map ((c i).ι.app j)) ≫ 𝟙 _
    rw [Category.comp_id, Sigma.map_comp_map]
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_map, Sigma.ι_map]
    rw [← Functor.map_comp, (c i).w f]
    rfl

include hc in
/-- The primitive returns the actual nested native coproduct cocone, with all its tags. -/
def nativeCoconeIsColimit : IsColimit (nativeCocone X F c) := by
  let G := Functor.pi' (fun i : I ↦ F i ⋙ sigmaConst.obj (X i)) ⋙ Sigma.functor I
  let t := nativeCocone X F c
  let ι (j : J) (i : I) (x : (F i).obj j) : X i ⟶ G.obj j :=
    Sigma.ι (fun _ : (F i).obj j ↦ X i) x ≫
      Sigma.ι (fun i : I ↦ (sigmaConst.obj (X i)).obj ((F i).obj j)) i
  let last (i : I) (x : (c i).pt) : X i ⟶ t.pt :=
    Sigma.ι (fun _ : (c i).pt ↦ X i) x ≫
      Sigma.ι (fun i : I ↦ (sigmaConst.obj (X i)).obj (c i).pt) i
  have hmap {j k : J} (f : j ⟶ k) (i : I) (x : (F i).obj j) :
      ι j i x ≫ G.map f = ι k i ((F i).map f x) := by
    change
      (Sigma.ι (fun _ : (F i).obj j ↦ X i) x ≫
        Sigma.ι (fun i : I ↦ ∐ fun _ : (F i).obj j ↦ X i) i) ≫
          Sigma.map (fun i : I ↦
            Sigma.map' ((F i).map f) (fun _ ↦ 𝟙 (X i))) =
        Sigma.ι (fun _ : (F i).obj k ↦ X i) ((F i).map f x) ≫
          Sigma.ι (fun i : I ↦ ∐ fun _ : (F i).obj k ↦ X i) i
    simp only [Category.assoc, Sigma.ι_map, Sigma.ι_comp_map'_assoc, Category.id_comp]
  have hleg (j : J) (i : I) (x : (F i).obj j) :
      ι j i x ≫ t.ι.app j = last i ((c i).ι.app j x) := by
    change
      (Sigma.ι (fun _ : (F i).obj j ↦ X i) x ≫
        Sigma.ι (fun i : I ↦ ∐ fun _ : (F i).obj j ↦ X i) i) ≫
          Sigma.map (fun i : I ↦
            Sigma.map' ((c i).ι.app j) (fun _ ↦ 𝟙 (X i))) =
        Sigma.ι (fun _ : (c i).pt ↦ X i) ((c i).ι.app j x) ≫
          Sigma.ι (fun i : I ↦ ∐ fun _ : (c i).pt ↦ X i) i
    simp only [Category.assoc, Sigma.ι_map, Sigma.ι_comp_map'_assoc, Category.id_comp]
  have hstage (j : J) : IsColimit (Cofan.mk (G.obj j)
      (fun a : Σ i : I, (F i).obj j ↦ ι j a.1 a.2)) :=
    Cofan.isColimitTrans _ (coproductIsCoproduct _)
      (fun i : I ↦ Sigma.ι (fun _ : (F i).obj j ↦ X i))
      (fun i ↦ coproductIsCoproduct _)
  have hfinal : IsColimit (Cofan.mk t.pt
      (fun a : Σ i : I, (c i).pt ↦ last a.1 a.2)) :=
    Cofan.isColimitTrans _ (coproductIsCoproduct _)
      (fun i : I ↦ Sigma.ι (fun _ : (c i).pt ↦ X i))
      (fun i ↦ coproductIsCoproduct _)
  exact CofanColimit.isColimit X F G ι hmap c hc t last hstage hfinal hleg

example : IsColimit (nativeCocone X F c) := nativeCoconeIsColimit X F c hc

example (j : J) (i : I) (x : (F i).obj j) :
    (Sigma.ι (fun _ : (F i).obj j ↦ X i) x ≫
      Sigma.ι (fun i : I ↦ (sigmaConst.obj (X i)).obj ((F i).obj j)) i) ≫
        (nativeCocone X F c).ι.app j =
      Sigma.ι (fun _ : (c i).pt ↦ X i) ((c i).ι.app j x) ≫
        Sigma.ι (fun i : I ↦ (sigmaConst.obj (X i)).obj (c i).pt) i := by
  change
    (Sigma.ι (fun _ : (F i).obj j ↦ X i) x ≫
      Sigma.ι (fun i : I ↦ ∐ fun _ : (F i).obj j ↦ X i) i) ≫
        Sigma.map (fun i : I ↦
          Sigma.map' ((c i).ι.app j) (fun _ ↦ 𝟙 (X i))) =
      Sigma.ι (fun _ : (c i).pt ↦ X i) ((c i).ι.app j x) ≫
        Sigma.ι (fun i : I ↦ ∐ fun _ : (c i).pt ↦ X i) i
  simp only [Category.assoc, Sigma.ι_map, Sigma.ι_comp_map'_assoc, Category.id_comp]

end NativeFamily

section Concrete

/-- Infinite varying original coefficients with independently raised coefficient/Hom universe. -/
def raisedCoefficients (n : ℕ) : Type 1 := ULift.{1} (Fin n)

example {J : Type uJ} [Category.{vJ} J] (F : ℕ → J ⥤ Type)
    (c : ∀ n : ℕ, Cocone (F n)) (hc : ∀ n : ℕ, IsColimit (c n)) :
    IsColimit (nativeCocone raisedCoefficients F c) :=
  nativeCoconeIsColimit raisedCoefficients F c hc

example (F : PEmpty.{1} → Discrete PEmpty.{1} ⥤ Type)
    (c : ∀ n : PEmpty.{1}, Cocone (F n)) :
    IsColimit (nativeCocone (fun n : PEmpty.{1} ↦ (nomatch n : Type)) F c) := by
  apply nativeCoconeIsColimit
  intro n
  exact nomatch n

example (F : ℕ → Discrete (ULift.{1} ℕ) ⥤ Type)
    (c : ∀ n : ℕ, Cocone (F n)) (hc : ∀ n : ℕ, IsColimit (c n)) :
    IsColimit (nativeCocone (fun n : ℕ ↦ Fin n) F c) :=
  nativeCoconeIsColimit (fun n : ℕ ↦ Fin n) F c hc

end Concrete

end CategoryTheory.Limits.CofanColimitTest

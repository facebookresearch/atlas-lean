/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Colimits of actual cofans with fixed coefficient tags

The original stage points, maps, coefficient tags and final cocone point
are retained. Heterogeneous Type colimits glue the original injection
families, and native cofan universal properties provide the desc and
uniqueness proofs. No bound on the Hom universe or rebuilt copower functor
is required by this primitive.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uI uJ vJ uL

namespace CategoryTheory.Limits.CofanColimit

variable {C : Type uC} [Category.{vC} C]
  {I : Type uI} (X : I → C)
  {J : Type uJ} [Category.{vJ} J]
  (F : I → J ⥤ Type uL)
  (G : J ⥤ C)
  (ι : ∀ (j : J) (i : I), (F i).obj j → (X i ⟶ G.obj j))
  (hmap : ∀ {j k : J} (f : j ⟶ k) (i : I) (x : (F i).obj j),
    ι j i x ≫ G.map f = ι k i ((F i).map f x))

include hmap in
/-- Original Type-colimit and cofan universal properties prove the SAME
final cocone colimiting. Each injection and each fixed coefficient tag is
retained, with independent index, label and coefficient Hom universes. -/
def isColimit
    (c : ∀ i : I, Cocone (F i)) (hc : ∀ i : I, IsColimit (c i))
    (t : Cocone G)
    (last : ∀ i : I, (c i).pt → (X i ⟶ t.pt))
    (hstage : ∀ j : J, IsColimit (Cofan.mk (G.obj j)
      (fun a : Σ i : I, (F i).obj j ↦ ι j a.1 a.2)))
    (hfinal : IsColimit (Cofan.mk t.pt
      (fun a : Σ i : I, (c i).pt ↦ last a.1 a.2)))
    (hleg : ∀ (j : J) (i : I) (x : (F i).obj j),
      ι j i x ≫ t.ι.app j = last i ((c i).ι.app j x)) : IsColimit t := by
  let hTypes (i : I) : ((F i).coconeTypesEquiv.symm (c i)).IsColimit :=
    (Types.isColimit_iff_coconeTypesIsColimit (c i)).1 ⟨hc i⟩
  let γ (s : Cocone G) (i : I) : (F i).CoconeTypes.{vC} :=
    { pt := X i ⟶ s.pt
      ι j x := ι j i x ≫ s.ι.app j
      ι_naturality {j k} f := by
        funext x
        change ι k i ((F i).map f x) ≫ s.ι.app k = ι j i x ≫ s.ι.app j
        calc
          ι k i ((F i).map f x) ≫ s.ι.app k =
              (ι j i x ≫ G.map f) ≫ s.ι.app k := by rw [hmap]
          _ = ι j i x ≫ s.ι.app j := by rw [Category.assoc, s.w f] }
  let values (s : Cocone G) (a : Σ i : I, (c i).pt) : X a.1 ⟶ s.pt :=
    (hTypes a.1).desc (γ s a.1) a.2
  let d (s : Cocone G) : t.pt ⟶ s.pt := Cofan.IsColimit.desc hfinal (values s)
  have hd (s : Cocone G) (i : I) (x : (c i).pt) :
      last i x ≫ d s = (hTypes i).desc (γ s i) x :=
    Cofan.IsColimit.fac hfinal (values s) ⟨i, x⟩
  refine { desc := d, fac := ?_, uniq := ?_ }
  · intro s j
    apply Cofan.IsColimit.hom_ext (hstage j)
    intro a
    change ι j a.1 a.2 ≫ (t.ι.app j ≫ d s) = ι j a.1 a.2 ≫ s.ι.app j
    calc
      ι j a.1 a.2 ≫ (t.ι.app j ≫ d s) =
          last a.1 ((c a.1).ι.app j a.2) ≫ d s := by rw [← Category.assoc, hleg]
      _ = (hTypes a.1).desc (γ s a.1) ((c a.1).ι.app j a.2) := hd s a.1 _
      _ = ι j a.1 a.2 ≫ s.ι.app j := (hTypes a.1).fac_apply (γ s a.1) j a.2
  · intro s m hm
    apply Cofan.IsColimit.hom_ext hfinal
    rintro ⟨i, x⟩
    change last i x ≫ m = last i x ≫ d s
    obtain ⟨j, y, hy⟩ := (hTypes i).ι_jointly_surjective x
    change (c i).ι.app j y = x at hy
    rw [← hy]
    calc
      last i ((c i).ι.app j y) ≫ m = (ι j i y ≫ t.ι.app j) ≫ m := by rw [hleg]
      _ = ι j i y ≫ s.ι.app j := by rw [Category.assoc, hm j]
      _ = (hTypes i).desc (γ s i) ((c i).ι.app j y) :=
        ((hTypes i).fac_apply (γ s i) j y).symm
      _ = last i ((c i).ι.app j y) ≫ d s := (hd s i _).symm

end CategoryTheory.Limits.CofanColimit

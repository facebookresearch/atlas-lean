/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.MonoFactorization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Preimage subfunctors as literal pullbacks

The native preimage of a subfunctor along a natural transformation is the
categorical pullback of its literal inclusion.  When the ambient map is monic,
the induced map to the chosen subfunctor is monic and its total elements are
bounded by those of that subfunctor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C]
variable {F F' : C ⥤ Type w}

/-- Native preimage commutes with arbitrary pointwise unions. -/
@[simp]
theorem preimage_iSup {ι : Type*} (G : ι → Subfunctor F) (p : F' ⟶ F) :
    (⨆ i, G i).preimage p = ⨆ i, (G i).preimage p := by
  ext X x
  simp only [Subfunctor.preimage_obj, Set.mem_preimage, Subfunctor.iSup_obj,
    Set.mem_iUnion]

/-- The native preimage square is a pullback, with its literal inclusions and
preimage map unchanged. -/
theorem preimage_isPullback (G : Subfunctor F) (p : F' ⟶ F) :
    IsPullback (G.preimage p).ι (G.fromPreimage p) p G.ι where
  w := (G.fromPreimage_ι p).symm
  isLimit' := by
    have hRange : ∀ (s : PullbackCone p G.ι),
        Subfunctor.range s.fst ≤ G.preimage p := by
      intro s X _ hx
      obtain ⟨x, rfl⟩ := hx
      simp only [Subfunctor.preimage_obj, Set.mem_preimage]
      have hCond : (s.fst ≫ p).app X x = (s.snd ≫ G.ι).app X x := by
        have h := congrArg (fun k : s.pt ⟶ F => k.app X x) s.condition
        simpa only [NatTrans.comp_app, types_comp_apply] using h
      have hL : (s.fst ≫ p).app X x = p.app X (s.fst.app X x) := rfl
      have hR : (s.snd ≫ G.ι).app X x = (s.snd.app X x).val := rfl
      rw [hL] at hCond
      rw [hR] at hCond
      rw [hCond]
      exact (s.snd.app X x).property
    refine ⟨PullbackCone.IsLimit.mk (G.fromPreimage_ι p).symm
      (fun s => Subfunctor.lift s.fst (hRange s))
      (fun s => Subfunctor.lift_ι s.fst (hRange s))
      (fun s => by
        apply (cancel_mono G.ι).mp
        calc
          (Subfunctor.lift s.fst (hRange s) ≫ G.fromPreimage p) ≫ G.ι =
              Subfunctor.lift s.fst (hRange s) ≫
                ((G.preimage p).ι ≫ p) := by
            rw [Category.assoc, G.fromPreimage_ι]
          _ = (Subfunctor.lift s.fst (hRange s) ≫
                (G.preimage p).ι) ≫ p := by rw [← Category.assoc]
          _ = s.fst ≫ p := by rw [Subfunctor.lift_ι]
          _ = s.snd ≫ G.ι := s.condition)
      (fun s m h₁ _ => by
        apply (cancel_mono (G.preimage p).ι).mp
        rw [h₁, Subfunctor.lift_ι])⟩

/-- Pulling back along a monomorphism gives a monic map to the selected
subfunctor. -/
instance mono_fromPreimage (G : Subfunctor F) (p : F' ⟶ F) [Mono p] :
    Mono (G.fromPreimage p) :=
  (G.preimage_isPullback p).mono_snd_of_mono

/-- Under a monic ambient map, the preimage has at most as many total elements
as the selected target subfunctor. -/
theorem mk_elements_preimage_le (G : Subfunctor F) (p : F' ⟶ F) [Mono p] :
    Cardinal.mk (G.preimage p).toFunctor.Elements ≤
      Cardinal.mk G.toFunctor.Elements :=
  Functor.mk_elements_le_of_mono (G.fromPreimage p)

/-- Taking the image of a subfunctor does not increase its total elements. -/
theorem mk_elements_image_le (G : Subfunctor F) {F'' : C ⥤ Type w}
    (p : F ⟶ F'') :
    Cardinal.mk (G.image p).toFunctor.Elements ≤
      Cardinal.mk G.toFunctor.Elements := by
  have h : Subfunctor.range (G.ι ≫ p) = G.image p := by
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
  rw [← h]
  exact Functor.mk_elements_le_of_epi (Subfunctor.toRange (G.ι ≫ p))

end CategoryTheory.Subfunctor

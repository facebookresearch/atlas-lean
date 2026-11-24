/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCommonIntervalMaps

/-!
# Literal original simplex readback of the coherent horn Hom extraction

Restriction of an actual supplied enriched simplex gives an actual horn
map. Its original objects, whole face functors and extracted common Hom
maps read back the original simplex without changing its vertices or
noninvertible Hom cells. No Kan or comparison outcome is a hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornFromSimplex
open SimplicialEnrichment
variable {C : Carrier.{u}} {n : ℕ} (σ : coherentSimplex.{u} ⦋n + 2⦌ ⟶ C) (i : Fin (n + 3))

/-- Restrict the same actual original enriched simplex along the original horn inclusion. -/
def horn : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C :=
  (Λ[n + 2, i]).ι ≫ SSet.yonedaEquiv.symm σ

/-- Original horn object extraction is the same individual supplied simplex object. -/
theorem object_readback (a : Fin (n + 3)) :
    HornFaces.object (horn σ i) a = σ.obj (.mk (ULift.up a)) := rfl

/-- Original horn face extraction is the same actual whole enriched simplex restriction. -/
theorem face_readback (j : Fin (n + 3)) (hj : j ≠ i) :
    HornFaces.faceFunctor (horn σ i) j hj = coherentSimplexMap (SimplexCategory.δ j) ≫ σ := rfl

/-- The common whole original Hom extraction reads back precisely the supplied original simplex Hom map. -/
theorem leftMap_readback (j k : Fin (n + 3)) (hj : j ≠ i) (hjk : j < k)
    (a b : ULift.{u} (Fin (n + 1)))
    (houtj : (ULift.up j : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
      TwoOutsideFaces.point j k hjk b < ULift.up j)
    (houtk : (ULift.up k : ULift.{u} (Fin (n + 3))) < TwoOutsideFaces.point j k hjk a ∨
      TwoOutsideFaces.point j k hjk b < ULift.up k) :
    CommonIntervalMaps.leftMap (horn σ i) j k hj hjk a b houtj houtk =
      σ.map (.mk (TwoOutsideFaces.point j k hjk a)) (.mk (TwoOutsideFaces.point j k hjk b)) := by
  change (TwoOutsideFaces.homIso j k hjk a b houtj houtk).inv ≫
    (((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b) ≫
      ((coherentSimplexMap (SimplexCategory.δ j)).map
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a))
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b)) ≫
          σ.map (.mk (TwoOutsideFaces.point j k hjk a)) (.mk (TwoOutsideFaces.point j k hjk b)))) ≫ 𝟙 _) = _
  simp only [Category.comp_id]
  have h := TwoOutsideFaces.homIso_operator j k hjk a b houtj houtk
  change (TwoOutsideFaces.homIso j k hjk a b houtj houtk).hom =
    (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b) ≫
      (coherentSimplexMap (SimplexCategory.δ j)).map
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a))
        ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b)) at h
  let e := TwoOutsideFaces.homIso j k hjk a b houtj houtk
  let f₁ := (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b)
  let f₂ := (coherentSimplexMap (SimplexCategory.δ j)).map
    ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk a))
    ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).obj (.mk b))
  let m := σ.map (.mk (TwoOutsideFaces.point j k hjk a)) (.mk (TwoOutsideFaces.point j k hjk b))
  change e.inv ≫ (f₁ ≫ (f₂ ≫ m)) = m
  have he : e.hom = f₁ ≫ f₂ := h
  have h₁ : e.inv ≫ (f₁ ≫ (f₂ ≫ m)) = e.inv ≫ ((f₁ ≫ f₂) ≫ m) :=
    congrArg (fun t => e.inv ≫ t) (Category.assoc f₁ f₂ m).symm
  have h₂ : e.inv ≫ ((f₁ ≫ f₂) ≫ m) = e.inv ≫ (e.hom ≫ m) :=
    congrArg (fun t => e.inv ≫ (t ≫ m)) he.symm
  have h₃ : e.inv ≫ (e.hom ≫ m) = (e.inv ≫ e.hom) ≫ m := (Category.assoc _ _ _).symm
  have h₄ : (e.inv ≫ e.hom) ≫ m = m :=
    (congrArg (fun t => t ≫ m) e.inv_hom_id).trans (Category.id_comp m)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end CategoryTheory.CoherentRealization.HornFromSimplex

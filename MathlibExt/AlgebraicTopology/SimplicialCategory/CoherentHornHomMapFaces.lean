/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornHomMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFaceOrderedRestriction

/-!
# Every actual supplied face of the assembled enriched coherent simplex

The original nonexceptional Hom restrictions and the actual retained
negative outer-Hom restrictions identify every supplied face. Both
individual object equations and all whole scalar Hom maps are retained.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornHomMapFaces
open SimplicialEnrichment HornBoxFaces HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
  [SSet.KanComplex (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2)))]

private theorem outer_restriction (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1)))) ≫
      HornHomMaps.homMap f hi₀ hiₙ ((HornBoxFaces.vertex k).succAbove 0)
        ((HornBoxFaces.vertex k).succAbove (Fin.last (n + 1))) =
      HornHomFaces.faceMap f (HornBoxFaces.vertex k) hk
        (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1)))) := by
  let E := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let F := HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk
  let a := (HornBoxFaces.vertex k).succAbove (0 : Fin (n + 2))
  let b := (HornBoxFaces.vertex k).succAbove (Fin.last (n + 1))
  let X := nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))
  let Z := HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))
  let S : X ⟶ outerHom.{u} n := eqToHom (congrArg₂ (fun a b : Fin (n + 3) => nerve
    (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)))
    (source_zero k) (target_last k))
  let T : (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) ⟶ Z := eqToHom (congrArg₂ (fun x y : C =>
    x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f) (target_last k)))
  let M : X ⟶ (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := HornHomMaps.homMap f hi₀ hiₙ a b
  let N : outerHom.{u} n ⟶ Z := HornHomMaps.homMap f hi₀ hiₙ 0 (Fin.last (n + 2))
  let e : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} (Fin.last (n + 1)))) ⟶ X :=
    E.map (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
  let R : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} (Fin.last (n +
    1)))) ⟶ (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := HornHomFaces.faceMap f (HornBoxFaces.vertex k) hk
    (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
  have hN : M ≫ T = S ≫ N :=
    eqToHom_naturality
      (f := fun p : Fin (n + 3) × Fin (n + 3) => nerve (SimplicialThickening.Path (ULift.up.{u} p.1)
        (ULift.up.{u} p.2)))
      (g := fun p : Fin (n + 3) × Fin (n + 3) => HornFaces.object f p.1 ⟶[SSet.{u}] HornFaces.object f p.2)
      (fun p => HornHomMaps.homMap f hi₀ hiₙ p.1 p.2)
      (show (a, b) = ((0 : Fin (n + 3)), Fin.last (n + 2)) from Prod.ext (source_zero k) (target_last k))
  apply (cancel_mono T).mp
  let Q := retargetMap F (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (source_zero k)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (target_last k)))
  have hO : e ≫ S ≫ N = Q :=
    (congrArg (fun g : outerHom.{u} n ⟶ Z => e ≫ S ≫ g) (HornHomMaps.homMap_outer f hi₀ hiₙ)).trans
      (HornOuterMap.negative_readback f hi₀ hiₙ k hk)
  have hL : (e ≫ M) ≫ T = Q :=
    (Category.assoc e M T).trans ((congrArg (fun g : X ⟶ Z => e ≫ g) hN).trans hO)
  have hR : R ≫ T = Q :=
    HomRetargetAlgebra.target_trans F (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
      (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _) (HornFaces.faceFunctor_obj f
        (HornBoxFaces.vertex k) hk _)
      (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f) (target_last k))
  exact hL.trans hR.symm

/-- Every original supplied face reads back its entire actual Hom map in the assembled simplex, including
  reverse intervals and the outer pair. -/
theorem hom_restriction (k : Fin (n + 3)) (hk : k ≠ i) (a b : Fin (n + 2)) :
    (coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      HornHomMaps.homMap f hi₀ hiₙ (k.succAbove a) (k.succAbove b) =
      HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  classical
  by_cases hab : a ≤ b
  · by_cases hN : k.succAbove a = 0 ∧ k.succAbove b = Fin.last (n + 2)
    · have hk₀ : k ≠ 0 := by
        intro h
        subst k
        have h' : (0 : Fin (n + 3)).succAbove a ≠ 0 := by rw [Fin.succAbove_zero]; exact Fin.succ_ne_zero a
        exact h' hN.1
      have hkₙ : k ≠ Fin.last (n + 2) := by
        intro h
        subst k
        have h' : (Fin.last (n + 2)).succAbove b ≠ Fin.last (n + 2) := by
          rw [Fin.succAbove_last]; exact ne_of_lt (Fin.castSucc_lt_last b)
        exact h' hN.2
      have ha : a = 0 := (Fin.succAboveOrderEmb k).injective (hN.1.trans (Fin.succAbove_ne_zero_zero hk₀).symm)
      have hb : b = Fin.last (n + 1) := (Fin.succAboveOrderEmb k).injective (hN.2.trans
        (Fin.succAbove_ne_last_last hkₙ).symm)
      subst a
      subst b
      let kI : Interior.{u} n := ⟨ULift.up k, Fin.pos_iff_ne_zero.mpr hk₀, Fin.lt_last_iff_ne_last.mpr hkₙ⟩
      exact outer_restriction f hi₀ hiₙ kI hk
    · have h : k.succAbove a ≠ 0 ∨ k.succAbove b ≠ Fin.last (n + 2) := by
        by_cases ha : k.succAbove a = 0
        · exact Or.inr (fun hb => hN ⟨ha, hb⟩)
        · exact Or.inl ha
      rw [HornHomMaps.homMap_ordered f hi₀ hiₙ (k.succAbove a) (k.succAbove b) ((Fin.succAboveOrderEmb
        k).monotone hab) h]
      exact HornFaceOrderedRestriction.restriction f hi₀ hiₙ k hk a b hab h
  · exact HomUnitsAndEmpty.empty_hom_ext
      (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n + 2))) ≤ ULift.up b from hab) _ _

/-- The actual assembled enriched simplex restricts to every supplied original coherent face as a whole
  enriched functor. -/
theorem simplex_face (k : Fin (n + 3)) (hk : k ≠ i) :
    coherentSimplexMap (SimplexCategory.δ k) ≫ HornHomMaps.simplex f hi₀ hiₙ = HornFaces.faceFunctor f k hk := by
  refine EnrichedFunctor.ext SSet.{u}
    (F := coherentSimplexMap (SimplexCategory.δ k) ≫ HornHomMaps.simplex f hi₀ hiₙ)
    (G := HornFaces.faceFunctor f k hk) (fun a => (HornFaces.faceFunctor_obj f k hk a).symm) ?_
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  let T := eqToIso (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (HornFaces.faceFunctor_obj f k hk (.mk (ULift.up.{u} a)))
    (HornFaces.faceFunctor_obj f k hk (.mk (ULift.up.{u} b))))
  change ((coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
    HornHomMaps.homMap f hi₀ hiₙ (k.succAbove a) (k.succAbove b)) ≫ T.inv =
      (HornFaces.faceFunctor f k hk).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b))
  exact (Iso.comp_inv_eq T).mpr (hom_restriction f hi₀ hiₙ k hk a b)

end CategoryTheory.CoherentRealization.HornHomMapFaces

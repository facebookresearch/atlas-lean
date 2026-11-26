/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFirstFaceRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentLastFaceRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra

/-!
# Supplied endpoint-face restrictions at specified original vertices

The existing genuine common-face restriction equations are read at the
supplied individual original endpoints. No agreement or transport
outcome is a premise; the only equations specify those endpoint labels.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.EndpointRestrictionRetarget
open SimplicialEnrichment HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The actual last endpoint-face restriction retains the two supplied original endpoint labels. -/
theorem last (hₙ : Fin.last (n + 2) ≠ i) (k : Fin (n + 3)) (hkₙ : k < Fin.last (n + 2))
    (a' b' : ULift.{u} (Fin (n + 1))) (hk : k ≠ i)
    {a b : Fin (n + 3)}
    (ha : (TwoOutsideFaces.point k (Fin.last (n + 2)) hkₙ a').down = a)
    (hb : (TwoOutsideFaces.point k (Fin.last (n + 2)) hkₙ b').down = b) :
    (coherentSimplexMap (SimplexCategory.δ k)).map
        ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a'))
        ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b')) ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 3) => nerve (SimplicialThickening.Path (ULift.up.{u} a)
        (ULift.up.{u} b))) ha hb) ≫
        HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hₙ
          ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) a')
          ((OrdinalFace.embedding (k.castPred (Fin.ne_last_of_lt hkₙ))) b')
          (LastFaceRestriction.outside k hkₙ a' b')
          ((common_vertex k (Fin.last (n + 2)) hkₙ a'.down).symm.trans ha)
          ((common_vertex k (Fin.last (n + 2)) hkₙ b'.down).symm.trans hb) =
      retargetMap (HornFaces.faceFunctor f k hk)
        ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a'))
        ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b'))
        ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) ha))
        ((HornFaces.faceFunctor_obj f k hk _).trans (congrArg (HornFaces.object f) hb)) := by
  subst a
  subst b
  change (coherentSimplexMap (SimplexCategory.δ k)).map
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a'))
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b')) ≫
    𝟙 _ ≫ LastFaceRestriction.map f hₙ k hkₙ a' b' =
      HornHomFaces.faceMap f k hk
        ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a'))
        ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b'))
  exact (congrArg (fun g => (coherentSimplexMap (SimplexCategory.δ k)).map
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk a'))
      ((coherentSimplexMap (SimplexCategory.δ ((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hkₙ)))).obj (.mk b')) ≫ g)
    (Category.id_comp (LastFaceRestriction.map f hₙ k hkₙ a' b'))).trans
      (LastFaceRestriction.restriction f hₙ k hkₙ a' b' hk)

/-- The actual first endpoint-face restriction retains the same two supplied original endpoint labels. -/
theorem first (h₀ : (0 : Fin (n + 3)) ≠ i) (k : Fin (n + 3)) (h₀k : 0 < k)
    (a' b' : ULift.{u} (Fin (n + 1))) (hk : k ≠ i)
    {a b : Fin (n + 3)}
    (ha : (TwoOutsideFaces.point 0 k h₀k a').down = a)
    (hb : (TwoOutsideFaces.point 0 k h₀k b').down = b) :
    (coherentSimplexMap (SimplexCategory.δ k)).map
        ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk a'))
        ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk b')) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        ((TwoOutsideFaces.point_right 0 k h₀k a').symm.trans (ULift.ext ha))
        ((TwoOutsideFaces.point_right 0 k h₀k b').symm.trans (ULift.ext hb))) ≫
        HornOutsideIntervals.faceMap f 0 h₀
          ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) a')
          ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt h₀k))) b')
          (FirstFaceRestriction.outside k h₀k a' b') ha hb =
      retargetMap (HornFaces.faceFunctor f k hk)
        ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk a'))
        ((coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))).obj (.mk b'))
        ((HornFaces.faceFunctor_obj f k hk _).trans
          (congrArg (HornFaces.object f) ((common_vertex 0 k h₀k a'.down).symm.trans ha)))
        ((HornFaces.faceFunctor_obj f k hk _).trans
          (congrArg (HornFaces.object f) ((common_vertex 0 k h₀k b'.down).symm.trans hb))) := by
  subst a
  subst b
  let d := coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))
  let x := d.obj (.mk a')
  let y := d.obj (.mk b')
  let S := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
    (TwoOutsideFaces.point_right 0 k h₀k a').symm (TwoOutsideFaces.point_right 0 k h₀k b').symm)
  let T := eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
    (congrArg (HornFaces.object f) (common_vertex 0 k h₀k a'.down).symm)
    (congrArg (HornFaces.object f) (common_vertex 0 k h₀k b'.down).symm))
  change (coherentSimplexMap (SimplexCategory.δ k)).map x y ≫ S ≫ FirstFaceRestriction.map f h₀ k h₀k a' b' =
    retargetMap (HornFaces.faceFunctor f k hk) x y
      ((HornFaces.faceFunctor_obj f k hk x).trans (congrArg (HornFaces.object f) (common_vertex 0 k h₀k a'.down).symm))
      ((HornFaces.faceFunctor_obj f k hk y).trans (congrArg (HornFaces.object f) (common_vertex 0 k h₀k b'.down).symm))
  exact (FirstFaceRestriction.restriction f h₀ k h₀k a' b' hk).trans
    (HomRetargetAlgebra.target_trans (HornFaces.faceFunctor f k hk) x y
      (HornFaces.faceFunctor_obj f k hk x) (HornFaces.faceFunctor_obj f k hk y)
      (congrArg (HornFaces.object f) (common_vertex 0 k h₀k a'.down).symm)
      (congrArg (HornFaces.object f) (common_vertex 0 k h₀k b'.down).symm))

end CategoryTheory.CoherentRealization.EndpointRestrictionRetarget

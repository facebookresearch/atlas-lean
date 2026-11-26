/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornInteriorFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornEndpointRestrictionRetarget
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornShortLegs

/-!
# The actual short Hom maps restrict to supplied nonendpoint faces

An individual interior vertex of the original supplied face is retained
in the ambient simplex. Both whole original short Hom maps restrict to
that face's actual enriched maps, with the original outer endpoints and
middle label specified literally.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornShortFaceRestrictions
open SimplicialEnrichment HornBoxFaces HornHomFaces

private theorem change_source {A B C : Carrier.{u}} (E : A ⟶ B) (F : A ⟶ C)
    {a b a' b' : A} (ha : a = a') (hb : b = b') {x y : B} {z w : C}
    (M : (x ⟶[SSet.{u}] y) ⟶ (z ⟶[SSet.{u}] w))
    (hx : E.obj a = x) (hy : E.obj b = y) (hz : F.obj a = z) (hw : F.obj b = w)
    (hx' : E.obj a' = x) (hy' : E.obj b' = y) (hz' : F.obj a' = z) (hw' : F.obj b' = w)
    (h : E.map a b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx hy) ≫ M =
      retargetMap F a b hz hw) :
    E.map a' b' ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx' hy') ≫ M =
      retargetMap F a' b' hz' hw' := by
  subst a'
  subst b'
  exact h

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (k : Interior.{u} n)
  (t : HornInteriorFace.SourceInterior n) (hk : HornBoxFaces.vertex k ≠ i)

/-- The entire left short Hom restricts to the supplied original face at its same individual middle vertex. -/
theorem left :
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val)) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (source_zero k)) (show (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up t.val) =
          (HornInteriorFace.middle k t).val from rfl)) ≫
        leftMap f hi₀ hiₙ (HornInteriorFace.middle k t) =
    retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
      (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val))
      ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
        (congrArg (HornFaces.object f) (source_zero k)))
      (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _) := by
  let E := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let F := HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk
  let d := coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1)))
  let a' : ULift.{u} (Fin (n + 1)) := ULift.up 0
  let b' : ULift.{u} (Fin (n + 1)) := ULift.up (t.val.castPred (ne_of_lt t.property.2))
  let b := HornInteriorFace.middle k t
  let ha := congrArg ULift.down (HornInteriorFace.left_zero k)
  let hb := congrArg ULift.down (HornInteriorFace.left_middle k t)
  have h := EndpointRestrictionRetarget.last f hiₙ.symm (HornBoxFaces.vertex k) k.property.2 a' b' hk
    (a := 0) (b := HornBoxFaces.vertex b) ha hb
  have hp₀ := HornInteriorFace.last_preimage k a' ha
    (show (0 : Fin (n + 3)) ≠ Fin.last (n + 2) from by
      intro h; have h' := congrArg Fin.val h; change 0 = n + 2 at h'; omega)
  have hp₁ := HornInteriorFace.last_preimage k b' hb (vertex_ne_last b)
  have hd₀ : d.obj (.mk a') = (.mk (ULift.up (0 : Fin (n + 2))) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk (OrdinalFace.embedding (Fin.last (n + 1)) a') = _
    congr 1
  have hd₁ : d.obj (.mk b') = (.mk (ULift.up t.val) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk (OrdinalFace.embedding (Fin.last (n + 1)) b') = _
    congr 1
    apply ULift.ext
    change (Fin.last (n + 1)).succAbove (t.val.castPred (ne_of_lt t.property.2)) = t.val
    simpa only [Fin.succAbove_last] using Fin.castSucc_castPred t.val (ne_of_lt t.property.2)
  let M := HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hiₙ.symm
    ((OrdinalFace.embedding ((HornBoxFaces.vertex k).castPred (vertex_ne_last k))) a')
    ((OrdinalFace.embedding ((HornBoxFaces.vertex k).castPred (vertex_ne_last k))) b')
    (LastFaceRestriction.outside (HornBoxFaces.vertex k) k.property.2 a' b')
    ((common_vertex (HornBoxFaces.vertex k) (Fin.last (n + 2)) k.property.2 a'.down).symm.trans ha)
    ((common_vertex (HornBoxFaces.vertex k) (Fin.last (n + 2)) k.property.2 b'.down).symm.trans hb)
  have hM : M = leftMap f hi₀ hiₙ b := by
    dsimp only [M]
    rw [HornShortLegs.leftMap_eq_lastFace f hi₀ hiₙ b]
    simp only [hp₀, hp₁]
    rfl
  have h' : E.map (d.obj (.mk a')) (d.obj (.mk b')) ≫
      eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} ⦋n + 2⦌ => a ⟶[SSet.{u}] b)
        (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) ha)
        (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) hb)) ≫ M =
      retargetMap F (d.obj (.mk a')) (d.obj (.mk b'))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) ha))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) hb)) := h
  have hFinal := change_source E F hd₀ hd₁ M
    (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) ha)
    (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) hb)
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) ha))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) hb))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (ULift.ext (source_zero k))) rfl
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (source_zero k)))
    (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _) h'
  exact (congrArg (fun g => E.map (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up t.val)) ≫
    eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} ⦋n + 2⦌ => a ⟶[SSet.{u}] b)
      (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (ULift.ext (source_zero k)))
        rfl) ≫ g) hM).symm.trans hFinal

/-- The entire right short Hom restricts to the same original face and individual middle vertex. -/
theorem right :
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        (show (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up t.val) =
          (HornInteriorFace.middle k t).val from rfl) (ULift.ext (target_last k))) ≫
        rightMap f hi₀ hiₙ (HornInteriorFace.middle k t) =
    retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
      (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1))))
      (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _)
      ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
        (congrArg (HornFaces.object f) (target_last k))) := by
  let E := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let F := HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk
  let d := coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2)))
  let a' : ULift.{u} (Fin (n + 1)) := ULift.up (t.val.pred (ne_of_gt t.property.1))
  let b' : ULift.{u} (Fin (n + 1)) := ULift.up (Fin.last n)
  let b := HornInteriorFace.middle k t
  let ha := congrArg ULift.down (HornInteriorFace.right_middle k t)
  let hb := congrArg ULift.down (HornInteriorFace.right_last k)
  have h := EndpointRestrictionRetarget.first f hi₀.symm (HornBoxFaces.vertex k) k.property.1 a' b' hk
    (a := HornBoxFaces.vertex b) (b := Fin.last (n + 2)) ha hb
  have hp₀ := HornInteriorFace.first_preimage k a' ha (vertex_ne_zero b)
  have hp₁ := HornInteriorFace.first_preimage k b' hb
    (show Fin.last (n + 2) ≠ (0 : Fin (n + 3)) from by
      intro h; have h' := congrArg Fin.val h; change n + 2 = 0 at h'; omega)
  have hd₀ : d.obj (.mk a') = (.mk (ULift.up t.val) : coherentSimplex.{u} ⦋n + 1⦌) := by
    change SimplicialThickening.mk ((OrdinalFace.embedding (0 : Fin (n + 2))) a') = _
    apply congrArg SimplicialThickening.mk
    apply ULift.ext
    change (t.val.pred (ne_of_gt t.property.1)).succ = t.val
    exact Fin.succ_pred _ _
  have hd₁ : d.obj (.mk b') = (.mk (ULift.up (Fin.last (n + 1))) : coherentSimplex.{u} ⦋n + 1⦌) := rfl
  let M := HornOutsideIntervals.faceMap f (0 : Fin (n + 3)) hi₀.symm
    ((OrdinalFace.embedding ((HornBoxFaces.vertex k).pred (vertex_ne_zero k))) a')
    ((OrdinalFace.embedding ((HornBoxFaces.vertex k).pred (vertex_ne_zero k))) b')
    (FirstFaceRestriction.outside (HornBoxFaces.vertex k) k.property.1 a' b') ha hb
  have hM : M = rightMap f hi₀ hiₙ b := by
    dsimp only [M]
    rw [HornShortLegs.rightMap_eq_firstFace f hi₀ hiₙ b]
    simp only [hp₀, hp₁]
    rfl
  let hx := (TwoOutsideFaces.point_right 0 (HornBoxFaces.vertex k) k.property.1 a').symm.trans (ULift.ext ha)
  let hy := (TwoOutsideFaces.point_right 0 (HornBoxFaces.vertex k) k.property.1 b').symm.trans (ULift.ext hb)
  have h' : E.map (d.obj (.mk a')) (d.obj (.mk b')) ≫
      eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} ⦋n + 2⦌ => a ⟶[SSet.{u}] b)
        (congrArg SimplicialThickening.mk hx) (congrArg SimplicialThickening.mk hy)) ≫ M =
      retargetMap F (d.obj (.mk a')) (d.obj (.mk b'))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
          (congrArg (HornFaces.object f) ((common_vertex 0 (HornBoxFaces.vertex k) k.property.1
            a'.down).symm.trans ha)))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
          (congrArg (HornFaces.object f) ((common_vertex 0 (HornBoxFaces.vertex k) k.property.1
            b'.down).symm.trans hb))) := h
  have hFinal := change_source E F hd₀ hd₁ M
    (congrArg SimplicialThickening.mk hx) (congrArg SimplicialThickening.mk hy)
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
      (congrArg (HornFaces.object f) ((common_vertex 0 (HornBoxFaces.vertex k) k.property.1 a'.down).symm.trans ha)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
      (congrArg (HornFaces.object f) ((common_vertex 0 (HornBoxFaces.vertex k) k.property.1 b'.down).symm.trans hb)))
    rfl (congrArg SimplicialThickening.mk (ULift.ext (target_last k)))
    (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _)
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
      (target_last k))) h'
  exact (congrArg (fun g => E.map (.mk (ULift.up t.val)) (.mk (ULift.up (Fin.last (n + 1)))) ≫
    eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} ⦋n + 2⦌ => a ⟶[SSet.{u}] b)
      rfl (congrArg SimplicialThickening.mk (ULift.ext (target_last k)))) ≫ g) hM).symm.trans hFinal

end CategoryTheory.CoherentRealization.HornShortFaceRestrictions

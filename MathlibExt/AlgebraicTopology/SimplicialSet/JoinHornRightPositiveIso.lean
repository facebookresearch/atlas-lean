/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightFaces

/-!
# The positive-left-dimensional right join--horn isomorphism
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

set_option maxHeartbeats 1000000 in
lemma joinBoundaryHornRightFaceSucc_toHorn
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) :
    joinBoundaryHornRightFaceSucc.{u} p q j t hne ≫
        joinBoundaryHornRightToHorn (p + 1) q j =
      horn.ι (rightJoinHornIndex (p + 1) q j) t hne := by
  rw [← cancel_mono
    (horn ((p + 1) + (q + 1) + 1)
      (rightJoinHornIndex (p + 1) q j)).ι]
  simp only [Category.assoc]
  rw [joinBoundaryHornRightToHorn_ι, horn.ι_ι]
  by_cases ht : t.val ≤ p + 1
  · rw [joinBoundaryHornRightFaceSucc_front p q j t hne ht]
    unfold joinBoundaryHornRightFrontFaceSucc
    rw [Category.assoc, Category.assoc, Category.assoc,
      (joinBoundaryHornRightPushoutObjObj (p + 1) q j).inr_ι_assoc]
    simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
    rw [boundary.ι_ι]
    have hdual := joinHorn_dualFrontPush
      (⟨t.val, by omega⟩ : Fin (p + 2)) t rfl
      (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1))
    simp only [Category.assoc]
    rw [hdual]
    simp only [Iso.inv_hom_id_assoc]
    rw [joinHornΔcastInv_eq]
    simp only [← Category.assoc]
    rw [joinHornΔcast_comp, joinHornΔcast_eq _ rfl,
      joinHornΔcast_rfl, Category.id_comp]
  · rw [joinBoundaryHornRightFaceSucc_back p q j t hne ht]
    unfold joinBoundaryHornRightBackFaceSucc
    rw [Category.assoc, Category.assoc, Category.assoc,
      (joinBoundaryHornRightPushoutObjObj (p + 1) q j).inl_ι_assoc]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [horn.ι_ι]
    simp only [Category.assoc]
    rw [← joinHorn_backPush_assoc]
    simp only [Iso.inv_hom_id, Category.comp_id]
    have hi : rightJoinHornIndex (p + 1) q
          (joinBackIndexSucc p q t ht) = t := by
      apply Fin.ext
      dsimp [rightJoinHornIndex, joinBackIndexSucc]
      have htlo : p + 2 ≤ t.val := by omega
      omega
    change joinHornΔcastInv _ ≫ stdSimplex.δ
        (rightJoinHornIndex (p + 1) q
          (joinBackIndexSucc p q t ht)) = stdSimplex.δ t
    rw [hi]
    rw [joinHornΔcastInv_eq, stdSimplex_δ_eq_map,
      joinHornΔcast, joinHornΔcastIso, Functor.mapIso_hom,
      ← Functor.map_comp]
    congr 1

/-- The inverse map obtained by descending the compatible face family. -/
@[no_expose]
noncomputable def joinBoundaryHornRightFromHornSucc
    (p q : ℕ) (j : Fin (q + 2)) :
    (horn ((p + 1) + (q + 1) + 1)
      (rightJoinHornIndex (p + 1) q j) : SSet.{u}) ⟶
      (joinBoundaryHornRightPushoutObjObj (p + 1) q j).pt :=
  (joinBoundaryHornRightFaceSucc_compatible.{u} p q j).desc

@[reassoc (attr := simp)]
lemma joinBoundaryHornRight_face_fromHornSucc
    (p q : ℕ) (j : Fin (q + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ rightJoinHornIndex (p + 1) q j) :
    horn.ι (rightJoinHornIndex (p + 1) q j) t hne ≫
        joinBoundaryHornRightFromHornSucc p q j =
      joinBoundaryHornRightFaceSucc p q j t hne := by
  apply horn.IsCompatible.ι_desc

lemma joinBoundaryHornRightFromHornSucc_toHorn
    (p q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightFromHornSucc p q j ≫
        joinBoundaryHornRightToHorn (p + 1) q j = 𝟙 _ := by
  apply horn.hom_ext'
  intro t ht
  simp only [← Category.assoc, joinBoundaryHornRight_face_fromHornSucc,
    joinBoundaryHornRightFaceSucc_toHorn, Category.comp_id]

private lemma joinBoundaryHornRight_inl_toHorn_fromHornSucc
    (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).inl ≫
        joinBoundaryHornRightToHorn (p + 1) q j ≫
          joinBoundaryHornRightFromHornSucc p q j =
      (joinBoundaryHornRightPushoutObjObj (p + 1) q j).inl := by
  rw [← Category.assoc, joinBoundaryHornRightPushout_inl_toHorn]
  apply joinBoundaryHornRight_hom_ext (p + 1) q j
  intro r hr
  rw [joinBoundaryHornRightFactorMap_face_assoc]
  rw [joinBoundaryHornRight_face_fromHornSucc]
  have hback : ¬(rightJoinHornIndex (p + 1) q r).val ≤ p + 1 := by
    dsimp [rightJoinHornIndex]
    omega
  rw [joinBoundaryHornRightFaceSucc_back p q j
    (rightJoinHornIndex (p + 1) q r)
    (rightJoinHornIndex_ne (p + 1) q j r hr) hback]
  unfold joinBoundaryHornRightBackFaceSucc
  rw [joinHornΔcastInv_eq, joinHornΔcast_eq _ rfl,
    joinHornΔcast_rfl]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  have hidx : joinBackIndexSucc p q
      (rightJoinHornIndex (p + 1) q r) hback = r := by
    apply Fin.ext
    dsimp [joinBackIndexSucc, rightJoinHornIndex]
    omega
  have hhorn : horn.ι j
        (joinBackIndexSucc p q
          (rightJoinHornIndex (p + 1) q r) hback)
        (joinBackIndexSucc_ne p q j
          (rightJoinHornIndex (p + 1) q r) hback
          (rightJoinHornIndex_ne (p + 1) q j r hr)) =
      horn.ι j r hr := by
    simp only [hidx]
  rw [hhorn]

set_option maxHeartbeats 1000000 in
private lemma joinBoundaryHornRight_inr_toHorn_fromHornSucc
    (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).inr ≫
        joinBoundaryHornRightToHorn (p + 1) q j ≫
          joinBoundaryHornRightFromHornSucc p q j =
      (joinBoundaryHornRightPushoutObjObj (p + 1) q j).inr := by
  rw [← Category.assoc, joinBoundaryHornRightPushout_inr_toHorn]
  apply joinBoundaryHornRightBoundary_hom_ext p q
  intro r
  rw [joinBoundaryHornRightBoundaryFactorMap_succ]
  rw [joinBoundaryHornRightBoundaryFactorMapSucc_face_assoc]
  rw [joinBoundaryHornRight_face_fromHornSucc]
  have hfront : (rightJoinFrontFaceIndex p q r).val ≤ p + 1 := by
    dsimp [rightJoinFrontFaceIndex]
    have := r.isLt
    omega
  rw [joinBoundaryHornRightFaceSucc_front p q j
    (rightJoinFrontFaceIndex p q r)
    (rightJoinFrontFaceIndex_ne p q j r) hfront]
  unfold joinBoundaryHornRightFrontFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [joinHornΔcast_comp_assoc, joinHornΔcast_eq _ rfl,
    joinHornΔcast_rfl, Category.id_comp]
  simp only [Iso.hom_inv_id_assoc]
  have hidx : (⟨(rightJoinFrontFaceIndex p q r).val, by
      dsimp [rightJoinFrontFaceIndex]
      exact r.isLt⟩ : Fin (p + 2)) = r := by
    apply Fin.ext
    rfl
  rw [hidx]
  rfl

lemma joinBoundaryHornRightToHorn_fromHornSucc
    (p q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightToHorn (p + 1) q j ≫
        joinBoundaryHornRightFromHornSucc p q j = 𝟙 _ := by
  apply (joinBoundaryHornRightPushoutObjObj (p + 1) q j).hom_ext
  · simpa only [Category.comp_id] using
      joinBoundaryHornRight_inl_toHorn_fromHornSucc p q j
  · simpa only [Category.comp_id] using
      joinBoundaryHornRight_inr_toHorn_fromHornSucc p q j

/-- The positive-left-dimensional right boundary--horn pushout is the shifted horn. -/
noncomputable def joinBoundaryHornRightPointIsoSucc
    (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPushoutObjObj.{u} (p + 1) q j).pt ≅
      (horn ((p + 1) + (q + 1) + 1)
        (rightJoinHornIndex (p + 1) q j) : SSet.{u}) where
  hom := joinBoundaryHornRightToHorn (p + 1) q j
  inv := joinBoundaryHornRightFromHornSucc p q j
  hom_inv_id := joinBoundaryHornRightToHorn_fromHornSucc p q j
  inv_hom_id := joinBoundaryHornRightFromHornSucc_toHorn p q j

@[simp]
lemma joinBoundaryHornRightPointIsoSucc_hom
    (p q : ℕ) (j : Fin (q + 2)) :
    (joinBoundaryHornRightPointIsoSucc.{u} p q j).hom =
      joinBoundaryHornRightToHorn (p + 1) q j :=
  rfl

end JoinHorn.Internal
end SSet

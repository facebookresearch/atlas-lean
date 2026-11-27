/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftFaces

/-!
# The positive-right-dimensional left join--horn isomorphism
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

set_option maxHeartbeats 1000000 in
lemma joinHornBoundaryLeftFaceSucc_toHorn
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p (q + 1) i) :
    joinHornBoundaryLeftFaceSucc.{u} p q i t hne ≫
        joinHornBoundaryLeftToHornSucc p q i =
      horn.ι (leftJoinHornIndex p (q + 1) i) t hne := by
  rw [← cancel_mono
    (horn ((p + 1) + (q + 1) + 1)
      (leftJoinHornIndex p (q + 1) i)).ι]
  simp only [Category.assoc]
  rw [joinHornBoundaryLeftToHornSucc_ι, horn.ι_ι]
  by_cases htf : t.val ≤ p + 1
  · rw [joinHornBoundaryLeftFaceSucc_front p q i t hne htf]
    unfold joinHornBoundaryLeftFrontFaceSucc
    rw [Category.assoc, Category.assoc, Category.assoc,
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inr_ι_assoc]
    simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
    rw [horn.ι_ι]
    have hdual := joinHorn_dualFrontPush
      (joinHornBoundaryLeftFrontIndexSucc p q t htf) t rfl
      (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1))
    simp only [Category.assoc]
    rw [hdual]
    simp only [Iso.inv_hom_id_assoc]
    rw [joinHornΔcastInv_eq]
    simp only [← Category.assoc]
    rw [joinHornΔcast_comp, joinHornΔcast_eq _ rfl,
      joinHornΔcast_rfl, Category.id_comp]
  · rw [joinHornBoundaryLeftFaceSucc_back p q i t hne htf]
    unfold joinHornBoundaryLeftBackFaceSucc
    rw [Category.assoc, Category.assoc, Category.assoc,
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inl_ι_assoc]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [boundary.ι_ι]
    simp only [Category.assoc]
    rw [← joinHorn_backPush_assoc]
    simp only [Iso.inv_hom_id, Category.comp_id]
    have hi : leftJoinBackFaceIndex p q
          (joinBackIndexSucc p q t htf) = t := by
      apply Fin.ext
      dsimp [leftJoinBackFaceIndex, joinBackIndexSucc]
      have htlo : p + 2 ≤ t.val := by omega
      omega
    change joinHornΔcastInv _ ≫ stdSimplex.δ
        (leftJoinBackFaceIndex p q
          (joinBackIndexSucc p q t htf)) = stdSimplex.δ t
    rw [hi]
    rw [joinHornΔcastInv_eq, stdSimplex_δ_eq_map,
      joinHornΔcast, joinHornΔcastIso, Functor.mapIso_hom,
      ← Functor.map_comp]
    congr 1


/-- The inverse map obtained by descending the compatible face family. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftFromHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (horn ((p + 1) + (q + 1) + 1)
      (leftJoinHornIndex p (q + 1) i) : SSet.{u}) ⟶
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).pt :=
  (joinHornBoundaryLeftFaceSucc_compatible.{u} p q i).desc

@[reassoc (attr := simp)]
lemma joinHornBoundaryLeft_face_fromHornSucc
    (p q : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + (q + 1) + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p (q + 1) i) :
    horn.ι (leftJoinHornIndex p (q + 1) i) t hne ≫
        joinHornBoundaryLeftFromHornSucc p q i =
      joinHornBoundaryLeftFaceSucc p q i t hne := by
  apply horn.IsCompatible.ι_desc

lemma joinHornBoundaryLeftFromHornSucc_toHorn
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftFromHornSucc p q i ≫
        joinHornBoundaryLeftToHornSucc p q i = 𝟙 _ := by
  apply horn.hom_ext'
  intro t ht
  simp only [← Category.assoc, joinHornBoundaryLeft_face_fromHornSucc,
    joinHornBoundaryLeftFaceSucc_toHorn, Category.comp_id]

set_option maxHeartbeats 1000000 in
private lemma joinHornBoundaryLeft_inl_toHorn_fromHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).inl ≫
        joinHornBoundaryLeftToHornSucc p q i ≫
          joinHornBoundaryLeftFromHornSucc p q i =
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inl := by
  rw [← Category.assoc, joinHornBoundaryLeftPushout_inl_toHornSucc]
  apply joinHornBoundaryLeftBoundary_hom_ext p q
  intro r
  rw [joinHornBoundaryLeftBoundaryFactorMapSucc_face_assoc]
  rw [joinHornBoundaryLeft_face_fromHornSucc]
  have hback : ¬(leftJoinBackFaceIndex p q r).val ≤ p + 1 := by
    dsimp [leftJoinBackFaceIndex]
    omega
  rw [joinHornBoundaryLeftFaceSucc_back p q i
    (leftJoinBackFaceIndex p q r)
    (leftJoinBackFaceIndex_ne p q i r) hback]
  unfold joinHornBoundaryLeftBackFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [joinHornΔcast_comp_assoc, joinHornΔcast_eq _ rfl,
    joinHornΔcast_rfl, Category.id_comp]
  simp only [Iso.hom_inv_id_assoc]
  have hidx : joinBackIndexSucc p q
      (leftJoinBackFaceIndex p q r) hback = r := by
    apply Fin.ext
    dsimp [joinBackIndexSucc, leftJoinBackFaceIndex]
    omega
  rw [hidx]

set_option maxHeartbeats 1000000 in
private lemma joinHornBoundaryLeft_inr_toHorn_fromHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).inr ≫
        joinHornBoundaryLeftToHornSucc p q i ≫
          joinHornBoundaryLeftFromHornSucc p q i =
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).inr := by
  rw [← Category.assoc, joinHornBoundaryLeftPushout_inr_toHornSucc]
  apply joinHornBoundaryLeftHorn_hom_ext p (q + 1) i
  intro r hr
  rw [joinHornBoundaryLeftHornFactorMap_face_assoc]
  rw [joinHornBoundaryLeft_face_fromHornSucc]
  have hfront : (leftJoinHornIndex p (q + 1) r).val ≤ p + 1 := by
    dsimp [leftJoinHornIndex]
    have := r.isLt
    omega
  rw [joinHornBoundaryLeftFaceSucc_front p q i
    (leftJoinHornIndex p (q + 1) r)
    (leftJoinHornIndex_ne p (q + 1) i r hr) hfront]
  unfold joinHornBoundaryLeftFrontFaceSucc
  rw [joinHornΔcastInv_eq]
  rw [joinHornΔcast_comp_assoc, joinHornΔcast_eq _ rfl,
    joinHornΔcast_rfl, Category.id_comp]
  simp only [Iso.hom_inv_id_assoc]
  have hidx : joinHornBoundaryLeftFrontIndexSucc p q
      (leftJoinHornIndex p (q + 1) r) hfront = r := by
    apply Fin.ext
    rfl
  have hhorn : horn.ι i
        (joinHornBoundaryLeftFrontIndexSucc p q
          (leftJoinHornIndex p (q + 1) r) hfront)
        (joinHornBoundaryLeftFrontIndexSucc_ne p q i
          (leftJoinHornIndex p (q + 1) r) hfront
          (leftJoinHornIndex_ne p (q + 1) i r hr)) =
      horn.ι i r hr := by
    simp only [hidx]
  rw [hhorn]

lemma joinHornBoundaryLeftToHorn_fromHornSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftToHornSucc p q i ≫
        joinHornBoundaryLeftFromHornSucc p q i = 𝟙 _ := by
  apply (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).hom_ext
  · simpa only [Category.comp_id] using
      joinHornBoundaryLeft_inl_toHorn_fromHornSucc p q i
  · simpa only [Category.comp_id] using
      joinHornBoundaryLeft_inr_toHorn_fromHornSucc p q i

/-- The left horn--boundary point isomorphism in positive right dimension. -/
noncomputable def joinHornBoundaryLeftPointIsoSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).pt ≅
      (horn ((p + 1) + (q + 1) + 1)
        (leftJoinHornIndex p (q + 1) i) : SSet.{u}) where
  hom := joinHornBoundaryLeftToHornSucc p q i
  inv := joinHornBoundaryLeftFromHornSucc p q i
  hom_inv_id := joinHornBoundaryLeftToHorn_fromHornSucc p q i
  inv_hom_id := joinHornBoundaryLeftFromHornSucc_toHorn p q i

@[reassoc]
lemma joinHornBoundaryLeftPointIsoSucc_hom_inl
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).inl ≫
        (joinHornBoundaryLeftPointIsoSucc p q i).hom =
      joinHornBoundaryLeftBoundaryFactorMapSucc p q i :=
  joinHornBoundaryLeftPushout_inl_toHornSucc p q i

@[reassoc]
lemma joinHornBoundaryLeftPointIsoSucc_hom_inr
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p (q + 1) i).inr ≫
        (joinHornBoundaryLeftPointIsoSucc p q i).hom =
      joinHornBoundaryLeftHornFactorMap p (q + 1) i :=
  joinHornBoundaryLeftPushout_inr_toHornSucc p q i

@[reassoc]
lemma joinHornBoundaryLeftPointIsoSucc_hom_ι
    (p q : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPointIsoSucc.{u} p q i).hom ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p (q + 1) i).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom :=
  joinHornBoundaryLeftToHornSucc_ι p q i

end JoinHorn.Internal
end SSet

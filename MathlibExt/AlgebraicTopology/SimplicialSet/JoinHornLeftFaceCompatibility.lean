/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornArithmetic
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornRightFactor

/-!
# Left join--horn face compatibility
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

lemma joinHorn_flip_map_eq {X X' Y : SSet.{u}} (f : X ⟶ X') :
    (join.flip.obj Y).map f = (join.map f).app Y := rfl

/-- A left-horn face transported into the shifted horn. -/
noncomputable def joinHornBoundaryLeftHornFaceMap
    (p q : ℕ) (i : Fin (p + 2))
    (r : ↑({i}ᶜ : Set (Fin (p + 2)))) :
    (join.obj (stdSimplex.face {r.1}ᶜ : SSet.{u})).obj
        (Δ[q] : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  (join.map (stdSimplex.faceSingletonComplIso r.1).inv).app
      (Δ[q] : SSet.{u}) ≫
    (joinStdSimplexIso p q).hom ≫
      joinHornΔcast (by omega : p + q + 1 = (p + 1) + q) ≫
        horn.ι (leftJoinHornIndex p q i)
          (leftJoinHornIndex p q r.1)
          (leftJoinHornIndex_ne p q i r.1 (by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))

set_option maxHeartbeats 1000000 in
@[reassoc]
lemma joinHornBoundaryLeftHornFaceMap_ι
    (p q : ℕ) (i : Fin (p + 2))
    (r : ↑({i}ᶜ : Set (Fin (p + 2)))) :
    joinHornBoundaryLeftHornFaceMap p q i r ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (join.map (stdSimplex.face {r.1}ᶜ).ι).app (Δ[q] : SSet.{u}) ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  unfold joinHornBoundaryLeftHornFaceMap
  rw [Category.assoc, Category.assoc, Category.assoc, horn.ι_ι]
  have hface : (stdSimplex.faceSingletonComplIso r.1).inv ≫
      stdSimplex.δ r.1 = (stdSimplex.face {r.1}ᶜ).ι := by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso r.1).hom,
      Iso.hom_inv_id_assoc, stdSimplex.faceSingletonComplIso_hom_ι]
  rw [← hface, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, cancel_epi]
  exact (joinHorn_dualFrontPush r.1 (leftJoinHornIndex p q r.1) rfl
    (by omega : p + q + 1 = (p + 1) + q)).symm

set_option backward.isDefEq.respectTransparency false in
lemma joinHornBoundaryLeftHornFaceMap_compatible
    (p q : ℕ) (i : Fin (p + 2))
    (a : (MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).L) :
    ((((horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
        Subcomplex.toSSetFunctor).map
          (join.flip.obj (Δ[q] : SSet.{u}))).fst a) ≫
        joinHornBoundaryLeftHornFaceMap p q i
          ((MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).fst a) =
      ((((horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
        Subcomplex.toSSetFunctor).map
          (join.flip.obj (Δ[q] : SSet.{u}))).snd a) ≫
        joinHornBoundaryLeftHornFaceMap p q i
          ((MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).snd a) := by
  rw [← cancel_mono
    (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι]
  simp only [Category.assoc]
  rw [joinHornBoundaryLeftHornFaceMap_ι,
    joinHornBoundaryLeftHornFaceMap_ι]
  simp only [← Category.assoc]
  rw [cancel_mono]
  let c := (horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
    Subcomplex.toSSetFunctor
  have hc := c.condition a
  have hπ (r : ↑({i}ᶜ : Set (Fin (p + 2)))) :
      c.π r = horn.faceι i r.1 (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2) := by
    rfl
  have hcfull := congrArg (fun z => z ≫ (horn (p + 1) i).ι) hc
  have hmap := congrArg (join.flip.obj (Δ[q] : SSet.{u})).map hcfull
  let I := (horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
    Subcomplex.toSSetFunctor
  have hmap' :
      (join.flip.obj (Δ[q] : SSet.{u})).map (I.fst a) ≫
          (join.flip.obj (Δ[q] : SSet.{u})).map
            (stdSimplex.face
              {((MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).fst a).1}ᶜ).ι =
        (join.flip.obj (Δ[q] : SSet.{u})).map (I.snd a) ≫
          (join.flip.obj (Δ[q] : SSet.{u})).map
            (stdSimplex.face
              {((MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).snd a).1}ᶜ).ι := by
    simpa only [c, I, hπ, Category.assoc, horn.faceι_ι, Functor.map_comp]
      using hmap
  change (join.flip.obj (Δ[q] : SSet.{u})).map (I.fst a) ≫
      (join.flip.obj (Δ[q] : SSet.{u})).map
        (stdSimplex.face
          {((MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).fst a).1}ᶜ).ι =
    (join.flip.obj (Δ[q] : SSet.{u})).map (I.snd a) ≫
      (join.flip.obj (Δ[q] : SSet.{u})).map
        (stdSimplex.face
          {((MultispanShape.ofLinearOrder ↑({i}ᶜ : Set (Fin (p + 2)))).snd a).1}ᶜ).ι
  exact hmap'



end JoinHorn.Internal
end SSet

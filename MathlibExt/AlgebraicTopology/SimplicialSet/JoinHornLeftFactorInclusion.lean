/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftFactor

/-!
# Final-inclusion law for the left joined-horn factor
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal
lemma joinHornBoundaryLeftHornFactorMap_ι
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftHornFactorMap.{u} p q i ≫
        (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι =
      (join.map (horn (p + 1) i).ι).app (Δ[q] : SSet.{u}) ≫
        (joinStdSimplexIso (p + 1) q).hom := by
  let _ : Nonempty ↑({i}ᶜ : Set (Fin (p + 2))) :=
    (Set.nonempty_compl_of_nontrivial i).to_subtype
  apply Multicofork.IsColimit.hom_ext (joinHornLeftMappedIsColimit.{u} p q i)
  intro r
  let rr : ↑({i}ᶜ : Set (Fin (p + 2))) :=
    ⟨r.1, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2⟩
  change (join.map (horn.faceι i rr.1 (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using rr.2))).app
      (Δ[q] : SSet.{u}) ≫
        (joinHornBoundaryLeftHornFactorMap p q i ≫
          (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι) =
    (join.map (horn.faceι i rr.1 (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using rr.2))).app
      (Δ[q] : SSet.{u}) ≫
        ((join.map (horn (p + 1) i).ι).app (Δ[q] : SSet.{u}) ≫
          (joinStdSimplexIso (p + 1) q).hom)
  calc
    _ = ((join.map (horn.faceι i rr.1 (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using rr.2))).app
        (Δ[q] : SSet.{u}) ≫ joinHornBoundaryLeftHornFactorMap p q i) ≫
          (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι := by
            rw [Category.assoc]
    _ = joinHornBoundaryLeftHornFaceMap p q i rr ≫
          (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i)).ι := by
            rw [joinHornBoundaryLeftHornFactorMap_face_raw]
    _ = (join.map (stdSimplex.face {rr.1}ᶜ).ι).app (Δ[q] : SSet.{u}) ≫
          (joinStdSimplexIso (p + 1) q).hom :=
            joinHornBoundaryLeftHornFaceMap_ι p q i rr
    _ = _ := by
      rw [← horn.faceι_ι i rr.1 (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using rr.2),
        Functor.map_comp, NatTrans.comp_app, Category.assoc]


end JoinHorn.Internal
end SSet

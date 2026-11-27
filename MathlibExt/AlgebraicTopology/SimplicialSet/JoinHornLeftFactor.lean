/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftFactorCore

/-!
# Left joined-horn factor API
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

set_option maxHeartbeats 1000000 in
@[reassoc]
lemma joinHornBoundaryLeftHornFactorMap_face
    (p q : ℕ) (i r : Fin (p + 2)) (hr : r ≠ i) :
    (join.map (horn.ι i r hr)).app (Δ[q] : SSet.{u}) ≫
        joinHornBoundaryLeftHornFactorMap p q i =
      (joinStdSimplexIso p q).hom ≫
        joinHornΔcast (by omega : p + q + 1 = (p + 1) + q) ≫
          horn.ι (leftJoinHornIndex p q i) (leftJoinHornIndex p q r)
            (leftJoinHornIndex_ne p q i r hr) := by
  let rr : ↑({i}ᶜ : Set (Fin (p + 2))) :=
    ⟨r, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hr⟩
  rw [← cancel_epi ((join.map
    (stdSimplex.faceSingletonComplIso r).inv).app (Δ[q] : SSet.{u}))]
  simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp]
  rw [horn.faceSingletonComplIso_inv_ι]
  change (join.map (horn.faceι i r hr)).app (Δ[q] : SSet.{u}) ≫
      joinHornBoundaryLeftHornFactorMap p q i =
    joinHornBoundaryLeftHornFaceMap p q i rr
  exact joinHornBoundaryLeftHornFactorMap_face_raw p q i rr


set_option backward.isDefEq.respectTransparency false in
lemma joinHornBoundaryLeftHorn_hom_ext
    (p q : ℕ) (i : Fin (p + 2)) {X : SSet.{u}}
    {f g : (join.obj (horn (p + 1) i : SSet.{u})).obj
      (Δ[q] : SSet.{u}) ⟶ X}
    (h : ∀ (r : Fin (p + 2)) (hr : r ≠ i),
      (join.map (horn.ι i r hr)).app (Δ[q] : SSet.{u}) ≫ f =
        (join.map (horn.ι i r hr)).app (Δ[q] : SSet.{u}) ≫ g) :
    f = g := by
  let _ : Nonempty ↑({i}ᶜ : Set (Fin (p + 2))) :=
    (Set.nonempty_compl_of_nontrivial i).to_subtype
  apply Multicofork.IsColimit.hom_ext (joinHornLeftMappedIsColimit p q i)
  intro r
  change (join.map (horn.faceι i r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))).app
        (Δ[q] : SSet.{u}) ≫ f =
    (join.map (horn.faceι i r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))).app
        (Δ[q] : SSet.{u}) ≫ g
  rw [← horn.faceSingletonComplIso_inv_ι, Functor.map_comp,
    NatTrans.comp_app, Category.assoc, Category.assoc, h r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2)]


end JoinHorn.Internal
end SSet

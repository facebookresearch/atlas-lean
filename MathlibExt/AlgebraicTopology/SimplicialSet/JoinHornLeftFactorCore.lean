/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftFaceCompatibility

/-!
# Left joined-horn colimit factor core
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

attribute [local instance] joinHorn_isConnectedWalkingMultispan

/-- The left-horn multicoequalizer after joining on the right. -/
noncomputable def joinHornLeftMappedCocone
    (p q : ℕ) (i : Fin (p + 2)) :=
  ((horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
    Subcomplex.toSSetFunctor).map (join.flip.obj (Δ[q] : SSet.{u}))

/-- The joined left-horn multicoequalizer remains a colimit. -/
noncomputable def joinHornLeftMappedIsColimit
    (p q : ℕ) (i : Fin (p + 2)) :
    IsColimit (joinHornLeftMappedCocone.{u} p q i) := by
  let _ : Nonempty ↑({i}ᶜ : Set (Fin (p + 2))) :=
    (Set.nonempty_compl_of_nontrivial i).to_subtype
  exact Multicofork.isColimitMapOfPreserves
    ((horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor)
    (join.flip.obj (Δ[q] : SSet.{u})) (horn.isColimit i)

/-- Colimit data defining the map from the left horn piece. -/
structure JoinHornBoundaryLeftHornFactorData
    (p q : ℕ) (i : Fin (p + 2)) where
  /-- The induced map from the joined horn. -/
  map : (join.obj (horn (p + 1) i : SSet.{u})).obj
      (Δ[q] : SSet.{u}) ⟶
    (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u})
  face (r : ↑({i}ᶜ : Set (Fin (p + 2)))) :
    (join.map (horn.faceι i r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))).app
        (Δ[q] : SSet.{u}) ≫ map =
      joinHornBoundaryLeftHornFaceMap p q i r

set_option backward.isDefEq.respectTransparency false in
/-- The chosen left-horn factor and its face equations. -/
noncomputable def joinHornBoundaryLeftHornFactorData
    (p q : ℕ) (i : Fin (p + 2)) :
    JoinHornBoundaryLeftHornFactorData.{u} p q i := by
  let m := Multicofork.IsColimit.desc (joinHornLeftMappedIsColimit p q i)
    (joinHornBoundaryLeftHornFaceMap p q i)
    (joinHornBoundaryLeftHornFaceMap_compatible p q i)
  refine { map := m, face := fun r => ?_ }
  have hfac := Multicofork.IsColimit.fac (joinHornLeftMappedIsColimit p q i)
    (joinHornBoundaryLeftHornFaceMap p q i)
    (joinHornBoundaryLeftHornFaceMap_compatible p q i) r
  change (join.map (horn.faceι i r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))).app
        (Δ[q] : SSet.{u}) ≫ m =
    joinHornBoundaryLeftHornFaceMap p q i r at hfac
  exact hfac

/-- The canonical map from the left horn piece to the shifted horn. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftHornFactorMap
    (p q : ℕ) (i : Fin (p + 2)) :
    (join.obj (horn (p + 1) i : SSet.{u})).obj (Δ[q] : SSet.{u}) ⟶
      (horn ((p + 1) + q + 1) (leftJoinHornIndex p q i) : SSet.{u}) :=
  (joinHornBoundaryLeftHornFactorData p q i).map

lemma joinHornBoundaryLeftHornFactorMap_face_raw
    (p q : ℕ) (i : Fin (p + 2))
    (r : ↑({i}ᶜ : Set (Fin (p + 2)))) :
    (join.map (horn.faceι i r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))).app
        (Δ[q] : SSet.{u}) ≫
        joinHornBoundaryLeftHornFactorMap p q i =
      joinHornBoundaryLeftHornFaceMap p q i r :=
  (joinHornBoundaryLeftHornFactorData p q i).face r


end JoinHorn.Internal
end SSet

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedSupportInteraction









namespace StatMech.FrontierD

noncomputable section



theorem fkRectRefinedBoundaryPrimalLift_liftedVertex
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectLiftedVertex R (fkRectRefinedBoundaryPrimalLift R d) =
      fkRectMedialDartPrimalLabel R d := by
  let e := fkRectTorusMedialEdgeEquiv R d.1
  have horient := fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation R e
  rcases d with ⟨v, side⟩
  change fkRectLiftedVertex R
      (fkRectRefinedBoundaryPrimalLift R (v, side)) = _
  cases h : fkRectClosedPairingAtEdge e <;> cases side
  all_goals simp [h, e] at horient
  all_goals
    simp [fkRectRefinedBoundaryPrimalLift,
      fkRectMedialDartPrimalLabel, e, h, horient]


theorem fkRectRefinedBoundaryPrimalPotential_exists_deck
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    ∃ u : Int × Int,
      fkRectRefinedBoundaryPrimalPotential R d =
        (4 * (fkRectSquareDeckTranslation R u).1,
          4 * (fkRectSquareDeckTranslation R u).2) := by
  let p := fkRectRefinedBoundaryPrimalLift R d
  let x := fkRectMedialDartPrimalLabel R d
  let q : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  have hpq : fkRectLiftedVertex R p = fkRectLiftedVertex R q := by
    rw [show fkRectLiftedVertex R p = x by
      exact fkRectRefinedBoundaryPrimalLift_liftedVertex R d]
    simp [q, fkRectLiftedVertex]
  obtain ⟨u, hu⟩ :=
    (fkRectLiftedVertex_eq_iff_exists_period R p q).mp hpq
  refine ⟨u, ?_⟩
  have hdevelop := fkRectSquareDevelopPoint_add_period R q u
  rw [← hu] at hdevelop
  unfold fkRectRefinedBoundaryPrimalPotential
  change (4 * (fkRectSquareDevelopPoint p -
      fkRectVertexSquarePoint R x).1,
    4 * (fkRectSquareDevelopPoint p -
      fkRectVertexSquarePoint R x).2) = _
  have hx : fkRectVertexSquarePoint R x = fkRectSquareDevelopPoint q := by
    rfl
  rw [hx, hdevelop]



theorem fkRectRefinedBoundaryCenterAfter_exists_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    ∃ u : Int × Int,
      fkRectRefinedBoundaryCenterAfter pairing d
          (fkRectRefinedBoundaryCanonicalCenter R d) n =
        ((fkRectRefinedBoundaryCanonicalCenter R
            ((fkMedialBoundaryStep pairing)^[n] d)).1 +
            4 * (fkRectSquareDeckTranslation R u).1,
          (fkRectRefinedBoundaryCanonicalCenter R
            ((fkMedialBoundaryStep pairing)^[n] d)).2 +
            4 * (fkRectSquareDeckTranslation R u).2) := by
  let d' := (fkMedialBoundaryStep pairing)^[n] d
  let A := fkRectMedialBoundaryPrimalSeamTrace R pairing d n
  obtain ⟨u, hu⟩ := fkRectRefinedBoundaryPrimalPotential_exists_deck R d
  obtain ⟨v, hv⟩ := fkRectRefinedBoundaryPrimalPotential_exists_deck R d'
  refine ⟨A + u - v, ?_⟩
  have hcenter := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d (0, 0) n
  simp only [add_zero] at hcenter
  rw [hcenter, hu, hv]
  apply Prod.ext <;>
    simp [A, d', fkRectSquareDeckTranslation] <;> ring

end

end StatMech.FrontierD

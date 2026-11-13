/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedWalkCarrier









namespace StatMech.FrontierD

open Equiv

noncomputable section



def fkRectCanonicalRefinedBoundaryOrbitDarts
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    List FKRectIntegralSquareDart :=
  fkRectRefinedBoundaryDarts
    (fkRectConfigurationToMedialPairing R omega) d
    (fkRectRefinedBoundaryCanonicalCenter R d)
    (orderOf (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega)))



def fkRectCanonicalRefinedBoundaryOrbitCoverDarts
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :=
  fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts R omega d)
    (fkRectRefinedBoundaryOrbitTranslation
      (fkRectConfigurationToMedialPairing R omega) d
      (fkRectRefinedBoundaryCanonicalCenter R d))



theorem fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint
        (fkRectRefinedBoundaryCanonicalCenter R d) d.2)
      ((fkRectRefinedDartPoint
          (fkRectRefinedBoundaryCanonicalCenter R d) d.2).1 +
          (fkRectRefinedBoundaryOrbitTranslation
            (fkRectConfigurationToMedialPairing R omega) d
            (fkRectRefinedBoundaryCanonicalCenter R d)).1,
        (fkRectRefinedDartPoint
          (fkRectRefinedBoundaryCanonicalCenter R d) d.2).2 +
          (fkRectRefinedBoundaryOrbitTranslation
            (fkRectConfigurationToMedialPairing R omega) d
            (fkRectRefinedBoundaryCanonicalCenter R d)).2)
      (fkRectCanonicalRefinedBoundaryOrbitDarts R omega d) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let n := orderOf (fkMedialBoundaryStep pairing)
  let c' := fkRectRefinedBoundaryCenterAfter pairing d c n
  let u := fkRectRefinedBoundaryOrbitTranslation pairing d c
  have hpath := fkRectRefinedBoundaryOrbitDarts_path pairing d c
  change FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint c' d.2)
      (fkRectRefinedBoundaryDarts pairing d c n) at hpath
  have hend : fkRectRefinedDartPoint c' d.2 =
      ((fkRectRefinedDartPoint c d.2).1 + u.1,
        (fkRectRefinedDartPoint c d.2).2 + u.2) := by
    unfold fkRectRefinedDartPoint u
      fkRectRefinedBoundaryOrbitTranslation c' n
    apply Prod.ext <;> simp <;> ring
  rw [hend] at hpath
  exact hpath



theorem fkRectRefinedBoundaryOrbitTranslation_ne_zero_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d) ≠ (0, 0) ↔
      fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) ≠ (0, 0) := by
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
    fkRectFourSquareDeck_ne_zero_iff]



theorem fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    {hw : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R hw) :
    fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d)
        C.coverDarts ≠ 0 ↔
      FKRectWindingIndependent
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
        (fkRectWalkWinding R w) := by
  change fkRectRefinedRawInteraction
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        (fkRectCanonicalRefinedBoundaryOrbitDarts R omega d)
        (fkRectRefinedBoundaryOrbitTranslation
          (fkRectConfigurationToMedialPairing R omega) d
          (fkRectRefinedBoundaryCanonicalCenter R d)))
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        C.darts C.translation) ≠ 0 ↔ _
  rw [fkRectSquareCoverDartList_interaction_ne_zero_iff
    (fkRectRefinedCoverTorus R)
    (fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d)
    C.path_translation]
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]
  change FKRectWindingIndependent
      (4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
        4 * (fkRectSquareDeckTranslation R
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2) ↔ _
  rw [hw.closed_develop_sub_eq_deck_winding R]
  exact fkRectWindingIndependent_four_squareDeck_iff R _ _



theorem fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_zero_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    {hw : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R hw) :
    fkRectRefinedRawInteraction
        (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d)
        C.coverDarts = 0 ↔
      ¬ FKRectWindingIndependent
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
        (fkRectWalkWinding R w) := by
  rw [← not_ne_iff]
  exact not_congr
    (fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff
      R omega d C)

end

end StatMech.FrontierD

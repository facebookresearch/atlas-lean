/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedBoundary
import Code.FrontierD.FKRectTorusDualEdges



namespace StatMech.FrontierD

noncomputable section



def fkRectRefinedDualEdgeStart (R : FKRectTorus) (d : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).1
  (4 * p.1 + 2, 4 * p.2 + 2)



def fkRectRefinedDualEdgeEnd (R : FKRectTorus) (d : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).2
  (4 * p.1 + 2, 4 * p.2 + 2)



def fkRectRefinedDualEdgeCenter (R : FKRectTorus) (d : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).1
  let q := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).2
  (2 * (p.1 + q.1) + 2, 2 * (p.2 + q.2) + 2)



def fkRectRefinedDualEdgeDarts (R : FKRectTorus) (d : R.EdgeIndex) :
    List FKRectIntegralSquareDart :=
  let p := fkRectRefinedDualEdgeStart R d
  if fkRectClosedPairingAtEdge d then
    [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
      ((p.1 - 3, p.2), 2)]
  else
    [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
      ((p.1, p.2 + 3), 1)]





theorem exists_fkRectRefinedDualEdgeCenter_edgeToDualEdge_eq_add_deck
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ∃ u : Int × Int,
      fkRectRefinedDualEdgeCenter R (fkRectEdgeToDualEdge R e) =
        ((fkRectRefinedPrimalEdgeCenter R e).1 +
            4 * (fkRectSquareDeckTranslation R u).1,
          (fkRectRefinedPrimalEdgeCenter R e).2 +
            4 * (fkRectSquareDeckTranslation R u).2) := by
  rcases e with ⟨b, x, y⟩
  cases b
  · by_cases hx : x.val = 0
    · refine ⟨(1, 0), ?_⟩
      by_cases hy : Even y.val
      all_goals simp [fkRectRefinedDualEdgeCenter,
        fkRectRefinedPrimalEdgeCenter, fkRectEdgeToDualEdge,
        fkRectLiftedIndexedEdgeEnds, fkRectSquareDevelopPoint,
        fkRectSquareDeckTranslation, fkRectCyclicPred_val, hx, hy]
      · obtain ⟨k, hk⟩ := hy
        omega
      · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
        omega
    · refine ⟨(0, 0), ?_⟩
      by_cases hy : Even y.val
      all_goals simp [fkRectRefinedDualEdgeCenter,
        fkRectRefinedPrimalEdgeCenter, fkRectEdgeToDualEdge,
        fkRectLiftedIndexedEdgeEnds, fkRectSquareDevelopPoint,
        fkRectSquareDeckTranslation, fkRectCyclicPred_val, hx, hy]
      · obtain ⟨k, hk⟩ := hy
        omega
      · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
        omega
  · refine ⟨(0, 0), ?_⟩
    by_cases hy : Even y.val
    all_goals simp [fkRectRefinedDualEdgeCenter,
      fkRectRefinedPrimalEdgeCenter, fkRectEdgeToDualEdge,
      fkRectLiftedIndexedEdgeEnds, fkRectSquareDevelopPoint,
      fkRectSquareDeckTranslation, hy]
    · obtain ⟨k, hk⟩ := hy
      omega
    · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
      omega



theorem fkRectRefinedDualEdgeDarts_eq_centerline
    (R : FKRectTorus) (d : R.EdgeIndex) :
    fkRectRefinedDualEdgeDarts R d =
      fkRectRefinedPrimalCenterlineDarts
        (fkRectClosedPairingAtEdge d)
        (fkRectRefinedDualEdgeCenter R d) := by
  have h := fkRectCanonicalSquareEdgeStep_eq R d
  by_cases hp : fkRectClosedPairingAtEdge d
  · simp [hp] at h
    unfold fkRectRefinedDualEdgeDarts
      fkRectRefinedPrimalCenterlineDarts
    simp only [hp, if_true]
    unfold fkRectRefinedDualEdgeStart fkRectRefinedDualEdgeCenter
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    simp
    all_goals omega
  · simp [hp] at h
    unfold fkRectRefinedDualEdgeDarts
      fkRectRefinedPrimalCenterlineDarts
    simp only [hp]
    unfold fkRectRefinedDualEdgeStart fkRectRefinedDualEdgeCenter
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    simp
    all_goals omega



theorem fkRectRefinedDualEdgeDarts_path
    (R : FKRectTorus) (d : R.EdgeIndex) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDualEdgeStart R d)
      (fkRectRefinedDualEdgeEnd R d)
      (fkRectRefinedDualEdgeDarts R d) := by
  have hend : fkRectRefinedDualEdgeEnd R d =
      if fkRectClosedPairingAtEdge d then
        ((fkRectRefinedDualEdgeStart R d).1 - 4,
          (fkRectRefinedDualEdgeStart R d).2)
      else
        ((fkRectRefinedDualEdgeStart R d).1,
          (fkRectRefinedDualEdgeStart R d).2 + 4) := by
    have h := fkRectCanonicalSquareEdgeStep_eq R d
    by_cases hp : fkRectClosedPairingAtEdge d = true
    · simp [hp] at h ⊢
      unfold fkRectRefinedDualEdgeStart fkRectRefinedDualEdgeEnd
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
    · have hp' : fkRectClosedPairingAtEdge d = false :=
        Bool.eq_false_of_not_eq_true hp
      simp [hp, hp'] at h ⊢
      unfold fkRectRefinedDualEdgeStart fkRectRefinedDualEdgeEnd
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  rw [hend]
  by_cases hp : fkRectClosedPairingAtEdge d
  · simpa [fkRectRefinedDualEdgeDarts, hp] using
      fkRectRefinedFourWest_path_public (fkRectRefinedDualEdgeStart R d)
  · simpa [fkRectRefinedDualEdgeDarts, hp] using
      fkRectRefinedFourNorth_path_public (fkRectRefinedDualEdgeStart R d)

end

end StatMech.FrontierD

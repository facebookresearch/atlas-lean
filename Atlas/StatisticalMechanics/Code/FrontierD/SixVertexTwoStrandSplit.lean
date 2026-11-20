/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoDisagreementStrand










namespace StatMech.FrontierD



theorem exists_list_prefix_sum_eq_of_unitSteps
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (target total : Int) (hsum : steps.sum = total)
    (htarget_nonneg : 0 <= target) (htarget_le : target <= total) :
    ∃ pre suf : List Int,
      steps = pre ++ suf /\ pre.sum = target := by
  induction steps generalizing target total with
  | nil =>
      have htarget : target = 0 := by simp at hsum; omega
      exact ⟨[], [], rfl, by simp [htarget]⟩
  | cons step steps ih =>
      have hstep := hsteps step (by simp)
      have htail : ∀ z ∈ steps, z = 1 \/ z = -1 := by
        intro z hz
        exact hsteps z (by simp [hz])
      by_cases htarget : target = 0
      · exact ⟨[], step :: steps, by simp, by simp [htarget]⟩
      · have htarget_pos : 0 < target := by omega
        rcases hstep with rfl | rfl
        · have htailSum : steps.sum = total - 1 := by
            simp only [List.sum_cons] at hsum
            omega
          have hlow : 0 <= target - 1 := by omega
          have hhigh : target - 1 <= total - 1 := by omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            ih htail (target - 1) (total - 1) htailSum hlow hhigh
          exact ⟨1 :: pre, suf, by simp [hsplit], by simp [hprefix]⟩
        · have htailSum : steps.sum = total + 1 := by
            simp only [List.sum_cons] at hsum
            omega
          have hlow : 0 <= target + 1 := by omega
          have hhigh : target + 1 <= total + 1 := by omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            ih htail (target + 1) (total + 1) htailSum hlow hhigh
          exact ⟨-1 :: pre, suf, by simp [hsplit], by simp [hprefix]⟩



theorem exists_two_unit_sum_arcs_of_sum_eq_two
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    ∃ first second : List Int,
      steps = first ++ second /\ first.sum = 1 /\ second.sum = 1 := by
  obtain ⟨first, second, hsplit, hfirst⟩ :=
    exists_list_prefix_sum_eq_of_unitSteps
      steps hsteps 1 2 hsum (by norm_num) (by norm_num)
  refine ⟨first, second, hsplit, hfirst, ?_⟩
  rw [hsplit, List.sum_append, hfirst] at hsum
  omega



theorem exists_two_unit_arcs_of_degreeTwoStrandSeamWord
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (hsum : (sixVertexDegreeTwoStrandSeamWord
      homega heta hdegree seed).sum = 2) :
    ∃ first second : List Int,
      sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed =
          first ++ second /\
        first.sum = 1 /\ second.sum = 1 :=
  exists_two_unit_sum_arcs_of_sum_eq_two
    (sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed)
    (sixVertexDegreeTwoStrandSeamWord_unitSteps
      homega heta hdegree seed) hsum



theorem exists_two_unit_arcs_of_all_degreeTwoStrands
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    ∃ first second : List Int,
      sixVertexDegreeTwoAllStrandsSeamWord homega heta hdegree =
          first ++ second /\
        first.sum = 1 /\ second.sum = 1 :=
  exists_two_unit_sum_arcs_of_sum_eq_two
    (sixVertexDegreeTwoAllStrandsSeamWord homega heta hdegree)
    (sixVertexDegreeTwoAllStrandsSeamWord_unitSteps
      homega heta hdegree)
    (sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two
      homega heta hdegree n homegaSector hetaSector hn)

end StatMech.FrontierD

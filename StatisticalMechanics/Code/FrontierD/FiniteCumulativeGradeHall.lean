/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairTotalCMonotone










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance finiteCumulativeGradeHallPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


theorem finiteGradeHall_of_upperCumulative
    {Source Target : Type*}
    [Fintype Source] [Fintype Target]
    (sourceGrade : Source -> Nat) (targetGrade : Target -> Nat)
    (hcumulative : forall grade,
      (Finset.univ.filter fun source => grade <= sourceGrade source).card <=
        (Finset.univ.filter fun target => grade <= targetGrade target).card) :
    forall sources : Finset Source,
      sources.card <=
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources,
            sourceGrade source <= targetGrade target).card := by
  intro sources
  by_cases hsources : sources = ∅
  · simp [hsources]
  · have hsourcesNonempty : sources.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hsources
    let grades := sources.image sourceGrade
    have hgrades : grades.Nonempty := hsourcesNonempty.image sourceGrade
    let minimum := grades.min' hgrades
    obtain ⟨minimumSource, hminimumSource, hminimumGrade⟩ :=
      Finset.mem_image.mp (Finset.min'_mem grades hgrades)
    have hsourcesUpper : sources ⊆
        Finset.univ.filter fun source => minimum <= sourceGrade source := by
      intro source hsource
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.min'_le grades (sourceGrade source)
        (Finset.mem_image.mpr ⟨source, hsource, rfl⟩)
    have htargetsUpper :
        (Finset.univ.filter fun target => minimum <= targetGrade target) ⊆
          (Finset.univ.filter fun target =>
            ∃ source ∈ sources,
              sourceGrade source <= targetGrade target) := by
      intro target htarget
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htarget ⊢
      refine ⟨minimumSource, hminimumSource, ?_⟩
      rw [hminimumGrade]
      exact htarget
    calc
      sources.card <=
          (Finset.univ.filter fun source =>
            minimum <= sourceGrade source).card :=
        Finset.card_le_card hsourcesUpper
      _ <= (Finset.univ.filter fun target =>
          minimum <= targetGrade target).card := hcumulative minimum
      _ <= (Finset.univ.filter fun target =>
          ∃ source ∈ sources,
            sourceGrade source <= targetGrade target).card :=
        Finset.card_le_card htargetsUpper


theorem exists_injective_gradeMonotone_of_upperCumulative
    {Source Target : Type*}
    [Fintype Source] [Fintype Target]
    (sourceGrade : Source -> Nat) (targetGrade : Target -> Nat)
    (hcumulative : forall grade,
      (Finset.univ.filter fun source => grade <= sourceGrade source).card <=
        (Finset.univ.filter fun target => grade <= targetGrade target).card) :
    exists matching : Source -> Target,
      Function.Injective matching /\
        forall source, sourceGrade source <= targetGrade (matching source) := by
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun source target => sourceGrade source <= targetGrade target)).mp
  exact finiteGradeHall_of_upperCumulative
    sourceGrade targetGrade hcumulative



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCCumulative
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcumulative : forall totalC,
      (Finset.univ.filter fun pair :
          SixVertexMarkedSectorConfiguration T
              ⟨middle.val - 1, by omega⟩ ×
            SixVertexMarkedSectorConfiguration T
              ⟨middle.val + 1, by omega⟩ =>
        totalC <= sixVertexTorusCTypeCount pair.1.1 +
          sixVertexTorusCTypeCount pair.2.1).card <=
      (Finset.univ.filter fun pair :
          SixVertexMarkedSectorConfiguration T middle ×
            SixVertexMarkedSectorConfiguration T middle =>
        totalC <= sixVertexTorusCTypeCount pair.1.1 +
          sixVertexTorusCTypeCount pair.2.1).card) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  let sourceGrade := fun pair :
      SixVertexMarkedSectorConfiguration T
          ⟨middle.val - 1, by omega⟩ ×
        SixVertexMarkedSectorConfiguration T
          ⟨middle.val + 1, by omega⟩ =>
    sixVertexTorusCTypeCount pair.1.1 +
      sixVertexTorusCTypeCount pair.2.1
  let targetGrade := fun pair :
      SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle =>
    sixVertexTorusCTypeCount pair.1.1 +
      sixVertexTorusCTypeCount pair.2.1
  obtain ⟨matching, hinjective, htotal⟩ :=
    exists_injective_gradeMonotone_of_upperCumulative
      sourceGrade targetGrade hcumulative
  let base :
      (SixVertexMarkedSectorConfiguration T
          ⟨middle.val - 1, by omega⟩ ×
        SixVertexMarkedSectorConfiguration T
          ⟨middle.val + 1, by omega⟩) ↪
      (SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle) :=
    ⟨matching, hinjective⟩
  exact sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCEmbedding
    T middle hmiddle_pos hmiddle_lt base htotal

end

end StatMech.FrontierD

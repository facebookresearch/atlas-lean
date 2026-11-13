/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexConfigurationPhysicalParticleHole
import Code.FrontierD.SixVertexFourByTwoTwoCycleHall










namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorThree :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨3, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoSectorThreeConfiguration (i : Fin 28) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorThree :=
  ⟨sixVertexArrowsComplement (sixVertexFourByTwoSectorOneConfiguration i).1,
    sixVertexArrowsComplement_iceRule
      (sixVertexFourByTwoSectorOneConfiguration i).2.1, by
      change sixVertexUpCount (fun x =>
        !(sixVertexFourByTwoSectorOneConfiguration i).1.vertical
          (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 3
      rw [sixVertexUpCount_complement]
      have hsector := (sixVertexFourByTwoSectorOneConfiguration i).2.2
      change sixVertexUpCount (fun x =>
        (sixVertexFourByTwoSectorOneConfiguration i).1.vertical
          (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 at hsector
      rw [hsector]
      norm_num [sixVertexFourByTwoTorus]⟩

theorem sixVertexFourByTwoSectorThreeConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorThreeConfiguration := by
  intro first second heq
  apply sixVertexFourByTwoSectorOneConfiguration_injective
  apply Subtype.ext
  apply sixVertexArrowsComplement_injective
  exact congrArg Subtype.val heq

theorem sixVertexFourByTwoSectorThreeConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorThreeConfiguration := by
  intro eta
  let hole : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
    ⟨sixVertexArrowsComplement eta.1,
      sixVertexArrowsComplement_iceRule eta.2.1, by
        change sixVertexUpCount (fun x =>
          !eta.1.vertical
            (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 1
        rw [sixVertexUpCount_complement]
        have hsector := eta.2.2
        change sixVertexUpCount (fun x =>
          eta.1.vertical
            (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 3 at hsector
        rw [hsector]
        norm_num [sixVertexFourByTwoTorus]⟩
  obtain ⟨i, hi⟩ := sixVertexFourByTwoSectorOneConfiguration_surjective hole
  refine ⟨i, Subtype.ext ?_⟩
  have harrows := congrArg Subtype.val hi
  change (sixVertexFourByTwoSectorOneConfiguration i).1 =
    sixVertexArrowsComplement eta.1 at harrows
  have hcomplement := congrArg sixVertexArrowsComplement harrows
  simpa [sixVertexFourByTwoSectorThreeConfiguration] using hcomplement

def sixVertexFourByTwoSectorThreeEquiv :
    Fin 28 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorThree :=
  Equiv.ofBijective sixVertexFourByTwoSectorThreeConfiguration
    ⟨sixVertexFourByTwoSectorThreeConfiguration_injective,
      sixVertexFourByTwoSectorThreeConfiguration_surjective⟩

abbrev sixVertexFourByTwoCentralSourceIndex := Fin 28 × Fin 28

abbrev sixVertexFourByTwoCentralTargetIndex :=
  {pair : Fin 50 × Fin 50 // pair.1 ≠ pair.2}

def sixVertexFourByTwoSectorOneCGrade : Fin 28 → Fin 2 := ![
  0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0
]

def sixVertexFourByTwoSectorTwoCGrade : Fin 50 → Fin 3 := ![
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1,
  1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]

theorem sixVertexFourByTwoConfiguration_cGrade_certificate :
    (∀ i : Fin 28,
      sixVertexCheckerHorizontalNontransitionCount
          (sixVertexFourByTwoSectorOneConfiguration i).1 =
        4 * (sixVertexFourByTwoSectorOneCGrade i).val) ∧
    (∀ i : Fin 50,
      sixVertexCheckerHorizontalNontransitionCount
          (sixVertexFourByTwoSectorTwoConfiguration i).1 =
        4 * (sixVertexFourByTwoSectorTwoCGrade i).val) := by
  decide +revert

theorem sixVertexFourByTwoSectorOneConfiguration_cTypeCount (i : Fin 28) :
    sixVertexTorusCTypeCount
        (sixVertexFourByTwoSectorOneConfiguration i).1 =
      4 * (sixVertexFourByTwoSectorOneCGrade i).val := by
  rw [sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount]
  exact sixVertexFourByTwoConfiguration_cGrade_certificate.1 i

theorem sixVertexFourByTwoSectorTwoConfiguration_cTypeCount (i : Fin 50) :
    sixVertexTorusCTypeCount
        (sixVertexFourByTwoSectorTwoConfiguration i).1 =
      4 * (sixVertexFourByTwoSectorTwoCGrade i).val := by
  rw [sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount]
  exact sixVertexFourByTwoConfiguration_cGrade_certificate.2 i

def sixVertexFourByTwoCentralSourceGrade
    (source : sixVertexFourByTwoCentralSourceIndex) : Fin 5 :=
  ⟨(sixVertexFourByTwoSectorOneCGrade source.1).val +
      (sixVertexFourByTwoSectorOneCGrade source.2).val, by omega⟩

def sixVertexFourByTwoCentralTargetGrade
    (target : sixVertexFourByTwoCentralTargetIndex) : Fin 5 :=
  ⟨(sixVertexFourByTwoSectorTwoCGrade target.1.1).val +
      (sixVertexFourByTwoSectorTwoCGrade target.1.2).val, by omega⟩

def sixVertexFourByTwoCentralSourceZeroRank (i : Fin 28) : Fin 16 :=
  ⟨if i.val < 8 then i.val else i.val - 12, by split_ifs <;> omega⟩

def sixVertexFourByTwoCentralSourceOneRank (i : Fin 28) : Fin 12 :=
  ⟨(i.val - 8) % 12, Nat.mod_lt _ (by norm_num)⟩

def sixVertexFourByTwoCentralTargetZeroIndex (i : Fin 24) : Fin 50 :=
  ⟨if i.val < 12 then i.val else i.val + 26, by split_ifs <;> omega⟩

def sixVertexFourByTwoCentralTargetOneIndex (i : Fin 24) : Fin 50 :=
  ⟨if i.val < 8 then i.val + 12
    else if i.val < 16 then i.val + 13 else i.val + 14, by
      split_ifs <;> omega⟩



def sixVertexFourByTwoCentralNonDiagonalPair (t : Nat) : Fin 24 × Fin 24 :=
  let first : Fin 24 := ⟨(t / 23) % 24, Nat.mod_lt _ (by norm_num)⟩
  let residue := t % 23
  let secondValue := if residue < first.val then residue else residue + 1
  (first, ⟨secondValue % 24, Nat.mod_lt _ (by norm_num)⟩)

def sixVertexFourByTwoCentralRawMatching
    (source : sixVertexFourByTwoCentralSourceIndex) : Fin 50 × Fin 50 :=
  if hfirst : (sixVertexFourByTwoSectorOneCGrade source.1).val = 0 then
    if hsecond : (sixVertexFourByTwoSectorOneCGrade source.2).val = 0 then
      let flat :=
        (sixVertexFourByTwoCentralSourceZeroRank source.1).val * 16 +
          (sixVertexFourByTwoCentralSourceZeroRank source.2).val
      let target := sixVertexFourByTwoCentralNonDiagonalPair flat
      (sixVertexFourByTwoCentralTargetZeroIndex target.1,
        sixVertexFourByTwoCentralTargetZeroIndex target.2)
    else
      (sixVertexFourByTwoCentralTargetZeroIndex
          ⟨(sixVertexFourByTwoCentralSourceZeroRank source.1).val, by omega⟩,
        sixVertexFourByTwoCentralTargetOneIndex
          ⟨(sixVertexFourByTwoCentralSourceOneRank source.2).val, by omega⟩)
  else if hsecond :
      (sixVertexFourByTwoSectorOneCGrade source.2).val = 0 then
    (sixVertexFourByTwoCentralTargetOneIndex
        ⟨(sixVertexFourByTwoCentralSourceOneRank source.1).val, by omega⟩,
      sixVertexFourByTwoCentralTargetZeroIndex
        ⟨(sixVertexFourByTwoCentralSourceZeroRank source.2).val, by omega⟩)
  else
    let flat :=
      (sixVertexFourByTwoCentralSourceOneRank source.1).val * 12 +
        (sixVertexFourByTwoCentralSourceOneRank source.2).val
    let target := sixVertexFourByTwoCentralNonDiagonalPair flat
    (sixVertexFourByTwoCentralTargetOneIndex target.1,
      sixVertexFourByTwoCentralTargetOneIndex target.2)

def sixVertexFourByTwoCentralRawTargetGrade
    (target : Fin 50 × Fin 50) : Fin 5 :=
  ⟨(sixVertexFourByTwoSectorTwoCGrade target.1).val +
      (sixVertexFourByTwoSectorTwoCGrade target.2).val, by omega⟩

set_option maxHeartbeats 5000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoCentralRawMatching_certificate :
    Function.Injective sixVertexFourByTwoCentralRawMatching ∧
      ∀ source,
        (sixVertexFourByTwoCentralRawMatching source).1 ≠
            (sixVertexFourByTwoCentralRawMatching source).2 ∧
          sixVertexFourByTwoCentralSourceGrade source =
            sixVertexFourByTwoCentralRawTargetGrade
              (sixVertexFourByTwoCentralRawMatching source) := by
  decide +revert

def sixVertexFourByTwoCentralIndexMatching
    (source : sixVertexFourByTwoCentralSourceIndex) :
    sixVertexFourByTwoCentralTargetIndex :=
  ⟨sixVertexFourByTwoCentralRawMatching source,
    sixVertexFourByTwoCentralRawMatching_certificate.2 source |>.1⟩

theorem sixVertexFourByTwoCentralIndexMatching_injective :
    Function.Injective sixVertexFourByTwoCentralIndexMatching := by
  intro first second heq
  apply sixVertexFourByTwoCentralRawMatching_certificate.1
  exact congrArg Subtype.val heq

theorem sixVertexFourByTwoCentralIndexMatching_grade
    (source : sixVertexFourByTwoCentralSourceIndex) :
    sixVertexFourByTwoCentralSourceGrade source =
      sixVertexFourByTwoCentralTargetGrade
        (sixVertexFourByTwoCentralIndexMatching source) :=
  sixVertexFourByTwoCentralRawMatching_certificate.2 source |>.2

def sixVertexFourByTwoCentralSourceEquiv :
    sixVertexFourByTwoCentralSourceIndex ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorThree) :=
  Equiv.prodCongr sixVertexFourByTwoSectorOneEquiv
    sixVertexFourByTwoSectorThreeEquiv

def sixVertexFourByTwoCentralTargetEquiv :
    (Fin 50 × Fin 50) ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo) :=
  Equiv.prodCongr sixVertexFourByTwoSectorTwoEquiv
    sixVertexFourByTwoSectorTwoEquiv

theorem sixVertexFourByTwoCentralSourceIndex_totalC
    (source : sixVertexFourByTwoCentralSourceIndex) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralSourceEquiv source) =
      4 * (sixVertexFourByTwoCentralSourceGrade source).val := by
  change
    sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorOneConfiguration source.1).1 +
        sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorThreeConfiguration source.2).1 = _
  simp only [sixVertexFourByTwoSectorThreeConfiguration,
    sixVertexArrowsComplement_cTypeCount,
    sixVertexFourByTwoSectorOneConfiguration_cTypeCount]
  simp [sixVertexFourByTwoCentralSourceGrade]
  omega

theorem sixVertexFourByTwoCentralTargetIndex_totalC
    (target : sixVertexFourByTwoCentralTargetIndex) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralTargetEquiv target.1) =
      4 * (sixVertexFourByTwoCentralTargetGrade target).val := by
  change
    sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorTwoConfiguration target.1.1).1 +
        sixVertexTorusCTypeCount
          (sixVertexFourByTwoSectorTwoConfiguration target.1.2).1 = _
  simp only [sixVertexFourByTwoSectorTwoConfiguration_cTypeCount]
  simp [sixVertexFourByTwoCentralTargetGrade]
  omega

def sixVertexFourByTwoCentralConfigurationMatching
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo :=
  sixVertexFourByTwoCentralTargetEquiv
    (sixVertexFourByTwoCentralIndexMatching
      (sixVertexFourByTwoCentralSourceEquiv.symm source)).1

theorem sixVertexFourByTwoCentralConfigurationMatching_injective :
    Function.Injective sixVertexFourByTwoCentralConfigurationMatching := by
  intro first second heq
  apply sixVertexFourByTwoCentralSourceEquiv.symm.injective
  apply sixVertexFourByTwoCentralIndexMatching_injective
  apply Subtype.ext
  apply sixVertexFourByTwoCentralTargetEquiv.injective
  exact heq

theorem sixVertexFourByTwoCentralConfigurationMatching_components_ne
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) :
    (sixVertexFourByTwoCentralConfigurationMatching source).1 ≠
      (sixVertexFourByTwoCentralConfigurationMatching source).2 := by
  intro heq
  let target := sixVertexFourByTwoCentralIndexMatching
    (sixVertexFourByTwoCentralSourceEquiv.symm source)
  apply target.2
  apply sixVertexFourByTwoSectorTwoEquiv.injective
  simpa [sixVertexFourByTwoCentralConfigurationMatching,
    sixVertexFourByTwoCentralTargetEquiv, target] using heq

theorem sixVertexFourByTwoCentralConfigurationMatching_totalC
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralConfigurationMatching source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  let index := sixVertexFourByTwoCentralSourceEquiv.symm source
  have hsource := sixVertexFourByTwoCentralSourceEquiv.apply_symm_apply source
  calc
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralConfigurationMatching source) =
        4 * (sixVertexFourByTwoCentralTargetGrade
          (sixVertexFourByTwoCentralIndexMatching index)).val := by
            unfold sixVertexFourByTwoCentralConfigurationMatching
            rw [sixVertexFourByTwoCentralTargetIndex_totalC]
    _ = 4 * (sixVertexFourByTwoCentralSourceGrade index).val := by
      rw [sixVertexFourByTwoCentralIndexMatching_grade]
    _ = sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralSourceEquiv index) :=
      (sixVertexFourByTwoCentralSourceIndex_totalC index).symm
    _ = sixVertexConfigurationPairTotalCPhysical source := by rw [hsource]

def sixVertexFourByTwoCentralConfigurationMatchingEmbedding :
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) where
  toFun := sixVertexFourByTwoCentralConfigurationMatching
  inj' := sixVertexFourByTwoCentralConfigurationMatching_injective

def sixVertexFourByTwoCentralPhysicalBranch (choice : Bool) :=
  if choice then
    sixVertexFourByTwoCentralConfigurationMatchingEmbedding.trans
      (Equiv.prodComm _ _).toEmbedding
  else sixVertexFourByTwoCentralConfigurationMatchingEmbedding

theorem sixVertexFourByTwoCentralPhysicalBranch_distinct source :
    sixVertexFourByTwoCentralPhysicalBranch false source ≠
      sixVertexFourByTwoCentralPhysicalBranch true source := by
  intro heq
  have hcomponents := congrArg Prod.fst heq
  exact sixVertexFourByTwoCentralConfigurationMatching_components_ne source
    (by simpa [sixVertexFourByTwoCentralPhysicalBranch] using hcomponents)

theorem sixVertexFourByTwoCentralPhysicalBranch_totalC
    (choice : Bool) (source) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralPhysicalBranch choice source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  cases choice <;>
    simpa [sixVertexFourByTwoCentralPhysicalBranch,
      sixVertexConfigurationPairTotalCPhysical, Nat.add_comm] using
      sixVertexFourByTwoCentralConfigurationMatching_totalC source

theorem sixVertexFourByTwoSectorTwo_pos :
    0 < sixVertexFourByTwoSectorTwo.val := by
  norm_num [sixVertexFourByTwoSectorTwo]

theorem sixVertexFourByTwoSectorTwo_lt_width :
    sixVertexFourByTwoSectorTwo.val < sixVertexFourByTwoTorus.width := by
  norm_num [sixVertexFourByTwoSectorTwo, sixVertexFourByTwoTorus]

def sixVertexFourByTwoCentralPhysicalSourceEmbedding :
    SixVertexConfigurationPhysicalSource sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width ↪
    (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorThree) where
  toFun source :=
    (⟨source.1.1, source.1.2.1, by
        simpa [sixVertexFourByTwoSectorOne,
          sixVertexFourByTwoSectorTwo] using source.1.2.2⟩,
      ⟨source.2.1, source.2.2.1, by
        simpa [sixVertexFourByTwoSectorThree,
          sixVertexFourByTwoSectorTwo] using source.2.2.2⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun pair => pair.1.1) heq
    · apply Subtype.ext
      exact congrArg (fun pair => pair.2.1) heq

@[simp] theorem sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC
    (source : SixVertexConfigurationPhysicalSource sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexFourByTwoCentralPhysicalSourceEmbedding source) =
      sixVertexConfigurationPairTotalCPhysical source := rfl



def sixVertexFourByTwoCentralPhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width where
  branch choice :=
    sixVertexFourByTwoCentralPhysicalSourceEmbedding.trans
      (sixVertexFourByTwoCentralPhysicalBranch choice)
  distinct source := by
    exact sixVertexFourByTwoCentralPhysicalBranch_distinct
      (sixVertexFourByTwoCentralPhysicalSourceEmbedding source)
  aggregateTotalC source := by
    change
      2 * sixVertexConfigurationPairTotalCPhysical source ≤
        sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoCentralPhysicalBranch false
              (sixVertexFourByTwoCentralPhysicalSourceEmbedding source)) +
          sixVertexConfigurationPairTotalCPhysical
            (sixVertexFourByTwoCentralPhysicalBranch true
              (sixVertexFourByTwoCentralPhysicalSourceEmbedding source))
    rw [sixVertexFourByTwoCentralPhysicalBranch_totalC,
      sixVertexFourByTwoCentralPhysicalBranch_totalC]
    simp only [sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC]
    omega

theorem sixVertexFourByTwoCentral_sectorTrace_logConcave_of_physicalBranches
    {c : Real} (hc : 1 ≤ c) :
    Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) *
        Matrix.trace (sixVertexSectorTransfer 4 3 c ^ 2) ≤
      Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) ^ 2 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorTwo] using
    sixVertexSectorTrace_logConcave_of_physicalPairedBranches
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorTwo_pos
      sixVertexFourByTwoSectorTwo_lt_width hc
      sixVertexFourByTwoCentralPhysicalPairedBranchEmbeddings

end

end StatMech.FrontierD

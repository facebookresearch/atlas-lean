/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.FiniteBidegreeCumulativeHall

namespace StatMech.FrontierD

noncomputable section

local instance cumulativePairedBranchDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev SixVertexConfigurationCumulativeSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :=
  SixVertexMarkedSectorConfiguration T
      ⟨middle.val - 1, by omega⟩ ×
    SixVertexMarkedSectorConfiguration T
      ⟨middle.val + 1, by omega⟩

abbrev SixVertexConfigurationCumulativeTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle

def sixVertexConfigurationCumulativeTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat :=
  sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1



abbrev SixVertexConfigurationCumulativePairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :=
  TwoBranchMonotoneEmbeddings
    (SixVertexConfigurationCumulativeSource T middle hmiddle_pos hmiddle_lt)
    (SixVertexConfigurationCumulativeTarget T middle)
    sixVertexConfigurationCumulativeTotalC
    sixVertexConfigurationCumulativeTotalC

theorem SixVertexConfigurationCumulativePairedBranchEmbeddings.upperCumulative
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (embeddings : SixVertexConfigurationCumulativePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    ∀ totalC,
      (Finset.univ.filter fun pair :
          SixVertexConfigurationCumulativeSource T middle hmiddle_pos
            hmiddle_lt =>
        totalC ≤ sixVertexConfigurationCumulativeTotalC pair).card ≤
      (Finset.univ.filter fun pair :
          SixVertexConfigurationCumulativeTarget T middle =>
        totalC ≤ sixVertexConfigurationCumulativeTotalC pair).card :=
  TwoBranchMonotoneEmbeddings.upperCumulative embeddings



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_cumulativePairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (embeddings : SixVertexConfigurationCumulativePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCCumulative
    T middle hmiddle_pos hmiddle_lt
  intro totalC
  simpa [sixVertexConfigurationCumulativeTotalC] using
    embeddings.upperCumulative totalC

end

end StatMech.FrontierD

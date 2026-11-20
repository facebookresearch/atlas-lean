/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch










open Finset

namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowsComplement {T : EvenTorus}
    (omega : SixVertexArrows T) : SixVertexArrows T where
  horizontal v := !omega.horizontal v
  vertical v := !omega.vertical v

@[simp] theorem sixVertexArrowsComplement_horizontal
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexArrowsComplement omega).horizontal v = !omega.horizontal v := rfl

@[simp] theorem sixVertexArrowsComplement_vertical
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexArrowsComplement omega).vertical v = !omega.vertical v := rfl

@[simp] theorem sixVertexArrowsComplement_complement
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexArrowsComplement (sixVertexArrowsComplement omega) = omega := by
  ext v <;> simp [sixVertexArrowsComplement]

theorem sixVertexArrowsComplement_injective {T : EvenTorus} :
    Function.Injective (@sixVertexArrowsComplement T) := by
  intro first second heq
  have h := congrArg sixVertexArrowsComplement heq
  simpa using h

theorem sixVertexArrowsComplement_iceRule
    {T : EvenTorus} {omega : SixVertexArrows T}
    (homega : omega.IceRule) :
    (sixVertexArrowsComplement omega).IceRule := by
  intro v
  have h := homega v
  unfold SixVertexArrows.incomingCount at h ⊢
  simp only [sixVertexArrowsComplement_horizontal,
    sixVertexArrowsComplement_vertical, Bool.not_not]
  generalize omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = west at h ⊢
  generalize omega.horizontal v = east at h ⊢
  generalize omega.vertical
      (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = south at h ⊢
  generalize omega.vertical v = north at h ⊢
  cases west <;> cases east <;> cases south <;> cases north <;> simp_all

theorem sixVertexArrowsComplement_isCType_iff
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexArrowsComplement omega).IsCType v ↔ omega.IsCType v := by
  unfold SixVertexArrows.IsCType
  simp only [sixVertexArrowsComplement_horizontal, Bool.not_not]
  generalize omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = west
  generalize omega.horizontal v = east
  cases west <;> cases east <;> decide +revert

@[simp] theorem sixVertexArrowsComplement_cTypeCount
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexTorusCTypeCount (sixVertexArrowsComplement omega) =
      sixVertexTorusCTypeCount omega := by
  classical
  unfold sixVertexTorusCTypeCount
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : omega.IsCType v
  · simp [h, (sixVertexArrowsComplement_isCType_iff omega v).2 h]
  · have hc : ¬ (sixVertexArrowsComplement omega).IsCType v :=
      fun hc => h ((sixVertexArrowsComplement_isCType_iff omega v).1 hc)
    simp [h, hc]

theorem sixVertexUpCount_complement {N : Nat} (row : SixVertexRow N) :
    sixVertexUpCount (fun i => !row i) = N - sixVertexUpCount row := by
  unfold sixVertexUpCount
  have hset : ({i | !row i} : Finset (Fin N)) =
      ({i | row i} : Finset (Fin N))ᶜ := by
    ext i
    cases row i <;> simp
  rw [hset, Finset.card_compl]
  simp

def sixVertexPhysicalParticleHoleMiddle
    {T : EvenTorus} (middle : Fin (T.width + 1)) : Fin (T.width + 1) :=
  ⟨T.width - middle.val, by omega⟩

theorem sixVertexPhysicalParticleHoleMiddle_pos
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_lt : middle.val < T.width) :
    0 < (sixVertexPhysicalParticleHoleMiddle middle).val := by
  simp [sixVertexPhysicalParticleHoleMiddle]
  omega

theorem sixVertexPhysicalParticleHoleMiddle_lt
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) :
    (sixVertexPhysicalParticleHoleMiddle middle).val < T.width := by
  have hwidth := T.width_pos
  have hmiddle_le : middle.val ≤ T.width := by omega
  have hcancel : T.width - middle.val + middle.val = T.width :=
    Nat.sub_add_cancel hmiddle_le
  simp only [sixVertexPhysicalParticleHoleMiddle]
  omega

def sixVertexPhysicalParticleHoleSourceEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width} :
    SixVertexConfigurationPhysicalSource T
        (sixVertexPhysicalParticleHoleMiddle middle)
        (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt)
        (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos) ↪
      SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt where
  toFun source :=
    (⟨sixVertexArrowsComplement source.2.1,
      sixVertexArrowsComplement_iceRule source.2.2.1, by
        change sixVertexUpCount (fun i =>
          !source.2.1.vertical (i, svFinLast T.height_pos)) = middle.val - 1
        rw [sixVertexUpCount_complement]
        have hsector := source.2.2.2
        change sixVertexUpCount (fun i =>
          source.2.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
        rw [hsector]
        simp [sixVertexPhysicalParticleHoleMiddle]
        omega⟩,
      ⟨sixVertexArrowsComplement source.1.1,
        sixVertexArrowsComplement_iceRule source.1.2.1, by
          change sixVertexUpCount (fun i =>
            !source.1.1.vertical (i, svFinLast T.height_pos)) = middle.val + 1
          rw [sixVertexUpCount_complement]
          have hsector := source.1.2.2
          change sixVertexUpCount (fun i =>
            source.1.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
          rw [hsector]
          simp [sixVertexPhysicalParticleHoleMiddle]
          omega⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.2.1) heq
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.1.1) heq

def sixVertexPhysicalParticleHoleTargetEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexConfigurationPhysicalTarget T middle ↪
      SixVertexConfigurationPhysicalTarget T
        (sixVertexPhysicalParticleHoleMiddle middle) where
  toFun target :=
    (⟨sixVertexArrowsComplement target.1.1,
      sixVertexArrowsComplement_iceRule target.1.2.1, by
        change sixVertexUpCount (fun i =>
          !target.1.1.vertical (i, svFinLast T.height_pos)) =
            T.width - middle.val
        rw [sixVertexUpCount_complement]
        have hsector := target.1.2.2
        change sixVertexUpCount (fun i =>
          target.1.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
        rw [hsector]⟩,
      ⟨sixVertexArrowsComplement target.2.1,
        sixVertexArrowsComplement_iceRule target.2.2.1, by
          change sixVertexUpCount (fun i =>
            !target.2.1.vertical (i, svFinLast T.height_pos)) =
              T.width - middle.val
          rw [sixVertexUpCount_complement]
          have hsector := target.2.2.2
          change sixVertexUpCount (fun i =>
            target.2.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
          rw [hsector]⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.1.1) heq
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.2.1) heq

@[simp] theorem sixVertexPhysicalParticleHoleSourceEmbedding_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T
      (sixVertexPhysicalParticleHoleMiddle middle)
      (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt)
      (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos)) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexPhysicalParticleHoleSourceEmbedding
          (middle := middle) (hmiddle_pos := hmiddle_pos)
          (hmiddle_lt := hmiddle_lt) source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  simp [sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalParticleHoleSourceEmbedding, Nat.add_comm]

@[simp] theorem sixVertexPhysicalParticleHoleTargetEmbedding_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexPhysicalParticleHoleTargetEmbedding target) =
      sixVertexConfigurationPairTotalCPhysical target := by
  simp [sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalParticleHoleTargetEmbedding]



def SixVertexConfigurationPhysicalPairedBranchEmbeddings.particleHole
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T
      (sixVertexPhysicalParticleHoleMiddle middle)
      (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt)
      (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos) where
  branch choice :=
    (sixVertexPhysicalParticleHoleSourceEmbedding
      (middle := middle)).trans
      ((embeddings.branch choice).trans
        (sixVertexPhysicalParticleHoleTargetEmbedding
          (middle := middle)))
  distinct source := by
    intro heq
    apply embeddings.distinct
      (sixVertexPhysicalParticleHoleSourceEmbedding source)
    apply sixVertexPhysicalParticleHoleTargetEmbedding.injective
    exact heq
  aggregateTotalC source := by
    change
      2 * sixVertexConfigurationPairTotalCPhysical source <=
        sixVertexConfigurationPairTotalCPhysical
            (sixVertexPhysicalParticleHoleTargetEmbedding
              (embeddings.branch false
                (sixVertexPhysicalParticleHoleSourceEmbedding source))) +
          sixVertexConfigurationPairTotalCPhysical
            (sixVertexPhysicalParticleHoleTargetEmbedding
              (embeddings.branch true
                (sixVertexPhysicalParticleHoleSourceEmbedding source)))
    simp only [sixVertexPhysicalParticleHoleTargetEmbedding_totalC]
    rw [← sixVertexPhysicalParticleHoleSourceEmbedding_totalC source]
    exact embeddings.aggregateTotalC
      (sixVertexPhysicalParticleHoleSourceEmbedding source)

end

end StatMech.FrontierD

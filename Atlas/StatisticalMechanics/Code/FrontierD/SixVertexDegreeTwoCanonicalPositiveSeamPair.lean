/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexCanonicalPositivePairSameCycleDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    DecidableRel
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle :=
  Classical.decRel _


def sixVertexDegreeTwoStrandCycleZeroIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)) :=
  ⟨0, orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
    homega heta hdegree seed)⟩


theorem sixVertexDegreeTwoStrandCycleEnumeration_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
      (sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed) = seed := by
  rfl

set_option maxHeartbeats 1000000 in


noncomputable def sixVertexDegreeTwoStrandCyclePosition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)) :=
  (sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed).symm
      ⟨dart, by
        rw [Equiv.Perm.mem_support]
        unfold sixVertexDegreeTwoStrandCyclePerm
        rw [Equiv.Perm.cycleOf_apply, if_pos hsame]
        exact sixVertexOrientedDegreeTwoStrandSuccessor_ne
          homega heta hdegree dart⟩

@[simp] theorem sixVertexDegreeTwoStrandCycleEnumeration_position
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart) :
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
        (sixVertexDegreeTwoStrandCyclePosition
          homega heta hdegree seed dart hsame) = dart := by
  exact congrArg Subtype.val
    ((sixVertexDegreeTwoStrandCycleEnumerationEquiv
      homega heta hdegree seed).apply_symm_apply _)

theorem sixVertexDegreeTwoStrandCyclePosition_ne_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart)
    (hne : seed ≠ dart) :
    sixVertexDegreeTwoStrandCyclePosition
      homega heta hdegree seed dart hsame ≠
        sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed := by
  intro hzero
  apply hne
  rw [← sixVertexDegreeTwoStrandCycleEnumeration_position
    homega heta hdegree seed dart hsame, hzero,
    sixVertexDegreeTwoStrandCycleEnumeration_zero]



noncomputable def sixVertexDegreeTwoStrandPositiveNonzeroIndices
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Finset (Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) := by
  classical
  exact Finset.univ.filter fun i =>
    i ≠ sixVertexDegreeTwoStrandCycleZeroIndex
      homega heta hdegree seed ∧
      sixVertexDegreeTwoStrandStepSeamSign hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) = 1

theorem sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart)
    (hne : seed ≠ dart)
    (hpositive : sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1) :
    (sixVertexDegreeTwoStrandPositiveNonzeroIndices
      homega heta hdegree seed).Nonempty := by
  classical
  refine ⟨sixVertexDegreeTwoStrandCyclePosition
    homega heta hdegree seed dart hsame, ?_⟩
  simp only [sixVertexDegreeTwoStrandPositiveNonzeroIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨sixVertexDegreeTwoStrandCyclePosition_ne_zero
      homega heta hdegree seed dart hsame hne,
    by simpa using hpositive⟩


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed.first)) :=
  (sixVertexDegreeTwoStrandPositiveNonzeroIndices
    homega heta hdegree seed.first).min'
      (sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty
        homega heta hdegree seed.first seed.second hsame seed.distinct
        seed.second_seamSign)

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.nextPositiveIndex hsame ∈
      sixVertexDegreeTwoStrandPositiveNonzeroIndices
        homega heta hdegree seed.first :=
  Finset.min'_mem _ _

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_ne_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.nextPositiveIndex hsame ≠
      sixVertexDegreeTwoStrandCycleZeroIndex
        homega heta hdegree seed.first := by
  classical
  exact (Finset.mem_filter.mp (seed.nextPositiveIndex_mem hsame)).2.1

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveIndex_minimal
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed.first)))
    (hi : i ≠ sixVertexDegreeTwoStrandCycleZeroIndex
      homega heta hdegree seed.first)
    (hpositive : sixVertexDegreeTwoStrandStepSeamSign hdegree
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree seed.first i) = 1) :
    seed.nextPositiveIndex hsame ≤ i := by
  classical
  apply Finset.min'_le
  simp [sixVertexDegreeTwoStrandPositiveNonzeroIndices, hi, hpositive]


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    SixVertexOrientedDisagreementDart omega eta :=
  sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
    (seed.nextPositiveIndex hsame)

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveDart_seamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree
      (seed.nextPositiveDart hsame) = 1 := by
  classical
  exact (Finset.mem_filter.mp (seed.nextPositiveIndex_mem hsame)).2.2

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.first_ne_nextPositiveDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.first ≠ seed.nextPositiveDart hsame := by
  intro heq
  apply seed.nextPositiveIndex_ne_zero hsame
  apply sixVertexDegreeTwoStrandCycleEnumeration_injective
    homega heta hdegree seed.first
  rw [sixVertexDegreeTwoStrandCycleEnumeration_zero]
  exact heq.symm

end

end StatMech.FrontierD

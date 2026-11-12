/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents










namespace StatMech.FrontierD

noncomputable section

local instance synchronizedUnitSelectorPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


noncomputable def sixVertexDegreeTwoSynchronizedComponentSelector
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) : Bool :=
  decide
    ((sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
      dart = component)

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentSelector_eq_true_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
        component dart = true ↔
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        dart = component := by
  simp [sixVertexDegreeTwoSynchronizedComponentSelector]



theorem sixVertexDegreeTwoSynchronizedComponentSelector_predecessors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false dart) =
      sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true dart) := by
  unfold sixVertexDegreeTwoSynchronizedComponentSelector
  rw [decide_eq_decide]
  exact sixVertexDegreeTwoSynchronizedComponent_predecessors_iff
    homega heta hdegree component dart


noncomputable def sixVertexDegreeTwoSynchronizedComponentDoubledSelector
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (state : DoubledAlignedState omega eta) : Bool :=
  sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
    component state.1

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (state : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (doubledAlignedBranchSwap state) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component state := rfl



noncomputable def sixVertexDegreeTwoSynchronizedComponentTransitionBit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (state : DoubledAlignedState omega eta) : Bool :=
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
      component state !=
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
      component ((doubledAlignedFirstReturnPerm homega heta hdegree).symm state)



theorem sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (dart, false) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (dart, true) := by
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionBit
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
  change
    (sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component dart !=
        sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component
            (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false dart)) =
      (sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component dart !=
        sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component
            (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true dart))
  rw [sixVertexDegreeTwoSynchronizedComponentSelector_predecessors]



theorem sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component =
      ∑ dart : SixVertexOrientedDisagreementDart omega eta,
        if sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
            component dart then
          sixVertexDegreeTwoStrandStepSeamSign hdegree dart
        else 0 := by
  unfold sixVertexDegreeTwoSynchronizedComponentCharge
    sixVertexDegreeTwoSynchronizedComponentSelector
  simp only [decide_eq_true_eq]



theorem sixVertexDegreeTwoSynchronizedComponentSelector_seamSum_eq_one
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
      component = 1) :
    (∑ dart : SixVertexOrientedDisagreementDart omega eta,
      if sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component dart then
        sixVertexDegreeTwoStrandStepSeamSign hdegree dart
      else 0) = 1 := by
  rw [← sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum]
  exact hcharge

end

end StatMech.FrontierD

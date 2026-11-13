/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairTwoCycleRelation











namespace StatMech.FrontierD

noncomputable section


structure SixVertexSignedWindingCycleTarget
    {T : EvenTorus} (source : SixVertexArrows T × SixVertexArrows T)
    (family : SixVertexAtMostTwoCycleFamily T) (sign : Bool) where
  target : SixVertexArrows T × SixVertexArrows T
  horizontalDelta :
    sixVertexPairUnionHorizontalDelta source target =
      fun v => if sign then family.horizontalFlow v
        else -family.horizontalFlow v
  verticalDelta :
    sixVertexPairUnionVerticalDelta source target =
      fun v => if sign then family.verticalFlow v
        else -family.verticalFlow v

namespace SixVertexSignedWindingCycleTarget



def swapTarget
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    SixVertexSignedWindingCycleTarget source family sign where
  target := (branch.target.2, branch.target.1)
  horizontalDelta := by
    rw [← branch.horizontalDelta]
    funext v
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    simp only [Prod.fst, Prod.snd]
    omega
  verticalDelta := by
    rw [← branch.verticalDelta]
    funext v
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    simp only [Prod.fst, Prod.snd]
    omega

@[simp] theorem swapTarget_target
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    branch.swapTarget.target = (branch.target.2, branch.target.1) := rfl



theorem target_ne_swapTarget_iff
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    branch.target ≠ branch.swapTarget.target ↔
      branch.target.1 ≠ branch.target.2 := by
  constructor
  · intro hne heq
    apply hne
    apply Prod.ext <;> simpa [heq]
  · intro hne heq
    exact hne (congrArg Prod.fst heq)


theorem related
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    sixVertexPairAtMostTwoCycleRelated source branch.target :=
  ⟨family, sign, branch.horizontalDelta, branch.verticalDelta⟩



def recover
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    SixVertexSignedWindingCycleTarget branch.target family (!sign) where
  target := source
  horizontalDelta := by
    funext v
    have h := congrFun branch.horizontalDelta v
    unfold sixVertexPairUnionHorizontalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega
  verticalDelta := by
    funext v
    have h := congrFun branch.verticalDelta v
    unfold sixVertexPairUnionVerticalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega

@[simp] theorem recover_target
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    branch.recover.target = source := rfl



theorem target_ne_source_of_horizontalFlow_ne_zero
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign)
    (v : T.Vertex) (hflow : family.horizontalFlow v ≠ 0) :
    branch.target ≠ source := by
  intro heq
  have h := congrFun branch.horizontalDelta v
  rw [heq] at h
  unfold sixVertexPairUnionHorizontalDelta at h
  cases sign <;> simp at h <;> omega

theorem target_ne_source_of_verticalFlow_ne_zero
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign)
    (v : T.Vertex) (hflow : family.verticalFlow v ≠ 0) :
    branch.target ≠ source := by
  intro heq
  have h := congrFun branch.verticalDelta v
  rw [heq] at h
  unfold sixVertexPairUnionVerticalDelta at h
  cases sign <;> simp at h <;> omega



theorem targets_ne_of_signedHorizontalFlow_ne
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {firstFamily secondFamily : SixVertexAtMostTwoCycleFamily T}
    {firstSign secondSign : Bool}
    (first : SixVertexSignedWindingCycleTarget source firstFamily firstSign)
    (second : SixVertexSignedWindingCycleTarget source secondFamily secondSign)
    (v : T.Vertex)
    (hflow : (if firstSign then firstFamily.horizontalFlow v
        else -firstFamily.horizontalFlow v) ≠
      if secondSign then secondFamily.horizontalFlow v
        else -secondFamily.horizontalFlow v) :
    first.target ≠ second.target := by
  intro heq
  have hfirst := congrFun first.horizontalDelta v
  have hsecond := congrFun second.horizontalDelta v
  rw [heq] at hfirst
  exact hflow (hfirst.symm.trans hsecond)


theorem targets_ne_of_signedVerticalFlow_ne
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {firstFamily secondFamily : SixVertexAtMostTwoCycleFamily T}
    {firstSign secondSign : Bool}
    (first : SixVertexSignedWindingCycleTarget source firstFamily firstSign)
    (second : SixVertexSignedWindingCycleTarget source secondFamily secondSign)
    (v : T.Vertex)
    (hflow : (if firstSign then firstFamily.verticalFlow v
        else -firstFamily.verticalFlow v) ≠
      if secondSign then secondFamily.verticalFlow v
        else -secondFamily.verticalFlow v) :
    first.target ≠ second.target := by
  intro heq
  have hfirst := congrFun first.verticalDelta v
  have hsecond := congrFun second.verticalDelta v
  rw [heq] at hfirst
  exact hflow (hfirst.symm.trans hsecond)



theorem opposite_targets_ne_of_horizontalFlow_ne_zero
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T}
    (negative : SixVertexSignedWindingCycleTarget source family false)
    (positive : SixVertexSignedWindingCycleTarget source family true)
    (v : T.Vertex) (hflow : family.horizontalFlow v ≠ 0) :
    negative.target ≠ positive.target := by
  intro heq
  have hnegative := congrFun negative.horizontalDelta v
  have hpositive := congrFun positive.horizontalDelta v
  unfold sixVertexPairUnionHorizontalDelta at hnegative hpositive
  simp only [Bool.false_eq_true, if_false] at hnegative
  simp only [if_true] at hpositive
  rw [heq] at hnegative
  omega



theorem opposite_targets_ne_of_verticalFlow_ne_zero
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T}
    (negative : SixVertexSignedWindingCycleTarget source family false)
    (positive : SixVertexSignedWindingCycleTarget source family true)
    (v : T.Vertex) (hflow : family.verticalFlow v ≠ 0) :
    negative.target ≠ positive.target := by
  intro heq
  have hnegative := congrFun negative.verticalDelta v
  have hpositive := congrFun positive.verticalDelta v
  unfold sixVertexPairUnionVerticalDelta at hnegative hpositive
  simp only [Bool.false_eq_true, if_false] at hnegative
  simp only [if_true] at hpositive
  rw [heq] at hnegative
  omega

end SixVertexSignedWindingCycleTarget

end

end StatMech.FrontierD

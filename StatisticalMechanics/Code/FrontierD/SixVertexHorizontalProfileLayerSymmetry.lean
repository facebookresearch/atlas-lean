/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileReflection









namespace StatMech.FrontierD

noncomputable section

def sixVertexReflectFirstHorizontalLayer
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (sixVertexReflectHorizontalField horizontal.1, horizontal.2)

def sixVertexReflectSecondHorizontalLayer
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (horizontal.1, sixVertexReflectHorizontalField horizontal.2)

theorem sixVertexReflectFirstHorizontalLayer_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexReflectFirstHorizontalLayer (T := T)) := by
  intro horizontal
  apply Prod.ext
  · funext v
    apply congrArg horizontal.1
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl
  · rfl

theorem sixVertexReflectSecondHorizontalLayer_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexReflectSecondHorizontalLayer (T := T)) := by
  intro horizontal
  apply Prod.ext
  · rfl
  · funext v
    apply congrArg horizontal.2
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl

theorem sixVertexHorizontalPairBigrade_reflectFirst
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade
    sixVertexReflectFirstHorizontalLayer
  rw [sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalZeroCount_reflect]

theorem sixVertexHorizontalPairBigrade_reflectSecond
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade
    sixVertexReflectSecondHorizontalLayer
  rw [sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalZeroCount_reflect]

def sixVertexReflectFirstHorizontalPairCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalPairCompletionProfile T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (sixVertexReflectOptionalHorizontalCompletionProfile profile.1, profile.2)

def sixVertexReflectSecondHorizontalPairCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalPairCompletionProfile T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (profile.1, sixVertexReflectOptionalHorizontalCompletionProfile profile.2)

theorem sixVertexReflectFirstHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectFirstHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  apply Prod.ext
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.1
  · rfl

theorem sixVertexReflectSecondHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectSecondHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  apply Prod.ext
  · rfl
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.2

theorem sixVertexHorizontalPairCompletionProfile_reflectFirst
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexReflectFirstHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  apply Prod.ext
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.1
  · rfl

theorem sixVertexHorizontalPairCompletionProfile_reflectSecond
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexReflectSecondHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  apply Prod.ext
  · rfl
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.2

def sixVertexHorizontalPairProfileFiberReflectFirstEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile} ≃
      {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 =
        sixVertexReflectFirstHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexReflectFirstHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectFirst]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectFirst, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexReflectFirstHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectFirst]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectFirst, horizontal.2,
        sixVertexReflectFirstHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1.1

def sixVertexHorizontalPairProfileFiberReflectSecondEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile} ≃
      {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 =
        sixVertexReflectSecondHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexReflectSecondHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectSecond]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectSecond, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexReflectSecondHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectSecond]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectSecond, horizontal.2,
        sixVertexReflectSecondHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1.1

theorem sixVertexHorizontalPairProfileMultiplicity_reflectFirst
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexReflectFirstHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberReflectFirstEquiv T grade profile).symm

theorem sixVertexHorizontalPairProfileMultiplicity_reflectSecond
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexReflectSecondHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberReflectSecondEquiv T grade profile).symm

def sixVertexSwapHorizontalLayers
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (horizontal.2, horizontal.1)

def sixVertexSwapHorizontalPairCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalPairCompletionProfile T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (profile.2, profile.1)

theorem sixVertexSwapHorizontalLayers_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexSwapHorizontalLayers (T := T)) := by
  intro horizontal
  rfl

theorem sixVertexSwapHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexSwapHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  rfl

theorem sixVertexHorizontalPairBigrade_swapLayers
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade sixVertexSwapHorizontalLayers
  simp only [add_comm]

theorem sixVertexHorizontalPairCompletionProfile_swapLayers
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexSwapHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  rfl

def sixVertexHorizontalPairProfileFiberSwapLayersEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile} ≃
      {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 =
        sixVertexSwapHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexSwapHorizontalLayers horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_swapLayers]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_swapLayers, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexSwapHorizontalLayers horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_swapLayers]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_swapLayers, horizontal.2,
        sixVertexSwapHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexSwapHorizontalLayers_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexSwapHorizontalLayers_involutive horizontal.1.1

theorem sixVertexHorizontalPairProfileMultiplicity_swapLayers
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexSwapHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberSwapLayersEquiv T grade profile).symm



theorem sixVertexHorizontalChooseSum_reflectFirst
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T right horizontal.1.2) =
      ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T left) horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T right horizontal.1.2 := by
  let reflect :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} ≃
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} :=
    { toFun := fun horizontal =>
        ⟨sixVertexReflectFirstHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectFirst]
          exact horizontal.2⟩
      invFun := fun horizontal =>
        ⟨sixVertexReflectFirstHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectFirst]
          exact horizontal.2⟩
      left_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1
      right_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1 }
  apply Fintype.sum_equiv reflect
  intro horizontal
  change _ =
    sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T left)
        (sixVertexReflectHorizontalField horizontal.1.1) *
      sixVertexHorizontalSectorCompletionChooseCount
        T right horizontal.1.2
  rw [sixVertexHorizontalSectorCompletionChooseCount_reflect,
    sixVertexHorizontalComplementSector_involutive]



theorem sixVertexHorizontalChooseSum_reflectSecond
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T right horizontal.1.2) =
      ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T right)
            horizontal.1.2 := by
  let reflect :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} ≃
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} :=
    { toFun := fun horizontal =>
        ⟨sixVertexReflectSecondHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectSecond]
          exact horizontal.2⟩
      invFun := fun horizontal =>
        ⟨sixVertexReflectSecondHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectSecond]
          exact horizontal.2⟩
      left_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1
      right_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1 }
  apply Fintype.sum_equiv reflect
  intro horizontal
  change _ =
    sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
      sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T right)
        (sixVertexReflectHorizontalField horizontal.1.2)
  rw [sixVertexHorizontalSectorCompletionChooseCount_reflect,
    sixVertexHorizontalComplementSector_involutive]





theorem horizontalChooseBigradeFibers_iff_diagonal_of_complement
    (T : EvenTorus)
    (lower upper middle : Fin (T.width + 1))
    (hcomplement : sixVertexHorizontalComplementSector T lower = upper) :
    SixVertexHorizontalChooseBigradeFiberDominates
        T lower upper middle middle ↔
      forall grade,
        (∑ horizontal :
            {horizontal : SixVertexHorizontalField T ×
                SixVertexHorizontalField T //
              sixVertexHorizontalPairBigrade horizontal = grade},
          sixVertexHorizontalSectorCompletionChooseCount
              T upper horizontal.1.1 *
            sixVertexHorizontalSectorCompletionChooseCount
              T upper horizontal.1.2) <=
          ∑ horizontal :
            {horizontal : SixVertexHorizontalField T ×
                SixVertexHorizontalField T //
              sixVertexHorizontalPairBigrade horizontal = grade},
            sixVertexHorizontalSectorCompletionChooseCount
                T middle horizontal.1.1 *
              sixVertexHorizontalSectorCompletionChooseCount
                T middle horizontal.1.2 := by
  unfold SixVertexHorizontalChooseBigradeFiberDominates
  constructor
  · intro hdom grade
    have hreflect :=
      sixVertexHorizontalChooseSum_reflectFirst T lower upper grade
    rw [hcomplement] at hreflect
    rw [← hreflect]
    exact hdom grade
  · intro hdom grade
    have hreflect :=
      sixVertexHorizontalChooseSum_reflectFirst T lower upper grade
    rw [hcomplement] at hreflect
    rw [hreflect]
    exact hdom grade

end

end StatMech.FrontierD

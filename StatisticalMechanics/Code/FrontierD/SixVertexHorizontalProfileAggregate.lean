/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalTwoCutSwitch










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropHorizontalProfileAggregate (p : Prop) :
    Decidable p :=
  Classical.propDecidable p


structure SixVertexHorizontalCompletionProfile (T : EvenTorus) where
  forcedTrue : Fin (T.width + 1)
  free : Fin (T.width + 1)
deriving DecidableEq, Fintype



def sixVertexHorizontalCompletionProfile
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T) :
    Option (SixVertexHorizontalCompletionProfile T) :=
  if hcompletion : Nonempty (SixVertexVerticalCompletion T horizontal) then
    some
      { forcedTrue :=
          ⟨(sixVertexHorizontalForcedTrueColumns horizontal).card,
            Nat.lt_succ_of_le (by
              simpa using Finset.card_le_univ
                (sixVertexHorizontalForcedTrueColumns horizontal))⟩
        free :=
          ⟨(sixVertexHorizontalFreeColumns horizontal).card,
            Nat.lt_succ_of_le (by
              simpa using Finset.card_le_univ
                (sixVertexHorizontalFreeColumns horizontal))⟩ }
  else none

def sixVertexHorizontalProfileChooseCount
    {T : EvenTorus} (sector : Fin (T.width + 1)) :
    Option (SixVertexHorizontalCompletionProfile T) -> Nat
  | none => 0
  | some profile =>
      if profile.forcedTrue.val <= sector.val then
        Nat.choose profile.free.val
          (sector.val - profile.forcedTrue.val)
      else 0


theorem sixVertexHorizontalSectorCompletionChooseCount_eq_profile
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalSectorCompletionChooseCount T sector horizontal =
      sixVertexHorizontalProfileChooseCount sector
        (sixVertexHorizontalCompletionProfile T horizontal) := by
  rw [sixVertexHorizontalSectorCompletionChooseCount]
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · rw [if_pos hcompletion]
    simp only [sixVertexHorizontalCompletionProfile, dif_pos hcompletion,
      sixVertexHorizontalProfileChooseCount]
    rw [sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card]
  · rw [if_neg hcompletion]
    rw [sixVertexHorizontalCompletionProfile, dif_neg hcompletion]
    rfl

abbrev SixVertexHorizontalPairCompletionProfile (T : EvenTorus) :=
  Option (SixVertexHorizontalCompletionProfile T) ×
    Option (SixVertexHorizontalCompletionProfile T)

def sixVertexHorizontalPairCompletionProfile
    (T : EvenTorus)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (sixVertexHorizontalCompletionProfile T horizontal.1,
    sixVertexHorizontalCompletionProfile T horizontal.2)

def sixVertexHorizontalPairProfileChooseWeight
    {T : EvenTorus} (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  sixVertexHorizontalProfileChooseCount left profile.1 *
    sixVertexHorizontalProfileChooseCount right profile.2

theorem sixVertexHorizontalPairChooseWeight_eq_profile
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2 =
      sixVertexHorizontalPairProfileChooseWeight left right
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_profile,
    sixVertexHorizontalSectorCompletionChooseCount_eq_profile]
  rfl


def sixVertexHorizontalPairProfileMultiplicity
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  Fintype.card
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile}


theorem sixVertexHorizontalChooseSum_eq_profileAggregate
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2) =
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalPairProfileChooseWeight left right profile := by
  simp_rw [sixVertexHorizontalPairChooseWeight_eq_profile]
  rw [<- Finset.sum_fiberwise Finset.univ
    (fun horizontal :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} =>
      sixVertexHorizontalPairCompletionProfile T horizontal.1)
    (fun horizontal =>
      sixVertexHorizontalPairProfileChooseWeight left right
        (sixVertexHorizontalPairCompletionProfile T horizontal.1))]
  apply Finset.sum_congr rfl
  intro profile hprofile
  rw [sixVertexHorizontalPairProfileMultiplicity, Fintype.card_subtype]
  let fiber := (Finset.univ.filter fun horizontal :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} =>
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile)
  change (∑ horizontal ∈ fiber,
      sixVertexHorizontalPairProfileChooseWeight left right
        (sixVertexHorizontalPairCompletionProfile T horizontal.1)) =
    fiber.card * sixVertexHorizontalPairProfileChooseWeight left right profile
  calc
    _ = ∑ _horizontal ∈ fiber,
          sixVertexHorizontalPairProfileChooseWeight left right profile := by
      apply Finset.sum_congr rfl
      intro horizontal hhorizontal
      have hprofileEq :
          sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile :=
        (Finset.mem_filter.mp hhorizontal).2
      rw [hprofileEq]
    _ = _ := by simp


def SixVertexHorizontalProfileAggregateDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    (∑ profile : SixVertexHorizontalPairCompletionProfile T,
      sixVertexHorizontalPairProfileMultiplicity T grade profile *
        sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile) <=
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalPairProfileChooseWeight
            targetLeft targetRight profile



theorem horizontalChooseBigradeFibers_iff_profileAggregate
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalChooseBigradeFiberDominates T
        sourceLeft sourceRight targetLeft targetRight ↔
      SixVertexHorizontalProfileAggregateDominates T
        sourceLeft sourceRight targetLeft targetRight := by
  constructor <;> intro hdom grade
  · rw [<- sixVertexHorizontalChooseSum_eq_profileAggregate,
      <- sixVertexHorizontalChooseSum_eq_profileAggregate]
    exact hdom grade
  · rw [sixVertexHorizontalChooseSum_eq_profileAggregate,
      sixVertexHorizontalChooseSum_eq_profileAggregate]
    exact hdom grade

end

end StatMech.FrontierD

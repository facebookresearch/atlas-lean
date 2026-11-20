/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileHall









open Finset

namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalProfileSignedKernel
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Int :=
  (sixVertexHorizontalPairProfileChooseWeight
      targetLeft targetRight profile : Int) -
    sixVertexHorizontalPairProfileChooseWeight
      sourceLeft sourceRight profile


def SixVertexHorizontalProfileAggregateSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    0 <= ∑ profile : SixVertexHorizontalPairCompletionProfile T,
      (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
        sixVertexHorizontalProfileSignedKernel
          sourceLeft sourceRight targetLeft targetRight profile



theorem profileAggregate_iff_signedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateDominates T
        sourceLeft sourceRight targetLeft targetRight ↔
      SixVertexHorizontalProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight := by
  unfold SixVertexHorizontalProfileAggregateDominates
    SixVertexHorizontalProfileAggregateSignedNonnegative
  constructor <;> intro hdom grade
  · have hcast :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalPairProfileChooseWeight
              sourceLeft sourceRight profile : Int)) <=
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalPairProfileChooseWeight
              targetLeft targetRight profile : Int) := by
      exact_mod_cast hdom grade
    have hkernel :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            sixVertexHorizontalProfileSignedKernel
              sourceLeft sourceRight targetLeft targetRight profile) =
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalPairProfileChooseWeight
              targetLeft targetRight profile : Int)) -
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalPairProfileChooseWeight
              sourceLeft sourceRight profile : Int) := by
      simp only [sixVertexHorizontalProfileSignedKernel, mul_sub,
        Finset.sum_sub_distrib]
    rw [hkernel]
    omega
  · have hsigned := hdom grade
    have hkernel :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            sixVertexHorizontalProfileSignedKernel
              sourceLeft sourceRight targetLeft targetRight profile) =
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalPairProfileChooseWeight
              targetLeft targetRight profile : Int)) -
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalPairProfileChooseWeight
              sourceLeft sourceRight profile : Int) := by
      simp only [sixVertexHorizontalProfileSignedKernel, mul_sub,
        Finset.sum_sub_distrib]
    rw [hkernel] at hsigned
    exact_mod_cast (show
      (∑ profile : SixVertexHorizontalPairCompletionProfile T,
        (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
          (sixVertexHorizontalPairProfileChooseWeight
            sourceLeft sourceRight profile : Int)) <=
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
          (sixVertexHorizontalPairProfileChooseWeight
            targetLeft targetRight profile : Int) by omega)

end

end StatMech.FrontierD

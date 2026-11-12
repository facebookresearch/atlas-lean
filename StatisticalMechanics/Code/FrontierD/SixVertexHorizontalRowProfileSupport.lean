/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Foundations.EqualFiberHall
import Code.FrontierD.SixVertexHorizontalResidualCompletions
import Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry










open Finset

namespace StatMech.FrontierD

noncomputable section


def sixVertexHorizontalRowZeroCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) : Nat :=
  ∑ i : Fin T.width,
    if sixVertexHorizontalGaugeBit horizontal (i, j) = false then 1 else 0


def sixVertexHorizontalPairRowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Fin T.height -> Nat :=
  fun j => sixVertexHorizontalRowZeroCount horizontal.1 j +
    sixVertexHorizontalRowZeroCount horizontal.2 j

abbrev SixVertexHorizontalRowZeroProfile (T : EvenTorus) :=
  Fin T.height -> Nat

theorem sum_sixVertexHorizontalRowZeroCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalRowZeroCount horizontal j) =
      sixVertexHorizontalZeroCount horizontal := by
  rw [sixVertexHorizontalZeroCount_eq_sum]
  unfold sixVertexHorizontalRowZeroCount
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem sum_sixVertexHorizontalPairRowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalPairRowZeroProfile horizontal j) =
      sixVertexHorizontalZeroCount horizontal.1 +
        sixVertexHorizontalZeroCount horizontal.2 := by
  unfold sixVertexHorizontalPairRowZeroProfile
  rw [Finset.sum_add_distrib,
    sum_sixVertexHorizontalRowZeroCount,
    sum_sixVertexHorizontalRowZeroCount]

theorem sixVertexHorizontalRowZeroCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowZeroCount
        (sixVertexReflectHorizontalField horizontal) j =
      sixVertexHorizontalRowZeroCount horizontal j := by
  unfold sixVertexHorizontalRowZeroCount
  simp_rw [sixVertexHorizontalGaugeBit_reflect]
  exact (sixVertexCyclicNegEquiv T.width_pos).sum_comp
    (fun i : Fin T.width =>
      if sixVertexHorizontalGaugeBit horizontal (i, j) = false then 1 else 0)


theorem sixVertexSwitchHorizontalPair_rowZeroProfile
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexHorizontalRowZeroCount
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold sixVertexSwitchHorizontalPair sixVertexHorizontalGaugeBit
  cases hmask : mask i <;> simp [hmask, add_comm]

theorem sixVertexReflectFirstHorizontalLayer_rowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexReflectFirstHorizontalLayer
  rw [sixVertexHorizontalRowZeroCount_reflect]

theorem sixVertexReflectSecondHorizontalLayer_rowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexReflectSecondHorizontalLayer
  rw [sixVertexHorizontalRowZeroCount_reflect]

theorem sixVertexSwapHorizontalLayers_rowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  simp [sixVertexHorizontalPairRowZeroProfile,
    sixVertexSwapHorizontalLayers, add_comm]

def sixVertexHorizontalActualDeficitRowProfile
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (source : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalRowZeroProfile T :=
  sixVertexHorizontalPairRowZeroProfile
    (sixVertexHorizontalActualDeficitPair source)

def sixVertexHorizontalActualSurplusRowProfile
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (target : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalRowZeroProfile T :=
  sixVertexHorizontalPairRowZeroProfile
    (sixVertexHorizontalActualSurplusPair target)




def sixVertexHorizontalActualRowProfileSupport
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop :=
  fun _ source target =>
    sixVertexHorizontalActualDeficitRowProfile source =
      sixVertexHorizontalActualSurplusRowProfile target


def SixVertexHorizontalRowProfileResidualCapacity
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade (profile : SixVertexHorizontalRowZeroProfile T),
    Fintype.card
        {source : SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualDeficitRowProfile source = profile} <=
      Fintype.card
        {target : SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualSurplusRowProfile target = profile}



theorem actualDeficitTokenHall_rowProfile_iff_capacity
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalActualDeficitTokenHall T
        sourceLeft sourceRight targetLeft targetRight
        (sixVertexHorizontalActualRowProfileSupport T
          sourceLeft sourceRight targetLeft targetRight) ↔
      SixVertexHorizontalRowProfileResidualCapacity T
        sourceLeft sourceRight targetLeft targetRight := by
  classical
  unfold SixVertexHorizontalActualDeficitTokenHall
    sixVertexHorizontalActualRowProfileSupport
    SixVertexHorizontalRowProfileResidualCapacity
  constructor
  · intro hHall grade
    let f := fun source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualDeficitRowProfile source
    let g := fun target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualSurplusRowProfile target
    apply (Fintype.hall_equalFiber_iff_card_fibers f g).mp
    intro S
    simpa [f, g] using hHall grade S
  · intro hcapacity grade
    let f := fun source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualDeficitRowProfile source
    let g := fun target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight =>
      sixVertexHorizontalActualSurplusRowProfile target
    have hHall :=
      (Fintype.hall_equalFiber_iff_card_fibers f g).mpr (hcapacity grade)
    intro S
    simpa [f, g] using hHall S



theorem configurationBigradeFibers_of_rowProfileResidualHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hHall : SixVertexHorizontalActualDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight
      (sixVertexHorizontalActualRowProfileSupport T
        sourceLeft sourceRight targetLeft targetRight)) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight :=
  configurationBigradeFibers_of_actualDeficitTokenHall T
    sourceLeft sourceRight targetLeft targetRight _ hHall



theorem configurationBigradeFibers_of_rowProfileResidualCapacity
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hcapacity : SixVertexHorizontalRowProfileResidualCapacity T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  apply configurationBigradeFibers_of_rowProfileResidualHall T
  exact (actualDeficitTokenHall_rowProfile_iff_capacity T
    sourceLeft sourceRight targetLeft targetRight).mpr hcapacity

end

end StatMech.FrontierD

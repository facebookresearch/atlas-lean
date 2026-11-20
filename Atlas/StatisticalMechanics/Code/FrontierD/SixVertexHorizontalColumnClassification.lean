/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalCompletionBigrade










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropHorizontalColumnClassification (p : Prop) :
    Decidable p :=
  Classical.propDecidable p


def sixVertexHorizontalFreeColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  Finset.univ.filter fun i => forall j,
    horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) =
      horizontal (i, j)


def sixVertexVerticalConstantColumnCompletion
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width)
    (hfree : forall j,
      horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) =
        horizontal (i, j))
    (seam : Bool) :
    SixVertexVerticalColumnCompletion T horizontal i :=
  ⟨fun _ => seam, fun j => by
    rw [hfree j]
    cases horizontal (i, j) <;> cases seam <;> simp⟩

private theorem sixVertexHorizontal_eq_of_column_previous_ne
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    {i : Fin T.width}
    (first second : SixVertexVerticalColumnCompletion T horizontal i)
    (j : Fin T.height)
    (hne : first.1 (SixVertexArrows.cyclicPred T.height_pos j) ≠
      second.1 (SixVertexArrows.cyclicPred T.height_pos j)) :
    horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) =
        horizontal (i, j) ∧
      first.1 j ≠ second.1 j := by
  have hfirst := first.2 j
  have hsecond := second.2 j
  generalize hleft :
      horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) = left
      at hfirst hsecond
  generalize hright : horizontal (i, j) = right at hfirst hsecond
  generalize hfp :
      first.1 (SixVertexArrows.cyclicPred T.height_pos j) = fp
      at hfirst hne
  generalize hsp :
      second.1 (SixVertexArrows.cyclicPred T.height_pos j) = sp
      at hsecond hne
  generalize hfc : first.1 j = fc at hfirst
  generalize hsc : second.1 j = sc at hsecond
  cases left <;> cases right <;> cases fp <;> cases sp <;>
    cases fc <;> cases sc <;> simp_all



theorem sixVertexHorizontalColumnSeamAllowed_both_iff_free
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width) :
    (sixVertexHorizontalColumnSeamAllowed horizontal i false ∧
        sixVertexHorizontalColumnSeamAllowed horizontal i true) ↔
      forall j,
        horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) =
          horizontal (i, j) := by
  constructor
  · rintro ⟨⟨first⟩, ⟨second⟩⟩
    rcases T with
      ⟨width, height, widthPos, heightPos, widthEven, heightEven⟩
    obtain ⟨height, rfl⟩ := Nat.exists_eq_succ_of_ne_zero heightPos.ne'
    have hstep : forall j : Fin (height + 1),
        horizontal (SixVertexArrows.cyclicPred widthPos i, j) =
            horizontal (i, j) ∧
          first.1.1 j ≠ second.1.1 j := by
      intro j
      induction j using Fin.induction with
      | zero =>
          apply sixVertexHorizontal_eq_of_column_previous_ne
            first.1 second.1 0
          have hfirst := first.2
          have hsecond := second.2
          change first.1.1 (svFinLast heightPos) = false at hfirst
          change second.1.1 (svFinLast heightPos) = true at hsecond
          have hpred :
              SixVertexArrows.cyclicPred heightPos
                  (0 : Fin (height + 1)) =
                svFinLast heightPos := by
            apply Fin.ext
            simp [SixVertexArrows.cyclicPred, svFinLast]
          rw [hpred, hfirst, hsecond]
          decide
      | succ j ih =>
          apply sixVertexHorizontal_eq_of_column_previous_ne
            first.1 second.1 j.succ
          simpa [svCyclicPred_succ] using ih.2
    exact fun j => (hstep j).1
  · intro hfree
    constructor
    · exact
        ⟨⟨sixVertexVerticalConstantColumnCompletion i hfree false, rfl⟩⟩
    · exact
        ⟨⟨sixVertexVerticalConstantColumnCompletion i hfree true, rfl⟩⟩



theorem sixVertexHorizontalColumnSeamAllowed_false_iff_forward
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed horizontal i false ↔
      SixVertexForwardInterlaced
        (fun j => horizontal
          (SixVertexArrows.cyclicPred T.width_pos i, j))
        (fun j => horizontal (i, j)) := by
  let left : SixVertexRow T.height := fun j => horizontal
    (SixVertexArrows.cyclicPred T.width_pos i, j)
  let right : SixVertexRow T.height := fun j => horizontal (i, j)
  constructor
  · rintro ⟨⟨column, hseam⟩⟩
    have hice : svHorizontalIce T.height_pos left right column.1 := column.2
    rcases svHorizontalIce_cases T.height_pos hice with hforward | hbackward
    · exact (svForwardInterlaced_iff_prefix left right
        (svHorizontalIce_upCount_eq T.height_pos hice)).2 hforward.2.1
    · rw [hseam] at hbackward
      exact Bool.noConfusion hbackward.1
  · intro hforwardInterlaced
    have hcount : sixVertexUpCount left = sixVertexUpCount right :=
      hforwardInterlaced.1
    have hforward : svRowPrefixForward left right :=
      (svForwardInterlaced_iff_prefix left right hcount).1
        hforwardInterlaced
    let column : SixVertexVerticalColumnCompletion T horizontal i :=
      ⟨svForwardHorizontal left right,
        svForwardHorizontal_ice T.height_pos left right hcount hforward⟩
    refine ⟨⟨column, ?_⟩⟩
    exact svForwardHorizontal_last T.height_pos left right hcount



theorem sixVertexHorizontalColumnSeamAllowed_true_iff_backward
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed horizontal i true ↔
      SixVertexForwardInterlaced
        (fun j => horizontal (i, j))
        (fun j => horizontal
          (SixVertexArrows.cyclicPred T.width_pos i, j)) := by
  let left : SixVertexRow T.height := fun j => horizontal
    (SixVertexArrows.cyclicPred T.width_pos i, j)
  let right : SixVertexRow T.height := fun j => horizontal (i, j)
  constructor
  · rintro ⟨⟨column, hseam⟩⟩
    have hice : svHorizontalIce T.height_pos left right column.1 := column.2
    rcases svHorizontalIce_cases T.height_pos hice with hforward | hbackward
    · rw [hseam] at hforward
      exact Bool.noConfusion hforward.1
    · exact (svForwardInterlaced_iff_prefix right left
        (svHorizontalIce_upCount_eq T.height_pos hice).symm).2 hbackward.2.1
  · intro hbackwardInterlaced
    have hcount : sixVertexUpCount left = sixVertexUpCount right :=
      hbackwardInterlaced.1.symm
    have hbackward : svRowPrefixForward right left :=
      (svForwardInterlaced_iff_prefix right left hcount.symm).1
        hbackwardInterlaced
    let column : SixVertexVerticalColumnCompletion T horizontal i :=
      ⟨svBackwardHorizontal left right,
        svBackwardHorizontal_ice T.height_pos left right hcount hbackward⟩
    refine ⟨⟨column, ?_⟩⟩
    exact svBackwardHorizontal_last T.height_pos left right hcount



theorem sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalTrueAllowedColumns horizontal \
        sixVertexHorizontalForcedTrueColumns horizontal =
      sixVertexHorizontalFreeColumns horizontal := by
  ext i
  simp only [Finset.mem_sdiff, sixVertexHorizontalForcedTrueColumns,
    Finset.mem_filter, sixVertexHorizontalTrueAllowedColumns,
    Finset.mem_univ, true_and, sixVertexHorizontalFreeColumns]
  constructor
  · rintro ⟨htrue, hnotForced⟩
    apply (sixVertexHorizontalColumnSeamAllowed_both_iff_free i).mp
    refine ⟨?_, htrue⟩
    by_contra hfalse
    exact hnotForced ⟨htrue, hfalse⟩
  · intro hfree
    have hboth :=
      (sixVertexHorizontalColumnSeamAllowed_both_iff_free i).mpr hfree
    exact ⟨hboth.2, fun hforced => hforced.2 hboth.1⟩



theorem sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (sixVertexHorizontalTrueAllowedColumns horizontal).card -
        (sixVertexHorizontalForcedTrueColumns horizontal).card =
      (sixVertexHorizontalFreeColumns horizontal).card := by
  rw [<- sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns]
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr
      (sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal)]

end

end StatMech.FrontierD

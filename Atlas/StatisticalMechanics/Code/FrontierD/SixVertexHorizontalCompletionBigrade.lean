/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Code.FrontierD.SixVertexConfigurationPairBigrade










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropHorizontalCompletion (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev SixVertexHorizontalField (T : EvenTorus) := T.Vertex -> Bool


def sixVertexArrowsOfFields
    {T : EvenTorus} (horizontal vertical : T.Vertex -> Bool) :
    SixVertexArrows T where
  horizontal := horizontal
  vertical := vertical



abbrev SixVertexVerticalCompletion
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T) :=
  {vertical : T.Vertex -> Bool //
    (sixVertexArrowsOfFields horizontal vertical).IceRule}


abbrev SixVertexHorizontalSectorCompletion
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :=
  {completion : SixVertexVerticalCompletion T horizontal //
    sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexArrowsOfFields horizontal completion.1)
      (svFinLast T.height_pos)) = sector.val}



def sixVertexSectorConfigurationEquivHorizontalCompletion
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    SixVertexMarkedSectorConfiguration T sector ≃
      Sigma (SixVertexHorizontalSectorCompletion T sector) where
  toFun omega :=
    ⟨omega.1.horizontal,
      ⟨⟨omega.1.vertical, omega.2.1⟩, omega.2.2⟩⟩
  invFun completed :=
    ⟨sixVertexArrowsOfFields completed.1 completed.2.1.1,
      completed.2.1.2, completed.2.2⟩
  left_inv omega := by
    apply Subtype.ext
    apply SixVertexArrows.ext <;> rfl
  right_inv completed := by
    rcases completed with ⟨horizontal, ⟨⟨vertical, hice⟩, hsector⟩⟩
    rfl



def sixVertexHorizontalGaugeBit
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (v : T.Vertex) : Bool :=
  horizontal v ^^ fkMedialVertexParity v

def sixVertexHorizontalZeroCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) : Nat :=
  Fintype.card {v : T.Vertex //
    sixVertexHorizontalGaugeBit horizontal v = false}

def sixVertexHorizontalNontransitionCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) : Nat :=
  ∑ v, if sixVertexHorizontalGaugeBit horizontal
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
        sixVertexHorizontalGaugeBit horizontal v then 1 else 0



def sixVertexHorizontalPairBigrade
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Nat × Nat :=
  (sixVertexHorizontalNontransitionCount horizontal.1 +
      sixVertexHorizontalNontransitionCount horizontal.2,
    2 * (sixVertexHorizontalZeroCount horizontal.1 +
      sixVertexHorizontalZeroCount horizontal.2))

@[simp] theorem sixVertexCheckerHorizontalZeroCount_eq_horizontal
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexCheckerHorizontalZeroCount omega =
      sixVertexHorizontalZeroCount omega.horizontal := by
  rfl

@[simp] theorem sixVertexCheckerHorizontalNontransitionCount_eq_horizontal
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexCheckerHorizontalNontransitionCount omega =
      sixVertexHorizontalNontransitionCount omega.horizontal := by
  rfl


theorem sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) :
    sixVertexConfigurationPairBigrade pair =
      sixVertexHorizontalPairBigrade
        (pair.1.1.horizontal, pair.2.1.horizontal) := by
  unfold sixVertexConfigurationPairBigrade
    sixVertexConfigurationPairTotalC sixVertexHorizontalPairBigrade
  rw [sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount,
    sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount,
    sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_zeroCount]
  rfl




def sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    {pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right //
      sixVertexConfigurationPairBigrade pair = grade} ≃
      Sigma fun horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} =>
        SixVertexHorizontalSectorCompletion T left horizontal.1.1 ×
          SixVertexHorizontalSectorCompletion T right horizontal.1.2 where
  toFun pair :=
    ⟨⟨(pair.1.1.1.horizontal, pair.1.2.1.horizontal), by
        rw [← sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade
          pair.1]
        exact pair.2⟩,
      (⟨⟨pair.1.1.1.vertical, pair.1.1.2.1⟩, pair.1.1.2.2⟩,
        ⟨⟨pair.1.2.1.vertical, pair.1.2.2.1⟩, pair.1.2.2.2⟩)⟩
  invFun completed := by
    let first : SixVertexMarkedSectorConfiguration T left :=
      ⟨sixVertexArrowsOfFields completed.1.1.1 completed.2.1.1.1,
        completed.2.1.1.2, completed.2.1.2⟩
    let second : SixVertexMarkedSectorConfiguration T right :=
      ⟨sixVertexArrowsOfFields completed.1.1.2 completed.2.2.1.1,
        completed.2.2.1.2, completed.2.2.2⟩
    exact ⟨(first, second), by
      rw [sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade]
      exact completed.1.2⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      apply SixVertexArrows.ext <;> rfl
  right_inv completed := by
    rcases completed with
      ⟨⟨⟨firstHorizontal, secondHorizontal⟩, hgrade⟩,
        ⟨⟨⟨firstVertical, firstIce⟩, firstSector⟩,
          ⟨⟨secondVertical, secondIce⟩, secondSector⟩⟩⟩
    rfl


theorem card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    Fintype.card
        {pair : SixVertexMarkedSectorConfiguration T left ×
            SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairBigrade pair = grade} =
      ∑ horizontal :
          {horizontal : SixVertexHorizontalField T ×
              SixVertexHorizontalField T //
            sixVertexHorizontalPairBigrade horizontal = grade},
        Fintype.card
            (SixVertexHorizontalSectorCompletion T left horizontal.1.1) *
          Fintype.card
            (SixVertexHorizontalSectorCompletion T right horizontal.1.2) := by
  rw [Fintype.card_congr
    (sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T left right grade), Fintype.card_sigma]
  simp only [Fintype.card_prod]


def sixVertexVerticalCompletionSeamRow
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    SixVertexRow T.width :=
  fun i => completion.1 (i, svFinLast T.height_pos)

private theorem sixVertexVerticalCompletion_step_eq
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    {first second : T.Vertex -> Bool}
    (hfirst : (sixVertexArrowsOfFields horizontal first).IceRule)
    (hsecond : (sixVertexArrowsOfFields horizontal second).IceRule)
    (i : Fin T.width) (j : Fin T.height)
    (hprevious : first
        (i, SixVertexArrows.cyclicPred T.height_pos j) =
      second (i, SixVertexArrows.cyclicPred T.height_pos j)) :
    first (i, j) = second (i, j) := by
  have hfirstVertex := hfirst (i, j)
  have hsecondVertex := hsecond (i, j)
  unfold SixVertexArrows.incomingCount sixVertexArrowsOfFields at hfirstVertex hsecondVertex
  simp only at hfirstVertex hsecondVertex
  rw [hprevious] at hfirstVertex
  generalize hfv : first (i, j) = fv at hfirstVertex
  generalize hsv : second (i, j) = sv at hsecondVertex
  cases fv <;> cases sv <;> simp_all



theorem sixVertexVerticalCompletionSeamRow_injective
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T} :
    Function.Injective
      (sixVertexVerticalCompletionSeamRow
        (T := T) (horizontal := horizontal)) := by
  rcases T with ⟨width, height, widthPos, heightPos, widthEven, heightEven⟩
  obtain ⟨height, rfl⟩ := Nat.exists_eq_succ_of_ne_zero heightPos.ne'
  intro first second hseam
  apply Subtype.ext
  funext vertex
  rcases vertex with ⟨i, j⟩
  induction j using Fin.induction with
  | zero =>
      apply sixVertexVerticalCompletion_step_eq
        first.2 second.2 i 0
      have hrow := congrFun hseam i
      change first.1 (i, svFinLast heightPos) =
        second.1 (i, svFinLast heightPos) at hrow
      change first.1
          (i, SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1))) =
        second.1
          (i, SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1)))
      have hpred :
          SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1)) =
            svFinLast heightPos := by
        apply Fin.ext
        simp [SixVertexArrows.cyclicPred, svFinLast]
      rw [hpred]
      exact hrow
  | succ j ih =>
      apply sixVertexVerticalCompletion_step_eq
        first.2 second.2 i j.succ
      simpa [svCyclicPred_succ] using ih



abbrev SixVertexVerticalColumnCompletion
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) :=
  {column : Fin T.height -> Bool // forall j,
    (horizontal
          (SixVertexArrows.cyclicPred T.width_pos i, j)).toNat +
        (!horizontal (i, j)).toNat +
        (column (SixVertexArrows.cyclicPred T.height_pos j)).toNat +
        (!column j).toNat = 2}


def sixVertexVerticalCompletionToColumns
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    (i : Fin T.width) ->
      SixVertexVerticalColumnCompletion T horizontal i :=
  fun i =>
    ⟨fun j => completion.1 (i, j), fun j => by
      simpa [SixVertexArrows.incomingCount, sixVertexArrowsOfFields]
        using completion.2 (i, j)⟩


def sixVertexVerticalCompletionOfColumns
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (columns : (i : Fin T.width) ->
      SixVertexVerticalColumnCompletion T horizontal i) :
    SixVertexVerticalCompletion T horizontal :=
  ⟨fun v => (columns v.1).1 v.2, fun v => by
    simpa [SixVertexArrows.incomingCount, sixVertexArrowsOfFields]
      using (columns v.1).2 v.2⟩


def sixVertexVerticalCompletionEquivColumns
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T) :
    SixVertexVerticalCompletion T horizontal ≃
      ((i : Fin T.width) ->
        SixVertexVerticalColumnCompletion T horizontal i) where
  toFun := sixVertexVerticalCompletionToColumns
  invFun := sixVertexVerticalCompletionOfColumns
  left_inv completion := by
    apply Subtype.ext
    funext v
    rfl
  right_inv columns := by
    funext i
    apply Subtype.ext
    funext j
    rfl


abbrev SixVertexVerticalColumnCompletionAtSeam
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) (seam : Bool) :=
  {column : SixVertexVerticalColumnCompletion T horizontal i //
    column.1 (svFinLast T.height_pos) = seam}

private theorem sixVertexVerticalColumnCompletion_step_eq
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    {i : Fin T.width}
    (first second : SixVertexVerticalColumnCompletion T horizontal i)
    (j : Fin T.height)
    (hprevious : first.1
        (SixVertexArrows.cyclicPred T.height_pos j) =
      second.1 (SixVertexArrows.cyclicPred T.height_pos j)) :
    first.1 j = second.1 j := by
  have hfirst := first.2 j
  have hsecond := second.2 j
  rw [hprevious] at hfirst
  generalize hfv : first.1 j = fv at hfirst
  generalize hsv : second.1 j = sv at hsecond
  cases fv <;> cases sv <;> simp_all


theorem sixVertexVerticalColumnCompletionAtSeam_subsingleton
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (i : Fin T.width) (seam : Bool) :
    Subsingleton
      (SixVertexVerticalColumnCompletionAtSeam
        T horizontal i seam) := by
  constructor
  intro first second
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rcases T with
    ⟨width, height, widthPos, heightPos, widthEven, heightEven⟩
  obtain ⟨height, rfl⟩ := Nat.exists_eq_succ_of_ne_zero heightPos.ne'
  induction j using Fin.induction with
  | zero =>
      apply sixVertexVerticalColumnCompletion_step_eq first.1 second.1 0
      change first.1.1
          (SixVertexArrows.cyclicPred heightPos
            (0 : Fin (height + 1))) =
        second.1.1
          (SixVertexArrows.cyclicPred heightPos
            (0 : Fin (height + 1)))
      have hpred :
          SixVertexArrows.cyclicPred heightPos (0 : Fin (height + 1)) =
            svFinLast heightPos := by
        apply Fin.ext
        simp [SixVertexArrows.cyclicPred, svFinLast]
      rw [hpred, first.2, second.2]
  | succ j ih =>
      apply sixVertexVerticalColumnCompletion_step_eq
        first.1 second.1 j.succ
      simpa [svCyclicPred_succ] using ih


abbrev SixVertexColumnCompletionFamilyInSector
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :=
  {columns : (i : Fin T.width) ->
      SixVertexVerticalColumnCompletion T horizontal i //
    sixVertexUpCount
      (fun i => (columns i).1 (svFinLast T.height_pos)) = sector.val}


def sixVertexHorizontalSectorCompletionEquivColumns
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalSectorCompletion T sector horizontal ≃
      SixVertexColumnCompletionFamilyInSector
        T sector horizontal :=
  Equiv.subtypeEquiv
    (sixVertexVerticalCompletionEquivColumns T horizontal)
    fun completion => by
      rfl



def sixVertexColumnCompletionFamilyEquivSectorRow
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    SixVertexColumnCompletionFamilyInSector T sector horizontal ≃
      Sigma fun row : SixVertexSector T.width sector.val =>
        (i : Fin T.width) ->
          SixVertexVerticalColumnCompletionAtSeam T horizontal i
            (sixVertexSectorRow row i) where
  toFun columns := by
    let seamRow : SixVertexRow T.width :=
      fun i => (columns.1 i).1 (svFinLast T.height_pos)
    let row : SixVertexSector T.width sector.val :=
      svRowSectorAt seamRow columns.2
    refine ⟨row, fun i => ⟨columns.1 i, ?_⟩⟩
    change seamRow i = sixVertexSectorRow row i
    rw [svRowSectorAt_row]
  invFun data := by
    refine ⟨fun i => (data.2 i).1, ?_⟩
    have hrow :
        (fun i => ((data.2 i).1.1 (svFinLast T.height_pos))) =
          sixVertexSectorRow data.1 := by
      funext i
      exact (data.2 i).2
    rw [hrow, sixVertexSectorRow_upCount]
  left_inv columns := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv data := by
    let seamRow : SixVertexRow T.width :=
      fun i => ((data.2 i).1.1 (svFinLast T.height_pos))
    have hcount : sixVertexUpCount seamRow = sector.val := by
      have hrow : seamRow = sixVertexSectorRow data.1 := by
        funext i
        exact (data.2 i).2
      rw [hrow, sixVertexSectorRow_upCount]
    let row : SixVertexSector T.width sector.val :=
      svRowSectorAt seamRow hcount
    have hrow : row = data.1 := by
      apply sixVertexSectorRow_injective
      rw [svRowSectorAt_row]
      funext i
      exact (data.2 i).2
    change (⟨row, _⟩ : Sigma fun row :
        SixVertexSector T.width sector.val =>
      (i : Fin T.width) ->
        SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)) = data
    apply Sigma.ext hrow
    let fiber := fun row : SixVertexSector T.width sector.val =>
      (i : Fin T.width) ->
        SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)
    have htype : fiber row = fiber data.1 := congrArg fiber hrow
    let lhs : fiber row := fun i =>
      ⟨(data.2 i).1, by
        rw [hrow]
        exact (data.2 i).2⟩
    have hcast : cast htype lhs = data.2 := by
      letI (i : Fin T.width) : Subsingleton
          (SixVertexVerticalColumnCompletionAtSeam T horizontal i
            (sixVertexSectorRow data.1 i)) :=
        sixVertexVerticalColumnCompletionAtSeam_subsingleton i _
      exact Subsingleton.elim _ _
    exact (cast_heq htype lhs).symm.trans (heq_of_eq hcast)



theorem card_sixVertexHorizontalSectorCompletion_eq_sum_columnFibers
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    Fintype.card
        (SixVertexHorizontalSectorCompletion T sector horizontal) =
      ∑ row : SixVertexSector T.width sector.val,
        ∏ i : Fin T.width,
          Fintype.card
            (SixVertexVerticalColumnCompletionAtSeam T horizontal i
              (sixVertexSectorRow row i)) := by
  rw [Fintype.card_congr
      (sixVertexHorizontalSectorCompletionEquivColumns
        T sector horizontal),
    Fintype.card_congr
      (sixVertexColumnCompletionFamilyEquivSectorRow
        T sector horizontal),
    Fintype.card_sigma]
  simp only [Fintype.card_pi]



noncomputable def sigmaSubsingletonEquivSubtypeNonempty
    {A : Type*} (fiber : A -> Type*)
    [fiberSubsingleton : forall a, Subsingleton (fiber a)] :
    (Sigma fiber) ≃ {a : A // Nonempty (fiber a)} where
  toFun value := ⟨value.1, ⟨value.2⟩⟩
  invFun value := ⟨value.1, Classical.choice value.2⟩
  left_inv value := by
    rcases value with ⟨a, value⟩
    apply Sigma.ext
    · rfl
    · exact heq_of_eq
        (@Subsingleton.elim _ (fiberSubsingleton a) _ _)
  right_inv value := by
    apply Subtype.ext
    rfl


abbrev SixVertexHorizontalAdmissibleSeamRow
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :=
  {row : SixVertexSector T.width sector.val //
    Nonempty ((i : Fin T.width) ->
      SixVertexVerticalColumnCompletionAtSeam T horizontal i
        (sixVertexSectorRow row i))}



noncomputable def sixVertexHorizontalSectorCompletionEquivAdmissibleSeamRow
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalSectorCompletion T sector horizontal ≃
      SixVertexHorizontalAdmissibleSeamRow T sector horizontal := by
  letI (row : SixVertexSector T.width sector.val)
      (i : Fin T.width) :
      Subsingleton
        (SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)) :=
    sixVertexVerticalColumnCompletionAtSeam_subsingleton i _
  exact (sixVertexHorizontalSectorCompletionEquivColumns
      T sector horizontal).trans
    ((sixVertexColumnCompletionFamilyEquivSectorRow
      T sector horizontal).trans
      (sigmaSubsingletonEquivSubtypeNonempty fun row =>
        (i : Fin T.width) ->
          SixVertexVerticalColumnCompletionAtSeam T horizontal i
            (sixVertexSectorRow row i)))


def sixVertexHorizontalColumnSeamAllowed
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) (seam : Bool) : Prop :=
  Nonempty
    (SixVertexVerticalColumnCompletionAtSeam T horizontal i seam)


def sixVertexHorizontalTrueAllowedColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  Finset.univ.filter fun i =>
    sixVertexHorizontalColumnSeamAllowed horizontal i true


def sixVertexHorizontalForcedTrueColumns
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Finset (Fin T.width) :=
  (sixVertexHorizontalTrueAllowedColumns horizontal).filter fun i =>
    Not (sixVertexHorizontalColumnSeamAllowed horizontal i false)

theorem sixVertexHorizontalForcedTrueColumns_subset_trueAllowed
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalForcedTrueColumns horizontal ⊆
      sixVertexHorizontalTrueAllowedColumns horizontal :=
  Finset.filter_subset _ _



theorem sixVertexHorizontalColumnSeamAllowed_false_or_true
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed horizontal i false \/
      sixVertexHorizontalColumnSeamAllowed horizontal i true := by
  let column := sixVertexVerticalCompletionToColumns completion i
  cases hseam : column.1 (svFinLast T.height_pos)
  · left
    exact ⟨⟨column, hseam⟩⟩
  · right
    exact ⟨⟨column, hseam⟩⟩




theorem sixVertexHorizontalAdmissibleSeamRow_iff_subset
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (sector : Fin (T.width + 1))
    (row : SixVertexSector T.width sector.val) :
    Nonempty ((i : Fin T.width) ->
        SixVertexVerticalColumnCompletionAtSeam T horizontal i
          (sixVertexSectorRow row i)) <->
      sixVertexHorizontalForcedTrueColumns horizontal ⊆ row.1 /\
        row.1 ⊆ sixVertexHorizontalTrueAllowedColumns horizontal := by
  constructor
  · rintro ⟨columns⟩
    constructor
    · intro i hi
      have hiData := Finset.mem_filter.mp hi
      by_contra hiRow
      have hfalse : sixVertexSectorRow row i = false := by
        simp [sixVertexSectorRow, hiRow]
      have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i false := by
        rw [<- hfalse]
        exact ⟨columns i⟩
      exact hiData.2 hallowed
    · intro i hiRow
      have htrue : sixVertexSectorRow row i = true := by
        simp [sixVertexSectorRow, hiRow]
      have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i true := by
        rw [<- htrue]
        exact ⟨columns i⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hallowed⟩
  · rintro ⟨hforced, htrue⟩
    refine ⟨fun i => ?_⟩
    by_cases hiRow : i ∈ row.1
    · have hiTrue : i ∈ sixVertexHorizontalTrueAllowedColumns horizontal :=
        htrue hiRow
      have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i true :=
        (Finset.mem_filter.mp hiTrue).2
      have hbit : sixVertexSectorRow row i = true := by
        simp [sixVertexSectorRow, hiRow]
      rw [hbit]
      exact Classical.choice hallowed
    · have hallowed :
          sixVertexHorizontalColumnSeamAllowed horizontal i false := by
        rcases sixVertexHorizontalColumnSeamAllowed_false_or_true
            completion i with hfalse | htrueAllowed
        · exact hfalse
        · by_contra hfalse
          have hiTrue :
              i ∈ sixVertexHorizontalTrueAllowedColumns horizontal :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrueAllowed⟩
          have hiForced :
              i ∈ sixVertexHorizontalForcedTrueColumns horizontal :=
            Finset.mem_filter.mpr ⟨hiTrue, hfalse⟩
          exact hiRow (hforced hiForced)
      have hbit : sixVertexSectorRow row i = false := by
        simp [sixVertexSectorRow, hiRow]
      rw [hbit]
      exact Classical.choice hallowed


noncomputable def sixVertexHorizontalAdmissibleSeamRowEquivPowerset
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (sector : Fin (T.width + 1)) :
    SixVertexHorizontalAdmissibleSeamRow T sector horizontal ≃
      {row : Finset (Fin T.width) //
        row ∈ ((sixVertexHorizontalTrueAllowedColumns horizontal).powersetCard
            sector.val).filter
          (sixVertexHorizontalForcedTrueColumns horizontal ⊆ ·)} where
  toFun row := ⟨row.1.1, by
    have hsub :=
      (sixVertexHorizontalAdmissibleSeamRow_iff_subset
        completion sector row.1).mp row.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hsub.2, row.1.2⟩, hsub.1⟩⟩
  invFun row :=
    let sectorRow : SixVertexSector T.width sector.val :=
      ⟨row.1, (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp row.2).1).2⟩
    ⟨sectorRow,
      (sixVertexHorizontalAdmissibleSeamRow_iff_subset
        completion sector sectorRow).mpr
          ⟨(Finset.mem_filter.mp row.2).2,
            (Finset.mem_powersetCard.mp
              (Finset.mem_filter.mp row.2).1).1⟩⟩
  left_inv row := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv row := by
    apply Subtype.ext
    rfl


theorem card_sixVertexHorizontalSectorCompletion_eq_choose
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (sector : Fin (T.width + 1)) :
    Fintype.card
        (SixVertexHorizontalSectorCompletion T sector horizontal) =
      if (sixVertexHorizontalForcedTrueColumns horizontal).card <= sector.val
      then Nat.choose
        ((sixVertexHorizontalTrueAllowedColumns horizontal).card -
          (sixVertexHorizontalForcedTrueColumns horizontal).card)
        (sector.val -
          (sixVertexHorizontalForcedTrueColumns horizontal).card)
      else 0 := by
  rw [Fintype.card_congr
      (sixVertexHorizontalSectorCompletionEquivAdmissibleSeamRow
        T sector horizontal),
    Fintype.card_congr
      (sixVertexHorizontalAdmissibleSeamRowEquivPowerset
        completion sector),
    Fintype.card_coe]
  split_ifs with hforced
  · exact Finset.card_filter_powersetCard_subset
      (sixVertexHorizontalForcedTrueColumns horizontal)
      (sixVertexHorizontalTrueAllowedColumns horizontal)
      sector.val
      (sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal)
      hforced
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro row hrow
    have hsubset := (Finset.mem_filter.mp hrow).2
    have hcard := Finset.card_le_card hsubset
    have hrowCard := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hrow).1).2
    omega



noncomputable def sixVertexHorizontalSectorCompletionChooseCount
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) : Nat :=
  if Nonempty (SixVertexVerticalCompletion T horizontal) then
    if (sixVertexHorizontalForcedTrueColumns horizontal).card <= sector.val
    then Nat.choose
      ((sixVertexHorizontalTrueAllowedColumns horizontal).card -
        (sixVertexHorizontalForcedTrueColumns horizontal).card)
      (sector.val -
        (sixVertexHorizontalForcedTrueColumns horizontal).card)
    else 0
  else 0

theorem card_sixVertexHorizontalSectorCompletion_eq_chooseCount
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    Fintype.card
        (SixVertexHorizontalSectorCompletion T sector horizontal) =
      sixVertexHorizontalSectorCompletionChooseCount
        T sector horizontal := by
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · rw [sixVertexHorizontalSectorCompletionChooseCount,
      if_pos hcompletion]
    exact card_sixVertexHorizontalSectorCompletion_eq_choose
      (Classical.choice hcompletion) sector
  · rw [sixVertexHorizontalSectorCompletionChooseCount,
      if_neg hcompletion]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun sectorCompletion => hcompletion ⟨sectorCompletion.1⟩⟩

theorem sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T)
    (hnonempty : Nonempty
      (SixVertexHorizontalSectorCompletion T sector horizontal)) :
    0 < sixVertexHorizontalSectorCompletionChooseCount
      T sector horizontal := by
  rw [← card_sixVertexHorizontalSectorCompletion_eq_chooseCount,
    Fintype.card_pos_iff]
  exact hnonempty

theorem sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T)
    (hempty : IsEmpty
      (SixVertexHorizontalSectorCompletion T sector horizontal)) :
    sixVertexHorizontalSectorCompletionChooseCount T sector horizontal = 0 := by
  rw [← card_sixVertexHorizontalSectorCompletion_eq_chooseCount,
    Fintype.card_eq_zero_iff]
  exact hempty



theorem card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    Fintype.card
        {pair : SixVertexMarkedSectorConfiguration T left ×
            SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairBigrade pair = grade} =
      ∑ horizontal :
          {horizontal : SixVertexHorizontalField T ×
              SixVertexHorizontalField T //
            sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount
            T left horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T right horizontal.1.2 := by
  rw [card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions]
  apply Finset.sum_congr rfl
  intro horizontal hhorizontal
  rw [card_sixVertexHorizontalSectorCompletion_eq_chooseCount,
    card_sixVertexHorizontalSectorCompletion_eq_chooseCount]



def SixVertexHorizontalChooseBigradeFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount
          T sourceLeft horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T sourceRight horizontal.1.2) <=
    ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount
          T targetLeft horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T targetRight horizontal.1.2

theorem configurationBigradeFibers_iff_horizontalChooseBigradeFibers
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexConfigurationPairBigradeFiberDominates T
        sourceLeft sourceRight targetLeft targetRight <->
      SixVertexHorizontalChooseBigradeFiberDominates T
        sourceLeft sourceRight targetLeft targetRight := by
  constructor <;> intro hfiber grade
  · rw [<- card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums,
      <- card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums]
    exact hfiber grade
  · rw [card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums,
      card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums]
    exact hfiber grade

end

end StatMech.FrontierD

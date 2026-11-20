/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents
import Code.FrontierD.SixVertexActiveKeyComponentRouting













open Finset

namespace StatMech.FrontierD

noncomputable section

local instance degreeTwoHighChargeHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev SixVertexHorizontalDegreeTwoHallSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  SixVertexHorizontalActualDeficitTokens T grade
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle

abbrev SixVertexHorizontalDegreeTwoHallTarget
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  SixVertexHorizontalActualSurplusTokens T grade
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle





def sixVertexHorizontalDegreeTwoHighCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1,
    ∃ component :
        (sixVertexDegreeTwoSynchronizedGraph pair.1.1.2.1 pair.1.2.2.1
          hdegree).ConnectedComponent,
      2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge
        pair.1.1.2.1 pair.1.2.2.1 hdegree component

abbrev SixVertexHorizontalDegreeTwoHighChargeSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade //
    sixVertexHorizontalDegreeTwoHighCharge source}

abbrev SixVertexHorizontalNotDegreeTwoHighChargeSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade //
    ¬ sixVertexHorizontalDegreeTwoHighCharge source}



def sixVertexHorizontalDegreeTwoUnitCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1,
    ∃ component :
        (sixVertexDegreeTwoSynchronizedGraph pair.1.1.2.1 pair.1.2.2.1
          hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge
        pair.1.1.2.1 pair.1.2.2.1 hdegree component = 1




theorem sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1) :
    sixVertexHorizontalDegreeTwoUnitCharge source ∨
      sixVertexHorizontalDegreeTwoHighCharge source := by
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source
  rcases sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
      pair.1.1.2.1 pair.1.2.2.1 hdegree with hunit | hnoUnit
  · left
    exact ⟨hdegree, hunit⟩
  · right
    have homegaSector : sixVertexUpCount
        (svTorusVerticalRows T pair.1.1.1 (svFinLast T.height_pos)) =
        middle.val - 1 := by
      simpa [pair, sixVertexHorizontalLowerSector] using pair.1.1.2.2
    have hetaSector : sixVertexUpCount
        (svTorusVerticalRows T pair.1.2.1 (svFinLast T.height_pos)) =
        middle.val + 1 := by
      simpa [pair, sixVertexHorizontalUpperSector] using pair.1.2.2.2
    obtain ⟨component, hcharge⟩ :=
      exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
        pair.1.1.2.1 pair.1.2.2.1 hdegree middle.val homegaSector
          hetaSector hmiddle_pos hnoUnit
    exact ⟨hdegree, component, hcharge⟩



theorem sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1)
    (hnot : ¬ sixVertexHorizontalDegreeTwoHighCharge source) :
    sixVertexHorizontalDegreeTwoUnitCharge source := by
  rcases sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge source hdegree
    with hunit | hhigh
  · exact hunit
  · exact False.elim (hnot hhigh)


structure SixVertexHorizontalDegreeTwoHighChargeWitness
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) where
  hdegree : SixVertexLocallyDegreeTwo
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1
  component :
    (sixVertexDegreeTwoSynchronizedGraph
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.2.1
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.2.1
      hdegree).ConnectedComponent
  charge : 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.2.1
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.2.1
    hdegree component

noncomputable def sixVertexHorizontalDegreeTwoHighChargeWitness
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeWitness source := by
  apply Classical.choice
  rcases source.2 with ⟨hdegree, component, hcharge⟩
  exact ⟨⟨hdegree, component, hcharge⟩⟩

noncomputable def sixVertexHorizontalDegreeTwoHighChargeSeed
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :=
  let witness := sixVertexHorizontalDegreeTwoHighChargeWitness source
  sixVertexDegreeTwoSynchronizedHighChargeSeed
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.2.1
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.2.1
    witness.hdegree witness.component witness.charge




noncomputable def sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  (sixVertexHorizontalDegreeTwoHighChargeSeed source).occurrenceEquiv



theorem sixVertexHorizontalDegreeTwoHighCharge_seed
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    let pair := sixVertexHorizontalActualDeficitConfigurationPair source.1
    ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1,
      ∃ component :
          (sixVertexDegreeTwoSynchronizedGraph pair.1.1.2.1 pair.1.2.2.1
            hdegree).ConnectedComponent,
        Nonempty (SixVertexDegreeTwoSynchronizedHighChargeSeed
          pair.1.1.2.1 pair.1.2.2.1 hdegree component) := by
  dsimp only
  rcases source.2 with ⟨hdegree, component, hcharge⟩
  exact ⟨hdegree, component,
    sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty
      _ _ hdegree component hcharge⟩








structure SixVertexHorizontalDegreeTwoRecoverableReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade → Bool →
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  source_recoverable : ∀ first firstBranch second secondBranch,
    target first firstBranch = target second secondBranch → first = second
  direct_supported : ∀ source :
      SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (target source.1 false)
  paired_distinct : ∀ source :
      SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    target source.1 false ≠ target source.1 true
  paired_supported : ∀ source :
      SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade,
    ∀ branch,
      sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
        hmiddle_pos hmiddle_lt grade source.1 (target source.1 branch)





structure SixVertexHorizontalDegreeTwoHighChargeHallRouting
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  direct : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade →
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  direct_injective : Function.Injective direct
  direct_supported : ∀ source,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (direct source)
  paired : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade → Bool →
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade
  paired_distinct : ∀ source, paired source false ≠ paired source true
  paired_supported : ∀ source branch,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (paired source branch)
  paired_output_recovers_occurrence : ∀ branch first second,
    paired first branch = paired second branch →
      sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
        sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second
  paired_injective_with_occurrence : ∀ branch first second,
    sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv first =
        sixVertexHorizontalDegreeTwoHighChargeOccurrenceEquiv second →
      paired first branch = paired second branch → first = second
  direct_paired_disjoint : ∀ directSource pairedSource branch,
    direct directSource ≠ paired pairedSource branch





def SixVertexHorizontalDegreeTwoRecoverableReconnection.toHallRouting
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoRecoverableReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade where
  direct source := reconnection.target source.1 false
  direct_injective := by
    intro first second heq
    apply Subtype.ext
    exact reconnection.source_recoverable
      first.1 false second.1 false heq
  direct_supported := reconnection.direct_supported
  paired source branch := reconnection.target source.1 branch
  paired_distinct := reconnection.paired_distinct
  paired_supported := reconnection.paired_supported
  paired_output_recovers_occurrence := by
    intro branch first second heq
    have hsource : first.1 = second.1 :=
      reconnection.source_recoverable
        first.1 branch second.1 branch heq
    have hsubtype : first = second := Subtype.ext hsource
    rw [hsubtype]
  paired_injective_with_occurrence := by
    intro branch first second _ heq
    apply Subtype.ext
    exact reconnection.source_recoverable
      first.1 branch second.1 branch heq
  direct_paired_disjoint := by
    intro directSource pairedSource branch heq
    have hsource : directSource.1 = pairedSource.1 :=
      reconnection.source_recoverable
        directSource.1 false pairedSource.1 branch heq
    exact directSource.2 (hsource ▸ pairedSource.2)


def SixVertexHorizontalDegreeTwoHighChargeHallRouting.PairedRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) : Prop :=
  ∃ branch, routing.paired source branch = target

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_branch_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) (branch) :
    Function.Injective (fun source => routing.paired source branch) := by
  intro first second heq
  exact routing.paired_injective_with_occurrence branch first second
    (routing.paired_output_recovers_occurrence branch first second heq) heq

noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedInverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade)
    (source : {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade // routing.PairedRelated source output}) :
    Bool :=
  Classical.choose source.2

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_spec
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade)
    (source : {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade // routing.PairedRelated source output}) :
    routing.paired source.1 (routing.pairedInverseBranch output source) =
      output :=
  Classical.choose_spec source.2



noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedInverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade // routing.PairedRelated source output} ↪
      Fin 2 where
  toFun source := finTwoEquiv.symm
    (routing.pairedInverseBranch output source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : routing.pairedInverseBranch output first =
        routing.pairedInverseBranch output second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply routing.paired_branch_injective
      (routing.pairedInverseBranch output first)
    calc
      routing.paired first.1 (routing.pairedInverseBranch output first) =
          output := routing.paired_inverse_spec output first
      _ = routing.paired second.1
          (routing.pairedInverseBranch output second) :=
        (routing.paired_inverse_spec output second).symm
      _ = routing.paired second.1
          (routing.pairedInverseBranch output first) := by rw [hbranch]

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    2 ≤ (Finset.univ.filter (routing.PairedRelated source)).card := by
  let certificate : Fin 2 ↪
      {target : SixVertexHorizontalDegreeTwoHallTarget T middle
          hmiddle_pos hmiddle_lt grade //
        routing.PairedRelated source target} :=
    { toFun := fun branch =>
        ⟨routing.paired source (finTwoEquiv branch),
          ⟨finTwoEquiv branch, rfl⟩⟩
      inj' := by
        intro first second heq
        have hinjective : Function.Injective (routing.paired source) := by
          intro firstBranch secondBranch hbranch
          cases firstBranch <;> cases secondBranch
          · rfl
          · exact False.elim (routing.paired_distinct source hbranch)
          · exact False.elim (routing.paired_distinct source hbranch.symm)
          · rfl
        apply finTwoEquiv.injective
        apply hinjective
        exact congrArg Subtype.val heq }
  have hcard := Fintype.card_le_of_embedding certificate
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    (Finset.univ.filter fun source =>
      routing.PairedRelated source target).card ≤ 2 := by
  have hcard := Fintype.card_le_of_embedding
    (routing.pairedInverseCode target)
  simpa [SixVertexHorizontalDegreeTwoHighChargeHallRouting.PairedRelated,
    Fintype.card_subtype] using hcard



theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    ∀ sources : Finset
        (SixVertexHorizontalDegreeTwoHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade),
      sources.card ≤
        (Finset.univ.filter fun target => ∃ source,
          source ∈ sources ∧ routing.PairedRelated source target).card := by
  apply finiteRelationHall_of_bidegree routing.PairedRelated 2 (by omega)
  · exact routing.paired_source_degree
  · exact routing.paired_inverse_degree



noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeSources T middle
        hmiddle_pos hmiddle_lt grade →
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade :=
  Classical.choose
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      routing.PairedRelated).mp routing.paired_hall)

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective routing.pairedMatching :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      routing.PairedRelated).mp routing.paired_hall)).1

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_related
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) (source) :
    routing.PairedRelated source (routing.pairedMatching source) :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      routing.PairedRelated).mp routing.paired_hall)).2 source



noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade :=
  if hhigh : sixVertexHorizontalDegreeTwoHighCharge source then
    routing.pairedMatching ⟨source, hhigh⟩
  else routing.direct ⟨source, hhigh⟩

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) (source) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (routing.reconnect source) := by
  by_cases hhigh : sixVertexHorizontalDegreeTwoHighCharge source
  · rw [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
      dif_pos hhigh]
    rcases routing.pairedMatching_related ⟨source, hhigh⟩ with
      ⟨branch, hbranch⟩
    rw [← hbranch]
    exact routing.paired_supported ⟨source, hhigh⟩ branch
  · rw [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
      dif_neg hhigh]
    exact routing.direct_supported ⟨source, hhigh⟩

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective routing.reconnect := by
  intro first second heq
  by_cases hfirst : sixVertexHorizontalDegreeTwoHighCharge first <;>
    by_cases hsecond : sixVertexHorizontalDegreeTwoHighCharge second
  · have hp : routing.pairedMatching ⟨first, hfirst⟩ =
        routing.pairedMatching ⟨second, hsecond⟩ := by
      simpa [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
        hfirst, hsecond] using heq
    exact congrArg Subtype.val (routing.pairedMatching_injective hp)
  · rcases routing.pairedMatching_related ⟨first, hfirst⟩ with
      ⟨branch, hbranch⟩
    exfalso
    apply routing.direct_paired_disjoint ⟨second, hsecond⟩
      ⟨first, hfirst⟩ branch
    calc
      routing.direct ⟨second, hsecond⟩ = routing.reconnect second := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hsecond]
      _ = routing.reconnect first := heq.symm
      _ = routing.pairedMatching ⟨first, hfirst⟩ := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hfirst]
      _ = routing.paired ⟨first, hfirst⟩ branch := hbranch.symm
  · rcases routing.pairedMatching_related ⟨second, hsecond⟩ with
      ⟨branch, hbranch⟩
    exfalso
    apply routing.direct_paired_disjoint ⟨first, hfirst⟩
      ⟨second, hsecond⟩ branch
    calc
      routing.direct ⟨first, hfirst⟩ = routing.reconnect first := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hfirst]
      _ = routing.reconnect second := heq
      _ = routing.pairedMatching ⟨second, hsecond⟩ := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hsecond]
      _ = routing.paired ⟨second, hsecond⟩ branch := hbranch.symm
  · have hd : routing.direct ⟨first, hfirst⟩ =
        routing.direct ⟨second, hsecond⟩ := by
      simpa [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
        hfirst, hsecond] using heq
    exact congrArg Subtype.val (routing.direct_injective hd)



noncomputable def
    SixVertexHorizontalDegreeTwoHighChargeHallRouting.toTokenComponents
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalTwoCycleTokenReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade where
  Component := Bool
  componentFintype := inferInstance
  sourceComponent source :=
    decide (sixVertexHorizontalDegreeTwoHighCharge source)
  reconnect := routing.reconnect
  supported := routing.reconnect_supported
  output_recovers_component first second heq := by
    rw [routing.reconnect_injective heq]
  injective_within_component first second _ heq :=
    routing.reconnect_injective heq

def SixVertexHorizontalDegreeTwoHighChargeHallRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade)



theorem offDiagonalTwoCycleMatching_of_degreeTwoHighChargeHallRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalDegreeTwoHighChargeHallRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  apply offDiagonalTwoCycleMatching_of_tokenComponentRoutings
  intro grade
  obtain ⟨routing⟩ := hroutings grade
  exact ⟨routing.toTokenComponents⟩



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoHighChargeHallRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hroutings : SixVertexHorizontalDegreeTwoHighChargeHallRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_degreeTwoHighChargeHallRoutings
        T middle hmiddle_pos hmiddle_lt hroutings)

end

end StatMech.FrontierD

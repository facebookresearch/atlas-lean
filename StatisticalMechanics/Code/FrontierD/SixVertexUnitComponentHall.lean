/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairDecoratedHall











open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexUnitComponentHallPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


abbrev BooleanLayer (Component : Type*) [Fintype Component]
    (cardinality : Nat) :=
  {s : Finset Component // s.card = cardinality}


def booleanMiddleLayerDownRelation
    {Component : Type*} [Fintype Component]
    {k : Nat} (source : BooleanLayer Component (k + 1))
    (target : BooleanLayer Component k) : Prop :=
  target.1 ⊆ source.1


noncomputable def booleanMiddleLayerAddedElement
    {Component : Type*} [Fintype Component]
    {k : Nat} (target : BooleanLayer Component k)
    (source : BooleanLayer Component (k + 1)) : Component := by
  have hcard : target.1.card < source.1.card := by
    rw [target.2, source.2]
    omega
  exact Classical.choose
    (Finset.exists_mem_notMem_of_card_lt_card hcard)

theorem booleanMiddleLayerAddedElement_mem_source
    {Component : Type*} [Fintype Component]
    {k : Nat} (target : BooleanLayer Component k)
    (source : BooleanLayer Component (k + 1)) :
    booleanMiddleLayerAddedElement target source ∈ source.1 :=
  (Classical.choose_spec (Finset.exists_mem_notMem_of_card_lt_card
    (by rw [target.2, source.2]; omega))).1

theorem booleanMiddleLayerAddedElement_not_mem_target
    {Component : Type*} [Fintype Component]
    {k : Nat} (target : BooleanLayer Component k)
    (source : BooleanLayer Component (k + 1)) :
    booleanMiddleLayerAddedElement target source ∉ target.1 :=
  (Classical.choose_spec (Finset.exists_mem_notMem_of_card_lt_card
    (by rw [target.2, source.2]; omega))).2

theorem booleanMiddleLayer_source_eq_insert_addedElement
    {Component : Type*} [Fintype Component]
    {k : Nat} (target : BooleanLayer Component k)
    (source : BooleanLayer Component (k + 1))
    (hrelated : booleanMiddleLayerDownRelation source target) :
    source.1 = insert
      (booleanMiddleLayerAddedElement target source) target.1 := by
  apply Finset.Subset.antisymm
  · intro component hcomponent
    by_cases hin : component ∈ target.1
    · simp [hin]
    · have hdiff : source.1 \ target.1 =
          {booleanMiddleLayerAddedElement target source} := by
        have hcardDiff : (source.1 \ target.1).card = 1 := by
          rw [Finset.card_sdiff_of_subset hrelated, source.2, target.2]
          omega
        obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hcardDiff
        have hchosen : booleanMiddleLayerAddedElement target source ∈
            source.1 \ target.1 := by
          simp [booleanMiddleLayerAddedElement_mem_source,
            booleanMiddleLayerAddedElement_not_mem_target]
        rw [honly] at hchosen
        have heq :
            booleanMiddleLayerAddedElement target source = only := by
          simpa using hchosen
        simpa [heq] using honly
      have : component ∈ source.1 \ target.1 := by simp [hcomponent, hin]
      rw [hdiff] at this
      have heq : component =
          booleanMiddleLayerAddedElement target source := by
        simpa using this
      simp [heq]
  · intro component hcomponent
    simp only [Finset.mem_insert] at hcomponent
    rcases hcomponent with rfl | hcomponent
    · exact booleanMiddleLayerAddedElement_mem_source target source
    · exact hrelated hcomponent



theorem booleanMiddleLayerDownRelation_hall
    {Component : Type*} [Fintype Component]
    (k : Nat) (hcard : Fintype.card Component = 2 * k) :
    forall sources : Finset (BooleanLayer Component (k + 1)),
      sources.card <=
        (Finset.univ.filter fun target : BooleanLayer Component k =>
          ∃ source ∈ sources,
            booleanMiddleLayerDownRelation source target).card := by
  classical
  apply finiteRelationHall_of_bidegree
    (booleanMiddleLayerDownRelation (Component := Component) (k := k))
    (k + 1) (by omega)
  · intro source
    let eraseTarget : {component // component ∈ source.1} ->
        {target : BooleanLayer Component k //
          booleanMiddleLayerDownRelation source target} :=
      fun component =>
        ⟨⟨source.1.erase component.1, by
            rw [Finset.card_erase_of_mem component.2, source.2]
            omega⟩,
          Finset.erase_subset _ _⟩
    have hinjective : Function.Injective eraseTarget := by
      intro first second heq
      apply Subtype.ext
      apply source.1.erase_injOn first.2 second.2
      exact congrArg (fun target => target.1.1) heq
    have hle := Fintype.card_le_of_injective eraseTarget hinjective
    have hdomain : Fintype.card {component // component ∈ source.1} =
        k + 1 := by
      simpa using source.2
    have hcodomain :
        Fintype.card {target : BooleanLayer Component k //
          booleanMiddleLayerDownRelation source target} =
        (Finset.univ.filter
          (booleanMiddleLayerDownRelation source)).card := by
      rw [Fintype.card_subtype]
    rw [hdomain, hcodomain] at hle
    exact hle
  · intro target
    let addedElement :
        {source : BooleanLayer Component (k + 1) //
          booleanMiddleLayerDownRelation source target} ->
        {component : Component // component ∉ target.1} :=
      fun source =>
        ⟨booleanMiddleLayerAddedElement target source.1,
          booleanMiddleLayerAddedElement_not_mem_target target source.1⟩
    have hinjective : Function.Injective addedElement := by
      intro first second heq
      apply Subtype.ext
      apply Subtype.ext
      rw [booleanMiddleLayer_source_eq_insert_addedElement
          target first.1 first.2,
        booleanMiddleLayer_source_eq_insert_addedElement
          target second.1 second.2]
      have hval := congrArg Subtype.val heq
      change booleanMiddleLayerAddedElement target first.1 =
        booleanMiddleLayerAddedElement target second.1 at hval
      rw [hval]
    have hle := Fintype.card_le_of_injective addedElement hinjective
    rw [Fintype.card_subtype] at hle
    calc
      (Finset.univ.filter fun source : BooleanLayer Component (k + 1) =>
          booleanMiddleLayerDownRelation source target).card <=
          Fintype.card {component : Component // component ∉ target.1} := hle
      _ = k := by
        rw [Fintype.card_subtype_compl]
        rw [Fintype.card_coe]
        rw [hcard, target.2]
        omega
      _ <= k + 1 := by omega

end

end StatMech.FrontierD

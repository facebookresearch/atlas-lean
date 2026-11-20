/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.FiniteCumulativeGradeHall
import Code.FrontierD.SixVertexMarkedPairDecoratedHall

open Finset

namespace StatMech.FrontierD

noncomputable section

local instance finiteBidegreeCumulativeHallPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



theorem finiteUpperCumulative_of_bidegree
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (related : Source → Target → Prop)
    (sourceGrade : Source → Nat) (targetGrade : Target → Nat)
    (degree : Nat) (hdegree : 0 < degree)
    (hforward : ∀ source,
      degree ≤ (Finset.univ.filter (related source)).card)
    (hinverse : ∀ target,
      (Finset.univ.filter fun source => related source target).card ≤ degree)
    (hmonotone : ∀ source target,
      related source target → sourceGrade source ≤ targetGrade target) :
    ∀ grade,
      (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤
        (Finset.univ.filter fun target => grade ≤ targetGrade target).card := by
  intro grade
  let sources := Finset.univ.filter fun source => grade ≤ sourceGrade source
  let neighbors := Finset.univ.filter fun target =>
    ∃ source ∈ sources, related source target
  have hhall := finiteRelationHall_of_bidegree related degree hdegree
    hforward hinverse sources
  have hsubset : neighbors ⊆
      Finset.univ.filter fun target => grade ≤ targetGrade target := by
    intro target htarget
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at htarget
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨source, hsource, hrelated⟩ := htarget
    have hgrade : grade ≤ sourceGrade source := by
      simpa [sources] using hsource
    exact hgrade.trans (hmonotone source target hrelated)
  change sources.card ≤
    (Finset.univ.filter fun target => grade ≤ targetGrade target).card
  exact hhall.trans (Finset.card_le_card hsubset)


theorem finiteUpperCumulative_of_twoBranchCapacity
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (related : Source → Target → Prop)
    (sourceGrade : Source → Nat) (targetGrade : Target → Nat)
    (hforward : ∀ source,
      2 ≤ (Finset.univ.filter (related source)).card)
    (hinverse : ∀ target,
      (Finset.univ.filter fun source => related source target).card ≤ 2)
    (hmonotone : ∀ source target,
      related source target → sourceGrade source ≤ targetGrade target) :
    ∀ grade,
      (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤
        (Finset.univ.filter fun target => grade ≤ targetGrade target).card :=
  finiteUpperCumulative_of_bidegree related sourceGrade targetGrade 2
    (by omega) hforward hinverse hmonotone



theorem exists_injective_gradeMonotone_of_twoBranchCapacity
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (related : Source → Target → Prop)
    (sourceGrade : Source → Nat) (targetGrade : Target → Nat)
    (hforward : ∀ source,
      2 ≤ (Finset.univ.filter (related source)).card)
    (hinverse : ∀ target,
      (Finset.univ.filter fun source => related source target).card ≤ 2)
    (hmonotone : ∀ source target,
      related source target → sourceGrade source ≤ targetGrade target) :
    ∃ matching : Source → Target,
      Function.Injective matching ∧
        ∀ source, sourceGrade source ≤ targetGrade (matching source) := by
  exact exists_injective_gradeMonotone_of_upperCumulative sourceGrade
    targetGrade (finiteUpperCumulative_of_twoBranchCapacity related sourceGrade
      targetGrade hforward hinverse hmonotone)



structure TwoBranchMonotoneEmbeddings
    (Source Target : Type*) (sourceGrade : Source → Nat)
    (targetGrade : Target → Nat) where
  branch : Bool → Source ↪ Target
  distinct : ∀ source, branch false source ≠ branch true source
  monotone : ∀ choice source,
    sourceGrade source ≤ targetGrade (branch choice source)

def TwoBranchMonotoneEmbeddings.Related
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (source : Source) (target : Target) : Prop :=
  ∃ choice, embeddings.branch choice source = target

theorem TwoBranchMonotoneEmbeddings.forward_degree
    {Source Target : Type*} [Fintype Target]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (source : Source) :
    2 ≤ (Finset.univ.filter (embeddings.Related source)).card := by
  let certificates : Fin 2 ↪ {target : Target // embeddings.Related source target} :=
    { toFun := fun choice =>
        ⟨embeddings.branch (finTwoEquiv choice) source,
          ⟨finTwoEquiv choice, rfl⟩⟩
      inj' := by
        intro first second heq
        apply finTwoEquiv.injective
        cases hfirst : finTwoEquiv first <;>
          cases hsecond : finTwoEquiv second
        · rfl
        · exact False.elim (embeddings.distinct source (by
            simpa [hfirst, hsecond] using congrArg Subtype.val heq))
        · exact False.elim (embeddings.distinct source (by
            simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm))
        · rfl }
  have hcard := Fintype.card_le_of_embedding certificates
  simpa [Fintype.card_subtype] using hcard

noncomputable def TwoBranchMonotoneEmbeddings.inverseChoice
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target)
    (source : {source : Source // embeddings.Related source target}) : Bool :=
  Classical.choose source.2

theorem TwoBranchMonotoneEmbeddings.branch_inverseChoice
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target)
    (source : {source : Source // embeddings.Related source target}) :
    embeddings.branch (embeddings.inverseChoice target source) source.1 =
      target :=
  Classical.choose_spec source.2

noncomputable def TwoBranchMonotoneEmbeddings.inverseCode
    {Source Target : Type*} {sourceGrade : Source → Nat}
    {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target) :
    {source : Source // embeddings.Related source target} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm (embeddings.inverseChoice target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hchoice : embeddings.inverseChoice target first =
        embeddings.inverseChoice target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply (embeddings.branch (embeddings.inverseChoice target first)).injective
    calc
      embeddings.branch (embeddings.inverseChoice target first) first.1 =
          target := embeddings.branch_inverseChoice target first
      _ = embeddings.branch (embeddings.inverseChoice target second) second.1 :=
        (embeddings.branch_inverseChoice target second).symm
      _ = embeddings.branch (embeddings.inverseChoice target first) second.1 := by
        rw [hchoice]

theorem TwoBranchMonotoneEmbeddings.inverse_degree
    {Source Target : Type*} [Fintype Source]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) (target : Target) :
    (Finset.univ.filter fun source => embeddings.Related source target).card ≤
      2 := by
  have hcard := Fintype.card_le_of_embedding (embeddings.inverseCode target)
  simpa [Fintype.card_subtype] using hcard

theorem TwoBranchMonotoneEmbeddings.upperCumulative
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) :
    ∀ grade,
      (Finset.univ.filter fun source => grade ≤ sourceGrade source).card ≤
        (Finset.univ.filter fun target => grade ≤ targetGrade target).card :=
  finiteUpperCumulative_of_twoBranchCapacity embeddings.Related sourceGrade
    targetGrade embeddings.forward_degree embeddings.inverse_degree
    (by
      intro source target hrelated
      obtain ⟨choice, rfl⟩ := hrelated
      exact embeddings.monotone choice source)

theorem TwoBranchMonotoneEmbeddings.exists_injective_gradeMonotone
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceGrade : Source → Nat} {targetGrade : Target → Nat}
    (embeddings : TwoBranchMonotoneEmbeddings Source Target sourceGrade
      targetGrade) :
    ∃ matching : Source → Target,
      Function.Injective matching ∧
        ∀ source, sourceGrade source ≤ targetGrade (matching source) :=
  exists_injective_gradeMonotone_of_upperCumulative sourceGrade targetGrade
    embeddings.upperCumulative

end

end StatMech.FrontierD

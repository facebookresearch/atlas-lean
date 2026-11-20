/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexConfigurationPairBigrade
import Code.FrontierD.SixVertexMarkedPairDecoratedHall











open Finset

namespace StatMech.FrontierD

noncomputable section

local instance configurationPairedBranchDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p

abbrev SixVertexConfigurationPairBigradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :=
  {pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right //
    sixVertexConfigurationPairBigrade pair = grade}

def sixVertexConfigurationLowerSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) : Fin (T.width + 1) :=
  ⟨middle.val - 1, by omega⟩

def sixVertexConfigurationUpperSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_lt : middle.val < T.width) : Fin (T.width + 1) :=
  ⟨middle.val + 1, by omega⟩



structure SixVertexConfigurationPairedBranchGeometricConstruction
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target :
    SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade ->
      Bool ->
        SixVertexConfigurationPairBigradeFiber T middle middle grade
  distinct : forall source, target source false ≠ target source true
  recoverable : forall branch first second,
    target first branch = target second branch -> first = second


structure SixVertexConfigurationPairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  branch : Bool ->
    SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade ↪
      SixVertexConfigurationPairBigradeFiber T middle middle grade
  distinct : forall source, branch false source ≠ branch true source

def SixVertexConfigurationPairedBranchGeometricConstruction.toEmbeddings
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (geometric : SixVertexConfigurationPairedBranchGeometricConstruction
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade where
  branch choice :=
    ⟨fun source => geometric.target source choice,
      fun _ _ heq => geometric.recoverable choice _ _ heq⟩
  distinct := geometric.distinct


def SixVertexConfigurationPairedBranchRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade) :
    Prop :=
  exists branch, embeddings.branch branch source = target

def SixVertexConfigurationPairedBranchEmbeddings.sourceCertificates
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) :
    Fin 2 ↪
      {target : SixVertexConfigurationPairBigradeFiber T middle middle grade //
        SixVertexConfigurationPairedBranchRelated
          embeddings source target} where
  toFun branch :=
    ⟨embeddings.branch (finTwoEquiv branch) source,
      ⟨finTwoEquiv branch, rfl⟩⟩
  inj' := by
    intro first second heq
    apply finTwoEquiv.injective
    cases hfirst : finTwoEquiv first <;>
      cases hsecond : finTwoEquiv second
    · rfl
    · exfalso
      exact embeddings.distinct source (by
        simpa [hfirst, hsecond] using congrArg Subtype.val heq)
    · exfalso
      exact embeddings.distinct source (by
        simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm)
    · rfl

theorem SixVertexConfigurationPairedBranchEmbeddings.source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) :
    2 <= (Finset.univ.filter
      (SixVertexConfigurationPairedBranchRelated embeddings source)).card := by
  have hcard := Fintype.card_le_of_embedding
    (embeddings.sourceCertificates source)
  simpa [Fintype.card_subtype] using hcard

noncomputable def
    SixVertexConfigurationPairedBranchEmbeddings.inverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade)
    (source : {source : SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade //
      SixVertexConfigurationPairedBranchRelated embeddings source target}) :
    Bool :=
  Classical.choose source.2

theorem SixVertexConfigurationPairedBranchEmbeddings.branch_inverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade)
    (source : {source : SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade //
      SixVertexConfigurationPairedBranchRelated embeddings source target}) :
    embeddings.branch (embeddings.inverseBranch target source) source.1 =
      target :=
  Classical.choose_spec source.2

noncomputable def SixVertexConfigurationPairedBranchEmbeddings.inverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade) :
    {source : SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade //
      SixVertexConfigurationPairedBranchRelated embeddings source target} ↪
        Fin 2 where
  toFun source := finTwoEquiv.symm
    (embeddings.inverseBranch target source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    have hbranch : embeddings.inverseBranch target first =
        embeddings.inverseBranch target second := by
      apply finTwoEquiv.symm.injective
      exact heq
    apply (embeddings.branch
      (embeddings.inverseBranch target first)).injective
    calc
      embeddings.branch (embeddings.inverseBranch target first) first.1 =
          target := embeddings.branch_inverseBranch target first
      _ = embeddings.branch (embeddings.inverseBranch target second) second.1 :=
        (embeddings.branch_inverseBranch target second).symm
      _ = embeddings.branch (embeddings.inverseBranch target first) second.1 :=
        by rw [hbranch]

theorem SixVertexConfigurationPairedBranchEmbeddings.inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade) :
    (Finset.univ.filter fun source =>
      SixVertexConfigurationPairedBranchRelated
        embeddings source target).card <= 2 := by
  have hcard := Fintype.card_le_of_embedding
    (embeddings.inverseCode target)
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexConfigurationPairedBranchEmbeddings.hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade) :
    forall sources : Finset (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade),
      sources.card <=
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexConfigurationPairedBranchRelated
              embeddings source target).card := by
  apply finiteRelationHall_of_bidegree
    (SixVertexConfigurationPairedBranchRelated embeddings) 2 (by omega)
  · exact embeddings.source_degree
  · exact embeddings.inverse_degree


def SixVertexConfigurationPairedBranchConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    Prop :=
  forall grade, Nonempty
    (SixVertexConfigurationPairedBranchGeometricConstruction T middle
      hmiddle_pos hmiddle_lt grade)

noncomputable def
    sixVertexConfigurationPairedBranchConstructionOfIsEmpty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (hempty : IsEmpty (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade)) :
    SixVertexConfigurationPairedBranchGeometricConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source := isEmptyElim source
  distinct source := isEmptyElim source
  recoverable _branch first := isEmptyElim first



theorem configurationPairedBranchConstructions_of_nonempty_sources
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : forall grade,
      Nonempty (SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) ->
      Nonempty
        (SixVertexConfigurationPairedBranchGeometricConstruction T middle
          hmiddle_pos hmiddle_lt grade)) :
    SixVertexConfigurationPairedBranchConstructions T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  cases isEmpty_or_nonempty (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) with
  | inl hempty =>
      exact ⟨sixVertexConfigurationPairedBranchConstructionOfIsEmpty
        hempty⟩
  | inr hnonempty => exact hconstruction grade hnonempty

theorem configurationBigradeFibers_of_pairedBranchConstructions
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : SixVertexConfigurationPairedBranchConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairBigradeFiberDominates T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) middle middle := by
  intro grade
  obtain ⟨geometric⟩ := hconstruction grade
  let embeddings := geometric.toEmbeddings
  let sources : Finset (SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) := Finset.univ
  have hHall := embeddings.hall sources
  calc
    Fintype.card (SixVertexConfigurationPairBigradeFiber T
        (sixVertexConfigurationLowerSector middle hmiddle_pos)
        (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) =
        sources.card := by simp [sources]
    _ <= (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexConfigurationPairedBranchRelated
              embeddings source target).card := hHall
    _ <= Fintype.card
        (SixVertexConfigurationPairBigradeFiber T middle middle grade) := by
      simpa only [Finset.card_univ] using Finset.card_le_univ
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexConfigurationPairedBranchRelated
              embeddings source target)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hconstruction : SixVertexConfigurationPairedBranchConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers
    T middle hmiddle_pos hmiddle_lt
  exact configurationBigradeFibers_of_pairedBranchConstructions hconstruction

theorem sixVertexSectorTrace_logConcave_of_configurationPairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hconstruction : SixVertexConfigurationPairedBranchConstructions
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    T.width T.height middle.val hc
      (sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationPairedBranches
        T middle hmiddle_pos hmiddle_lt hconstruction)

end

end StatMech.FrontierD

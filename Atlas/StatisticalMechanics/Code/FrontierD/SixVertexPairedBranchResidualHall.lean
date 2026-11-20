/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching














open Finset

namespace StatMech.FrontierD

noncomputable section

local instance pairedBranchResidualDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p




structure SixVertexHorizontalPairedBranchResidualAtlas
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target :
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
      Bool ->
        SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
  target_injective : forall source, Function.Injective (target source)
  supported : forall source branch,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (target source branch)
  inverseCode : forall output,
    {source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
      exists branch, target source branch = output} ↪ Fin 2




structure SixVertexHorizontalPairedBranchResidualConstruction
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target :
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
      Bool ->
        SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
  target_injective : forall source, Function.Injective (target source)
  branch_injective : forall branch,
    Function.Injective (fun source => target source branch)
  supported : forall source branch,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (target source branch)



abbrev SixVertexHorizontalSurplusConfigurationPreimage
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat)
    (configuration : {pair : SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle //
      sixVertexConfigurationPairBigrade pair = grade}) :=
  {token : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualSurplusConfigurationPair token = configuration}





structure SixVertexHorizontalPairedBranchResidualGeometricConstruction
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  targetConfiguration :
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
      Bool ->
        {pair : SixVertexMarkedSectorConfiguration T middle ×
            SixVertexMarkedSectorConfiguration T middle //
          sixVertexConfigurationPairBigrade pair = grade}
  realization : forall source branch,
    SixVertexHorizontalSurplusConfigurationPreimage T middle
      hmiddle_pos hmiddle_lt grade (targetConfiguration source branch)
  distinct : forall source,
    targetConfiguration source false ≠ targetConfiguration source true
  recoverable : forall branch first second,
    targetConfiguration first branch = targetConfiguration second branch ->
      sixVertexHorizontalActualDeficitConfigurationPair first =
        sixVertexHorizontalActualDeficitConfigurationPair second
  supported : forall source branch,
    SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source).1
      (targetConfiguration source branch).1



noncomputable def
    SixVertexHorizontalPairedBranchResidualGeometricConstruction.toConstruction
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (geometric : SixVertexHorizontalPairedBranchResidualGeometricConstruction
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source branch := (geometric.realization source branch).1
  target_injective source := by
    intro first second heq
    cases first <;> cases second
    · rfl
    · exfalso
      apply geometric.distinct source
      calc
        geometric.targetConfiguration source false =
            sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source false).1 :=
          (geometric.realization source false).2.symm
        _ = sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source true).1 := congrArg _ heq
        _ = geometric.targetConfiguration source true :=
          (geometric.realization source true).2
    · exfalso
      apply geometric.distinct source
      symm
      calc
        geometric.targetConfiguration source true =
            sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source true).1 :=
          (geometric.realization source true).2.symm
        _ = sixVertexHorizontalActualSurplusConfigurationPair
              (geometric.realization source false).1 := congrArg _ heq
        _ = geometric.targetConfiguration source false :=
          (geometric.realization source false).2
    · rfl
  branch_injective branch := by
    intro first second heq
    apply sixVertexHorizontalActualDeficitConfigurationPair_injective
    apply geometric.recoverable branch first second
    calc
      geometric.targetConfiguration first branch =
          sixVertexHorizontalActualSurplusConfigurationPair
            (geometric.realization first branch).1 :=
        (geometric.realization first branch).2.symm
      _ = sixVertexHorizontalActualSurplusConfigurationPair
            (geometric.realization second branch).1 := congrArg _ heq
      _ = geometric.targetConfiguration second branch :=
        (geometric.realization second branch).2
  supported source branch := by
    change SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source).1
      (sixVertexHorizontalActualSurplusConfigurationPair
        (geometric.realization source branch).1).1
    rw [(geometric.realization source branch).2]
    exact geometric.supported source branch




structure SixVertexHorizontalPairedBranchResidualEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  branch : Bool ->
    SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ↪
      SixVertexHorizontalActualSurplusTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
  distinct : forall source, branch false source ≠ branch true source
  supported : forall source choice,
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (branch choice source)



def SixVertexHorizontalPairedBranchResidualEmbeddings.toConstruction
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexHorizontalPairedBranchResidualEmbeddings
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source branch := embeddings.branch branch source
  target_injective source := by
    intro first second heq
    cases first <;> cases second
    · rfl
    · exact False.elim (embeddings.distinct source heq)
    · exact False.elim (embeddings.distinct source heq.symm)
    · rfl
  branch_injective branch := (embeddings.branch branch).injective
  supported := embeddings.supported

noncomputable def
    SixVertexHorizontalPairedBranchResidualConstruction.inverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)
    (source : {source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
      exists branch, construction.target source branch = output}) : Bool :=
  Classical.choose source.2

theorem SixVertexHorizontalPairedBranchResidualConstruction.target_inverseBranch
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)
    (source : {source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
      exists branch, construction.target source branch = output}) :
    construction.target source.1
        (construction.inverseBranch output source) = output :=
  Classical.choose_spec source.2



noncomputable def
    SixVertexHorizontalPairedBranchResidualConstruction.inverseCode
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade)
    (output : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    {source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
      exists branch, construction.target source branch = output} ↪ Fin 2 where
  toFun source := finTwoEquiv.symm
    (construction.inverseBranch output source)
  inj' := by
    intro first second heq
    apply Subtype.ext
    apply construction.branch_injective
      (construction.inverseBranch output first)
    have hbranch : construction.inverseBranch output first =
        construction.inverseBranch output second := by
      apply finTwoEquiv.symm.injective
      exact heq
    calc
      construction.target first.1
          (construction.inverseBranch output first) = output :=
        construction.target_inverseBranch output first
      _ = construction.target second.1
          (construction.inverseBranch output second) :=
        (construction.target_inverseBranch output second).symm
      _ = construction.target second.1
          (construction.inverseBranch output first) := by rw [hbranch]


noncomputable def
    SixVertexHorizontalPairedBranchResidualConstruction.toAtlas
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (construction : SixVertexHorizontalPairedBranchResidualConstruction
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade where
  target := construction.target
  target_injective := construction.target_injective
  supported := construction.supported
  inverseCode := construction.inverseCode



noncomputable def
    sixVertexHorizontalPairedBranchResidualConstructionOfIsEmpty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (hempty : IsEmpty
      (SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)) :
    SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade where
  target source := isEmptyElim source
  target_injective source := isEmptyElim source
  branch_injective branch source := isEmptyElim source
  supported source := isEmptyElim source


def SixVertexHorizontalPairedBranchResidualRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle)
    (target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) : Prop :=
  exists branch, atlas.target source branch = target



def SixVertexHorizontalPairedBranchResidualAtlas.sourceCertificates
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    Fin 2 ↪
      {target : SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
        SixVertexHorizontalPairedBranchResidualRelated
          atlas source target} where
  toFun branch :=
    ⟨atlas.target source (finTwoEquiv branch), ⟨finTwoEquiv branch, rfl⟩⟩
  inj' := by
    intro first second heq
    apply finTwoEquiv.injective
    apply atlas.target_injective source
    exact congrArg (fun target => target.1) heq

theorem SixVertexHorizontalPairedBranchResidualAtlas.source_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    2 <= (Finset.univ.filter
      (SixVertexHorizontalPairedBranchResidualRelated atlas source)).card := by
  have hcard := Fintype.card_le_of_embedding
    (atlas.sourceCertificates source)
  simpa [Fintype.card_subtype] using hcard

theorem SixVertexHorizontalPairedBranchResidualAtlas.source_nonempty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    (Finset.univ.filter
      (SixVertexHorizontalPairedBranchResidualRelated atlas source)).Nonempty := by
  apply Finset.card_pos.mp
  have hdegree := atlas.source_degree source
  omega

theorem SixVertexHorizontalPairedBranchResidualAtlas.inverse_degree
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    (Finset.univ.filter fun source =>
      SixVertexHorizontalPairedBranchResidualRelated atlas source target).card <=
        2 := by
  have hcard := Fintype.card_le_of_embedding (atlas.inverseCode target)
  simpa [SixVertexHorizontalPairedBranchResidualRelated,
    Fintype.card_subtype] using hcard



theorem SixVertexHorizontalPairedBranchResidualAtlas.hall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (atlas : SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade) :
    forall sources : Finset
      (SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle),
      sources.card <=
        (Finset.univ.filter fun target => exists source,
          source ∈ sources ∧
            SixVertexHorizontalPairedBranchResidualRelated
              atlas source target).card := by
  apply finiteRelationHall_of_bidegree
    (SixVertexHorizontalPairedBranchResidualRelated atlas) 2 (by omega)
  · exact atlas.source_degree
  · exact atlas.inverse_degree


def SixVertexHorizontalPairedBranchResidualAtlases
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade : Nat × Nat, Nonempty
    (SixVertexHorizontalPairedBranchResidualAtlas T middle
      hmiddle_pos hmiddle_lt grade)


def SixVertexHorizontalPairedBranchResidualConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade : Nat × Nat, Nonempty
    (SixVertexHorizontalPairedBranchResidualConstruction T middle
      hmiddle_pos hmiddle_lt grade)

theorem pairedBranchResidualAtlases_of_constructions
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨construction⟩ := hconstruction grade
  exact ⟨construction.toAtlas⟩




theorem offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨construction⟩ := hconstruction grade
  exact ⟨fun source => construction.target source false,
    construction.branch_injective false,
    fun source => construction.supported source false⟩



theorem pairedBranchResidualConstructions_of_nonempty_sources
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hconstruction : forall grade : Nat × Nat,
      Nonempty
        (SixVertexHorizontalActualDeficitTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) ->
      Nonempty
        (SixVertexHorizontalPairedBranchResidualConstruction T middle
          hmiddle_pos hmiddle_lt grade)) :
    SixVertexHorizontalPairedBranchResidualConstructions T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  cases isEmpty_or_nonempty
      (SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) with
  | inl hempty =>
      exact ⟨sixVertexHorizontalPairedBranchResidualConstructionOfIsEmpty
        hempty⟩
  | inr hnonempty => exact hconstruction grade hnonempty



theorem offDiagonalTwoCycleMatching_of_pairedBranchAtlases
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨atlas⟩ := hatlas grade
  have hmatching :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (SixVertexHorizontalPairedBranchResidualRelated atlas)).mp atlas.hall
  obtain ⟨matching, hinjective, hrelated⟩ := hmatching
  refine ⟨matching, hinjective, ?_⟩
  intro source
  obtain ⟨branch, htarget⟩ := hrelated source
  rw [← htarget]
  exact atlas.supported source branch

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchAtlases
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_pairedBranchAtlases hatlas)

theorem sixVertexSectorTrace_logConcave_of_pairedBranchAtlases
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hatlas : SixVertexHorizontalPairedBranchResidualAtlases T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt hc
      (offDiagonalTwoCycleMatching_of_pairedBranchAtlases hatlas)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_pairedBranchConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct
        hconstruction)

theorem sixVertexSectorTrace_logConcave_of_pairedBranchConstructions
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hconstruction : SixVertexHorizontalPairedBranchResidualConstructions
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt hc
      (offDiagonalTwoCycleMatching_of_pairedBranchConstructions_direct
        hconstruction)

end

end StatMech.FrontierD

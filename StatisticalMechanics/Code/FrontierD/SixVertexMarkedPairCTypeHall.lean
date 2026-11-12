/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairDecoratedHall
import Code.FrontierD.SixVertexPairReconnectionWitness
import Mathlib.Data.Fintype.EquivFin












open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropCTypeHall (p : Prop) : Decidable p :=
  Classical.propDecidable p



theorem exists_injective_gradePreserving_iff_fiberCard
    {Source Target Grade : Type*} [Fintype Source] [Fintype Target]
    [DecidableEq Grade]
    (sourceGrade : Source -> Grade) (targetGrade : Target -> Grade) :
    (exists matching : Source -> Target,
        Function.Injective matching /\
          forall source, sourceGrade source = targetGrade (matching source)) <->
      forall grade : Grade,
        Fintype.card {source : Source // sourceGrade source = grade} <=
          Fintype.card {target : Target // targetGrade target = grade} := by
  constructor
  · rintro ⟨matching, hinjective, hgrade⟩ grade
    let fiberEmbedding :
        {source : Source // sourceGrade source = grade} ↪
          {target : Target // targetGrade target = grade} :=
      { toFun := fun source =>
          ⟨matching source.1, (hgrade source.1).symm.trans source.2⟩
        inj' := by
          intro source₁ source₂ heq
          apply Subtype.ext
          apply hinjective
          exact congrArg Subtype.val heq }
    exact Fintype.card_le_of_embedding fiberEmbedding
  · intro hfiber
    let embedding : forall grade : Grade,
        {source : Source // sourceGrade source = grade} ↪
          {target : Target // targetGrade target = grade} :=
      fun grade => Classical.choice
        (Function.Embedding.nonempty_iff_card_le.mpr (hfiber grade))
    let gradedEmbedding :
        (Sigma fun grade : Grade =>
          {source : Source // sourceGrade source = grade}) ↪
        (Sigma fun grade : Grade =>
          {target : Target // targetGrade target = grade}) :=
      { toFun := fun graded =>
          ⟨graded.1, embedding graded.1 graded.2⟩
        inj' := by
          rintro ⟨grade₁, source₁⟩ ⟨grade₂, source₂⟩ heq
          have hgrade : grade₁ = grade₂ := congrArg Sigma.fst heq
          subst grade₂
          have hfiberEq :
              embedding grade₁ source₁ = embedding grade₁ source₂ := by
            exact eq_of_heq (Sigma.mk.inj heq).2
          have hsource := (embedding grade₁).injective hfiberEq
          cases hsource
          rfl }
    let matchingEmbedding : Source ↪ Target :=
      (Equiv.sigmaFiberEquiv sourceGrade).symm.toEmbedding |>.trans
        (gradedEmbedding.trans
          (Equiv.sigmaFiberEquiv targetGrade).toEmbedding)
    refine ⟨matchingEmbedding, matchingEmbedding.injective, ?_⟩
    intro source
    exact (embedding (sourceGrade source) ⟨source, rfl⟩).2.symm



theorem exists_injective_bigradePreserving_iff_fiberCard
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (sourceGrade : Source -> Nat × Nat)
    (targetGrade : Target -> Nat × Nat) :
    (exists matching : Source -> Target,
        Function.Injective matching /\
          forall source, sourceGrade source = targetGrade (matching source)) <->
      forall grade : Nat × Nat,
        Fintype.card {source : Source // sourceGrade source = grade} <=
          Fintype.card {target : Target // targetGrade target = grade} :=
  exists_injective_gradePreserving_iff_fiberCard sourceGrade targetGrade



def sixVertexMarkedDecoratedPairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (pair : SixVertexMarkedDecoratedPair T left right k) : Nat :=
  sixVertexTorusCTypeCount pair.1.1.1 +
    sixVertexTorusCTypeCount pair.1.2.1


def sixVertexConfigurationPairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat :=
  sixVertexTorusCTypeCount pair.1.1 +
    sixVertexTorusCTypeCount pair.2.1

theorem sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right)
    (k total : Nat) (htotal : sixVertexConfigurationPairTotalC pair = total) :
    sixVertexMarkedPairMultiplicityNat pair.1.1 pair.2.1 k =
      2 ^ (total - k) * total.choose k := by
  simp only [sixVertexMarkedPairMultiplicityNat,
    sixVertexConfigurationPairTotalC] at htotal ⊢
  rw [htotal]

@[simp] theorem sixVertexMarkedDecoratedPairTotalC_eq_pairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (pair : SixVertexMarkedDecoratedPair T left right k) :
    sixVertexMarkedDecoratedPairTotalC pair =
      sixVertexConfigurationPairTotalC pair.1 :=
  rfl




noncomputable def sixVertexMarkedDecoratedPairTotalCFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k total : Nat) :
    {decorated : SixVertexMarkedDecoratedPair T left right k //
        sixVertexMarkedDecoratedPairTotalC decorated = total} ≃
      ({pair : SixVertexMarkedSectorConfiguration T left ×
          SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairTotalC pair = total} ×
        Fin (2 ^ (total - k) * total.choose k)) where
  toFun decorated :=
    ⟨⟨decorated.1.1, decorated.2⟩,
      Fin.cast
        (sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq
          decorated.1.1 k total decorated.2)
        decorated.1.2⟩
  invFun decorated :=
    ⟨⟨decorated.1.1,
        Fin.cast
          (sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq
            decorated.1.1 k total decorated.1.2).symm
          decorated.2⟩,
      decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · simp

theorem card_sixVertexMarkedDecoratedPairTotalCFiber
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k total : Nat) :
    Fintype.card
        {decorated : SixVertexMarkedDecoratedPair T left right k //
          sixVertexMarkedDecoratedPairTotalC decorated = total} =
      Fintype.card
          {pair : SixVertexMarkedSectorConfiguration T left ×
              SixVertexMarkedSectorConfiguration T right //
            sixVertexConfigurationPairTotalC pair = total} *
        (2 ^ (total - k) * total.choose k) := by
  rw [Fintype.card_congr
    (sixVertexMarkedDecoratedPairTotalCFiberEquiv
      T left right k total)]
  simp



def SixVertexMarkedDecoratedPairEqualTotalC
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (source : SixVertexMarkedDecoratedPair T lower upper k)
    (target : SixVertexMarkedDecoratedPair T middle middle k) : Prop :=
  sixVertexMarkedDecoratedPairTotalC source =
    sixVertexMarkedDecoratedPairTotalC target



def SixVertexMarkedDecoratedPairTotalCFiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1))
    (k : Nat) : Prop :=
  forall total : Nat,
    Fintype.card
        {source : SixVertexMarkedDecoratedPair T lower upper k //
          sixVertexMarkedDecoratedPairTotalC source = total} <=
      Fintype.card
        {target : SixVertexMarkedDecoratedPair T middle middle k //
          sixVertexMarkedDecoratedPairTotalC target = total}


def SixVertexConfigurationPairTotalCFiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall total : Nat,
    Fintype.card
        {source : SixVertexMarkedPairSource T lower upper //
          sixVertexConfigurationPairTotalC source = total} <=
      Fintype.card
        {target : SixVertexMarkedPairTarget T middle //
          sixVertexConfigurationPairTotalC target = total}



def SixVertexConfigurationPairTotalCReconnection
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  exists matching : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle,
    Function.Injective matching /\
      forall source,
        sixVertexConfigurationPairTotalC source =
          sixVertexConfigurationPairTotalC (matching source)

theorem configurationPairTotalCReconnection_iff_fiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexConfigurationPairTotalCReconnection T lower middle upper <->
      SixVertexConfigurationPairTotalCFiberDominates
        T lower middle upper :=
  exists_injective_gradePreserving_iff_fiberCard
    sixVertexConfigurationPairTotalC sixVertexConfigurationPairTotalC



theorem decoratedTotalCFiberDominates_of_configurationPair
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper) (k : Nat) :
    SixVertexMarkedDecoratedPairTotalCFiberDominates
      T lower middle upper k := by
  intro total
  rw [card_sixVertexMarkedDecoratedPairTotalCFiber,
    card_sixVertexMarkedDecoratedPairTotalCFiber]
  exact Nat.mul_le_mul_right _ (hfiber total)



theorem exists_injective_equalTotalC_of_fiberDominates
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (hfiber : SixVertexMarkedDecoratedPairTotalCFiberDominates
      T lower middle upper k) :
    exists matching : SixVertexMarkedDecoratedPair T lower upper k ->
        SixVertexMarkedDecoratedPair T middle middle k,
      Function.Injective matching /\
        forall source,
          SixVertexMarkedDecoratedPairEqualTotalC source (matching source) := by
  let embedding : forall total : Nat,
      {source : SixVertexMarkedDecoratedPair T lower upper k //
        sixVertexMarkedDecoratedPairTotalC source = total} ↪
      {target : SixVertexMarkedDecoratedPair T middle middle k //
        sixVertexMarkedDecoratedPairTotalC target = total} :=
    fun total => Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (hfiber total))
  let gradedEmbedding :
      (Sigma fun total : Nat =>
        {source : SixVertexMarkedDecoratedPair T lower upper k //
          sixVertexMarkedDecoratedPairTotalC source = total}) ↪
      (Sigma fun total : Nat =>
        {target : SixVertexMarkedDecoratedPair T middle middle k //
          sixVertexMarkedDecoratedPairTotalC target = total}) :=
    { toFun := fun graded =>
        ⟨graded.1, embedding graded.1 graded.2⟩
      inj' := by
        rintro ⟨total₁, source₁⟩ ⟨total₂, source₂⟩ heq
        have htotal : total₁ = total₂ := congrArg Sigma.fst heq
        subst total₂
        have hfiberEq :
            embedding total₁ source₁ = embedding total₁ source₂ := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have hsource := (embedding total₁).injective hfiberEq
        cases hsource
        rfl }
  let matchingEmbedding :
      SixVertexMarkedDecoratedPair T lower upper k ↪
        SixVertexMarkedDecoratedPair T middle middle k :=
    (Equiv.sigmaFiberEquiv
      (fun source : SixVertexMarkedDecoratedPair T lower upper k =>
        sixVertexMarkedDecoratedPairTotalC source)).symm.toEmbedding |>.trans
      (gradedEmbedding.trans
        (Equiv.sigmaFiberEquiv
          (fun target : SixVertexMarkedDecoratedPair T middle middle k =>
            sixVertexMarkedDecoratedPairTotalC target)).toEmbedding)
  refine ⟨matchingEmbedding, matchingEmbedding.injective, ?_⟩
  intro source
  exact (embedding (sixVertexMarkedDecoratedPairTotalC source)
    ⟨source, rfl⟩).2.symm



theorem sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (hfiber : SixVertexMarkedDecoratedPairTotalCFiberDominates
      T lower middle upper k) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
      SixVertexMarkedDecoratedPairEqualTotalC := by
  rw [sixVertexMarkedDecoratedPairHall_iff_exists_injective]
  exact exists_injective_equalTotalC_of_fiberDominates hfiber



theorem sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper) (k : Nat) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
      SixVertexMarkedDecoratedPairEqualTotalC :=
  sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates
    (decoratedTotalCFiberDominates_of_configurationPair hfiber k)



theorem sixVertexMarkedDecoratedPairHall_equalTotalC_of_reconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexConfigurationPairTotalCReconnection
      T lower middle upper) (k : Nat) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
      SixVertexMarkedDecoratedPairEqualTotalC :=
  sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair
    ((configurationPairTotalCReconnection_iff_fiberDominates
      T lower middle upper).mp hreconnect) k



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall
    T middle hmiddle_pos hmiddle_lt
  intro k
  exact ⟨SixVertexMarkedDecoratedPairEqualTotalC,
    sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair
      hfiber k⟩



theorem sixVertexSectorTrace_logConcave_of_totalCFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hfiber : SixVertexConfigurationPairTotalCFiberDominates T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
  exact sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    T.width T.height middle.val hc
      (sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
      T middle hmiddle_pos hmiddle_lt hfiber)



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCReconnection
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hreconnect : SixVertexConfigurationPairTotalCReconnection T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
    T middle hmiddle_pos hmiddle_lt
      ((configurationPairTotalCReconnection_iff_fiberDominates T
        ⟨middle.val - 1, by omega⟩ middle
        ⟨middle.val + 1, by omega⟩).mp hreconnect)




theorem sixVertexMarkedDecoratedPairHall_equalTotalC_iff_fiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) (k : Nat) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k
        SixVertexMarkedDecoratedPairEqualTotalC <->
      SixVertexMarkedDecoratedPairTotalCFiberDominates
        T lower middle upper k := by
  constructor
  · intro hall total
    obtain ⟨matching, hinjective, hrelated⟩ :=
      (sixVertexMarkedDecoratedPairHall_iff_exists_injective
        T lower middle upper k SixVertexMarkedDecoratedPairEqualTotalC).mp hall
    let fiberEmbedding :
        {source : SixVertexMarkedDecoratedPair T lower upper k //
          sixVertexMarkedDecoratedPairTotalC source = total} ↪
        {target : SixVertexMarkedDecoratedPair T middle middle k //
          sixVertexMarkedDecoratedPairTotalC target = total} :=
      { toFun := fun source =>
          ⟨matching source.1,
            (hrelated source.1).symm.trans source.2⟩
        inj' := by
          intro source₁ source₂ heq
          apply Subtype.ext
          apply hinjective
          exact congrArg Subtype.val heq }
    exact Fintype.card_le_of_embedding fiberEmbedding
  · exact sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates



theorem sixVertexFourByTwo_reconnection_equalTotalC :
    sixVertexTorusCTypeCount sixVertexFourByTwoLowArrows +
        sixVertexTorusCTypeCount sixVertexFourByTwoHighArrows =
      sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows +
        sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows := by
  rw [sixVertexFourByTwoLowArrows_cTypeCount,
    sixVertexFourByTwoHighArrows_cTypeCount,
    sixVertexFourByTwoMiddleArrows_cTypeCount]

end

end StatMech.FrontierD

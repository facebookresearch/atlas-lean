/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch












namespace StatMech.FrontierD

noncomputable section



structure SixVertexConfigurationPhysicalCommonFactor
    (smallT largeT : EvenTorus)
    (smallMiddle : Fin (smallT.width + 1))
    (largeMiddle : Fin (largeT.width + 1))
    (hsmall_pos : 0 < smallMiddle.val)
    (hsmall_lt : smallMiddle.val < smallT.width)
    (hlarge_pos : 0 < largeMiddle.val)
    (hlarge_lt : largeMiddle.val < largeT.width) where
  Factor : Type
  sourceEquiv :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ≃
      SixVertexConfigurationPhysicalSource smallT smallMiddle
          hsmall_pos hsmall_lt × Factor
  targetEquiv :
    SixVertexConfigurationPhysicalTarget largeT largeMiddle ≃
      SixVertexConfigurationPhysicalTarget smallT smallMiddle × Factor
  factorTotalC : Factor → Nat
  source_totalC : forall source,
    sixVertexConfigurationPairTotalCPhysical source =
      sixVertexConfigurationPairTotalCPhysical (sourceEquiv source).1 +
        factorTotalC (sourceEquiv source).2
  target_totalC : forall target,
    sixVertexConfigurationPairTotalCPhysical target =
      sixVertexConfigurationPairTotalCPhysical (targetEquiv target).1 +
        factorTotalC (targetEquiv target).2


def SixVertexConfigurationPhysicalCommonFactor.liftBranch
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    (factorization : SixVertexConfigurationPhysicalCommonFactor
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt)
    (choice : Bool) :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ↪
      SixVertexConfigurationPhysicalTarget largeT largeMiddle where
  toFun source :=
    factorization.targetEquiv.symm
      (embeddings.branch choice (factorization.sourceEquiv source).1,
        (factorization.sourceEquiv source).2)
  inj' := by
    intro first second heq
    have hpair := congrArg factorization.targetEquiv heq
    simp only [Equiv.apply_symm_apply] at hpair
    have hfirst := (embeddings.branch choice).injective
      (congrArg (fun pair => pair.1) hpair)
    have hsecond := congrArg (fun pair => pair.2) hpair
    exact factorization.sourceEquiv.injective (Prod.ext hfirst hsecond)



def SixVertexConfigurationPhysicalCommonFactor.lift
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    (factorization : SixVertexConfigurationPhysicalCommonFactor
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      largeT largeMiddle hlarge_pos hlarge_lt where
  branch choice := factorization.liftBranch embeddings choice
  distinct source := by
    intro heq
    apply embeddings.distinct (factorization.sourceEquiv source).1
    have hpair := congrArg factorization.targetEquiv heq
    simpa [SixVertexConfigurationPhysicalCommonFactor.liftBranch] using
      congrArg Prod.fst hpair
  aggregateTotalC source := by
    have hsmall := embeddings.aggregateTotalC
      (factorization.sourceEquiv source).1
    rw [factorization.source_totalC,
      factorization.target_totalC, factorization.target_totalC]
    simp [SixVertexConfigurationPhysicalCommonFactor.liftBranch]
    omega





structure SixVertexConfigurationPhysicalFiberExtension
    (smallT largeT : EvenTorus)
    (smallMiddle : Fin (smallT.width + 1))
    (largeMiddle : Fin (largeT.width + 1))
    (hsmall_pos : 0 < smallMiddle.val)
    (hsmall_lt : smallMiddle.val < smallT.width)
    (hlarge_pos : 0 < largeMiddle.val)
    (hlarge_lt : largeMiddle.val < largeT.width)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt) where
  SourceFiber :
    SixVertexConfigurationPhysicalSource smallT smallMiddle
      hsmall_pos hsmall_lt → Type
  TargetFiber :
    SixVertexConfigurationPhysicalTarget smallT smallMiddle → Type
  sourceEquiv :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ≃
      Sigma SourceFiber
  targetEquiv :
    SixVertexConfigurationPhysicalTarget largeT largeMiddle ≃
      Sigma TargetFiber
  sourceFiberTotalC : forall base, SourceFiber base → Nat
  targetFiberTotalC : forall base, TargetFiber base → Nat
  source_totalC : forall source,
    sixVertexConfigurationPairTotalCPhysical source =
      sixVertexConfigurationPairTotalCPhysical (sourceEquiv source).1 +
        sourceFiberTotalC (sourceEquiv source).1 (sourceEquiv source).2
  target_totalC : forall target,
    sixVertexConfigurationPairTotalCPhysical target =
      sixVertexConfigurationPairTotalCPhysical (targetEquiv target).1 +
        targetFiberTotalC (targetEquiv target).1 (targetEquiv target).2
  fiberBranch : forall choice base,
    SourceFiber base ↪ TargetFiber (embeddings.branch choice base)
  fiberAggregateTotalC : forall base fiber,
    2 * sourceFiberTotalC base fiber <=
      targetFiberTotalC (embeddings.branch false base)
          (fiberBranch false base fiber) +
        targetFiberTotalC (embeddings.branch true base)
          (fiberBranch true base fiber)


def SixVertexConfigurationPhysicalFiberExtension.liftBranch
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt}
    (extension : SixVertexConfigurationPhysicalFiberExtension
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt embeddings)
    (choice : Bool) :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ↪
      SixVertexConfigurationPhysicalTarget largeT largeMiddle :=
  extension.sourceEquiv.toEmbedding |>.trans
    (Function.Embedding.sigmaMap (embeddings.branch choice)
      (extension.fiberBranch choice)) |>.trans
    extension.targetEquiv.symm.toEmbedding

@[simp] theorem
    SixVertexConfigurationPhysicalFiberExtension.targetEquiv_liftBranch
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt}
    (extension : SixVertexConfigurationPhysicalFiberExtension
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt embeddings)
    (choice : Bool)
    (source : SixVertexConfigurationPhysicalSource largeT largeMiddle
      hlarge_pos hlarge_lt) :
    extension.targetEquiv (extension.liftBranch choice source) =
      ⟨embeddings.branch choice (extension.sourceEquiv source).1,
        extension.fiberBranch choice (extension.sourceEquiv source).1
          (extension.sourceEquiv source).2⟩ := by
  change extension.targetEquiv (extension.targetEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem SixVertexConfigurationPhysicalFiberExtension.liftBranch_totalC
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt}
    (extension : SixVertexConfigurationPhysicalFiberExtension
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt embeddings)
    (choice : Bool)
    (source : SixVertexConfigurationPhysicalSource largeT largeMiddle
      hlarge_pos hlarge_lt) :
    sixVertexConfigurationPairTotalCPhysical
        (extension.liftBranch choice source) =
      sixVertexConfigurationPairTotalCPhysical
          (embeddings.branch choice (extension.sourceEquiv source).1) +
        extension.targetFiberTotalC
          (embeddings.branch choice (extension.sourceEquiv source).1)
          (extension.fiberBranch choice
            (extension.sourceEquiv source).1
            (extension.sourceEquiv source).2) := by
  rw [extension.target_totalC]
  rw [extension.targetEquiv_liftBranch]



def SixVertexConfigurationPhysicalFiberExtension.lift
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt}
    (extension : SixVertexConfigurationPhysicalFiberExtension
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt embeddings) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      largeT largeMiddle hlarge_pos hlarge_lt where
  branch choice := extension.liftBranch choice
  distinct source := by
    intro heq
    apply embeddings.distinct (extension.sourceEquiv source).1
    have hpair := congrArg extension.targetEquiv heq
    simpa only [extension.targetEquiv_liftBranch] using
      congrArg Sigma.fst hpair
  aggregateTotalC source := by
    have hbase := embeddings.aggregateTotalC
      (extension.sourceEquiv source).1
    have hfiber := extension.fiberAggregateTotalC
      (extension.sourceEquiv source).1 (extension.sourceEquiv source).2
    have hsource := extension.source_totalC source
    have hfalse := extension.liftBranch_totalC false source
    have htrue := extension.liftBranch_totalC true source
    change 2 * sixVertexConfigurationPairTotalCPhysical source <=
      sixVertexConfigurationPairTotalCPhysical
          (extension.liftBranch false source) +
        sixVertexConfigurationPairTotalCPhysical
          (extension.liftBranch true source)
    calc
      2 * sixVertexConfigurationPairTotalCPhysical source =
          2 * (sixVertexConfigurationPairTotalCPhysical
              (extension.sourceEquiv source).1 +
            extension.sourceFiberTotalC
              (extension.sourceEquiv source).1
              (extension.sourceEquiv source).2) := by rw [hsource]
      _ = 2 * sixVertexConfigurationPairTotalCPhysical
              (extension.sourceEquiv source).1 +
            2 * extension.sourceFiberTotalC
              (extension.sourceEquiv source).1
              (extension.sourceEquiv source).2 := by omega
      _ <= (sixVertexConfigurationPairTotalCPhysical
                (embeddings.branch false
                  (extension.sourceEquiv source).1) +
              sixVertexConfigurationPairTotalCPhysical
                (embeddings.branch true
                  (extension.sourceEquiv source).1)) +
            (extension.targetFiberTotalC
                (embeddings.branch false
                  (extension.sourceEquiv source).1)
                (extension.fiberBranch false
                  (extension.sourceEquiv source).1
                  (extension.sourceEquiv source).2) +
              extension.targetFiberTotalC
                (embeddings.branch true
                  (extension.sourceEquiv source).1)
                (extension.fiberBranch true
                  (extension.sourceEquiv source).1
                  (extension.sourceEquiv source).2)) :=
        Nat.add_le_add hbase hfiber
      _ = (sixVertexConfigurationPairTotalCPhysical
                (embeddings.branch false
                  (extension.sourceEquiv source).1) +
              extension.targetFiberTotalC
                (embeddings.branch false
                  (extension.sourceEquiv source).1)
                (extension.fiberBranch false
                  (extension.sourceEquiv source).1
                  (extension.sourceEquiv source).2)) +
            (sixVertexConfigurationPairTotalCPhysical
                (embeddings.branch true
                  (extension.sourceEquiv source).1) +
              extension.targetFiberTotalC
                (embeddings.branch true
                  (extension.sourceEquiv source).1)
                (extension.fiberBranch true
                  (extension.sourceEquiv source).1
                  (extension.sourceEquiv source).2)) := by omega
      _ = sixVertexConfigurationPairTotalCPhysical
              (extension.liftBranch false source) +
            sixVertexConfigurationPairTotalCPhysical
              (extension.liftBranch true source) :=
        congrArg₂ (fun first second => first + second)
          hfalse.symm htrue.symm



def equivProdFiberTrans {A B C F G : Type}
    (first : B ≃ A × F) (second : C ≃ B × G) :
    C ≃ A × (F × G) where
  toFun value :=
    ((first (second value).1).1,
      ((first (second value).1).2, (second value).2))
  invFun value :=
    second.symm (first.symm (value.1, value.2.1), value.2.2)
  left_inv value := by simp
  right_inv value := by
    rcases value with ⟨value, factor, rest⟩
    simp



def SixVertexConfigurationPhysicalCommonFactor.trans
    {firstT secondT thirdT : EvenTorus}
    {firstMiddle : Fin (firstT.width + 1)}
    {secondMiddle : Fin (secondT.width + 1)}
    {thirdMiddle : Fin (thirdT.width + 1)}
    {hfirst_pos : 0 < firstMiddle.val}
    {hfirst_lt : firstMiddle.val < firstT.width}
    {hsecond_pos : 0 < secondMiddle.val}
    {hsecond_lt : secondMiddle.val < secondT.width}
    {hthird_pos : 0 < thirdMiddle.val}
    {hthird_lt : thirdMiddle.val < thirdT.width}
    (first : SixVertexConfigurationPhysicalCommonFactor
      firstT secondT firstMiddle secondMiddle hfirst_pos hfirst_lt
      hsecond_pos hsecond_lt)
    (second : SixVertexConfigurationPhysicalCommonFactor
      secondT thirdT secondMiddle thirdMiddle hsecond_pos hsecond_lt
      hthird_pos hthird_lt) :
    SixVertexConfigurationPhysicalCommonFactor
      firstT thirdT firstMiddle thirdMiddle hfirst_pos hfirst_lt
      hthird_pos hthird_lt where
  Factor := first.Factor × second.Factor
  sourceEquiv := equivProdFiberTrans first.sourceEquiv second.sourceEquiv
  targetEquiv := equivProdFiberTrans first.targetEquiv second.targetEquiv
  factorTotalC factor :=
    first.factorTotalC factor.1 + second.factorTotalC factor.2
  source_totalC source := by
    rw [second.source_totalC, first.source_totalC]
    simp [equivProdFiberTrans, Nat.add_assoc]
  target_totalC target := by
    rw [second.target_totalC, first.target_totalC]
    simp [equivProdFiberTrans, Nat.add_assoc]

end

end StatMech.FrontierD

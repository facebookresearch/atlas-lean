/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairResolvedInjection
import Code.FrontierD.SixVertexLoopPairBigrade











namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropResolvedLoopBridge (p : Prop) : Decidable p :=
  Classical.propDecidable p

def sixVertexResolvedLoopMarkedPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (decorated : SixVertexResolvedLoopMarkedPair T left right k) : Nat × Nat :=
  sixVertexLoopDecoratedPairBigrade decorated.1

theorem sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k) :
    sixVertexResolvedLoopMarkedPairBigrade
        (sixVertexExplicitResolvedMarkedPairEquivLoopMarked
          T left right k resolved) =
      sixVertexExplicitResolvedBigrade resolved := by
  let loopMarked := sixVertexExplicitResolvedMarkedPairEquivLoopMarked
    T left right k resolved
  let loops := loopMarked.1
  apply Prod.ext
  · change sixVertexLoopDecoratedPairTotalC loops =
      fkColoredLoopPairingPairTotalC
        (sixVertexExplicitResolvedColoredPair resolved)
    rw [← sixVertexLoopDecoratedPairColored_totalC]
    unfold fkColoredLoopPairingPairTotalC
    simp only [sixVertexLoopDecoratedPairColored_false_arrows,
      sixVertexLoopDecoratedPairColored_true_arrows,
      sixVertexExplicitResolvedColoredPair_arrows]
    change sixVertexTorusCTypeCount loops.1.1.1 +
        sixVertexTorusCTypeCount loops.1.2.1 =
      sixVertexTorusCTypeCount resolved.1.1.1.1 +
        sixVertexTorusCTypeCount resolved.1.1.2.1
    have hpair : loops.1 = resolved.1.1 := rfl
    rw [hpair]
  · change fkColoredTrueStrandSlotCount
        (sixVertexLoopDecoratedPairColored loops) =
      fkColoredTrueStrandSlotCount
        (sixVertexExplicitResolvedColoredPair resolved)
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro slot
    change (fkColoredLayeredSlotColor
        (sixVertexLoopDecoratedPairColored loops) slot = true) ↔ _
    have hcolor : fkColoredLayeredSlotColor
        (sixVertexLoopDecoratedPairColored loops) slot =
      fkColoredLayeredSlotColor
        (sixVertexExplicitResolvedColoredPair resolved) slot := by
      rcases slot with ⟨layer, v, side⟩
      cases layer <;> rfl
    simp [hcolor]

noncomputable def sixVertexExplicitResolvedBigradeFiberEquivLoopMarked
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat)
    (grade : Nat × Nat) :
    {resolved : SixVertexExplicitResolvedMarkedPair T left right k //
        sixVertexExplicitResolvedBigrade resolved = grade} ≃
      {decorated : SixVertexResolvedLoopMarkedPair T left right k //
        sixVertexResolvedLoopMarkedPairBigrade decorated = grade} :=
  Equiv.subtypeEquiv
    (sixVertexExplicitResolvedMarkedPairEquivLoopMarked T left right k)
    fun resolved => by
      rw [sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade]

noncomputable def sixVertexResolvedLoopMarkedBigradeFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat)
    (grade : Nat × Nat) :
    {decorated : SixVertexResolvedLoopMarkedPair T left right k //
        sixVertexResolvedLoopMarkedPairBigrade decorated = grade} ≃
      ({loops : SixVertexLoopDecoratedPair T left right //
          sixVertexLoopDecoratedPairBigrade loops = grade} ×
        Fin (grade.1.choose k)) where
  toFun decorated :=
    (⟨decorated.1.1, decorated.2⟩,
      Fin.cast
        (congrArg (fun g : Nat × Nat => g.1.choose k) decorated.2)
        decorated.1.2)
  invFun decorated :=
    ⟨⟨decorated.1.1,
        Fin.cast
          (congrArg (fun g : Nat × Nat => g.1.choose k)
            decorated.1.2).symm
          decorated.2⟩,
      decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      rfl
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl

theorem card_sixVertexExplicitResolvedBigradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat)
    (grade : Nat × Nat) :
    Fintype.card
        {resolved : SixVertexExplicitResolvedMarkedPair T left right k //
          sixVertexExplicitResolvedBigrade resolved = grade} =
      Fintype.card
          {loops : SixVertexLoopDecoratedPair T left right //
            sixVertexLoopDecoratedPairBigrade loops = grade} *
        grade.1.choose k := by
  rw [Fintype.card_congr
      (sixVertexExplicitResolvedBigradeFiberEquivLoopMarked
        T left right k grade),
    Fintype.card_congr
      (sixVertexResolvedLoopMarkedBigradeFiberEquiv
        T left right k grade)]
  simp


def SixVertexLoopDecoratedPairBigradeFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade,
    Fintype.card {source : SixVertexLoopDecoratedPair
        T sourceLeft sourceRight //
      sixVertexLoopDecoratedPairBigrade source = grade} <=
    Fintype.card {target : SixVertexLoopDecoratedPair
        T targetLeft targetRight //
      sixVertexLoopDecoratedPairBigrade target = grade}

theorem resolvedBigradeFibers_of_loopBigradeFibers
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (hfiber : SixVertexLoopDecoratedPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexExplicitResolvedBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  intro k grade
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card {source : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k //
      sixVertexExplicitResolvedBigrade source = grade} =
        Fintype.card
            {loops : SixVertexLoopDecoratedPair T sourceLeft sourceRight //
              sixVertexLoopDecoratedPairBigrade loops = grade} *
          grade.1.choose k :=
      card_sixVertexExplicitResolvedBigradeFiber
        T sourceLeft sourceRight k grade
    _ <= Fintype.card
            {loops : SixVertexLoopDecoratedPair T targetLeft targetRight //
              sixVertexLoopDecoratedPairBigrade loops = grade} *
          grade.1.choose k :=
      Nat.mul_le_mul_right (grade.1.choose k) (hfiber grade)
    _ = Fintype.card {target : SixVertexExplicitResolvedMarkedPair
        T targetLeft targetRight k //
      sixVertexExplicitResolvedBigrade target = grade} :=
      (card_sixVertexExplicitResolvedBigradeFiber
        T targetLeft targetRight k grade).symm



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexLoopDecoratedPairBigradeFiberDominates T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (resolvedBigradeFibers_of_loopBigradeFibers hfiber)

end

end StatMech.FrontierD

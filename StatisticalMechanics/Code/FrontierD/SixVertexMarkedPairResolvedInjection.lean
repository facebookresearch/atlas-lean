/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairExplicitDecoration
import Code.FrontierD.SixVertexColoredStrandSplice











namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropResolvedInjection (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance instFintypeExplicitMarkedDecoratedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    Fintype (SixVertexExplicitMarkedDecoratedPair T left right k) :=
  Fintype.ofEquiv (SixVertexMarkedDecoratedPair T left right k)
    (sixVertexExplicitMarkedDecoratedPairEquiv T left right k).symm


abbrev SixVertexExplicitResolvedMarkedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :=
  Sigma fun source : SixVertexExplicitMarkedDecoratedPair T left right k =>
    SixVertexExplicitMarkedResolution source.2


def sixVertexExplicitResolvedCompatiblePairing
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k)
    (layer : Bool) :
    SixVertexCompatibleLoopPairing
      (sixVertexArrowPairLayer resolved.1.1.1.1
        resolved.1.1.2.1 layer) :=
  ⟨sixVertexExplicitResolvedPairing resolved.1.2 resolved.2 layer,
    sixVertexExplicitResolvedPairing_compatible
      resolved.1.1.1.2.1 resolved.1.1.2.2.1
      resolved.1.2 resolved.2 layer⟩




def sixVertexExplicitResolvedColoredPair
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k) :
    FKColoredLoopPairingPair T := fun layer =>
  (sixVertexExplicitResolvedCompatiblePairing resolved layer).toColored



def sixVertexExplicitResolvedBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k) :
    Nat × Nat :=
  (fkColoredLoopPairingPairTotalC
      (sixVertexExplicitResolvedColoredPair resolved),
    fkColoredTrueStrandSlotCount
      (sixVertexExplicitResolvedColoredPair resolved))


def SixVertexExplicitResolvedBigradeFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall k grade,
    Nat.card {source : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k //
      sixVertexExplicitResolvedBigrade source = grade} <=
    Nat.card {target : SixVertexExplicitResolvedMarkedPair
        T targetLeft targetRight k //
      sixVertexExplicitResolvedBigrade target = grade}

@[simp] theorem sixVertexExplicitResolvedColoredPair_arrows
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k)
    (layer : Bool) :
    (sixVertexExplicitResolvedColoredPair resolved layer).arrows =
      sixVertexArrowPairLayer resolved.1.1.1.1
        resolved.1.1.2.1 layer := by
  exact SixVertexCompatibleLoopPairing.toColored_arrows _

@[simp] theorem sixVertexExplicitResolvedColoredPair_pairing
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k)
    (layer : Bool) :
    (sixVertexExplicitResolvedColoredPair resolved layer).pairing =
      sixVertexExplicitResolvedPairing
        resolved.1.2 resolved.2 layer :=
  rfl

theorem card_sixVertexExplicitResolvedMarkedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    Fintype.card
        (SixVertexExplicitResolvedMarkedPair T left right k) =
      Fintype.card
          (SixVertexExplicitMarkedDecoratedPair T left right k) * 2 ^ k := by
  rw [Fintype.card_sigma]
  simp_rw [card_sixVertexExplicitMarkedResolution]
  simp

theorem markedResolutionFactor_identity (total k : Nat) :
    (2 ^ (total - k) * total.choose k) * 2 ^ k =
      2 ^ total * total.choose k := by
  by_cases hk : k <= total
  · calc
      (2 ^ (total - k) * total.choose k) * 2 ^ k =
          (2 ^ (total - k) * 2 ^ k) * total.choose k := by
            ac_rfl
      _ = 2 ^ total * total.choose k := by
        rw [Nat.pow_sub_mul_pow 2 hk]
  · have hchoose : total.choose k = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hchoose]



abbrev SixVertexResolvedLoopMarkedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :=
  Sigma fun decorated : SixVertexLoopDecoratedPair T left right =>
    Fin ((sixVertexLoopDecoratedPairTotalC decorated).choose k)



noncomputable def sixVertexResolvedDecorationEquivLoopPairingsMarked
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) (k : Nat) :
    (Sigma fun decoration : SixVertexExplicitMarkedPairDecoration
        pair.1.1 pair.2.1 k =>
      SixVertexExplicitMarkedResolution decoration) ≃
      (Sigma fun _pairings :
          SixVertexCompatibleLoopPairing pair.1.1 ×
            SixVertexCompatibleLoopPairing pair.2.1 =>
        Fin ((sixVertexConfigurationPairTotalC pair).choose k)) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_sigma, Fintype.card_sigma]
  simp_rw [card_sixVertexExplicitMarkedResolution]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    card_sixVertexExplicitMarkedPairDecoration]
  simp only [Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_prod,
    card_sixVertexCompatibleLoopPairing pair.1.1 pair.1.2.1,
    card_sixVertexCompatibleLoopPairing pair.2.1 pair.2.2.1]
  rw [← pow_add]
  exact markedResolutionFactor_identity
    (sixVertexConfigurationPairTotalC pair) k



noncomputable def sixVertexExplicitResolvedMarkedPairEquivLoopMarked
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    SixVertexExplicitResolvedMarkedPair T left right k ≃
      SixVertexResolvedLoopMarkedPair T left right k :=
  (Equiv.sigmaAssoc fun
      (pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right)
      (decoration : SixVertexExplicitMarkedPairDecoration
        pair.1.1 pair.2.1 k) =>
      SixVertexExplicitMarkedResolution decoration).trans
    ((Equiv.sigmaCongrRight fun pair =>
      sixVertexResolvedDecorationEquivLoopPairingsMarked pair k).trans
    (Equiv.sigmaAssoc fun
      (pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right)
      (_pairings : SixVertexCompatibleLoopPairing pair.1.1 ×
        SixVertexCompatibleLoopPairing pair.2.1) =>
      Fin ((sixVertexConfigurationPairTotalC pair).choose k)).symm)

theorem card_sixVertexExplicitMarkedDecoratedPair_eq_compact
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    Fintype.card
        (SixVertexExplicitMarkedDecoratedPair T left right k) =
      Fintype.card (SixVertexMarkedDecoratedPair T left right k) :=
  Fintype.card_congr
    (sixVertexExplicitMarkedDecoratedPairEquiv T left right k)



theorem card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection
    {T : EvenTorus} {sourceLeft sourceRight targetLeft targetRight :
      Fin (T.width + 1)} {k : Nat}
    (matching : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k ->
      SixVertexExplicitResolvedMarkedPair T targetLeft targetRight k)
    (hinjective : Function.Injective matching) :
    Fintype.card
        (SixVertexMarkedDecoratedPair T sourceLeft sourceRight k) <=
      Fintype.card
        (SixVertexMarkedDecoratedPair T targetLeft targetRight k) := by
  have hresolved := Fintype.card_le_of_injective matching hinjective
  rw [card_sixVertexExplicitResolvedMarkedPair,
    card_sixVertexExplicitResolvedMarkedPair,
    card_sixVertexExplicitMarkedDecoratedPair_eq_compact,
    card_sixVertexExplicitMarkedDecoratedPair_eq_compact] at hresolved
  exact Nat.le_of_mul_le_mul_right hresolved (pow_pos (by norm_num) k)



theorem sixVertexMarkedSectorPairMass_le_of_resolvedInjection
    {T : EvenTorus} {sourceLeft sourceRight targetLeft targetRight :
      Fin (T.width + 1)} {k : Nat}
    (matching : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k ->
      SixVertexExplicitResolvedMarkedPair T targetLeft targetRight k)
    (hinjective : Function.Injective matching) :
    sixVertexMarkedSectorPairMass T sourceLeft sourceRight k <=
      sixVertexMarkedSectorPairMass T targetLeft targetRight k := by
  have hcard := card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection
    matching hinjective
  have hcardReal :
      (Fintype.card
          (SixVertexMarkedDecoratedPair T sourceLeft sourceRight k) : Real) <=
        Fintype.card
          (SixVertexMarkedDecoratedPair T targetLeft targetRight k) := by
    exact_mod_cast hcard
  simpa only [card_sixVertexMarkedDecoratedPair_eq_pairMass] using hcardReal



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (matching : forall k : Nat,
      SixVertexExplicitResolvedMarkedPair T
          ⟨middle.val - 1, by omega⟩
          ⟨middle.val + 1, by omega⟩ k ->
        SixVertexExplicitResolvedMarkedPair T middle middle k)
    (hinjective : forall k, Function.Injective (matching k)) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  intro k
  unfold sixVertexMarkedTraceLogConcavityDifference
  rw [Polynomial.coeff_sub]
  apply sub_nonneg.mpr
  have hmass := sixVertexMarkedSectorPairMass_le_of_resolvedInjection
    (matching k) (hinjective k)
  simpa only [sixVertexMarkedSectorPairMass_eq_coeff,
    Fin.val_mk, pow_two] using hmass




theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexExplicitResolvedBigradeFiberDominates T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  let witness (k : Nat) :=
    (exists_injective_bigradePreserving_iff_fiberCard
      (fun source : SixVertexExplicitResolvedMarkedPair T
          ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k =>
        sixVertexExplicitResolvedBigrade source)
      (fun target : SixVertexExplicitResolvedMarkedPair T middle middle k =>
        sixVertexExplicitResolvedBigrade target)).2 (fun grade => by
          simpa only [Nat.card_eq_fintype_card] using hfiber k grade)
  let matching (k : Nat) :
      SixVertexExplicitResolvedMarkedPair T
          ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k ->
        SixVertexExplicitResolvedMarkedPair T middle middle k :=
    Classical.choose (witness k)
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections
    T middle hmiddle_pos hmiddle_lt matching
  intro k
  exact (Classical.choose_spec (witness k)).1

end

end StatMech.FrontierD

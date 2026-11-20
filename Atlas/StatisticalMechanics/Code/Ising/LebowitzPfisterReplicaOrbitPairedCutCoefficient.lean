/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection












open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPairedCutCoefficientDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoPairedCuts
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcuts : forall
      (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
      (z : LPReplicaOffdiagDecoratedSource G sites i j q),
      LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
        G sites i j q hcard z) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  by_cases hsmall :
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2
  · exact lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two
      G sites hsite hij q hsmall
  · have hcard : 2 <=
        Fintype.card (LPReplicaOrbitCommonSlot G sites q) := by omega
    exact lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoRightPairedCuts
      G sites i j q hcard (hcuts hcard)


theorem lpReplicaAggregateProfileOrbitInequality_of_canonicalLastTwoPairedCuts
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcuts : ∀ q i j, i ≠ j -> ∀
      (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
      (z : LPReplicaOffdiagDecoratedSource G sites i j q),
      LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
        G sites i j q hcard z) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_atomCard
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoPairedCuts
    G sites hsite hij q (hcuts q i j hij)



theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_canonicalLastTwoPairedCuts
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcuts : ∀ q i j, i ≠ j -> ∀
      (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
      (z : LPReplicaOffdiagDecoratedSource G sites i j q),
      LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
        G sites i j q hcard z) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have haggregate :=
    lpReplicaAggregateProfileOrbitInequality_of_canonicalLastTwoPairedCuts
      G sites hsite beta J hf r hbeta hJ hhf hr hcuts
  have hmatch := lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr haggregate
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch

end

end StatMech.Ising

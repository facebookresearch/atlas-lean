/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedLemmaOneCardBridge
import Code.FrontierA.GrahamFourColorBalancedBridge
import Code.FrontierA.GrahamRowDataRepairRelation





open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem grahamLemmaOneMixedCoefficientWeight_summable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (j k l m : V) :
    Summable (fun total : G.edgeFinset -> Nat =>
      grahamLemmaOneMixedProfileCoefficient G total j k l m *
        weight G beta J (ofEdgeFun G total)) := by
  let f := fun z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) =>
    ((if sources G (ofEdgeFun G z.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = {k, l}
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) k m
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = ∅
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0))
  let Q := grahamPairPairEquivSigma (E := G.edgeFinset)
  have hf : Summable f := by
    let P : Current V -> Prop := fun n => ¬ CurrentConnected G n k m
    have hmix := summable_gatedSourcePairSummand G beta J {j, k} {k, l} P
    have hvac := summable_gatedSourcePairSummand G beta J ∅ ∅ (fun _ => True)
    have hp := summable_mul_of_summable_norm hmix.norm hvac.norm
    apply hp.congr
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [f, P, if_true, mul_one]
  have hfnn : forall z, 0 <= f z := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    have ha := StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G a)
    have hb := StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G b)
    have hc := StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G c)
    have hd := StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G d)
    dsimp only [f]
    split_ifs <;> positivity
  have hF : Summable (fun s => f (Q.symm s)) :=
    Q.symm.summable_iff.mpr hf
  have houter : Summable (fun total =>
      ∑' split, f (Q.symm ⟨total, split⟩)) :=
    ((summable_sigma_of_nonneg (fun s => hfnn (Q.symm s))).mp hF).2
  apply houter.congr
  intro total
  rw [tsum_fintype]
  unfold grahamLemmaOneMixedProfileCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro split hs
  dsimp [f, Q, grahamPairPairEquivSigma, grahamQuadEquivSigma]
  have hfourth :
      grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 =
        (fun e => total e - split.1.1 e - split.1.2.1 e - split.1.2.2 e) :=
    rfl
  simp only [hfourth]
  by_cases h1 : sources G (ofEdgeFun G split.1.1) = {j, k} <;>
    by_cases h2 : sources G (ofEdgeFun G split.1.2.1) = {k, l} <;>
    by_cases h3 : sources G (ofEdgeFun G split.1.2.2) = ∅ <;>
    by_cases h4 : sources G (ofEdgeFun G
      (fun e => total e - split.1.1 e - split.1.2.1 e - split.1.2.2 e)) = ∅ <;>
    by_cases h5 : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
  all_goals simp only [h1, h2, h3, h4, h5, if_true, if_false,
    not_false_eq_true, zero_mul, mul_zero, mul_one]
  simpa only [grahamFourSplitMultiplicity, mul_assoc] using
    grahamWeight_split4_eq_binom G beta J total
      split.1.1 split.1.2.1 split.1.2.2 split.2



theorem grahamWeightedLemmaOne_of_fiberMinors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (j k l m : V)
    (hminor : forall total : G.edgeFinset -> Nat,
      GrahamFiberMinor (endsM G total) Finset.univ j k l m) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m <=
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 := by
  let sep := fun total : G.edgeFinset -> Nat =>
    grahamLemmaOneSeparatedProfileCoefficient G total j k l m *
      weight G beta J (ofEdgeFun G total)
  let mix := fun total : G.edgeFinset -> Nat =>
    grahamLemmaOneMixedProfileCoefficient G total j k l m *
      weight G beta J (ofEdgeFun G total)
  have hcoeff (total : G.edgeFinset -> Nat) :
      grahamLemmaOneSeparatedProfileCoefficient G total j k l m <=
        grahamLemmaOneMixedProfileCoefficient G total j k l m := by
    rw [grahamLemmaOneSeparatedProfileCoefficient_eq_card,
      grahamLemmaOneMixedProfileCoefficient_eq_card]
    exact_mod_cast grahamLemmaOne_card_le_of_balancedMinor
      (endsM G total) Finset.univ j k l m (hminor total)
  have hpoint : forall total, sep total <= mix total := by
    intro total
    exact mul_le_mul_of_nonneg_right (hcoeff total)
      (StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _)
  have hmix : Summable mix := by
    simpa only [mix] using
      grahamLemmaOneMixedCoefficientWeight_summable
        G beta J hbeta hJ j k l m
  have hsep0 : forall total, 0 <= sep total := by
    intro total
    dsimp only [sep]
    apply mul_nonneg
    · rw [grahamLemmaOneSeparatedProfileCoefficient_eq_card]
      positivity
    · exact StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _
  have hsep : Summable sep :=
    Summable.of_nonneg_of_le hsep0 hpoint hmix
  calc
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
          sourcePairDisconnSum G beta J {k, l} ∅ k m =
        grahamLemmaOneSeparatedFourMass G beta J j k l m :=
      (grahamLemmaOneSeparatedFourMass_eq G beta J j k l m).symm
    _ = grahamLemmaOneSeparatedProfileMass G beta J j k l m :=
      grahamLemmaOneSeparatedFourMass_eq_profileMass G beta J j k l m
    _ = ∑' total, sep total := by
      simpa only [sep] using
        grahamLemmaOneSeparatedProfileMass_eq_coefficient G beta J j k l m
    _ <= ∑' total, mix total := hsep.tsum_le_tsum hpoint hmix
    _ = grahamLemmaOneMixedProfileMass G beta J j k l m := by
      simpa only [mix] using
        (grahamLemmaOneMixedProfileMass_eq_coefficient G beta J j k l m).symm
    _ = grahamLemmaOneMixedFourMass G beta J j k l m :=
      (grahamLemmaOneMixedFourMass_eq_profileMass G beta J j k l m).symm
    _ = sourcePairDisconnSum G beta J {j, k} {k, l} k m *
          currentSum G beta J ∅ ^ 2 :=
      grahamLemmaOneMixedFourMass_eq G beta J j k l m



theorem grahamWeightedLemmaOne_of_rowDataRepairHall
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (j k l m : V)
    (hhall : forall total : G.edgeFinset -> Nat,
      RowDataRepairHall (endsM G total) Finset.univ j k l m) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m <=
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 := by
  apply grahamWeightedLemmaOne_of_fiberMinors G beta J hbeta hJ
  intro total
  exact GrahamFiberMinor_of_weightedRowMinor _ _ _ _ _ _
    (GrahamWeightedRowMinor_of_rowDataRepairHall _ _ _ _ _ _ (hhall total))

end StatMech.FrontierA

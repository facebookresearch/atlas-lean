/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamLemmaOneFourColor
import Code.FrontierA.GrahamWeightedFourReplicaCore
import Code.FrontierA.GrahamWeightedFourCurrent
import Code.Sharpness.DeltaBound

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def grahamLemmaOneMixedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
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



noncomputable def grahamLemmaOneSeparatedFourMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)),
    ((if sources G (ofEdgeFun G z.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) k m
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k m
        then 1 else 0))


def grahamFourthProfile
    {E : Type*} (total a b c : E -> Nat) : E -> Nat :=
  fun e => total e - a e - b e - c e


noncomputable def grahamFourSplitMultiplicity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat)
    (split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e}) : Real :=
  ∏ e : G.edgeFinset,
    (Nat.choose (total e) (split.1.1 e) : Real) *
      (Nat.choose (total e - split.1.1 e) (split.1.2.1 e) : Real) *
      (Nat.choose (total e - split.1.1 e - split.1.2.1 e)
        (split.1.2.2 e) : Real)


noncomputable def grahamLemmaOneMixedProfileCoefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) //
    ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
    grahamFourSplitMultiplicity G total split *
      (if sources G (ofEdgeFun G split.1.1) = {j, k} then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = {k, l} then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = ∅ then 1 else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then 1 else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0)


noncomputable def grahamLemmaOneSeparatedProfileCoefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V) : Real :=
  ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) //
    ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
    grahamFourSplitMultiplicity G total split *
      (if sources G (ofEdgeFun G split.1.1) = {j, k} then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = ∅ then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = {k, l} then 1 else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then 1 else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.2.2 e +
            grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 e)) k m
        then 1 else 0)


noncomputable def grahamLemmaOneMixedProfileMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' total : G.edgeFinset -> Nat,
    ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
      (if sources G (ofEdgeFun G split.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G split.1.1) else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G split.1.2.1) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = ∅
        then weight G beta J (ofEdgeFun G split.1.2.2) else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then weight G beta J (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) else 0)


noncomputable def grahamLemmaOneSeparatedProfileMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Real :=
  ∑' total : G.edgeFinset -> Nat,
    ∑ split : {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e},
      (if sources G (ofEdgeFun G split.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G split.1.1) else 0) *
      (if sources G (ofEdgeFun G split.1.2.1) = ∅
        then weight G beta J (ofEdgeFun G split.1.2.1) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
        then 1 else 0) *
      (if sources G (ofEdgeFun G split.1.2.2) = {k, l}
        then weight G beta J (ofEdgeFun G split.1.2.2) else 0) *
      (if sources G (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅
        then weight G beta J (ofEdgeFun G
          (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => split.1.2.2 e +
            grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 e)) k m
        then 1 else 0)


theorem grahamLemmaOneMixedFourMass_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) :
    grahamLemmaOneMixedFourMass G beta J j k l m =
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 := by
  let P : Current V -> Prop := fun n => ¬ CurrentConnected G n k m
  have hmix := summable_gatedSourcePairSummand G beta J {j, k} {k, l} P
  have hvac := summable_gatedSourcePairSummand G beta J ∅ ∅ (fun _ => True)
  have hprod := summable_mul_of_summable_norm hmix.norm hvac.norm
  rw [pow_two, ← sourcePairSum_eq_mul, ← gatedSourcePairSum_true]
  rw [show sourcePairDisconnSum G beta J {j, k} {k, l} k m =
      gatedSourcePairSum G beta J {j, k} {k, l} P by rfl]
  unfold grahamLemmaOneMixedFourMass gatedSourcePairSum
  rw [Summable.tsum_mul_tsum hmix hvac hprod]
  apply tsum_congr
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp only [P, if_true, mul_one]


theorem grahamLemmaOneSeparatedFourMass_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) :
    grahamLemmaOneSeparatedFourMass G beta J j k l m =
      sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m := by
  let P : Current V -> Prop := fun n => ¬ CurrentConnected G n k m
  have hleft := summable_gatedSourcePairSummand G beta J {j, k} ∅ P
  have hright := summable_gatedSourcePairSummand G beta J {k, l} ∅ P
  have hprod := summable_mul_of_summable_norm hleft.norm hright.norm
  rw [show sourcePairDisconnSum G beta J {j, k} ∅ k m =
      gatedSourcePairSum G beta J {j, k} ∅ P by rfl]
  rw [show sourcePairDisconnSum G beta J {k, l} ∅ k m =
      gatedSourcePairSum G beta J {k, l} ∅ P by rfl]
  unfold grahamLemmaOneSeparatedFourMass gatedSourcePairSum
  rw [Summable.tsum_mul_tsum hleft hright hprod]


theorem grahamLemmaOneMixedFourMass_eq_profileMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) :
    grahamLemmaOneMixedFourMass G beta J j k l m =
      grahamLemmaOneMixedProfileMass G beta J j k l m := by
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
  have hF : Summable (fun s => f (Q.symm s)) := by
    exact Q.symm.summable_iff.mpr hf
  unfold grahamLemmaOneMixedFourMass grahamLemmaOneMixedProfileMass
  change (∑' z, f z) = _
  calc
    (∑' z, f z) = ∑' z, f (Q.symm (Q z)) := by
      apply tsum_congr
      intro z
      rw [Equiv.symm_apply_apply]
    _ = ∑' s, f (Q.symm s) := Q.tsum_eq (fun s => f (Q.symm s))
    _ = ∑' total, ∑ split, f (Q.symm ⟨total, split⟩) := by
      rw [Summable.tsum_sigma hF]
      apply tsum_congr
      intro total
      rw [tsum_fintype]
    _ = _ := by
      apply tsum_congr
      intro total
      apply Finset.sum_congr rfl
      intro split hs
      change f (Q.symm ⟨total, split⟩) = _
      dsimp [f, Q, grahamPairPairEquivSigma, grahamQuadEquivSigma,
        grahamFourthProfile]
      rw [show grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 =
          (fun e => total e - split.1.1 e - split.1.2.1 e - split.1.2.2 e) by
        rfl]
      ring


theorem grahamLemmaOneSeparatedFourMass_eq_profileMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) :
    grahamLemmaOneSeparatedFourMass G beta J j k l m =
      grahamLemmaOneSeparatedProfileMass G beta J j k l m := by
  let f := fun z : ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
      ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) =>
    ((if sources G (ofEdgeFun G z.1.1) = {j, k}
        then weight G beta J (ofEdgeFun G z.1.1) else 0) *
      (if sources G (ofEdgeFun G z.1.2) = ∅
        then weight G beta J (ofEdgeFun G z.1.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.1.1 e + z.1.2 e)) k m
        then 1 else 0)) *
    ((if sources G (ofEdgeFun G z.2.1) = {k, l}
        then weight G beta J (ofEdgeFun G z.2.1) else 0) *
      (if sources G (ofEdgeFun G z.2.2) = ∅
        then weight G beta J (ofEdgeFun G z.2.2) else 0) *
      (if ¬ CurrentConnected G
          (ofEdgeFun G (fun e => z.2.1 e + z.2.2 e)) k m
        then 1 else 0))
  let Q := grahamPairPairEquivSigma (E := G.edgeFinset)
  have hf : Summable f := by
    let P : Current V -> Prop := fun n => ¬ CurrentConnected G n k m
    have hleft := summable_gatedSourcePairSummand G beta J {j, k} ∅ P
    have hright := summable_gatedSourcePairSummand G beta J {k, l} ∅ P
    have hp := summable_mul_of_summable_norm hleft.norm hright.norm
    apply hp.congr
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  have hF : Summable (fun s => f (Q.symm s)) := by
    exact Q.symm.summable_iff.mpr hf
  unfold grahamLemmaOneSeparatedFourMass grahamLemmaOneSeparatedProfileMass
  change (∑' z, f z) = _
  calc
    (∑' z, f z) = ∑' z, f (Q.symm (Q z)) := by
      apply tsum_congr
      intro z
      rw [Equiv.symm_apply_apply]
    _ = ∑' s, f (Q.symm s) := Q.tsum_eq (fun s => f (Q.symm s))
    _ = ∑' total, ∑ split, f (Q.symm ⟨total, split⟩) := by
      rw [Summable.tsum_sigma hF]
      apply tsum_congr
      intro total
      rw [tsum_fintype]
    _ = _ := by
      apply tsum_congr
      intro total
      apply Finset.sum_congr rfl
      intro split hs
      change f (Q.symm ⟨total, split⟩) = _
      dsimp [f, Q, grahamPairPairEquivSigma, grahamQuadEquivSigma,
        grahamFourthProfile]
      have hfourth :
          grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 =
            (fun e => total e - split.1.1 e - split.1.2.1 e - split.1.2.2 e) :=
        rfl
      simp only [hfourth]
      ring



theorem grahamLemmaOneMixedProfileMass_eq_coefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) :
    grahamLemmaOneMixedProfileMass G beta J j k l m =
      ∑' total : G.edgeFinset -> Nat,
        grahamLemmaOneMixedProfileCoefficient G total j k l m *
          weight G beta J (ofEdgeFun G total) := by
  unfold grahamLemmaOneMixedProfileMass
  apply tsum_congr
  intro total
  unfold grahamLemmaOneMixedProfileCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro split hs
  by_cases h1 : sources G (ofEdgeFun G split.1.1) = {j, k} <;>
    by_cases h2 : sources G (ofEdgeFun G split.1.2.1) = {k, l} <;>
    by_cases h3 : sources G (ofEdgeFun G split.1.2.2) = ∅ <;>
    by_cases h4 : sources G (ofEdgeFun G
      (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅ <;>
    by_cases h5 : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m
  all_goals simp only [h1, h2, h3, h4, h5, if_true, if_false,
    not_false_eq_true, zero_mul, mul_zero, mul_one]
  simpa only [grahamFourSplitMultiplicity] using
    grahamWeight_split4_eq_binom G beta J total
      split.1.1 split.1.2.1 split.1.2.2 split.2



theorem grahamLemmaOneSeparatedProfileMass_eq_coefficient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) :
    grahamLemmaOneSeparatedProfileMass G beta J j k l m =
      ∑' total : G.edgeFinset -> Nat,
        grahamLemmaOneSeparatedProfileCoefficient G total j k l m *
          weight G beta J (ofEdgeFun G total) := by
  unfold grahamLemmaOneSeparatedProfileMass
  apply tsum_congr
  intro total
  unfold grahamLemmaOneSeparatedProfileCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro split hs
  by_cases h1 : sources G (ofEdgeFun G split.1.1) = {j, k} <;>
    by_cases h2 : sources G (ofEdgeFun G split.1.2.1) = ∅ <;>
    by_cases h3 : sources G (ofEdgeFun G split.1.2.2) = {k, l} <;>
    by_cases h4 : sources G (ofEdgeFun G
      (grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2)) = ∅ <;>
    by_cases h5 : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => split.1.1 e + split.1.2.1 e)) k m <;>
    by_cases h6 : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => split.1.2.2 e +
        grahamFourthProfile total split.1.1 split.1.2.1 split.1.2.2 e)) k m
  all_goals simp only [h1, h2, h3, h4, h5, h6, if_true, if_false,
    not_false_eq_true, zero_mul, mul_zero, mul_one]
  simpa only [grahamFourSplitMultiplicity] using
    grahamWeight_split4_eq_binom G beta J total
      split.1.1 split.1.2.1 split.1.2.2 split.2

end StatMech.FrontierA

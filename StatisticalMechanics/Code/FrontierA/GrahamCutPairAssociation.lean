/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamComponentAssociationReduction
import Mathlib.Combinatorics.SetFamily.FourFunctions











open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



def GrahamCutPairAssociationAt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V) : Prop :=
  (∑ S : Finset V, isingCutMass G beta J m S *
      grahamCutPairCorrelation G beta J j k S) *
      (∑ S : Finset V, isingCutMass G beta J m S *
        grahamCutPairCorrelation G beta J k l S) <=
    ∑ S : Finset V, isingCutMass G beta J m S *
      (grahamCutPairCorrelation G beta J j k S *
        grahamCutPairCorrelation G beta J k l S)



theorem grahamCutPairAssociationAt_of_cutPositiveAssociation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (j k l m : V)
    (hassoc : GrahamCutPositiveAssociation G beta J m) :
    GrahamCutPairAssociationAt G beta J j k l m := by
  exact hassoc
    (grahamCutPairCorrelation G beta J j k)
    (grahamCutPairCorrelation G beta J k l)
    (grahamCutPairCorrelation_monotone G beta J hbeta hJ j k)
    (grahamCutPairCorrelation_monotone G beta J hbeta hJ k l)





theorem grahamCutPairAssociationAt_of_fourFunctions
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (j k l m : V)
    (hfour : forall A B : Finset V,
      (isingCutMass G beta J m A *
          grahamCutPairCorrelation G beta J j k A) *
          (isingCutMass G beta J m B *
            grahamCutPairCorrelation G beta J k l B) <=
        isingCutMass G beta J m (A ∩ B) *
          (isingCutMass G beta J m (A ∪ B) *
            (grahamCutPairCorrelation G beta J j k (A ∪ B) *
              grahamCutPairCorrelation G beta J k l (A ∪ B)))) :
    GrahamCutPairAssociationAt G beta J j k l m := by
  let mu := isingCutMass G beta J m
  let f := grahamCutPairCorrelation G beta J j k
  let g := grahamCutPairCorrelation G beta J k l
  have hmu : (0 : Finset V -> Real) <= mu := by
    intro S
    unfold mu isingCutMass
    exact mul_nonneg (sq_nonneg _)
      (gatedSourcePairSum_nonneg G beta J hbeta hJ ∅ ∅
        (fun n => notConnComp G n m = S))
  have hf : (0 : Finset V -> Real) <= f := by
    intro S
    unfold f grahamCutPairCorrelation
    split
    · apply StatMech.Ising.acr_expectationJ_nonneg G beta
        (couplingIn J S) hbeta
      · intro e
        unfold couplingIn
        split <;> simp_all [hJ e]
    · exact le_rfl
  have hg : (0 : Finset V -> Real) <= g := by
    intro S
    unfold g grahamCutPairCorrelation
    split
    · apply StatMech.Ising.acr_expectationJ_nonneg G beta
        (couplingIn J S) hbeta
      · intro e
        unfold couplingIn
        split <;> simp_all [hJ e]
    · exact le_rfl
  have hff := four_functions_theorem_univ
    (mu * f) (mu * g) mu (mu * (f * g))
    (mul_nonneg hmu hf) (mul_nonneg hmu hg) hmu
    (mul_nonneg hmu (mul_nonneg hf hg)) (by
      intro A B
      simpa only [Pi.mul_apply, mu, f, g] using hfour A B)
  have hnorm := sum_isingCutMass_eq_one G beta J m
  have hnorm' : (∑ S : Finset V, mu S) = 1 := by
    simpa only [mu] using hnorm
  unfold GrahamCutPairAssociationAt
  change
    (∑ S : Finset V, mu S * f S) * (∑ S : Finset V, mu S * g S) <=
      ∑ S : Finset V, mu S * (f S * g S)
  rw [hnorm', one_mul] at hff
  exact hff




theorem grahamCutPairAssociationAt_iff_weightedLemmaOne
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V}
    (hjk : Ne j k) (hkl : Ne k l)
    (hjm : Ne j m) (hkm : Ne k m) (hlm : Ne l m) :
    GrahamCutPairAssociationAt G beta J j k l m <->
      sourcePairDisconnSum G beta J {j, k} ∅ k m *
          sourcePairDisconnSum G beta J {k, l} ∅ k m <=
        sourcePairDisconnSum G beta J {j, k} {k, l} k m *
          currentSum G beta J ∅ ^ 2 := by
  have hf := sum_cutPairCorrelation_eq_sourcePairDisconn_div
    G beta J hjk hjm hkm
  have hg := sum_cutPairCorrelation_eq_sourcePairDisconn_div
    G beta J hkl hkm hlm
  have hfg := sum_cutPairCorrelation_mul_eq_mixedDisconn_div
    G beta J (m := m) hjk hkl
  have hgate := sourcePairDisconnSum_gate_shift_left
    G beta J (m := m) (∅ : Finset V) hjk
  have hZ : 0 < currentSum G beta J ∅ :=
    StatMech.Ising.acr_currentSum_empty_pos G beta J
  unfold GrahamCutPairAssociationAt
  rw [hf, hg, hfg, hgate]
  constructor <;> intro h
  · field_simp [hZ.ne'] at h
    nlinarith
  · field_simp [hZ.ne']
    nlinarith

end StatMech.FrontierA

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamWeightedLemmaOneCardBridge
import Code.FrontierA.GrahamFourColorBalancedBridge

open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem grahamLemmaOneSeparatedProfileCoefficient_le_of_total_disconnected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V)
    (hdisc : ¬ CurrentConnected G (ofEdgeFun G total) k m) :
    grahamLemmaOneSeparatedProfileCoefficient G total j k l m <=
      grahamLemmaOneMixedProfileCoefficient G total j k l m := by
  have hcopy : ¬ RandomCurrent.connK (endsM G total)
      (Finset.univ : Finset (Copy G total)) k m := by
    rw [connK_univ_iff]
    exact hdisc
  rw [grahamLemmaOneSeparatedProfileCoefficient_eq_card,
    grahamLemmaOneMixedProfileCoefficient_eq_card]
  exact_mod_cast grahamLemmaOne_card_le_of_total_disconnected
    (endsM G total) Finset.univ j k l m hcopy



theorem not_currentConnected_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) {u v : V} (huv : ¬ G.Reachable u v) :
    ¬ CurrentConnected G n u v := by
  intro h
  exact huv (h.mono (currentSubgraph_le G n))



theorem grahamLemmaOneSeparatedProfileCoefficient_le_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) (j k l m : V)
    (hkm : ¬ G.Reachable k m) :
    grahamLemmaOneSeparatedProfileCoefficient G total j k l m <=
      grahamLemmaOneMixedProfileCoefficient G total j k l m :=
  grahamLemmaOneSeparatedProfileCoefficient_le_of_total_disconnected
    G total j k l m
      (not_currentConnected_of_not_reachable G (ofEdgeFun G total) hkm)



theorem sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A B : Finset V)
    {u v : V} (huv : ¬ G.Reachable u v) :
    sourcePairDisconnSum G beta J A B u v =
      sourcePairSum G beta J A B := by
  unfold sourcePairDisconnSum sourcePairSum
  apply tsum_congr
  rintro ⟨p, q⟩
  have hdisc : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => p e + q e)) u v :=
    not_currentConnected_of_not_reachable G _ huv
  simp only [hdisc, not_false_eq_true, if_true, mul_one]



theorem grahamWeightedLemmaOne_eq_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V)
    (hkm : ¬ G.Reachable k m) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m =
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 := by
  rw [sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable
      G beta J {j, k} ∅ hkm,
    sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable
      G beta J {k, l} ∅ hkm,
    sourcePairDisconnSum_eq_sourcePairSum_of_not_reachable
      G beta J {j, k} {k, l} hkm,
    sourcePairSum_eq_mul, sourcePairSum_eq_mul, sourcePairSum_eq_mul]
  ring


theorem grahamWeightedLemmaOne_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (j k l m : V)
    (hkm : ¬ G.Reachable k m) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m <=
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 :=
  (grahamWeightedLemmaOne_eq_of_not_reachable G beta J j k l m hkm).le

end StatMech.FrontierA

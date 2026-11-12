/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.ComparisonHolley
import Code.FK.EdgeMarginal
import Code.FK.Tilt














namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def configHammingCount (omega eta : ConfigSpace (Sym2 V)) : Nat :=
  (diffSet G omega eta).card + (diffSet G eta omega).card


theorem openCount_add_diffSet_card
    (omega eta : ConfigSpace (Sym2 V)) :
    openCount G omega + (diffSet G omega eta).card =
      openCount G eta + (diffSet G eta omega).card := by
  have hForward := openCount_sup G eta omega
  have hReverse := openCount_sup G omega eta
  have hForward' :
      openCount G (eta ⊔ omega) =
        openCount G omega + (diffSet G omega eta).card := by
    simpa only [openCount, chOpenCount, diffSet, Bool.and_eq_true,
      Bool.not_eq_true'] using hForward
  have hReverse' :
      openCount G (omega ⊔ eta) =
        openCount G eta + (diffSet G eta omega).card := by
    simpa only [openCount, chOpenCount, diffSet, Bool.and_eq_true,
      Bool.not_eq_true'] using hReverse
  rw [sup_comm] at hForward'
  exact hForward'.symm.trans hReverse'

omit [DecidableEq V] in


theorem numClustersBC_le_add_target_diffSet
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (omega eta : ConfigSpace (Sym2 V)) :
    numClustersBC G C omega <=
      numClustersBC G C eta + (diffSet G omega eta).card := by
  classical
  let S := diffSet G omega eta
  let A := openSub G omega ⊔ C
  let B := openSub G eta ⊔ C
  have hAdd := card_connectedComponent_le_sup_fromEdgeSet
    (V := V) S A
  have hB : B <= A ⊔ SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) := by
    intro x y hxy
    rw [SimpleGraph.sup_adj] at hxy ⊢
    rcases hxy with hOpen | hC
    · by_cases hSource : omega s(x, y) = true
      · left
        rw [SimpleGraph.sup_adj]
        left
        rw [openSub_adj]
        exact ⟨hOpen.1, hSource⟩
      · right
        rw [SimpleGraph.fromEdgeSet_adj]
        constructor
        · change s(x, y) ∈ (S : Set (Sym2 V))
          simp only [S, diffSet, Finset.mem_coe, Finset.mem_filter,
            SimpleGraph.mem_edgeFinset]
          exact ⟨hOpen.1, by simpa using hSource, hOpen.2⟩
        · exact hOpen.1.ne
    · left
      rw [SimpleGraph.sup_adj]
      exact Or.inr hC
  have hComponents :
      Nat.card (A ⊔ SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent <=
        Nat.card B.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.card_le_card_of_le hB
  unfold numClustersBC
  dsimp only [A, B, S] at hAdd hComponents
  omega



theorem bcScore_le_add_configHammingCount
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (omega eta : ConfigSpace (Sym2 V)) :
    openCount G omega + 2 * numClustersBC G C omega <=
      openCount G eta + 2 * numClustersBC G C eta +
        configHammingCount G omega eta := by
  have hOpen := openCount_add_diffSet_card G omega eta
  have hClusters := numClustersBC_le_add_target_diffSet G C omega eta
  unfold configHammingCount
  omega



theorem bcScore_le_add_configHammingCount_add_boundaryGap
    (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (M : Nat) (omega eta : ConfigSpace (Sym2 V))
    (hgap : numClustersBC G C eta <= numClustersBC G D eta + M) :
    openCount G omega + 2 * numClustersBC G C omega <=
      openCount G eta + 2 * numClustersBC G D eta +
        configHammingCount G omega eta + 2 * M := by
  have hScore := bcScore_le_add_configHammingCount G C omega eta
  omega

end

end StatMech.FK

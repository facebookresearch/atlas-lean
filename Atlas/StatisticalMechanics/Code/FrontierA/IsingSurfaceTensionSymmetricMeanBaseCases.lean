/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionCriticalSymmetricMean










namespace StatMech.FrontierA

open StatMech StatMech.Ising

noncomputable section


theorem fis_interface_eq_empty_of_right_empty
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K) :
    StatMech.FK.fis_interface G H K = ∅ := by
  classical
  ext e
  constructor
  · intro he
    exfalso
    rw [StatMech.FK.fis_interface, Finset.mem_sdiff,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨hK, hnot⟩ := he
    induction e using Sym2.ind with
    | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at hK hnot
        match x, y with
        | Sum.inl a, Sum.inl b => exact hnot (hcross.inl a b hK)
        | Sum.inl _, Sum.inr b => exact isEmptyElim b
        | Sum.inr a, _ => exact isEmptyElim a
  · simp


theorem unequalReplicaBridgeInteraction_eq_zero_of_right_empty
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (a : ConfigSpace V) (b : ConfigSpace W) :
    unequalReplicaBridgeInteraction G H K a b = 0 := by
  rw [unequalReplicaBridgeInteraction,
    fis_interface_eq_empty_of_right_empty G H K hcross]
  simp


theorem unequalReplicaBridgeMean_eq_zero_of_right_empty
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeMean G H K J hf hg r = 0 := by
  have hinteraction (a : ConfigSpace V) (b : ConfigSpace W) :
      unequalReplicaBridgeInteraction G H K a b = 0 :=
    unequalReplicaBridgeInteraction_eq_zero_of_right_empty
      G H K hcross a b
  simp [unequalReplicaBridgeMean, hinteraction]


instance oddPrismUpperBlockSite_zero_isEmpty :
    IsEmpty (OddPrismUpperBlockSite 0) :=
  ⟨by
    intro v
    have hz : v.1.z.val = 0 := by omega
    exact v.2 (by simp [oddPrismAtOrBelowCenter])⟩



theorem oddPrismUnequalBridgeMean_zero_prism (beta r : Real) :
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0)
        (oddPrismUnequalGlueGraph 0) beta
        (fun v => beta * oddPrismPlusField 0 v.1)
        (fun v => beta * oddPrismPlusField 0 v.1) r = 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph 0).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph 0).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph 0).Adj := Classical.decRel _
  exact unequalReplicaBridgeMean_eq_zero_of_right_empty
    (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0)
    (oddPrismUnequalGlueGraph 0)
    (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph 0)
      (oddPrismAtOrBelowCenter 0)) beta _ _ r



theorem oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism (beta : Real) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta 0 := by
  intro t _ _
  rw [oddPrismUnequalBridgeMean_zero_prism beta t,
    oddPrismUnequalBridgeMean_zero_prism beta (-t),
    oddPrismUnequalBridgeMean_zero_prism beta 0]
  norm_num



theorem oddPrismUnequalBridgeSymmetricMeanOrder_zero_coupling (n : Nat) :
    OddPrismUnequalBridgeSymmetricMeanOrder 0 n := by
  intro t ht0 ht1
  have ht : t = 0 := le_antisymm ht1 ht0
  subst t
  simp only [neg_zero, two_mul]
  exact le_rfl

end

end StatMech.FrontierA

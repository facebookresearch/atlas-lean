/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopLowTempKacWard









namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section


theorem kwg_lowTempDualSum_pos (P : PlanarZ2Subgraph) (beta : Real) :
    0 < kwg_lowTempDualSum P beta := by
  unfold kwg_lowTempDualSum
  apply Finset.sum_pos'
  · intro F _
    by_cases hF : kwg_IsEven (kwg_dualEnds P) F
    · rw [if_pos hF]
      positivity
    · rw [if_neg hF]
  · refine ⟨∅, Finset.mem_univ _, ?_⟩
    simp [kwg_IsEven]



theorem coe_isingExpectation_twoPoint_sq_eq_lowTempKacWard_detRatio
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v)
    (embedding : KWStraightLineEmbedding
      (kwg_subdivGraph (kwg_dualEnds P))) :
    (isingExpectation P.G beta 0
        (fun config => spin config u * spin config v) : Complex) ^ 2 =
      (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P))
        (kwg_subdivWeight (V := kwg_Face P)
          (fun e => kwg_pathEdgeSign P path e *
            (Real.exp (-2 * beta) : Complex)))
        embedding.turnPhase).det /
      (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P))
        (kwg_subdivWeight (V := kwg_Face P)
          (fun _ => (Real.exp (-2 * beta) : Complex)))
        embedding.turnPhase).det := by
  have hratio := isingExpectation_twoPoint_eq_kwg_lowTempDualRatio
    P beta path
  have hratioComplex :
      (isingExpectation P.G beta 0
          (fun config => spin config u * spin config v) : Complex) =
        (kwg_lowTempPathDualSum P beta path : Complex) /
          (kwg_lowTempDualSum P beta : Complex) := by
    exact_mod_cast hratio
  rw [hratioComplex, div_pow,
    kwg_lowTempPathDualSum_sq_eq_kacWard_det P beta path embedding,
    kwg_lowTempDualSum_sq_eq_kacWard_det P beta embedding]

end

end StatMech.Onsager

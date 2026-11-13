/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryCycleCompanion











namespace StatMech.FrontierD

noncomputable section



def FKRectPrimalBoundaryCompanionUnique
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall (x : R.Vertex)
    (C D E : FKRectConfigurationBlackBoundaryCycle R omega),
    C ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega x ->
    D ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega x ->
    E ∈ fkRectPrimalClusterNonzeroBoundaryCycles R omega x ->
    D ≠ C -> E ≠ C -> D = E


theorem fkRectPrimalBoundaryCompanionUnique_of_card_nonzero_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (hcard : forall x : R.Vertex,
      (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card <= 2) :
    FKRectPrimalBoundaryCompanionUnique R omega := by
  classical
  intro x C D E hC hD hE hDC hEC
  by_contra hDE
  let T : Finset (FKRectConfigurationBlackBoundaryCycle R omega) :=
    {C, D, E}
  have hTsub : T ⊆ fkRectPrimalClusterNonzeroBoundaryCycles R omega x := by
    intro A hA
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact hC
    · exact hD
    · exact hE
  have hTcard : T.card = 3 := by
    simp [T, Ne.symm hDC, Ne.symm hEC, hDE]
  have hle := Finset.card_le_card hTsub
  rw [hTcard] at hle
  have hxcard := hcard x
  omega



theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique
    (R : FKRectTorus) (omega : R.Configuration)
    (hunique : FKRectPrimalBoundaryCompanionUnique R omega)
    (x : R.Vertex) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card <= 2 := by
  classical
  let S := fkRectPrimalClusterNonzeroBoundaryCycles R omega x
  by_cases hS : S.Nonempty
  · obtain ⟨C, hC⟩ := hS
    have hCspec :
        fkRectBlackBoundaryCycleInPrimalCluster R omega x C ∧
          fkRectBlackBoundaryCycleWinding R omega C ≠ 0 := by
      simpa [S, fkRectPrimalClusterNonzeroBoundaryCycles] using hC
    obtain ⟨D, hDC, hDcluster, hDne⟩ :=
      exists_other_nonzero_blackBoundaryCycle_in_primalCluster
        R omega x C hCspec.1 hCspec.2
    have hD : D ∈ S := by
      simp [S, fkRectPrimalClusterNonzeroBoundaryCycles, hDcluster, hDne]
    have hsub : S ⊆ {C, D} := by
      intro E hE
      by_cases hEC : E = C
      · simp [hEC]
      · have hED : E = D := by
          exact hunique x C E D hC hE hD hEC hDC
        simp [hED]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hzero' :
        fkRectPrimalClusterNonzeroBoundaryCycles R omega x = ∅ := by
      simpa [S] using hzero
    rw [hzero']
    simp




theorem card_nonzero_le_two_iff_primalBoundaryCompanionUnique
    (R : FKRectTorus) (omega : R.Configuration) :
    (forall x : R.Vertex,
        (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card <= 2) ↔
      FKRectPrimalBoundaryCompanionUnique R omega := by
  constructor
  · exact fkRectPrimalBoundaryCompanionUnique_of_card_nonzero_le_two R omega
  · intro h x
    exact
      card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_companionUnique
        R omega h x

end

end StatMech.FrontierD

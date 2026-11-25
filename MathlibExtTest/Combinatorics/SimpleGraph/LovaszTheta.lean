/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
public import Mathlib.Combinatorics.SimpleGraph.Circulant

@[expose] public section

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

/-! Non-vacuity: the sandwich pins down theta exactly on the edgeless and complete graphs. -/

/-- The edgeless graph on three vertices has `ϑ = 3`: three independent vertices, three cliques. -/
example : lovaszTheta (⊥ : SimpleGraph (Fin 3)) = 3 := by
  apply le_antisymm
  · have hcol : (⊥ : SimpleGraph (Fin 3))ᶜ.Colorable 3 := by
      simpa using (⊤ : SimpleGraph (Fin 3)).colorable_of_fintype
    exact_mod_cast lovaszTheta_le_of_colorable hcol
  · have h := indepNum_le_lovaszTheta (⊥ : SimpleGraph (Fin 3))
    have hα : (⊥ : SimpleGraph (Fin 3)).indepNum = 3 := by
      rw [← SimpleGraph.cliqueNum_compl, compl_bot, SimpleGraph.cliqueNum_top]
      simp
    rw [hα] at h
    exact_mod_cast h

/-- The complete graph on three vertices has `ϑ = 1`. -/
example : lovaszTheta (⊤ : SimpleGraph (Fin 3)) = 1 := by
  apply le_antisymm
  · have hcol : (⊤ : SimpleGraph (Fin 3))ᶜ.Colorable 1 := by
      rw [compl_top]
      exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (by simp)⟩
    exact_mod_cast lovaszTheta_le_of_colorable hcol
  · have h := indepNum_le_lovaszTheta (⊤ : SimpleGraph (Fin 3))
    have hα : (⊤ : SimpleGraph (Fin 3)).indepNum = 1 := by
      rw [← SimpleGraph.cliqueNum_compl, compl_top, SimpleGraph.cliqueNum_bot]
    rw [hα] at h
    exact_mod_cast h

/-- The coordinate vectors form an orthogonal labeling of the edgeless graph, and Lemma 1 applies
to the whole vertex set with the all-ones handle. -/
example : ∑ v : Fin 3, cost (∑ j : Fin 3, EuclideanSpace.single j (1 : ℝ))
    (EuclideanSpace.single v (1 : ℝ)) ≤ 1 := by
  apply sum_cost_le_one (G := ⊥)
  · intro u v huv _
    rw [EuclideanSpace.inner_single_left]
    simp [Ne.symm huv]
  · exact fun _ _ _ _ _ => by simp

/-- The sandwich theorem specialised to the 5-cycle. -/
example : ((SimpleGraph.cycleGraph 5).indepNum : ℝ) ≤ lovaszTheta (SimpleGraph.cycleGraph 5) ∧
    lovaszTheta (SimpleGraph.cycleGraph 5) ≤
      ((SimpleGraph.cycleGraph 5)ᶜ.chromaticNumber.toNat : ℝ) :=
  sandwich _

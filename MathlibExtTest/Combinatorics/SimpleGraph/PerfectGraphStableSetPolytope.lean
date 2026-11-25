/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.PerfectGraphStableSetPolytope

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
open MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted

/-- The vector that splits unit mass equally between two adjacent vertices is in STAB. -/
example : (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ stab (⊤ : SimpleGraph (Fin 2)) := by
  classical
  have hperfect : IsPerfect (⊤ : SimpleGraph (Fin 2)) := by
    intro s
    let _ := Fintype.ofFinite s
    simp [SimpleGraph.induce_top, SimpleGraph.chromaticNumber_top, SimpleGraph.cliqueNum_top,
      Nat.card_eq_fintype_card]
  rw [(isPerfect_iff_stab_eq_qstab _).mp hperfect]
  refine ⟨fun _ => by norm_num, fun Q _ => ?_⟩
  have hcard : Q.card ≤ 2 := by simpa using Q.card_le_univ
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hbound : (Q.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  linarith

/-- Equality of the polytopes gives perfection even for an empty graph. -/
example (G : SimpleGraph (Fin 0)) : IsPerfect G := by
  apply (isPerfect_iff_stab_eq_qstab G).mpr
  have hstable : charVec (∅ : Finset (Fin 0)) ∈ stab G :=
    subset_convexHull ℝ _ ⟨∅, by simp, rfl⟩
  have hclique : (0 : Fin 0 → ℝ) ∈ qstab G := ⟨le_rfl, fun Q _ => by simp⟩
  ext x
  constructor
  · intro _
    rwa [Subsingleton.elim x (0 : Fin 0 → ℝ)]
  · intro _
    rwa [Subsingleton.elim x (charVec ∅)]

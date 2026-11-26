/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.PerfectGraphStableSetPolytope
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

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

-- The cliques and the independent sets of the 5-cycle have at most two vertices.
private theorem cycleGraph_five_clique_card (Q : Finset (Fin 5))
    (hQ : (SimpleGraph.cycleGraph 5).IsClique (Q : Set (Fin 5))) : Q.card ≤ 2 := by
  revert Q
  decide

private theorem cycleGraph_five_indep_card (S : Finset (Fin 5))
    (hS : (SimpleGraph.cycleGraph 5).IsIndepSet (S : Set (Fin 5))) : S.card ≤ 2 := by
  revert S
  decide

/-- The 5-cycle is not perfect: the half-weight vector satisfies every clique constraint, so it
lies in QSTAB, but its coordinates sum to `5 / 2`, while they sum to at most `2` on STAB. -/
example : ¬ IsPerfect (SimpleGraph.cycleGraph 5) := by
  classical
  rw [isPerfect_iff_stab_eq_qstab]
  intro h
  have hq : (fun _ : Fin 5 => (1 / 2 : ℝ)) ∈ qstab (SimpleGraph.cycleGraph 5) := by
    refine ⟨fun _ => by norm_num, fun Q hQ => ?_⟩
    have hcard : (Q.card : ℝ) ≤ 2 := by exact_mod_cast cycleGraph_five_clique_card Q hQ
    simp only [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hsum : stab (SimpleGraph.cycleGraph 5) ⊆ {x | ∑ v, x v ≤ 2} := by
    refine convexHull_min ?_ (convex_halfSpace_le ⟨fun x y => ?_, fun c x => ?_⟩ 2)
    · rintro _ ⟨S, hS, rfl⟩
      have hcard : (S.card : ℝ) ≤ 2 := by exact_mod_cast cycleGraph_five_indep_card S hS
      simpa [charVec, Finset.univ_inter] using hcard
    · simp [Finset.sum_add_distrib]
    · simp [Finset.mul_sum]
  have h52 := hsum (h ▸ hq)
  norm_num at h52

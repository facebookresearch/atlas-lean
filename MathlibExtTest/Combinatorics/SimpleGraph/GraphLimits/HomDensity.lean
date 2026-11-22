/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.SidorenkoFourCycle
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.Graphon
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.WeakRegularity

/-! Tests for homomorphism densities, the counting lemma and the four-cycle inequality. -/

namespace MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits

/-- The edge density of the triangle `K₃` is `6 / 9`: six of the nine maps `Fin 2 → Fin 3`
are homomorphisms of `K₂`. -/
example : homDensity (⊤ : SimpleGraph (Fin 2)) (adjWeight (⊤ : SimpleGraph (Fin 3))) = 2 / 3 := by
  rw [homDensity_top_fin_two]
  simp [adjWeight, Fin.sum_univ_three]
  norm_num

/-- The homomorphism count form: `t(K₂, K₃) = hom(K₂, K₃) / 3²`. -/
example : homDensity (⊤ : SimpleGraph (Fin 2)) (adjWeight (⊤ : SimpleGraph (Fin 3))) =
    (Nat.card ((⊤ : SimpleGraph (Fin 2)) →g (⊤ : SimpleGraph (Fin 3))) : ℝ) / 3 ^ 2 := by
  rw [homDensity_adjWeight]
  simp

/-- The counting lemma applies to a simple graph against the constant weight `1 / 2` (the expected
graph of `G(3, 1/2)`): the hypotheses are satisfiable by nondegenerate weights. -/
example (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj] :
    |homDensity F (adjWeight (⊤ : SimpleGraph (Fin 3))) - homDensity F (fun _ : Sym2 (Fin 3) => (1 / 2 : ℝ))| ≤
      F.edgeFinset.card *
        cutNorm (adjWeight (⊤ : SimpleGraph (Fin 3)) - fun _ : Sym2 (Fin 3) => (1 / 2 : ℝ)) :=
  abs_homDensity_sub_homDensity_le F _ _ (adjWeight_mem_unitInterval _)
    (fun _ => by norm_num)

/-- The edgeless graph has density `1`. -/
example : homDensity (⊥ : SimpleGraph (Fin 5)) (adjWeight (⊤ : SimpleGraph (Fin 3))) = 1 :=
  homDensity_bot _

/-- Densities of `[0, 1]`-weighted graphs lie in `[0, 1]`. -/
example (F : SimpleGraph (Fin 3)) [DecidableRel F.Adj] (G : SimpleGraph (Fin 7))
    [DecidableRel G.Adj] :
    0 ≤ homDensity F (adjWeight G) ∧ homDensity F (adjWeight G) ≤ 1 :=
  ⟨homDensity_nonneg F fun z => (adjWeight_mem_unitInterval G z).1,
    homDensity_le_one F (adjWeight_mem_unitInterval G)⟩

/-- Sidorenko's inequality for `C₄`, here in the triangle. -/
example : homDensity (⊤ : SimpleGraph (Fin 2)) (adjWeight (⊤ : SimpleGraph (Fin 3))) ^ 4 ≤
    homDensity (SimpleGraph.cycleGraph 4) (adjWeight (⊤ : SimpleGraph (Fin 3))) :=
  homDensity_cycleGraph_four_ge _

/-- A constant sequence of graphs is convergent. -/
example : IsConvergentGraphSequence (N := fun _ => 3) fun _ => (⊤ : SimpleGraph (Fin 3)) :=
  fun _ _ _ => ⟨_, tendsto_const_nhds⟩

/-- The weak regularity lemma for the triangle with `ε = 1 / 2`: a partition into at most
`4 ^ 4` classes approximating `K₃` within `‖K₃‖₂ / 2` in the cut norm. -/
example : ∃ P : Finpartition (Finset.univ : Finset (Fin 3)),
    (P.parts.card : ℝ) ≤ (4 : ℝ) ^ (1 / (1 / 2 : ℝ) ^ 2) ∧
      cutNorm (adjWeight (⊤ : SimpleGraph (Fin 3)) - partitionAverage P (adjWeight ⊤)) ≤
        1 / 2 * kernelL2Norm (adjWeight (⊤ : SimpleGraph (Fin 3))) :=
  exists_cutNorm_sub_partitionAverage_le _ (by norm_num)

/-- Refining a partition by two sets multiplies the number of its classes by at most four. -/
example (P : Finpartition (Finset.univ : Finset (Fin 5))) (S T : Finset (Fin 5)) :
    (refineBy P S T).parts.card ≤ 4 * P.parts.card :=
  card_refineBy_parts_le P S T

end MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits

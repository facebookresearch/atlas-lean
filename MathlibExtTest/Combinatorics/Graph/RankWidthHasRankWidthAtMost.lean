/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.RankWidthHasRankWidthAtMost

/-!
# Tests for rank-width bounded by clique-width

Applications to empty graphs, single vertices, and expressions using union, join, and relabelling.
-/

namespace MathlibExtTest.Combinatorics.Graph.RankWidthHasRankWidthAtMost

open SimpleGraph

example : (⊥ : SimpleGraph (Fin 0)).HasRankWidthAtMost 0 :=
  HasCliqueWidthAtMost.hasRankWidthAtMost (Or.inl inferInstance)

example : (⊤ : SimpleGraph Unit).HasRankWidthAtMost 1 :=
  (hasCliqueWidthAtMost_one_of_unique (⊤ : SimpleGraph Unit)).hasRankWidthAtMost

private def pairLabels : Unit ⊕ Unit → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

private theorem pair_expression : CWExpressible 2 (Unit ⊕ Unit) ⊤ pairLabels := by
  have h := CWExpressible.join 0 1 (by decide : (0 : Fin 2) ≠ 1)
    (CWExpressible.union (CWExpressible.vertex Unit (0 : Fin 2))
      (CWExpressible.vertex Unit (1 : Fin 2)))
  convert h using 1
  · ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      cases x <;> cases y <;> simp [fromRel_adj]
  · rfl

example : (⊤ : SimpleGraph (Unit ⊕ Unit)).HasRankWidthAtMost 2 :=
  (show (⊤ : SimpleGraph (Unit ⊕ Unit)).HasCliqueWidthAtMost 2 from
    Or.inr ⟨pairLabels, pair_expression⟩).hasRankWidthAtMost

private def triangleLabels : (Unit ⊕ Unit) ⊕ Unit → Fin 2 :=
  Sum.elim (fun _ => 0) (fun _ => 1)

private theorem triangle_expression :
    CWExpressible 2 ((Unit ⊕ Unit) ⊕ Unit) ⊤ triangleLabels := by
  have hpair := CWExpressible.relabel 1 0 pair_expression
  have h := CWExpressible.join 0 1 (by decide : (0 : Fin 2) ≠ 1)
    (CWExpressible.union hpair (CWExpressible.vertex Unit (1 : Fin 2)))
  convert h using 1
  · ext x y
    rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
      cases x <;> cases y <;> simp [fromRel_adj, pairLabels]
  · funext x
    rcases x with (x | x) | x <;> simp [pairLabels, triangleLabels]

example : (⊤ : SimpleGraph ((Unit ⊕ Unit) ⊕ Unit)).HasRankWidthAtMost 2 :=
  (show (⊤ : SimpleGraph ((Unit ⊕ Unit) ⊕ Unit)).HasCliqueWidthAtMost 2 from
    Or.inr ⟨triangleLabels, triangle_expression⟩).hasRankWidthAtMost

end MathlibExtTest.Combinatorics.Graph.RankWidthHasRankWidthAtMost

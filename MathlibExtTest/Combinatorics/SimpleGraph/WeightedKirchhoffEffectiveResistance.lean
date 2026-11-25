/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.WeightedKirchhoffEffectiveResistance
import MathlibExt.Combinatorics.EndpointMapMultigraph.DartLaplacian
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # A triangle with unequal edge conductances -/

namespace MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
open EndpointMapMultigraph Matrix

private def conductance (e : Sym2 (Fin 3)) : ℝ :=
  if e = s(0, 1) then 2 else 1

/-- The two trees containing the doubled edge have weight two each, and the third weight one. -/
example :
    (∑ᶠ T : {T : (⊤ : SimpleGraph (Fin 3)).Subgraph // IsSpanningTree T ∧ T.Adj 0 1},
        ∏ᶠ e ∈ T.1.edgeSet, conductance e) /
      (∑ᶠ T : {T : (⊤ : SimpleGraph (Fin 3)).Subgraph // IsSpanningTree T},
        ∏ᶠ e ∈ T.1.edgeSet, conductance e) = 4 / 5 := by
  let G : SimpleGraph (Fin 3) := ⊤
  let d (x y : Fin 3) (h : x ≠ y) : G.Dart := ⟨(x, y), h⟩
  let darts : Fin 6 → G.Dart := ![d 0 1 (by decide), d 1 0 (by decide),
    d 0 2 (by decide), d 2 0 (by decide), d 1 2 (by decide), d 2 1 (by decide)]
  have hbij : Function.Bijective darts := by
    constructor
    · change ∀ i j, darts i = darts j → i = j
      decide +revert
    · change ∀ e, ∃ i, darts i = e
      decide +revert
  have sum_darts (w : G.Dart → ℝ) : ∑ e, w e = ∑ i, w (darts i) :=
    (Fintype.sum_bijective darts hbij _ _ (fun _ => rfl)).symm
  let f : Fin 3 → ℝ := ![2 / 5, 0, 1 / 5]
  have huv : G.Adj 0 1 := by decide
  have hc (e : Sym2 (Fin 3)) : 0 < conductance e := by unfold conductance; split <;> norm_num
  have hf : laplacian (fun e : G.Dart => e.fst) (fun e => e.snd)
      (fun e => conductance e.edge / 2) *ᵥ f = Pi.single 0 1 - Pi.single 1 1 := by
    funext x
    fin_cases x <;>
      norm_num [Matrix.mulVec, dotProduct, laplacian_apply, sum_darts, Fin.sum_univ_succ,
        darts, d, f, orientedIncidence_apply, conductance, Sym2.eq_iff, Pi.single_apply]
  rw [weighted_spanningTree_adj_div G SimpleGraph.connected_top conductance (fun e _ => hc e) huv,
    (effectiveResistance_eq_sub_of_laplacian_mulVec _ _
      (fun e : G.Dart => (half_pos (hc e.edge)).le) huv.ne hf).1]
  norm_num [conductance, f]

end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

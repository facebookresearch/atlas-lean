/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Choose.Cast
import MathlibExt.Combinatorics.SimpleGraph.CutMoments

open Finset

namespace CutMomentsTest

/-! ### The subset-count helper, including the zero branch -/

/-- Three-element subsets of `Fin 5` containing `{0, 1}` and avoiding `{2}`:
the free element is `3` or `4`. -/
example : #{S ∈ (univ : Finset (Fin 5)).powersetCard 3 |
    ({0, 1} : Finset (Fin 5)) ⊆ S ∧ Disjoint S {2}} = 2 := by
  rw [card_powersetCard_filter_subset_disjoint (by decide) (by decide)]
  decide

/-- With `t = 1` and two prescribed inside vertices the count is `0`, not the
truncated `choose _ 0 = 1`. -/
example : #{S ∈ (univ : Finset (Fin 5)).powersetCard 1 |
    ({0, 1} : Finset (Fin 5)) ⊆ S ∧ Disjoint S {2}} = 0 := by
  rw [card_powersetCard_filter_subset_disjoint_eq_ite]
  decide

/-- Overlapping prescribed sets give `0`. -/
example : #{S ∈ (univ : Finset (Fin 5)).powersetCard 2 |
    ({0} : Finset (Fin 5)) ⊆ S ∧ Disjoint S {0, 1}} = 0 := by
  rw [card_powersetCard_filter_subset_disjoint_eq_ite]
  decide

/-! ### Two disjoint edges on four vertices, `t = 2` -/

/-- The graph on `Fin 4` with edges `01` and `23`. -/
def twoEdges : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun i j => i.val / 2 = j.val / 2

instance : DecidableRel twoEdges.Adj := fun i j =>
  inferInstanceAs
    (Decidable (i ≠ j ∧ (i.val / 2 = j.val / 2 ∨ j.val / 2 = i.val / 2)))

lemma twoEdges_card_edgeFinset : #twoEdges.edgeFinset = 2 := by decide

lemma twoEdges_degree (v : Fin 4) : twoEdges.degree v = 1 := by
  revert v; decide

/-- Brute force: the cut sizes of the six `2`-subsets add up to `8`. -/
lemma twoEdges_sum_brute :
    ∑ S ∈ (univ : Finset (Fin 4)).powersetCard 2,
      #(twoEdges.interedges S Sᶜ) = 8 := by decide

/-- Brute force: their squares add up to `16`, so `E[R²] = 8/3`. -/
lemma twoEdges_sum_sq_brute :
    ∑ S ∈ (univ : Finset (Fin 4)).powersetCard 2,
      #(twoEdges.interedges S Sᶜ) ^ 2 = 16 := by decide

/-- The exact sum theorem reproduces the brute-force value. -/
example : 2 * #twoEdges.edgeFinset * (Fintype.card (Fin 4) - 2).choose (2 - 1)
    = 8 := by
  rw [← twoEdges.sum_card_interedges_compl_powersetCard (by norm_num)]
  exact twoEdges_sum_brute

/-- The variance theorem gives `8/9` here (`E[R] = 4/3`, `E[R²] = 8/3`). -/
example :
    (∑ S ∈ (univ : Finset (Fin 4)).powersetCard 2,
        ((#(twoEdges.interedges S Sᶜ) : ℝ) -
          (∑ T ∈ (univ : Finset (Fin 4)).powersetCard 2,
            (#(twoEdges.interedges T Tᶜ) : ℝ)) /
            (Fintype.card (Fin 4)).choose 2) ^ 2) /
        (Fintype.card (Fin 4)).choose 2 = 8 / 9 := by
  rw [twoEdges.variance_card_interedges_compl_powersetCard (by simp)
    (by norm_num) (by simp)]
  simp only [twoEdges_card_edgeFinset, twoEdges_degree, Fintype.card_fin]
  norm_num

/-- The mean theorem gives `4/3` here. -/
example :
    (∑ S ∈ (univ : Finset (Fin 4)).powersetCard 2,
        (#(twoEdges.interedges S Sᶜ) : ℝ)) /
        (Fintype.card (Fin 4)).choose 2 = 4 / 3 := by
  rw [twoEdges.mean_card_interedges_compl_powersetCard (by norm_num)
    (by simp)]
  simp only [twoEdges_card_edgeFinset, Fintype.card_fin]
  norm_num

/-! ### The complete graph: the variance is `0` -/

/-- For `K_n` the cut size is constant, and the variance formula gives `0`. -/
example (n t : ℕ) (hn : 4 ≤ n) (ht : 1 ≤ t) (htn : t < n) :
    (∑ S ∈ (univ : Finset (Fin n)).powersetCard t,
        ((#((⊤ : SimpleGraph (Fin n)).interedges S Sᶜ) : ℝ) -
          (∑ T ∈ (univ : Finset (Fin n)).powersetCard t,
            (#((⊤ : SimpleGraph (Fin n)).interedges T Tᶜ) : ℝ)) /
            (Fintype.card (Fin n)).choose t) ^ 2) /
        (Fintype.card (Fin n)).choose t = 0 := by
  rw [SimpleGraph.variance_card_interedges_compl_powersetCard _
    (by simpa using hn) ht (by simpa using htn)]
  have hM : ((#(⊤ : SimpleGraph (Fin n)).edgeFinset : ℕ) : ℝ) =
      n * (n - 1) / 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
      Nat.cast_choose_two ℝ]
  have hd : ∀ v : Fin n, ((⊤ : SimpleGraph (Fin n)).degree v : ℝ) = n - 1 := by
    intro v
    rw [SimpleGraph.complete_graph_degree, Fintype.card_fin]
    have : 1 ≤ n := by omega
    push_cast [this]
    ring
  simp only [hM, hd, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (n : ℝ) ≠ 0 := by linarith
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (n : ℝ) - 3 ≠ 0 := by linarith
  field_simp
  ring

/-! ### `t = 1`: the variance of the degree of a uniform vertex -/

/-- With `t = 1` the formula reduces to `S₂ / n - (2M / n) ^ 2`. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 4 ≤ Fintype.card V) :
    (∑ S ∈ (univ : Finset V).powersetCard 1,
        ((#(G.interedges S Sᶜ) : ℝ) -
          (∑ T ∈ (univ : Finset V).powersetCard 1,
            (#(G.interedges T Tᶜ) : ℝ)) / (Fintype.card V).choose 1) ^ 2) /
        (Fintype.card V).choose 1 =
      (∑ v, (G.degree v : ℝ) ^ 2) / Fintype.card V -
        (2 * #G.edgeFinset / Fintype.card V) ^ 2 := by
  rw [G.variance_card_interedges_compl_powersetCard hn le_rfl (by omega)]
  have h4 : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have h0 : (Fintype.card V : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-! ### The mean on small vertex sets (`n = 2`, `n = 3`) -/

/-- `n = 2`, `t = 1`, one edge: the single edge is always cut. -/
example :
    (∑ S ∈ (univ : Finset (Fin 2)).powersetCard 1,
        (#((⊤ : SimpleGraph (Fin 2)).interedges S Sᶜ) : ℝ)) /
        (Fintype.card (Fin 2)).choose 1 = 1 := by
  rw [SimpleGraph.mean_card_interedges_compl_powersetCard _ le_rfl (by simp)]
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

/-- `n = 3`, `t = 1`, the triangle: every vertex has degree `2`. -/
example :
    (∑ S ∈ (univ : Finset (Fin 3)).powersetCard 1,
        (#((⊤ : SimpleGraph (Fin 3)).interedges S Sᶜ) : ℝ)) /
        (Fintype.card (Fin 3)).choose 1 = 2 := by
  rw [SimpleGraph.mean_card_interedges_compl_powersetCard _ le_rfl (by simp)]
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

end CutMomentsTest

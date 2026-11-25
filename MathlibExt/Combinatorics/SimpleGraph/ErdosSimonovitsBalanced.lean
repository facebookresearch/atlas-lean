/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/1077.lean` (Formal Conjectures), for the claim and its negation.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Balanced
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The Erdős–Simonovits balanced subgraph claim

`mainPositive_refuted` disproves the proposed vertex bound by concentrating the edges of a
complete bipartite graph on a small fraction of the vertices.
-/

@[expose] public section

open Filter

namespace MathlibExt.GraphTheory.ErdosProblem1077Wanted

open Classical in
/-- **Erdős–Simonovits balanced subgraph claim.** For all reals $\varepsilon$ and $\alpha$ with
$0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all sufficiently large real $D$ and then all
sufficiently large $n$, every simple graph $G$ on the vertex set $\{0, \dots, n-1\}$ with more
than $n^{1+\alpha}$ edges has a (not necessarily induced) subgraph $H$ with some number $m$ of
vertices such that $H$ is $D$-balanced (its maximum degree is at most $D$ times its minimum
degree), $m > n^{1-\alpha}$, and $H$ has more than $\varepsilon m^{1+\alpha}$ edges.

This claim (Erdős Problem 1077) is false. -/
def mainPositive : Prop :=
  ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 → ∀ᶠ D in atTop, ∀ᶠ n in atTop,
    ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
      ∃ (H : SimpleGraph.Subgraph G),
        letI m := H.verts.ncard
        SimpleGraph.IsBalanced H.coe D ∧
        m > (n : ℝ) ^ (1 - α) ∧
        H.edgeSet.ncard > ε * m ^ (1 + α)

/-- **Negation of the Erdős–Simonovits balanced subgraph claim.** The proposition that the
Erdős–Simonovits balanced subgraph claim fails, that is, that it is not the case that for all
reals $\varepsilon$ and $\alpha$ with $0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all
sufficiently large real $D$ and then all sufficiently large $n$, every simple graph $G$ on the
vertex set $\{0, \dots, n-1\}$ with more than $n^{1+\alpha}$ edges has a (not necessarily
induced) subgraph $H$ with some number $m$ of vertices such that $H$ is $D$-balanced (its maximum
degree is at most $D$ times its minimum degree), $m > n^{1-\alpha}$, and $H$ has more than
$\varepsilon m^{1+\alpha}$ edges. -/
def disprovedMain : Prop := ¬ mainPositive

open Classical in
private lemma verts_subset_support_of_balanced {V : Type*} [Fintype V] {G : SimpleGraph V}
    (H : G.Subgraph) {D : ℝ} (hbal : H.coe.IsBalanced D) (he : 0 < H.edgeSet.ncard) :
    H.verts ⊆ G.support := by
  classical
  have hmin : H.coe.minDegree ≠ 0 := by
    intro hzero
    have hbot : H.coe = ⊥ := by simpa [SimpleGraph.IsBalanced, hzero] using hbal
    rw [← H.image_coe_edgeSet_coe, hbot] at he
    simp at he
  intro v hv
  let u : H.verts := ⟨v, hv⟩
  have : Nonempty H.verts := ⟨u⟩
  have hall : H.coe.support = Set.univ := by
    by_contra h
    exact hmin (SimpleGraph.minDegree_eq_zero_iff_support_ne.mpr h)
  obtain ⟨w, huw⟩ := H.coe.mem_support.mp (hall ▸ Set.mem_univ u)
  exact (H.coe_adj_sub u w huw).mem_support_left

/--
**The Erdős–Simonovits balanced subgraph claim is false.** It is not the case that for all reals
$\varepsilon$ and $\alpha$ with $0 < \varepsilon < 1$ and $0 < \alpha < 1$, for all sufficiently
large real $D$ and then all sufficiently large $n$, every simple graph $G$ on the vertex set
$\{0, \dots, n-1\}$ with more than $n^{1+\alpha}$ edges has a (not necessarily induced) subgraph
$H$ with some number $m$ of vertices such that $H$ is $D$-balanced (its maximum degree is at most
$D$ times its minimum degree), $m > n^{1-\alpha}$, and $H$ has more than $\varepsilon m^{1+\alpha}$
edges.

The disproof uses a bipartite witness: the requirement $m > n^{1-\alpha}$ is too strong, and the
correct order is $n^{\alpha}$ per Jun Gao and Jiang–Longbrake [JiLo25], per erdosproblems.com/1077.

Source:
External Lean disproof of Erdos Problem 1077, plby/lean-proofs at commit
dfe2d78128b493c572cf525b1b8edf4897fb7664,
https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos1077.lean#L265.
Moved from `OpenConjectures/GraphTheory/ErdosProblem1077`.
-/
theorem mainPositive_refuted : ¬ mainPositive := by
  classical
  intro claim
  obtain ⟨D, hD⟩ := (claim (1 / 2) (by norm_num) (by norm_num)
    (1 / 6) (by norm_num) (by norm_num)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.1 hD
  let t := N + 2
  have ht : 2 ≤ t := Nat.le_add_left 2 N
  have ht₁ : 1 ≤ t := by omega
  have hparts : t ^ 4 + t ^ 4 ≤ t ^ 5 := by
    rw [pow_succ t 4, ← two_mul, mul_comm (t ^ 4)]
    exact Nat.mul_le_mul_right _ ht
  -- The two parts of size t⁴ carry all the edges.
  let A := Fin (t ^ 4)
  obtain ⟨f⟩ : Nonempty ((A ⊕ A) ↪ Fin (t ^ 6)) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa [A] using hparts.trans (pow_le_pow_right' ht₁ (by decide : 5 ≤ 6)))
  let K := completeBipartiteGraph A A
  let G := K.map f
  have hcard : G.edgeSet.ncard = t ^ 8 := by
    rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ f.sym2Map.injective,
      Set.ncard_def, SimpleGraph.encard_edgeSet_completeBipartiteGraph]
    simp [A, ← pow_add]
  have hdense : ((t ^ 6 : ℕ) : ℝ) ^ (1 + 1 / 6 : ℝ) < G.edgeSet.ncard := by
    rw [hcard, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg t)]
    norm_num
    exact_mod_cast pow_lt_pow_right₀ (by omega : 1 < t) (by decide : 7 < 8)
  have hN' : N ≤ t ^ 6 := (Nat.le_add_right N 2).trans (le_self_pow₀ ht₁ (by decide))
  obtain ⟨H, hbal, hlarge, hedges⟩ := hN _ hN' G hdense
  have hpos : 0 < H.edgeSet.ncard := by
    have h : (0 : ℝ) < H.edgeSet.ncard := lt_of_le_of_lt (by positivity) hedges
    exact_mod_cast h
  have hbound : H.verts.ncard ≤ t ^ 5 := calc
    H.verts.ncard ≤ G.support.ncard :=
      Set.ncard_le_ncard (verts_subset_support_of_balanced H hbal hpos)
    _ ≤ t ^ 4 + t ^ 4 := by
      rw [SimpleGraph.support_map, Set.ncard_image_of_injective _ f.injective]
      simpa [A, Nat.card_sum] using K.support.ncard_le_card
    _ ≤ t ^ 5 := hparts
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg t)] at hlarge
  norm_num at hlarge
  exact (not_lt_of_ge hbound) (by exact_mod_cast hlarge)

end MathlibExt.GraphTheory.ErdosProblem1077Wanted

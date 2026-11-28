/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Ramsey3/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: P. Manrique, H. Xia, S. Szeider.
The theorem statement restates the value R(3,5) = 14 in the “Known values” table at
commit e2e19eef093a77882da57f348def029533ec2d5e for the repository's graph Ramsey number.
-/

/-
Portions of this file are adapted from:

`lean/ComparatorChallenges/CycleCliqueRamsey.lean` (openai/math,
https://github.com/openai/math), revision `3344da59991ed94f9ba711217b29c1d760badfa6`.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source file and the applicable license files name no copyright holder or authors.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-!
# The Ramsey numbers R(3, 3) and R(3, 5)

Every graph on six vertices contains a triangle in the graph or its complement.
The five-cycle and its complement have no triangles, so six is sharp.

Every triangle-free graph on fourteen vertices has five independent vertices.
The circulant graph on thirteen vertices with jumps one and five shows that this bound is sharp.
Together these give `SimpleGraph.graphRamsey_three_three` and `graphRamsey_three_five`.

## References

* R. E. Greenwood and A. M. Gleason, [*Combinatorial Relations and Chromatic
  Graphs*](https://doi.org/10.4153/CJM-1955-001-4), Canadian Journal of Mathematics 7 (1955),
  1–7, Theorem 1 for R(3, 3) and §3 for R(3, 5). The six-vertex argument in §1 comes from
  the March 1953 William Lowell Putnam Mathematical Competition, as reported by L. E. Bush,
  *The William Lowell Putnam Mathematical Competition*, American Mathematical Monthly 60 (1953),
  539–542.
* OpenAI, [`OAI.CycleClique.thm_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CycleCliqueRamsey.lean#L23-L27),
  exceptional (3, 3) case. The two formulations agree because the three-cycle is the complete
  graph on three vertices (`SimpleGraph.cycleGraph_three_eq_top`).
* The Lean proof of `SimpleGraph.graphRamsey_three_three` reuses `card_lt_six` and
  `cliqueFree_of_sublists` and follows the infimum argument of `graphRamsey_three_five`
  in this module (`MathlibExt.Combinatorics.SimpleGraph.RamseyThreeFive`).
-/

namespace MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

open _root_.SimpleGraph
open MathlibExt.Combinatorics.RamseyErdosLowerBound (classicalRamsey_mono)

section UpperBound

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- All neighbors of a vertex in a triangle-free graph are independent. -/
private lemma degree_lt_of_no_indepSet [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hI : Gᶜ.CliqueFree k) (v : V) : G.degree v < k := by
  by_contra! h
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := G.neighborFinset v) h
  apply hI s
  refine ⟨(G.isClique_compl).mpr ((G.isIndepSet_neighborSet_of_triangleFree hG v).mono ?_), hcard⟩
  simpa only [← G.coe_neighborFinset v] using Finset.coe_subset.mpr hs

omit [Fintype V] in
/-- On the non-neighbors of `v`, an independent `k`-set would extend to one of size `k+1`. -/
private lemma nonneighbors {v : V} (hG : G.CliqueFree 3) (hI : Gᶜ.CliqueFree (k + 1)) :
    let H := G.induce (Gᶜ.neighborSet v)
    H.CliqueFree 3 ∧ Hᶜ.CliqueFree k := by
  classical
  let S := Gᶜ.neighborSet v
  have he : (G.induce S)ᶜ = Gᶜ.induce S := by
    ext a b
    simp [compl_adj, Subtype.ext_iff]
  refine ⟨(G.cliqueFree_induce_iff S 3).2 hG.cliqueFreeOn, ?_⟩
  change (G.induce S)ᶜ.CliqueFree k
  rw [he, cliqueFree_induce_iff]
  exact fun _ hs hc => hI _ (hc.insert fun b hb => hs hb)

private lemma card_lt_six (hG : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 3) :
    Fintype.card V < 6 := by
  classical
  by_contra! h
  have ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hd := degree_lt_of_no_indepSet hG hI v
  have hc := degree_lt_of_no_indepSet hI (by simpa only [compl_compl] using hG) v
  rw [degree_compl] at hc
  omega

private lemma card_lt_nine (hG : G.CliqueFree 3) (hI : Gᶜ.CliqueFree 4) :
    Fintype.card V < 9 := by
  classical
  by_contra! h
  -- Each vertex has at most three neighbors and at most five non-neighbors.
  have bounds (v : V) : G.degree v = 3 ∧ Fintype.card V = 9 := by
    have hd := degree_lt_of_no_indepSet hG hI v
    obtain ⟨ht, hi⟩ := nonneighbors (v := v) hG hI
    have hc := card_lt_six ht hi
    rw [card_neighborSet_eq_degree, degree_compl] at hc
    omega
  have ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  -- A cubic graph on nine vertices would have odd degree sum.
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [fun w => (bounds w).1, Finset.sum_const, Finset.card_univ, (bounds v).2,
    smul_eq_mul] at hsum
  omega

private lemma ramsey_at_fourteen : classicalRamsey 3 5 14 := by
  classical
  intro G
  rw [← not_cliqueFree_iff_top_isContained, ← not_cliqueFree_iff_top_isContained]
  by_contra! h
  have hd := degree_lt_of_no_indepSet h.1 h.2 0
  obtain ⟨ht, hi⟩ := nonneighbors (v := 0) h.1 h.2
  have hc := card_lt_nine ht hi
  rw [card_neighborSet_eq_degree, degree_compl, Fintype.card_fin] at hc
  omega

end UpperBound

/-- The length-`k` sublists of the vertex list contain an ordering of every `k`-set. -/
private lemma cliqueFree_of_sublists {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ((List.finRange n).sublistsLen k).all (fun l => !decide (l.Pairwise G.Adj)) = true) :
    G.CliqueFree k := by
  intro s hs
  let l := (List.finRange n).filter (· ∈ s)
  have hmem (v : Fin n) : v ∈ l ↔ v ∈ s := by simp [l]
  have he : l.toFinset = s := by ext v; simp [hmem]
  have hd : l.Nodup := (List.nodup_finRange n).filter _
  have hl : l ∈ (List.finRange n).sublistsLen k := by
    refine List.mem_sublistsLen.mpr ⟨List.filter_sublist, ?_⟩
    rw [← List.toFinset_card_of_nodup hd, he, hs.card_eq]
  have hc : l.Pairwise G.Adj := hd.imp_of_mem fun ha hb =>
    hs.isClique ((hmem _).mp ha) ((hmem _).mp hb)
  simpa [hc] using List.all_eq_true.mp h l hl

private lemma not_ramsey_at_thirteen : ¬ classicalRamsey 3 5 13 := by
  let G := circulantGraph ({1, 5} : Set (Fin 13))
  have ht : G.CliqueFree 3 := cliqueFree_of_sublists G (by decide +kernel)
  have hi : Gᶜ.CliqueFree 5 := cliqueFree_of_sublists Gᶜ (by decide +kernel)
  intro h
  exact (h G).elim (fun hc => hc.not_cliqueFree ht) (fun hc => hc.not_cliqueFree hi)

/-- **The value of $R(3, 5)$.** The classical Ramsey number $R(3, 5)$ equals $14$.

Source: Greenwood and Gleason (1955), op. cit.; Radziszowski, DS1;
OEIS A000791; listed in SqueezeBench `SqueezeBench/Problems/Ramsey3/README.md`. -/
public theorem graphRamsey_three_five : graphRamsey 3 5 = 14 := by
  rw [graphRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le ramsey_at_fourteen)
  refine le_csInf ⟨14, ramsey_at_fourteen⟩ fun n hn => ?_
  by_contra! h
  exact not_ramsey_at_thirteen (classicalRamsey_mono (by omega : n ≤ 13) hn)

end MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

namespace SimpleGraph

open MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted
  (card_lt_six cliqueFree_of_sublists)
open MathlibExt.Combinatorics.RamseyErdosLowerBound (classicalRamsey_mono)

/-- **The triangle–triangle Ramsey number is six.** Every graph on six vertices contains a
triangle or has a triangle in its complement. Five vertices do not suffice, as the cycle on
five vertices and its complement are both triangle-free. This is the exceptional triangle case
of the cycle–clique Ramsey formula, since the cycle on three vertices is the complete graph.

Source: [cycle–clique Ramsey numbers, exceptional $(3,3)$ case](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CycleCliqueRamsey.lean#L23-L27). -/
public theorem graphRamsey_three_three : graphRamsey 3 3 = 6 := by
  have h₆ : classicalRamsey 3 3 6 := by
    intro G
    rw [← not_cliqueFree_iff_top_isContained, ← not_cliqueFree_iff_top_isContained]
    by_contra! h
    exact (Nat.lt_irrefl 6) (by simpa only [Fintype.card_fin] using card_lt_six h.1 h.2)
  have h₅ : ¬ classicalRamsey 3 3 5 := by
    intro h
    have ht : (cycleGraph 5).CliqueFree 3 := cliqueFree_of_sublists _ (by decide +kernel)
    have hc : (cycleGraph 5)ᶜ.CliqueFree 3 := cliqueFree_of_sublists _ (by decide +kernel)
    exact (h (cycleGraph 5)).elim (fun h => h.not_cliqueFree ht) (fun h => h.not_cliqueFree hc)
  rw [graphRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le h₆)
  refine le_csInf ⟨6, h₆⟩ fun n hn => ?_
  by_contra! h
  exact h₅ (classicalRamsey_mono (by omega : n ≤ 5) hn)

end SimpleGraph

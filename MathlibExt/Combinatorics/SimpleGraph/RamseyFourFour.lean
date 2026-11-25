/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Ramsey/README.md` (leansolving/SqueezeBench):
Copyright the SqueezeBench contributors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: P. Manrique, H. Xia, S. Szeider.
The theorem statement restates the value R(4,4) = 18 in the “Known values” table at
commit e2e19eef093a77882da57f348def029533ec2d5e for the repository's graph Ramsey number.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound

/-!
# The Ramsey number R(4, 4)

Every graph on eighteen vertices contains a clique of size four or an
independent set of size four, and the Paley graph on seventeen vertices
contains neither. Together these give `graphRamsey_four_four`.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

open _root_.SimpleGraph
open MathlibExt.Combinatorics.RamseyErdosLowerBound (classicalRamsey_mono exists_classicalRamsey)

namespace FourFour

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
  have bounds (v : V) : G.degree v = 3 ∧ Fintype.card V = 9 := by
    have hd := degree_lt_of_no_indepSet hG hI v
    obtain ⟨ht, hi⟩ := nonneighbors (v := v) hG hI
    have hc := card_lt_six ht hi
    rw [card_neighborSet_eq_degree, degree_compl] at hc
    omega
  have ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [fun w => (bounds w).1, Finset.sum_const, Finset.card_univ, (bounds v).2,
    smul_eq_mul] at hsum
  omega

end UpperBound

/-- The Ramsey property for `(4, 4)` holds at `18`: a vertex of a graph on
eighteen vertices has at least nine neighbors or at least nine non-neighbors,
and either set carries a `K_3` extending to a `K_4`, or a `K_4` in the
complement, by the bound for `(3, 4)` above. -/
private lemma ramsey_at_eighteen : classicalRamsey 4 4 18 := by
  classical
  intro G
  rw [← not_cliqueFree_iff_top_isContained, ← not_cliqueFree_iff_top_isContained]
  by_contra! h
  obtain ⟨hG, hI⟩ := h
  set S := G.neighborSet (0 : Fin 18) with hS
  set T := Gᶜ.neighborSet (0 : Fin 18) with hT
  have hcompl_induce : ∀ (H : SimpleGraph (Fin 18)) (U : Set (Fin 18)),
      (H.induce U)ᶜ = Hᶜ.induce U := by
    intro H U
    ext a b
    simp [compl_adj, Subtype.ext_iff]
  have hS3 : (G.induce S).CliqueFree 3 := by
    rw [cliqueFree_induce_iff]
    have h4 : G.CliqueFreeOn Set.univ 4 := hG.cliqueFreeOn
    have h3 := CliqueFreeOn.of_succ G h4 (Set.mem_univ (0 : Fin 18))
    simpa [hS] using h3
  have hS4 : (G.induce S)ᶜ.CliqueFree 4 := by
    rw [hcompl_induce, cliqueFree_induce_iff]
    exact hI.cliqueFreeOn
  have hcardS : Fintype.card S < 9 := card_lt_nine hS3 hS4
  have hT3 : ((G.induce T)ᶜ).CliqueFree 3 := by
    rw [hcompl_induce, cliqueFree_induce_iff]
    have h4 : Gᶜ.CliqueFreeOn Set.univ 4 := hI.cliqueFreeOn
    have h3 := CliqueFreeOn.of_succ Gᶜ h4 (Set.mem_univ (0 : Fin 18))
    simpa [hT] using h3
  have hT4 : ((G.induce T)ᶜ)ᶜ.CliqueFree 4 := by
    rw [compl_compl, cliqueFree_induce_iff]
    exact hG.cliqueFreeOn
  have hcardT : Fintype.card T < 9 := card_lt_nine hT3 hT4
  rw [card_neighborSet_eq_degree] at hcardS
  have hcardT' : Fintype.card ↥(Gᶜ.neighborSet (0 : Fin 18)) < 9 := hcardT
  rw [card_neighborSet_eq_degree, degree_compl, Fintype.card_fin] at hcardT'
  omega

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

/-- The Paley graph on seventeen vertices has no `K_4` and no independent
`4`-set, so the Ramsey property for `(4, 4)` fails at `17`. The kernel checks
every `4`-set, for the graph and for its complement (`decide +kernel`). -/
private lemma not_ramsey_at_seventeen : ¬ classicalRamsey 4 4 17 := by
  let G := circulantGraph ({1, 2, 4, 8, 9, 13, 15, 16} : Set (Fin 17))
  have ht : G.CliqueFree 4 := cliqueFree_of_sublists G (by decide +kernel)
  have hi : Gᶜ.CliqueFree 4 := cliqueFree_of_sublists Gᶜ (by decide +kernel)
  intro h
  exact (h G).elim (fun hc => hc.not_cliqueFree ht) (fun hc => hc.not_cliqueFree hi)

end FourFour

/-- **The value of $R(4, 4)$.** The classical Ramsey number $R(4, 4)$ equals $18$.

Source: R. E. Greenwood and A. M. Gleason, *Combinatorial relations and
chromatic graphs*, Canad. J. Math. 7 (1955), 1–7; S. P. Radziszowski, *Small
Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1;
listed in leansolving/SqueezeBench `SqueezeBench/Problems/Ramsey/README.md`. -/
public theorem graphRamsey_four_four : graphRamsey 4 4 = 18 := by
  rw [graphRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le FourFour.ramsey_at_eighteen)
  refine le_csInf ⟨18, FourFour.ramsey_at_eighteen⟩ fun n hn => ?_
  by_contra! h
  exact FourFour.not_ramsey_at_seventeen (classicalRamsey_mono (by omega : n ≤ 17) hn)

end MathlibExt.Combinatorics.SimpleGraph.SmallRamseyNumbersWanted

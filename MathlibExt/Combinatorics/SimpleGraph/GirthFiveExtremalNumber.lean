/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/ExGirthFive/Def.lean` and `SqueezeBench/Problems/ExGirthFive/README.md`
(leansolving/SqueezeBench, commit e2e19eef093a77882da57f348def029533ec2d5e):
the extremal-number definition and the statement of its value at fifty vertices.
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modification notice: the definition renames `f` and omits the lower cutoff at one and the
helper lemmas. The value reported in the README is stated and proved as a theorem.
SqueezeBench ships no `NOTICE` file.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

/-!
# The girth-five extremal number on fifty vertices

`girthFiveExtremalNumber_fifty` proves that a graph on fifty vertices with girth at least
five has at most 175 edges and that the Hoffman–Singleton graph attains this bound.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted

open Finset _root_.SimpleGraph

open Classical in
/-- **Girth-five extremal number.** For a natural number $n$, $\mathrm{ex}(n; \{C_3, C_4\})$
is the largest number of edges of a simple graph on $n$ vertices whose girth is at least $5$,
that is, which contains no triangle and no four-cycle (OEIS A006856). An acyclic graph has
infinite girth, so the empty graph always qualifies. -/
noncomputable def girthFiveExtremalNumber (n : ℕ) : ℕ :=
  (univ.filter fun G : SimpleGraph (Fin n) => 5 ≤ G.egirth).sup (fun G => #G.edgeFinset)

variable {V : Type*} {G : SimpleGraph V}

private lemma no_triangle (hg : 5 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hp : p.IsCycle := by
    refine Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨Walk.IsPath.mk' ?_, by simp [p]⟩
    change [b, c, a].Nodup
    simp [hbc.ne, hca.ne, hab.ne.symm]
  have h := hg.trans hp.egirth_le_length
  exact (by decide : ¬ (5 : ℕ∞) ≤ 3) h

private lemma no_quadrangle (hg : 5 ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hp : p.IsCycle := by
    refine Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨Walk.IsPath.mk' ?_, by simp [p]⟩
    change [b, c, d, a].Nodup
    simp [hbc.ne, hcd.ne, hda.ne, hab.ne.symm, hac.symm, hbd]
  have h := hg.trans hp.egirth_le_length
  exact (by decide : ¬ (5 : ℕ∞) ≤ 4) h

private lemma sum_neighbor_degrees_le [Fintype V] [DecidableRel G.Adj]
    (hg : 5 ≤ G.egirth) (u : V) :
    ∑ v ∈ G.neighborFinset u, G.degree v ≤ Fintype.card V - 1 := by
  classical
  -- Each neighbor accounts for itself and all its neighbors other than the root.
  let branch (v : V) := insert v ((G.neighborFinset v).erase u)
  have hcard v (hv : v ∈ G.neighborFinset u) : #(branch v) = G.degree v := by
    have hu := (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hv).symm
    simp [branch, card_insert_of_notMem, card_erase_add_one hu]
  have hd : (G.neighborFinset u : Set V).PairwiseDisjoint branch := by
    intro v hv w hw hvw
    have huv := (G.mem_neighborFinset _ _).mp hv
    have huw := (G.mem_neighborFinset _ _).mp hw
    apply Finset.disjoint_left.mpr
    intro x hxv hxw
    simp only [branch, mem_insert, mem_erase, mem_neighborFinset] at hxv hxw
    rcases hxv with rfl | ⟨hxu, hvx⟩ <;> rcases hxw with he | ⟨_, hwx⟩
    · exact hvw he
    · exact no_triangle hg huw hwx huv.symm
    · subst w
      exact no_triangle hg huv hvx huw.symm
    · exact no_quadrangle hg huv hvx hwx.symm huw.symm hxu.symm hvw
  have hs : (G.neighborFinset u).biUnion branch ⊆ univ.erase u := by
    intro x hx
    obtain ⟨v, hv, hx⟩ := mem_biUnion.mp hx
    rcases mem_insert.mp hx with rfl | h
    · exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hv).ne.symm, mem_univ _⟩
    · exact mem_erase.mpr ⟨(mem_erase.mp h).1, mem_univ _⟩
  simpa only [card_biUnion hd, sum_congr rfl hcard, card_erase_of_mem (mem_univ u), card_univ]
    using card_le_card hs

private lemma card_edges_le (G : SimpleGraph (Fin 50)) [DecidableRel G.Adj]
    (hg : 5 ≤ G.egirth) : #G.edgeFinset ≤ 175 := by
  classical
  have hsum := sum_le_sum (s := univ) fun u _ => sum_neighbor_degrees_le hg u
  have hsq : ∑ v, G.degree v ^ 2 ≤ 50 * 49 := by
    calc
      _ = ∑ v, ∑ _u ∈ G.neighborFinset v, G.degree v := by simp [sq]
      _ = ∑ u, ∑ v ∈ G.neighborFinset u, G.degree v :=
        sum_comm' (by simp [adj_comm, and_comm])
      _ ≤ _ := by simpa using hsum
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [G.sum_degrees_eq_twice_card_edges, card_univ, Fintype.card_fin] at hcs
  nlinarith

/-- Five pentagons and five pentagrams, joined by the rule
`(i, j) ~ (k, j + i*k)` in coordinates modulo five. -/
private def hoffmanSingletonAdj (v w : Fin 50) : Bool :=
  let i := v.val / 5
  let j := v.val % 5
  let k := w.val / 5
  let l := w.val % 5
  if i == k then
    let step := if i < 5 then 1 else 2
    (j + step) % 5 == l || (l + step) % 5 == j
  else if i < 5 && 5 ≤ k then (j + i * k) % 5 == l
  else if k < 5 && 5 ≤ i then (l + i * k) % 5 == j
  else false

private def hoffmanSingleton : SimpleGraph (Fin 50) where
  Adj v w := hoffmanSingletonAdj v w
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

private instance decAdjHoffmanSingleton : DecidableRel hoffmanSingleton.Adj :=
  fun v w => inferInstanceAs (Decidable (hoffmanSingletonAdj v w = true))

private lemma hoffmanSingleton_degree : ∀ v, hoffmanSingleton.degree v = 7 := by
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  decide +kernel

private lemma hoffmanSingleton_edges : #hoffmanSingleton.edgeFinset = 175 := by
  have hsum := hoffmanSingleton.sum_degrees_eq_twice_card_edges
  simp only [hoffmanSingleton_degree, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

-- Distinct vertices have zero common neighbors if adjacent and one otherwise.
private lemma hoffmanSingleton_commonNeighbors : ∀ v w : Fin 50, v ≠ w →
    #(hoffmanSingleton.neighborFinset v ∩ hoffmanSingleton.neighborFinset w) =
      if hoffmanSingleton.Adj v w then 0 else 1 := by
  simp only [neighborFinset_eq_filter]
  decide +kernel

private lemma hoffmanSingleton_girth : 5 ≤ hoffmanSingleton.egirth := by
  rw [le_egirth]
  intro u p hp
  change (↑(5 : ℕ) : ℕ∞) ≤ ↑p.length
  rw [ENat.natCast_le_natCast]
  by_contra! h
  have hlen := hp.three_le_length
  have mem_common {a b c} (hac : hoffmanSingleton.Adj a c) (hbc : hoffmanSingleton.Adj b c) :
      c ∈ hoffmanSingleton.neighborFinset a ∩ hoffmanSingleton.neighborFinset b := by
    simp [hac, hbc]
  rcases (show p.length = 3 ∨ p.length = 4 by omega) with h3 | h4
  · obtain ⟨f⟩ := (cycleGraph_isContained_iff (by decide : 2 < 3)).2 ⟨u, p, hp, h3⟩
    have edge (i j : Fin 3) (hij : (cycleGraph 3).Adj i j) := f.toHom.map_rel hij
    have h01 := edge 0 1 (by decide)
    have hpos := card_pos.mpr ⟨_, mem_common (edge 0 2 (by decide)) (edge 1 2 (by decide))⟩
    rw [hoffmanSingleton_commonNeighbors _ _ h01.ne] at hpos
    simp only [h01, ite_true, lt_self_iff_false] at hpos
  · obtain ⟨f⟩ := (cycleGraph_isContained_iff (by decide : 2 < 4)).2 ⟨u, p, hp, h4⟩
    have edge (i j : Fin 4) (hij : (cycleGraph 4).Adj i j) := f.toHom.map_rel hij
    have hc := hoffmanSingleton_commonNeighbors _ _ (f.injective.ne (by decide : (0 : Fin 4) ≠ 2))
    have hle : #(hoffmanSingleton.neighborFinset (f 0) ∩ hoffmanSingleton.neighborFinset (f 2))
        ≤ 1 := hc.trans_le (by split <;> decide)
    exact f.injective.ne (by decide : (1 : Fin 4) ≠ 3) (card_le_one_iff.mp hle
      (mem_common (edge 0 1 (by decide)) (edge 2 1 (by decide)))
      (mem_common (edge 0 3 (by decide)) (edge 2 3 (by decide))))

/-- **Girth-five extremal number on fifty vertices.** The girth-five extremal number
$\mathrm{ex}(50; \{C_3, C_4\})$, the largest number of edges of a simple graph on $50$
vertices that contains no triangle and no four-cycle, equals $175$.

For graphs on $n$ vertices of girth at least $5$, the Hoffman–Singleton graph attains the
Moore-type bound $\frac{n}{2} \sqrt{n - 1}$ on the number of edges, with $n = 50$.

Source: A. J. Hoffman and R. R. Singleton, *On Moore graphs with diameters 2
and 3*, IBM J. Res. Develop. 4 (1960), 497–504; OEIS A006856; listed in
SqueezeBench `SqueezeBench/Problems/ExGirthFive/README.md`. -/
theorem girthFiveExtremalNumber_fifty : girthFiveExtremalNumber 50 = 175 := by
  classical
  apply le_antisymm
  · simp only [girthFiveExtremalNumber, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
    exact fun G hg => card_edges_le G hg
  · unfold girthFiveExtremalNumber
    refine le_trans ?_ (Finset.le_sup (b := hoffmanSingleton) ?_)
    · convert hoffmanSingleton_edges.ge
    · simpa only [mem_filter, mem_univ, true_and] using hoffmanSingleton_girth

end MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted

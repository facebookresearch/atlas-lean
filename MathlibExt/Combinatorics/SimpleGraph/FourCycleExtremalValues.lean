/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/ExC4/README.md` (SqueezeBench), for the values in the statement.
Copyright the SqueezeBench contributors. Authors: P. Manrique, H. Xia, S. Szeider.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
the values below are taken from the "Known values" section of
leansolving/SqueezeBench at commit e2e19eef093a77882da57f348def029533ec2d5e
(`SqueezeBench/Problems/ExC4/README.md`; authors P. Manrique, H. Xia,
S. Szeider), distributed under the Apache License, Version 2.0. SqueezeBench
ships no `NOTICE` file. Changes made: SqueezeBench's `ExC4.f` is Mathlib's
`SimpleGraph.extremalNumber n (cycleGraph 4)` pinned to `0` at `n = 0`; the
statement uses the Mathlib function directly, and the table of values is proved here.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import all MathlibExt.Combinatorics.SimpleGraph.FourCycleProjectivePlaneExtremal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic

/-!
# Extremal numbers of the four-cycle up to twenty vertices

`extremalNumber n (cycleGraph 4)` is the largest number of edges of a graph on
`Fin n` with no (not necessarily induced) four-cycle (OEIS A006855).

`extremalNumber_cycleGraph_four_one_to_twenty` gives the first twenty positive-order values.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted

open _root_.SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

-- Count oriented edges from one vertex set to another, allowing the sets to overlap.
private def arcs (A B : Finset V) : ℕ := ∑ x ∈ A, #(G.neighborFinset x ∩ B)

private lemma arcs_comm (A B : Finset V) : arcs G A B = arcs G B A := by
  classical
  have expand (S T : Finset V) : arcs G S T = ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
    simp only [arcs, sum_boole]
    apply sum_congr rfl
    intro x _
    congr 1
    ext y
    simp [and_comm]
  rw [expand, sum_comm, expand]
  simp_rw [adj_comm]

private lemma arcs_union (A B C : Finset V) (h : Disjoint A B) :
    arcs G (A ∪ B) C = arcs G A C + arcs G B C := sum_union h

private lemma arcs_self (S : Finset V) :
    arcs G S S = 2 * #(G.induce (S : Set V)).edgeFinset := by
  classical
  rw [← sum_degrees_eq_twice_card_edges, arcs, ← sum_attach]
  apply sum_congr rfl
  intro x _
  rw [← card_neighborFinset_eq_degree]
  apply card_bij' (fun y hy => ⟨y, (mem_inter.mp hy).2⟩) (fun y _ => y.val)
  all_goals simp_all [mem_neighborFinset]

private abbrev triDegree (v : V) := arcs G (G.neighborFinset v) (G.neighborFinset v)

private def triangleGraph : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ z, G.Adj x z ∧ G.Adj y z
  symm := ⟨fun _ _ ⟨h, z, hx, hy⟩ => ⟨h.symm, z, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

open scoped Classical in
private lemma triangleGraph_degree (hf : (cycleGraph 4).Free G) (v : V) :
    (triangleGraph G).degree v = triDegree G v := by
  classical
  change _ = ∑ w ∈ G.neighborFinset v, _
  have coeff (w : V) (hw : w ∈ G.neighborFinset v) :
      #(G.neighborFinset w ∩ G.neighborFinset v) =
        if (triangleGraph G).Adj v w then 1 else 0 := by
    have hvw := (G.mem_neighborFinset _ _).mp hw
    have hb := card_inter_le_one hf hvw.ne.symm
    have hp : (triangleGraph G).Adj v w ↔ (G.neighborFinset w ∩ G.neighborFinset v).Nonempty := by
      simp [triangleGraph, hvw, Finset.Nonempty, and_comm]
    split
    · next h => have := card_pos.mpr (hp.mp h); omega
    · next h => simpa [nonempty_iff_ne_empty] using mt hp.mpr h
  rw [sum_congr rfl coeff, sum_boole]
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [mem_filter, mem_neighborFinset, iff_and_self]
  exact fun h => h.1

private lemma triDegree_sum (hf : (cycleGraph 4).Free G) : 6 ∣ ∑ v, triDegree G v := by
  classical
  let H := triangleGraph G
  have edge {x y} (h : H.Adj x y) : G.Adj x y := h.1
  have hl : H.LocallyLinear := by
    constructor
    · intro s hs t ht hst a ha b hb
      by_contra hab
      have unpack {s : Finset V} (hs : H.IsNClique 3 s) (ha : a ∈ s) (hb : b ∈ s) :
          ∃ c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
        obtain ⟨c, hc, he⟩ := exists_mem_ne (a := a) (s := s.erase b) (by
          rw [card_erase_of_mem hb, hs.card_eq]; decide)
        have hcb := (mem_erase.mp hc).1
        have hcs := (mem_erase.mp hc).2
        refine ⟨c, edge (hs.1 ha hcs he.symm), edge (hs.1 hb hcs hcb.symm), ?_⟩
        symm
        apply eq_of_subset_of_card_le (by simp [insert_subset, ha, hb, hcs])
        simp [hs.card_eq, hab, he.symm, hcb.symm]
      obtain ⟨c, hac, hbc, hs'⟩ := unpack hs ha.1 hb.1
      obtain ⟨d, had, hbd, ht'⟩ := unpack ht ha.2 hb.2
      exact hst (by rw [hs', ht', common_neighbor_unique hf hab hac hbc had hbd])
    · intro a b hab
      obtain ⟨hab', c, hac, hbc⟩ := hab
      have hac' : H.Adj a c := ⟨hac, b, hab', hbc.symm⟩
      have hbc' : H.Adj b c := ⟨hbc, a, hab'.symm, hac.symm⟩
      refine ⟨{a, b, c}, is3Clique_triple_iff.mpr ⟨?_, hac', hbc'⟩, by simp, by simp⟩
      exact ⟨hab', c, hac, hbc⟩
  simp_rw [← triangleGraph_degree G hf]
  change 6 ∣ ∑ v, H.degree v
  rw [H.sum_degrees_eq_twice_card_edges, hl.card_edgeFinset]
  exact ⟨_, by ring⟩

private def values : List ℕ :=
  [0, 0, 1, 3, 4, 6, 7, 9, 11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46]

private def bound (n : ℕ) := values[n]?.getD 0

private def floorDegree (n : ℕ) := bound n + 1 - bound (n - 1)

private lemma arcs_univ (S : Finset V) : arcs G S univ = ∑ v ∈ S, G.degree v := by
  simp [arcs]

private lemma arcs_le (S T : Finset V) (h : ∀ x ∈ S, #(G.neighborFinset x ∩ T) ≤ 1) :
    arcs G S T ≤ #S := by simpa [arcs] using sum_le_sum h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma triangleGraph_le : triangleGraph G ≤ G := fun _ _ h => h.1

-- Partition at a root into the root, its neighbors, and the remaining vertices.
private lemma root_counts (hf : (cycleGraph 4).Free G) (v : V)
    (ih : ∀ k < Fintype.card V, extremalNumber k (cycleGraph 4) ≤ bound k) :
    ∃ p, p ≤ Fintype.card V - 1 - G.degree v ∧
      (∑ w ∈ G.neighborFinset v, G.degree w) = G.degree v + triDegree G v + p ∧
      #G.edgeFinset ≤ G.degree v + triDegree G v / 2 + p +
        bound (Fintype.card V - 1 - G.degree v) := by
  classical
  let N := G.neighborFinset v
  let R := (insert v N)ᶜ
  have hv : v ∉ N := G.notMem_neighborFinset_self v
  have hr : #R = Fintype.card V - 1 - G.degree v := by
    rw [show #R = _ from card_compl _, card_insert_of_notMem hv]
    change Fintype.card V - (G.degree v + 1) = _
    omega
  have hsplit : ({v} ∪ N) ∪ R = univ := by rw [singleton_union]; exact sup_compl_eq_top
  have expand (B : Finset V) : arcs G univ B = arcs G {v} B + arcs G N B + arcs G R B := by
    conv_lhs => rw [← hsplit]
    rw [arcs_union, arcs_union]
    · simpa using hv
    · rw [singleton_union]; exact disjoint_compl_right
  have one (B : Finset V) : arcs G {v} B = #(N ∩ B) := by simp [arcs, N]
  have hNR : Disjoint N R := (disjoint_compl_right (a := insert v N)).mono_left (subset_insert v N)
  have hRN : N ∩ R = ∅ := disjoint_iff_inter_eq_empty.mp hNR
  have rootN : arcs G {v} N = G.degree v := by simp [one, N]
  have rootR : arcs G {v} R = 0 := by simp [one, hRN]
  have rootSum := expand N
  rw [arcs_comm, arcs_univ, rootN] at rootSum
  have hrSum := expand R
  rw [arcs_comm, arcs_univ, rootR, arcs_comm G N R, zero_add] at hrSum
  have total := expand univ
  rw [arcs_univ, G.sum_degrees_eq_twice_card_edges, one, inter_univ, arcs_univ, arcs_univ,
    rootSum, hrSum] at total
  have hfree : (cycleGraph 4).Free (G.induce (R : Set V)) :=
    fun h => hf (h.trans ⟨Copy.induce G _⟩)
  have he := card_edgeFinset_le_extremalNumber hfree
  rw [show Fintype.card (R : Set V) = #R from Fintype.card_coe R] at he
  have hlt := G.degree_lt_card_verts v
  have hupper := he.trans (ih #R (by omega))
  rw [hr] at hupper
  have ht := arcs_self G N
  have hu := arcs_self G R
  refine ⟨arcs G R N, ?_, rootSum, ?_⟩
  · rw [← hr]
    apply arcs_le
    intro w hw
    apply card_inter_le_one hf
    rintro rfl
    simp [R] at hw
  · change #G.edgeFinset ≤ G.degree v + arcs G N N / 2 + _ + _
    have hc : #N = G.degree v := rfl
    omega

private lemma triDegree_le (hf : (cycleGraph 4).Free G) (v : V) : triDegree G v ≤ G.degree v := by
  classical
  rw [← triangleGraph_degree G hf]
  exact degree_le_of_le (triangleGraph_le G)

-- It suffices to exclude graphs with precisely one more edge than the claimed value.
private lemma upper_of_exclude (n b : ℕ)
    (h : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (cycleGraph 4).Free G → #G.edgeFinset = b + 1 → False) :
    extremalNumber n (cycleGraph 4) ≤ b := by
  classical
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hf
  by_contra! hb
  obtain ⟨s, hs, hcard⟩ := exists_subset_card_eq hb
  let H := fromEdgeSet (s : Set (Sym2 (Fin n)))
  have hle : H ≤ G := by
    change fromEdgeSet _ ≤ G
    rw [fromEdgeSet_le]
    exact fun e he => mem_edgeFinset.mp (hs he.1)
  have he : H.edgeFinset = s := by
    ext e
    simp only [mem_edgeFinset, H, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe, and_iff_left_iff_imp]
    exact fun h => G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hs h))
  apply h H (fun h' => hf (h'.trans (IsContained.of_le hle)))
  convert (congrArg Finset.card he).trans hcard

-- Possible degrees after removing one vertex and after removing its closed neighborhood.
private def width (n : ℕ) : ℕ := if n ∈ [9, 11, 18, 19] then 1 else 0

private lemma degree_table : ∀ n d : Fin 21,
    d < n → floorDegree n ≤ d →
    d.val * floorDegree n ≤ d.val + 2 * (d.val / 2) + (n.val - 1 - d.val) →
    bound n + 1 ≤ d.val + d.val / 2 + (n.val - 1 - d.val) + bound (n.val - 1 - d.val) →
    d.val ≤ floorDegree n + width n := by decide +kernel

private lemma residual_orders : ∀ n : Fin 21,
    n.val * floorDegree n ≤ 2 * (bound n + 1) →
    2 * (bound n + 1) ≤ n.val * (floorDegree n + width n) →
    n.val ∈ [2, 8, 9, 11, 14, 18, 19] := by decide +kernel

private lemma degree_band {n : ℕ} (hn : n ≤ 20) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hf : (cycleGraph 4).Free G) (he : #G.edgeFinset = bound n + 1)
    (ih : ∀ k < n, extremalNumber k (cycleGraph 4) ≤ bound k) (v : Fin n) :
    floorDegree n ≤ G.degree v ∧ G.degree v ≤ floorDegree n + width n := by
  have lo (x : Fin n) : floorDegree n ≤ G.degree x := by
    have h := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hf x
    rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, he] at h
    have hx := x.isLt
    have := h.trans (ih _ (by omega))
    unfold floorDegree
    omega
  have hdeg := G.degree_lt_card_verts v
  rw [Fintype.card_fin] at hdeg
  obtain ⟨p, hp, hs, hb⟩ := root_counts G hf v (by simpa using ih)
  rw [Fintype.card_fin] at hp hb
  have ht := triDegree_le G hf v
  have ht2 := arcs_self G (G.neighborFinset v)
  change triDegree G v = _ at ht2
  have hmin := sum_le_sum (s := G.neighborFinset v) (fun x _ => lo x)
  simp only [sum_const, card_neighborFinset_eq_degree, smul_eq_mul, hs] at hmin
  refine ⟨lo v, degree_table ⟨n, by omega⟩ ⟨G.degree v, by omega⟩ hdeg (lo v) ?_ ?_⟩
  all_goals dsimp only
  all_goals omega

private def highVerts (l : ℕ) := univ.filter fun v => G.degree v = l + 1

private abbrev highCount (l : ℕ) (v : V) := #(G.neighborFinset v ∩ highVerts G l)

private lemma band_sum (l : ℕ) (band : ∀ v, l ≤ G.degree v ∧ G.degree v ≤ l + 1)
    (S : Finset V) : ∑ v ∈ S, G.degree v = #S * l + #(S ∩ highVerts G l) := by
  have eqn x : G.degree x = l + if x ∈ highVerts G l then 1 else 0 := by
    have := band x
    simp only [highVerts, mem_filter, mem_univ, true_and]
    split <;> omega
  simp_rw [eqn]
  rw [sum_add_distrib, sum_const, smul_eq_mul, sum_boole, filter_mem_eq_inter]
  rfl

private lemma highCount_sum (l : ℕ) :
    ∑ v, highCount G l v = #(highVerts G l) * (l + 1) := by
  change arcs G univ _ = _
  rw [arcs_comm, arcs_univ]
  apply sum_const_nat
  simp [highVerts]

private lemma full_neighbor_triangle (hf : (cycleGraph 4).Free G) {v w : V}
    (h : G.Adj v w) (hw : triDegree G w = G.degree w) : 0 < triDegree G v := by
  classical
  let H := triangleGraph G
  have hs : H.neighborFinset w = G.neighborFinset w :=
    eq_of_subset_of_card_le (fun x hx => by
      exact (G.mem_neighborFinset _ _).mpr ((H.mem_neighborFinset _ _).mp hx).1)
      (by simpa only [card_neighborFinset_eq_degree, ← hw] using (triangleGraph_degree G hf w).ge)
  have hmem : v ∈ H.neighborFinset w := hs ▸ (G.mem_neighborFinset _ _).mpr h.symm
  have hh := (H.mem_neighborFinset _ _).mp hmem
  rw [← triangleGraph_degree G hf]
  exact (H.degree_pos_iff_exists_adj v).mpr ⟨w, hh.symm⟩

-- The local profiles needed after imposing the degree band. Here t counts oriented
-- edges among the neighbors and k counts neighbors in the higher degree class.
private def profile (n d t k : ℕ) : Bool :=
  match n with
  | 8 => t == 2
  | 9 => t + 4 == 2 * d
  | 11 => if d == 4 then k == 2 && t == 4 else 0 < k && (t == 0 || 2 ≤ k)
  | 14 => false
  | 18 => d != 5 || k ≤ 1
  | 19 => d != 5 || k ≤ 2
  | _ => true

private lemma profile_table : ∀ n : Fin 21, ∀ d t k : Fin 6,
    floorDegree n ≤ d.val → d.val ≤ floorDegree n + width n →
    t.val ≤ d.val → t.val % 2 = 0 → k.val ≤ d.val →
    (width n = 0 → k.val = 0) →
    let p := d.val * floorDegree n + k.val - (d.val + t.val)
    d.val + t.val + p = d.val * floorDegree n + k.val →
    p ≤ n.val - 1 - d.val →
    bound n + 1 ≤ d.val + t.val / 2 + p + bound (n.val - 1 - d.val) →
    profile n d t k := by decide +kernel

private lemma profiles {n : ℕ} (hn : n ≤ 20) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hf : (cycleGraph 4).Free G) (he : #G.edgeFinset = bound n + 1)
    (ih : ∀ k < n, extremalNumber k (cycleGraph 4) ≤ bound k) (v : Fin n) :
    profile n (G.degree v) (triDegree G v) (highCount G (floorDegree n) v) := by
  have db := degree_band hn G hf he ih
  have dbv := db v
  have hw : width n ≤ 1 := by unfold width; split <;> decide
  have maxD : ∀ j : Fin 21, floorDegree j + width j ≤ 5 := by decide +kernel
  have hd5 := maxD ⟨n, by omega⟩
  dsimp only at hd5
  have ht := triDegree_le G hf v
  have hk : highCount G (floorDegree n) v ≤ G.degree v :=
    card_le_card inter_subset_left
  obtain ⟨p, hp, hs, hb⟩ := root_counts G hf v (by simpa using ih)
  rw [Fintype.card_fin] at hp hb
  rw [he] at hb
  rw [band_sum G (floorDegree n) (fun w => ⟨(db w).1, by have := (db w).2; omega⟩),
    card_neighborFinset_eq_degree] at hs
  change G.degree v * floorDegree n + highCount G (floorDegree n) v = _ at hs
  have ht2 := arcs_self G (G.neighborFinset v)
  change triDegree G v = _ at ht2
  have hz (h : width n = 0) : highVerts G (floorDegree n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have := (db x).2
    simp only [highVerts, mem_filter, mem_univ, true_and] at hx
    omega
  apply profile_table ⟨n, by omega⟩ ⟨G.degree v, by omega⟩ ⟨triDegree G v, by omega⟩
      ⟨highCount G (floorDegree n) v, by omega⟩ dbv.1 dbv.2 ht (by dsimp only; omega) hk
  · intro h
    simp [hz h]
  all_goals dsimp only; omega

-- Double count ordered pairs of high vertices with a common neighbor. Apply two
-- different integer tangents to k*(k-1) in the two degree classes.
private lemma high_pairs (hf : (cycleGraph 4).Free G) (l cap : ℕ)
    (hc : ∀ v ∈ highVerts G l, highCount G l v ≤ cap) :
    let h : ℤ := #(highVerts G l)
    let n : ℤ := Fintype.card V
    6 * (h * (l + 1)) - 4 * (h * cap) - 2 * h - 12 * (n - h) ≤ h * (h - 1) := by
  classical
  let A := highVerts G l
  let k (v : V) : ℤ := highCount G l v
  have hisum : (∑ v ∈ A, k v) ≤ (A.card : ℤ) * cap := by
    dsimp only [k, A]
    exact_mod_cast (by simpa using sum_le_sum hc :
      ∑ v ∈ highVerts G l, highCount G l v ≤ #(highVerts G l) * cap)
  have hs : ∑ v, k v = (A.card : ℤ) * (l + 1) := by
    dsimp only [k, A]
    exact_mod_cast highCount_sum G l
  have splitSum := sum_add_sum_compl A k
  have splitPairs := sum_add_sum_compl A (fun v => k v * (k v - 1))
  have pairs := paths_count hf univ A
  change ∑ v, k v * (k v - 1) ≤ _ at pairs
  have hh := tangent A k 2
  have hl := tangent Aᶜ k 4
  have hcomp : ((Aᶜ.card : ℕ) : ℤ) = Fintype.card V - (A.card : ℤ) := by
    rw [card_compl, Nat.cast_sub (card_le_univ A)]
  dsimp only
  change 6 * ((A.card : ℤ) * _) - _ - _ - _ ≤ _
  rw [hcomp] at hl
  linarith

private lemma upper (n : ℕ) (hn : n ≤ 20) : extremalNumber n (cycleGraph 4) ≤ bound n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    apply upper_of_exclude
    intro G _ hf he
    have prev k (hk : k < n) := ih k hk (by omega)
    have db := degree_band hn G hf he prev
    have ds := G.sum_degrees_eq_twice_card_edges
    rw [he] at ds
    have lo := sum_le_sum (s := univ) fun (v : Fin n) _ => (db v).1
    have hi := sum_le_sum (s := univ) fun (v : Fin n) _ => (db v).2
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ds] at lo hi
    have ord := residual_orders ⟨n, by omega⟩ lo hi
    have pr := profiles hn G hf he prev
    have hw : width n ≤ 1 := by unfold width; split <;> decide
    have ha := band_sum G (floorDegree n) (fun v => ⟨(db v).1, by have := (db v).2; omega⟩) univ
    rw [ds, card_univ, Fintype.card_fin, univ_inter] at ha
    have tri := triDegree_sum G hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ord
    rcases ord with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h0 := (db 0).1
      have h1 := G.degree_lt_card_verts 0
      change 2 ≤ _ at h0
      rw [Fintype.card_fin] at h1
      omega
    · have eqn (v : Fin 8) : triDegree G v = 2 := by simpa [profile] using pr v
      simp_rw [eqn] at tri
      norm_num at tri
    · have eqn (v : Fin 9) : triDegree G v + 4 = 2 * G.degree v := by
        simpa [profile] using pr v
      have total := sum_congr (s₁ := univ) rfl (fun v _ => eqn v)
      rw [sum_add_distrib, ← mul_sum, ds] at total
      change (∑ v, triDegree G v) + 36 = 56 at total
      omega
    · -- On eleven vertices, all edges at a degree-four vertex belong to triangles.
      -- Consequently every vertex has at least two neighbors of degree four.
      change 38 = 11 * 3 + #(highVerts G 3) at ha
      have loc (v : Fin 11) := pr v
      change ∀ v, (if G.degree v == 4 then highCount G 3 v == 2 && triDegree G v == 4
        else 0 < highCount G 3 v && (triDegree G v == 0 || 2 ≤ highCount G 3 v)) = true at loc
      have hhigh {w : Fin 11} (hw : w ∈ highVerts G 3) : G.degree w = 4 := (mem_filter.mp hw).2
      have hk (v : Fin 11) : 2 ≤ highCount G 3 v := by
        have hv := loc v
        split at hv
        · simp only [Bool.and_eq_true, beq_iff_eq] at hv
          omega
        · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
          obtain ⟨w, hw⟩ := card_pos.mp hv.1
          have hd := hhigh (mem_inter.mp hw).2
          have ht : highCount G 3 w = 2 ∧ triDegree G w = 4 := by
            simpa [hd] using loc w
          have htpos := full_neighbor_triangle G hf
            ((G.mem_neighborFinset _ _).mp (mem_inter.mp hw).1) (ht.2.trans hd.symm)
          omega
      have hs := sum_le_sum (s := univ) fun v _ => hk v
      rw [highCount_sum] at hs
      change 22 ≤ #(highVerts G 3) * 4 at hs
      omega
    · exact Bool.noConfusion (pr 0)
    · have cap v (hv : v ∈ highVerts G 4) : highCount G 4 v ≤ 1 := by
        have hd : G.degree v = 5 := (mem_filter.mp hv).2
        simpa [profile, hd, show floorDegree 18 = 4 from rfl] using pr v
      have hp := high_pairs G hf 4 1 cap
      change 80 = 18 * 4 + #(highVerts G 4) at ha
      have card : #(highVerts G 4) = 8 := by omega
      norm_num [card] at hp
    · have cap v (hv : v ∈ highVerts G 4) : highCount G 4 v ≤ 2 := by
        have hd : G.degree v = 5 := (mem_filter.mp hv).2
        simpa [profile, hd, show floorDegree 19 = 4 from rfl] using pr v
      have hp := high_pairs G hf 4 2 cap
      change 86 = 19 * 4 + #(highVerts G 4) at ha
      have card : #(highVerts G 4) = 10 := by omega
      norm_num [card] at hp

-- Adjacency rows of the orthogonal polarity graphs of orders three and four.
-- In each row, bit j records adjacency to vertex j. The smaller graph is padded
-- with isolated vertices so that the two tables use a common vertex type.
private def row (large : Bool) (v : Fin 21) : ℕ :=
  let rows : List ℕ := if large then
    [2031616, 74272, 100488, 83012, 1048800, 149522, 533528, 295444, 1110016, 267394, 135752,
      528420, 1052416, 557378, 262440, 139652, 1048591, 33825, 541313, 272449, 69905]
  else [7680, 804, 658, 4544, 2116, 1090, 4152, 1036, 2058, 4103, 2209, 1297, 585]
  rows[v.val]?.getD 0

private def witnessGraph (large : Bool) : SimpleGraph (Fin 21) where
  Adj x y := (row large x).testBit y.val
  symm := ⟨by revert large; decide +kernel⟩
  loopless := ⟨by revert large; decide +kernel⟩

private instance decAdjWitness (large : Bool) : DecidableRel (witnessGraph large).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

private lemma witness_free (large : Bool) : (cycleGraph 4).Free (witnessGraph large) := by
  have pairs : ∀ (b : Bool) (x y : Fin 21), x ≠ y →
      #(univ.filter fun z : Fin 21 => (row b x).testBit z.val && (row b y).testBit z.val) ≤ 1 := by
    decide +kernel
  apply free_from_common_unique
  intro x y a c hxy hxa hya hxc hyc
  exact card_le_one_iff.mp (pairs large x y hxy)
    (by simpa [witnessGraph] using And.intro hxa hya)
    (by simpa [witnessGraph] using And.intro hxc hyc)

-- Vertex masks for the induced subgraphs attaining the twenty lower bounds.
private def vertexMask (n : ℕ) : ℕ :=
  [0, 1, 513, 4609, 519, 4615, 4623, 4687, 4703, 4735, 7007, 5887, 7935, 8191,
    1025743, 1947597, 1947599, 1947615, 1949663, 1933311, 1966079][n]?.getD 0

private def vertices (n : ℕ) : Finset (Fin 21) := univ.filter fun v => (vertexMask n).testBit v.val

private lemma lower (n : Fin 21) : bound n ≤ extremalNumber n (cycleGraph 4) := by
  let S := vertices n
  let G := witnessGraph (13 < n.val)
  have size : ∀ i : Fin 21, #(vertices i) = i.val := by decide +kernel
  have edges : ∀ i : Fin 21, arcs (witnessGraph (13 < i.val)) (vertices i) (vertices i) =
      2 * bound i := by
    simp only [arcs, neighborFinset_eq_filter]
    decide +kernel
  have hf : (cycleGraph 4).Free (G.induce (S : Set (Fin 21))) :=
    fun h => witness_free _ (h.trans ⟨Copy.induce G _⟩)
  have h := card_edgeFinset_le_extremalNumber hf
  rw [show Fintype.card (S : Set (Fin 21)) = n.val from (Fintype.card_coe S).trans (size n)] at h
  have hc := arcs_self G S
  change arcs G S S = 2 * _ at hc
  have he : arcs G S S = 2 * bound n := edges n
  omega

/-- **Extremal numbers of the four-cycle up to twenty vertices.** For a natural number $n$, let
$\mathrm{ex}(n; C_4)$ be the largest number of edges of a simple graph on $n$ vertices that
contains no four-cycle $C_4$ as a (not necessarily induced) subgraph. For
$n = 1, 2, \dots, 20$ the values of $\mathrm{ex}(n; C_4)$ are, in order,
$0, 1, 3, 4, 6, 7, 9, 11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46$.

Source: C. R. J. Clapham, A. Flockhart, and J. Sheehan, *Graphs without
four-cycles*, J. Graph Theory 13 (1989), 29–47 (`n ≤ 21`); OEIS A006855;
listed in leansolving/SqueezeBench `SqueezeBench/Problems/ExC4/README.md`. -/
public theorem extremalNumber_cycleGraph_four_one_to_twenty :
    (List.range 20).map (fun i => extremalNumber (i + 1) (cycleGraph 4)) =
      [0, 1, 3, 4, 6, 7, 9, 11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46] := by
  have eqn (i : ℕ) (hi : i ∈ List.range 20) :
      extremalNumber (i + 1) (cycleGraph 4) = bound (i + 1) := by
    have := List.mem_range.mp hi
    exact le_antisymm (upper _ (by omega)) (lower ⟨i + 1, by omega⟩)
  exact (List.map_congr_left eqn).trans (by decide)

end MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted

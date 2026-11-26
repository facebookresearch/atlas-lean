/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Splicing path families through a separator

The standard proof of Menger's theorem splits a graph at a minimum separator `S`, finds disjoint
paths from `A` to `S` and from `S` to `B`, and concatenates them at `S`. This file proves the
concatenation step for families: given paths `pA i` ending at `tgtA i ∈ S` and paths `pB i`
starting there, if each `pA i` meets `S` only at its end, each `pB i` meets `S` only at its start,
every common vertex of an `A`-path and a `B`-path lies in `S`, the `A`-paths are pairwise
disjoint, the `B`-paths are pairwise disjoint, and the endpoints `tgtA i` are distinct, then the
concatenations are pairwise vertex-disjoint paths.

## Main definitions

* `StatMech.Combinatorics.mgs_spliced pA pB i`: the concatenation of `pA i` and `pB i`.

## Main results

* `StatMech.Combinatorics.mgs_append_isPath`: two paths meeting only at the common endpoint
  concatenate to a path.
* `StatMech.Combinatorics.mgs_spliced_isPath`: each spliced walk is a path.
* `StatMech.Combinatorics.mgs_spliced_disjoint`: distinct spliced paths are vertex-disjoint.

## References

* R. Diestel, *Graph Theory*, 5th ed. (2017), Section 3.3 (proof of Menger's theorem).
-/

@[expose] public section

namespace StatMech.Combinatorics

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- The start of a path does not occur again among its later vertices. -/
lemma mgs_start_not_mem_tail {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [← cons_tail_support] at hnd
  exact (List.nodup_cons.mp hnd).1

/-- Two paths `p : u ⟶ v` and `q : v ⟶ w` whose only common vertex is `v` concatenate to a path. -/
lemma mgs_append_isPath {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [isPath_def, support_append]
  refine List.Nodup.append hp.support_nodup ((List.tail_sublist _).nodup hq.support_nodup) ?_
  rw [List.disjoint_left]
  intro x hxp hxqt
  have hxq : x ∈ q.support := List.tail_subset _ hxqt
  have hxv : x = v := hmeet x hxp hxq
  subst hxv
  exact (mgs_start_not_mem_tail hq) hxqt

/-- The walk from `srcA i` to `wB i` obtained by following `pA i` and then `pB i`. -/
def mgs_spliced {ι : Type*} {srcA tgtA wB : ι → V}
    (pA : (i : ι) → G.Walk (srcA i) (tgtA i))
    (pB : (i : ι) → G.Walk (tgtA i) (wB i)) (i : ι) :
    G.Walk (srcA i) (wB i) :=
  (pA i).append (pB i)

/-- Each spliced walk is a path when every `A`-path meets `S` only at its end and every common
vertex of an `A`-path and a `B`-path lies in `S`. -/
lemma mgs_spliced_isPath {ι : Type*} {srcA tgtA wB : ι → V}
    (pA : (i : ι) → G.Walk (srcA i) (tgtA i))
    (pB : (i : ι) → G.Walk (tgtA i) (wB i)) {S : Set V}
    (hApath : ∀ i, (pA i).IsPath) (hBpath : ∀ i, (pB i).IsPath)
    (hAmeetB : ∀ i i' x, x ∈ (pA i).support → x ∈ (pB i').support → x ∈ S)
    (hAcapS : ∀ i x, x ∈ (pA i).support → x ∈ S → x = tgtA i)
    (i : ι) : (mgs_spliced pA pB i).IsPath := by
  refine mgs_append_isPath (hApath i) (hBpath i) (fun x hxp hxq => ?_)
  exact hAcapS i x hxp (hAmeetB i i x hxp hxq)

/-- Distinct spliced paths share no vertex, given pairwise disjoint `A`-paths, pairwise disjoint
`B`-paths, distinct junction vertices `tgtA i`, and the separator conditions: common vertices of
`A`- and `B`-paths lie in `S`, and each path meets `S` only at its junction vertex. -/
lemma mgs_spliced_disjoint {ι : Type*} {srcA tgtA wB : ι → V}
    (pA : (i : ι) → G.Walk (srcA i) (tgtA i))
    (pB : (i : ι) → G.Walk (tgtA i) (wB i)) {S : Set V}
    (hAinj : Function.Injective tgtA)
    (hAA : ∀ i i', i ≠ i' → ∀ x, x ∈ (pA i).support → x ∈ (pA i').support → False)
    (hBB : ∀ i i', i ≠ i' → ∀ x, x ∈ (pB i).support → x ∈ (pB i').support → False)
    (hAmeetB : ∀ i i' x, x ∈ (pA i).support → x ∈ (pB i').support → x ∈ S)
    (hAcapS : ∀ i x, x ∈ (pA i).support → x ∈ S → x = tgtA i)
    (hBcapS : ∀ i x, x ∈ (pB i).support → x ∈ S → x = tgtA i)
    {i i' : ι} (hii : i ≠ i') {x : V}
    (hxi : x ∈ (mgs_spliced pA pB i).support)
    (hxi' : x ∈ (mgs_spliced pA pB i').support) : False := by
  simp only [mgs_spliced, mem_support_append_iff] at hxi hxi'
  rcases hxi with hAi | hBi <;> rcases hxi' with hAi' | hBi'
  · exact hAA i i' hii x hAi hAi'
  · have hS := hAmeetB i i' x hAi hBi'
    have e1 := hAcapS i x hAi hS
    have e2 := hBcapS i' x hBi' hS
    exact hii (hAinj (e1.symm.trans e2))
  · have hS := hAmeetB i' i x hAi' hBi
    have e1 := hAcapS i' x hAi' hS
    have e2 := hBcapS i x hBi hS
    exact hii (hAinj (e2.symm.trans e1))
  · exact hBB i i' hii x hBi hBi'

end StatMech.Combinatorics

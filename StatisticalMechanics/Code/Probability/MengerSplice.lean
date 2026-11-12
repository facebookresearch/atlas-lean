/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Mathlib.Combinatorics.SimpleGraph.Paths

namespace StatMech.Combinatorics

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}


lemma mgs_start_not_mem_tail {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [← cons_tail_support] at hnd
  exact (List.nodup_cons.mp hnd).1



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



def mgs_spliced {ι : Type*} {srcA tgtA wB : ι → V}
    (pA : (i : ι) → G.Walk (srcA i) (tgtA i))
    (pB : (i : ι) → G.Walk (tgtA i) (wB i)) (i : ι) :
    G.Walk (srcA i) (wB i) :=
  (pA i).append (pB i)




lemma mgs_spliced_isPath {ι : Type*} {srcA tgtA wB : ι → V}
    (pA : (i : ι) → G.Walk (srcA i) (tgtA i))
    (pB : (i : ι) → G.Walk (tgtA i) (wB i)) {S : Set V}
    (hApath : ∀ i, (pA i).IsPath) (hBpath : ∀ i, (pB i).IsPath)
    (hAmeetB : ∀ i i' x, x ∈ (pA i).support → x ∈ (pB i').support → x ∈ S)
    (hAcapS : ∀ i x, x ∈ (pA i).support → x ∈ S → x = tgtA i)
    (i : ι) : (mgs_spliced pA pB i).IsPath := by
  refine mgs_append_isPath (hApath i) (hBpath i) (fun x hxp hxq => ?_)
  exact hAcapS i x hxp (hAmeetB i i x hxp hxq)







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
  · 
    have hS := hAmeetB i i' x hAi hBi'
    have e1 := hAcapS i x hAi hS
    have e2 := hBcapS i' x hBi' hS
    exact hii (hAinj (e1.symm.trans e2))
  · 
    have hS := hAmeetB i' i x hAi' hBi
    have e1 := hAcapS i' x hAi' hS
    have e2 := hBcapS i x hBi hS
    exact hii (hAinj (e2.symm.trans e1))
  · exact hBB i i' hii x hBi hBi'

end StatMech.Combinatorics

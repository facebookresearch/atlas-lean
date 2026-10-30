/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Menger.LinkageSeparator
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Menger.LinkageSeparator`

* A linkage of size `2` by trivial paths in the complete graph on `Fin 2` from `univ` to `univ`;
  `mfm_card_le_separator` then forces every separator to have two vertices.
* `{0}` separates `{0}` from `{1}`; `mfm_exists_linkage_one` gives a one-path linkage, since
  every separator is nonempty.
* `mfm_isABSeparator_empty_iff` in the edgeless graph on `Fin 2`.
-/

@[expose] public section

open StatMech.Combinatorics

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Menger.LinkageSeparator

/-- Two trivial paths, one at each vertex of `Fin 2`. -/
def L : MfmLinkage (⊤ : SimpleGraph (Fin 2)) Finset.univ Finset.univ 2 where
  src := id
  tgt := id
  walk _ := SimpleGraph.Walk.nil
  src_mem _ := Finset.mem_univ _
  tgt_mem _ := Finset.mem_univ _
  isPath _ := SimpleGraph.Walk.IsPath.nil
  disjoint i j hij v hi hj := by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hi hj
    exact hij (hi.symm.trans hj)

example (S : Finset (Fin 2)) (hS : MfmIsABSeparator ⊤ Finset.univ Finset.univ S) : 2 ≤ S.card :=
  mfm_card_le_separator L hS

example : MfmIsABSeparator (⊤ : SimpleGraph (Fin 2)) {0} {1} {0} := by
  intro a b ha _ p
  simp only [Finset.mem_singleton] at ha ⊢
  exact ⟨a, p.start_mem_support, ha⟩

example : Nonempty (MfmLinkage (⊤ : SimpleGraph (Fin 2)) {0} {1} 1) := by
  refine mfm_exists_linkage_one fun S hS => ?_
  have hadj : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by simp
  obtain ⟨v, -, hv⟩ := hS (by simp) (by simp) (SimpleGraph.Walk.cons hadj .nil)
  exact Finset.card_pos.mpr ⟨v, hv⟩

example : MfmIsABSeparator (⊥ : SimpleGraph (Fin 2)) {0} {1} ∅ := by
  rw [mfm_isABSeparator_empty_iff]
  intro a ha b hb hr
  simp only [Finset.mem_singleton] at ha hb
  subst ha hb
  exact absurd (SimpleGraph.reachable_bot.mp hr) (by decide)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Menger.LinkageSeparator

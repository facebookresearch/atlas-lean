/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianFourColorFamilies











open Finset
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


def grahamGlobalMiddleSwap (q : GrahamFourColoring ι) :
    GrahamFourColoring ι where
  color1 := q.color1
  color2 := q.color3
  color3 := q.color2

@[simp] theorem grahamGlobalMiddleSwap_color1 (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color1 = q.color1 := rfl

@[simp] theorem grahamGlobalMiddleSwap_color2 (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color2 = q.color3 := rfl

@[simp] theorem grahamGlobalMiddleSwap_color3 (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color3 = q.color2 := rfl

@[simp] theorem grahamGlobalMiddleSwap_color4
    (U : Finset ι) (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color4 U = q.color4 U := by
  unfold GrahamFourColoring.color4 grahamGlobalMiddleSwap
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

@[simp] theorem grahamGlobalMiddleSwap_involutive
    (q : GrahamFourColoring ι) :
    grahamGlobalMiddleSwap (grahamGlobalMiddleSwap q) = q := by
  cases q
  rfl

theorem grahamGlobalMiddleSwap_isPartition_iff
    (U : Finset ι) (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).IsPartition U ↔ q.IsPartition U := by
  unfold GrahamFourColoring.IsPartition grahamGlobalMiddleSwap
  constructor
  · rintro ⟨h1, h3, h2, h13, h12, h32⟩
    exact ⟨h1, h2, h3, h12, h13, h32.symm⟩
  · rintro ⟨h1, h2, h3, h12, h13, h23⟩
    exact ⟨h1, h3, h2, h13, h12, h23.symm⟩



noncomputable def finiteTreeDiagonalColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V) :
    Finset (GrahamFourColoring ι) :=
  (grahamFourColorings U).filter (fun q =>
    sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = ∅ ∧
      sources ends q.color3 = {k, l} ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color3) i k)

@[simp] theorem mem_finiteTreeDiagonalColorings
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (q : GrahamFourColoring ι) :
    q ∈ finiteTreeDiagonalColorings ends U i j k l ↔
      q.IsPartition U ∧
      sources ends q.color1 = {i, j} ∧
      sources ends q.color2 = ∅ ∧
      sources ends q.color3 = {k, l} ∧
      sources ends (q.color4 U) = ∅ ∧
      connK ends (q.color1 ∪ q.color3) i k := by
  simp [finiteTreeDiagonalColorings]



theorem grahamGlobalMiddleSwap_mem_diagonal_iff
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (q : GrahamFourColoring ι) :
    grahamGlobalMiddleSwap q ∈
        finiteTreeDiagonalColorings ends U i j k l ↔
      q ∈ finiteTreeMixedColorings ends U i j k l := by
  rw [mem_finiteTreeDiagonalColorings, mem_finiteTreeMixedColorings,
    grahamGlobalMiddleSwap_isPartition_iff,
    grahamGlobalMiddleSwap_color1,
    grahamGlobalMiddleSwap_color2,
    grahamGlobalMiddleSwap_color3,
    grahamGlobalMiddleSwap_color4]
  tauto



theorem finiteTreeMixedColorings_card_eq_diagonal
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V) :
    #(finiteTreeMixedColorings ends U i j k l) =
      #(finiteTreeDiagonalColorings ends U i j k l) := by
  apply Finset.card_bij (fun q _ => grahamGlobalMiddleSwap q)
  · intro q hq
    exact (grahamGlobalMiddleSwap_mem_diagonal_iff ends U i j k l q).2 hq
  · intro q hq r hr hqr
    simpa only [grahamGlobalMiddleSwap_involutive] using
      congrArg grahamGlobalMiddleSwap hqr
  · intro q hq
    refine ⟨grahamGlobalMiddleSwap q, ?_, ?_⟩
    · rw [← grahamGlobalMiddleSwap_mem_diagonal_iff ends U i j k l]
      simpa only [grahamGlobalMiddleSwap_involutive] using hq
    · exact grahamGlobalMiddleSwap_involutive q




def FiniteTreeDiagonalBranchInequality
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V) : Prop :=
  #(finiteTreeDiagonalColorings ends U i j k l) ≤
    ∑ y : V, #(finiteTreeSeparatedBranchColorings ends U i j k l y)



theorem finiteTreeMixedColorings_card_le_sum_of_diagonal
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (h : FiniteTreeDiagonalBranchInequality ends U i j k l) :
    #(finiteTreeMixedColorings ends U i j k l) ≤
      ∑ y : V, #(finiteTreeSeparatedBranchColorings ends U i j k l y) := by
  rw [finiteTreeMixedColorings_card_eq_diagonal]
  exact h

end StatMech.FrontierA

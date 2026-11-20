/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorBalancedCore
import Code.FrontierA.GrahamCorrections










open Finset
open scoped symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent
open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]





theorem connK_sdiff_or_meets_edgeConnected
    (ends : ι -> Sym2 V) (H X : Finset ι) (i k v : V)
    (hXconn : ∀ e ∈ X, ∀ x ∈ ends e, connK ends X k x)
    (hiv : connK ends H i v) :
    connK ends (H \ X) i v ∨
      ∃ y, connK ends (H \ X) i y ∧ connK ends X k y := by
  induction hiv with
  | refl =>
      exact Or.inl Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
      rcases ih with hprefix | hmeet
      · rcases hstep with ⟨e, heH, hb, hc, hbc⟩
        by_cases heX : e ∈ X
        · exact Or.inr ⟨b, hprefix, hXconn e heX b hb⟩
        · exact Or.inl (hprefix.tail
            ⟨e, Finset.mem_sdiff.mpr ⟨heH, heX⟩, hb, hc, hbc⟩)
      · exact Or.inr hmeet



theorem exists_connK_sdiff_meets_of_edgeConnected
    (ends : ι -> Sym2 V) (H X : Finset ι) (i k : V)
    (hXconn : ∀ e ∈ X, ∀ x ∈ ends e, connK ends X k x)
    (hik : connK ends H i k) :
    ∃ y, connK ends (H \ X) i y ∧ connK ends X k y := by
  rcases connK_sdiff_or_meets_edgeConnected ends H X i k k hXconn hik with
    hsurvives | hmeet
  · exact ⟨k, hsurvives, Relation.ReflTransGen.refl⟩
  · exact hmeet

theorem edgeComponent_subset_edges
    (ends : ι -> Sym2 V) (K : Finset ι) (k : V) :
    edgeComponent ends K k ⊆ K := by
  intro e he
  rw [edgeComponent, Finset.mem_filter] at he
  exact he.1



theorem connK_edgeComponent_of_conn
    (ends : ι -> Sym2 V) (K : Finset ι) (k x : V)
    (hkx : connK ends K k x) :
    connK ends (edgeComponent ends K k) k x := by
  induction hkx with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hstep ih =>
      rcases hstep with ⟨e, heK, ha, hb, hab⟩
      have hka : connK ends K k a :=
        connK_mono (edgeComponent_subset_edges ends K k) ih
      exact ih.tail ⟨e,
        mem_edgeComponent_of_reachable_endpoint hka heK ha,
        ha, hb, hab⟩



theorem edgeComponent_endpoint_connK
    (ends : ι -> Sym2 V) (K : Finset ι) (k : V) :
    ∀ e ∈ edgeComponent ends K k, ∀ x ∈ ends e,
      connK ends (edgeComponent ends K k) k x := by
  intro e he x hx
  rw [edgeComponent, Finset.mem_filter] at he
  exact connK_edgeComponent_of_conn ends K k x (he.2 x hx)


def finiteTreeMiddleUnion (U : Finset ι) (c : ↑U -> Fin 4) : Finset ι :=
  colorClass U c 1 ∪ colorClass U c 2


def FiniteTreeMiddleTransferWitness
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4) (X : Finset ι) : Prop :=
  X ⊆ finiteTreeMiddleUnion U c ∧ sources ends X = {k, l} ∧
    connK ends X k l



noncomputable def finiteTreeMiddleTransferFromUnion
    (ends : ι -> Sym2 V) (M : Finset ι) (k l : V) : Finset ι :=
  if h : ∃ X, X ⊆ M ∧ sources ends X = {k, l} ∧ connK ends X k l then
    Classical.choose h
  else ∅



noncomputable def finiteTreeMiddleTransfer
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4) : Finset ι :=
  finiteTreeMiddleTransferFromUnion ends (finiteTreeMiddleUnion U c) k l

theorem finiteTreeMiddleTransfer_spec
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
    FiniteTreeMiddleTransferWitness ends U k l c
      (finiteTreeMiddleTransfer ends U k l c) := by
  unfold finiteTreeMiddleTransfer
  unfold finiteTreeMiddleTransferFromUnion
  unfold FiniteTreeMiddleTransferWitness at h ⊢
  rw [dif_pos h]
  exact Classical.choose_spec h


theorem finiteTreeMiddleUnion_middleSwapOn
    (U X : Finset ι) (c : ↑U -> Fin 4)
    (hX : X ⊆ finiteTreeMiddleUnion U c) :
    finiteTreeMiddleUnion U (middleSwapOn U X c) =
      finiteTreeMiddleUnion U c := by
  unfold finiteTreeMiddleUnion at hX ⊢
  rw [colorClass_middleSwapOn_one U X c hX,
    colorClass_middleSwapOn_two U X c hX]
  ext e
  have he := @hX e
  have hd : Disjoint (colorClass U c 1) (colorClass U c 2) :=
    colorClass_disjoint U c (by decide)
  rw [Finset.disjoint_left] at hd
  by_cases he1 : e ∈ colorClass U c 1 <;>
    by_cases he2 : e ∈ colorClass U c 2 <;>
    by_cases heX : e ∈ X <;>
    simp_all [Finset.mem_union, Finset.mem_symmDiff]

theorem finiteTreeMiddleTransferWitness_middleSwapOn_iff
    (ends : ι -> Sym2 V) (U X Y : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (hX : X ⊆ finiteTreeMiddleUnion U c) :
    FiniteTreeMiddleTransferWitness ends U k l
        (middleSwapOn U X c) Y ↔
      FiniteTreeMiddleTransferWitness ends U k l c Y := by
  unfold FiniteTreeMiddleTransferWitness
  rw [finiteTreeMiddleUnion_middleSwapOn U X c hX]


theorem finiteTreeMiddleTransfer_selected_invariant
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
    finiteTreeMiddleTransfer ends U k l
        (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) =
      finiteTreeMiddleTransfer ends U k l c := by
  have hspec := finiteTreeMiddleTransfer_spec ends U k l c h
  have hsub := hspec.1
  have hu := finiteTreeMiddleUnion_middleSwapOn U
    (finiteTreeMiddleTransfer ends U k l c) c hsub
  exact congrArg (fun M => finiteTreeMiddleTransferFromUnion ends M k l) hu


def FiniteTreeMixedPattern
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (c : ↑U -> Fin 4) : Prop :=
  sources ends (colorClass U c 0) = {i, j} ∧
    sources ends (colorClass U c 1) = {k, l} ∧
    sources ends (colorClass U c 2) = ∅ ∧
    sources ends (colorClass U c 3) = ∅ ∧
    connK ends (colorClass U c 0 ∪ colorClass U c 1) i k



def FiniteTreeSeparatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l : V)
    (c : ↑U -> Fin 4) : Prop :=
  sources ends (colorClass U c 0) = {i, j} ∧
    sources ends (colorClass U c 1) = ∅ ∧
    sources ends (colorClass U c 2) = {k, l} ∧
    sources ends (colorClass U c 3) = ∅



theorem exists_finiteTreeMiddleTransferWitness_of_mixed
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X := by
  have hconn : connK ends (colorClass U c 1) k l :=
    StatMech.Walls.gc6_pairingPath_abstract ends
      (colorClass U c 1) (colorClass U c 1)
      (fun e he => hloop e (colorClass_subset U c 1 he))
      Finset.Subset.rfl hmix.2.1 hkl
  obtain ⟨X, hX, hsrc⟩ := exists_conn_set ends
    (colorClass U c 1) hconn hkl
  refine ⟨X, ?_, hsrc, ?_⟩
  · exact hX.trans Finset.subset_union_left
  · exact path_exists ends X
      (fun e he => hloop e
        (colorClass_subset U c 1 (hX he))) k l
      (by rw [← mem_sources, hsrc]; simp)
      (by
        intro x hx
        rw [← mem_sources, hsrc] at hx
        simpa using hx)
      hkl




noncomputable def finiteTreeSourceComponentTransfer
    (ends : ι -> Sym2 V) (U : Finset ι) (k : V)
    (c : ↑U -> Fin 4) : Finset ι :=
  edgeComponent ends (colorClass U c 1) k

theorem finiteTreeSourceComponentTransfer_spec
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    finiteTreeSourceComponentTransfer ends U k c ⊆
        finiteTreeMiddleUnion U c ∧
      sources ends (finiteTreeSourceComponentTransfer ends U k c) = {k, l} ∧
      (∀ e ∈ finiteTreeSourceComponentTransfer ends U k c,
        ∀ x ∈ ends e,
          connK ends (finiteTreeSourceComponentTransfer ends U k c) k x) := by
  have hconn : connK ends (colorClass U c 1) k l :=
    StatMech.Walls.gc6_pairingPath_abstract ends
      (colorClass U c 1) (colorClass U c 1)
      (fun e he => hloop e (colorClass_subset U c 1 he))
      Finset.Subset.rfl hmix.2.1 hkl
  have hsrc : sources ends
      (edgeComponent ends (colorClass U c 1) k) = {k, l} := by
    rw [sources_edgeComponent, hmix.2.1]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hconn
  unfold finiteTreeSourceComponentTransfer
  refine ⟨?_, hsrc, edgeComponent_endpoint_connK ends
    (colorClass U c 1) k⟩
  exact (edgeComponent_subset_edges ends (colorClass U c 1) k).trans
    Finset.subset_union_left



theorem finiteTree_sourceComponentSwitch_separatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    FiniteTreeSeparatedSources ends U i j k l
      (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) := by
  have hs := finiteTreeSourceComponentTransfer_spec
    ends U c hloop hkl hmix
  unfold FiniteTreeSeparatedSources
  rw [colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one U _ c hs.1,
    colorClass_middleSwapOn_two U _ c hs.1,
    colorClass_middleSwapOn_three,
    sources_symmDiff, sources_symmDiff,
    hmix.1, hmix.2.1, hmix.2.2.1, hmix.2.2.2.1, hs.2.1]
  simp



theorem finiteTree_sourceComponentSwitch_hasCommonVertex
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    ∃ y,
      connK ends
          (colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 0 ∪
            colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 1) i y ∧
      connK ends
          (colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 2 ∪
            colorClass U
              (middleSwapOn U
                (finiteTreeSourceComponentTransfer ends U k c) c) 3) k y := by
  let X := finiteTreeSourceComponentTransfer ends U k c
  have hs := finiteTreeSourceComponentTransfer_spec
    ends U c hloop hkl hmix
  have hX1 : X ⊆ colorClass U c 1 := by
    exact edgeComponent_subset_edges ends (colorClass U c 1) k
  have hmeet := exists_connK_sdiff_meets_of_edgeConnected ends
    (colorClass U c 0 ∪ colorClass U c 1) X i k hs.2.2
    hmix.2.2.2.2
  have hrow0 : (colorClass U c 0 ∪ colorClass U c 1) \ X ⊆
      colorClass U (middleSwapOn U X c) 0 ∪
        colorClass U (middleSwapOn U X c) 1 := by
    intro e he
    rcases Finset.mem_sdiff.mp he with ⟨he01, heX⟩
    rcases Finset.mem_union.mp he01 with he0 | he1
    · rw [colorClass_middleSwapOn_zero]
      exact Finset.mem_union_left _ he0
    · apply Finset.mem_union_right
      rw [colorClass_middleSwapOn_one U X c hs.1]
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨he1, heX⟩)
  have hrow1 : X ⊆
      colorClass U (middleSwapOn U X c) 2 ∪
        colorClass U (middleSwapOn U X c) 3 := by
    intro e heX
    apply Finset.mem_union_left
    rw [colorClass_middleSwapOn_two U X c hs.1]
    apply Finset.mem_symmDiff.mpr
    exact Or.inr ⟨heX, fun he2 =>
      Finset.disjoint_left.mp
        (colorClass_disjoint U c (show (1 : Fin 4) ≠ 2 by decide))
        (hX1 heX) he2⟩
  obtain ⟨y, hiy, hky⟩ := hmeet
  exact ⟨y, connK_mono hrow0 hiy, connK_mono hrow1 hky⟩


noncomputable def finiteTreeInvariantComponentTransfer
    (ends : ι -> Sym2 V) (U : Finset ι) (k : V)
    (c : ↑U -> Fin 4) : Finset ι :=
  edgeComponent ends (finiteTreeMiddleUnion U c) k

theorem finiteTreeInvariantComponentTransfer_spec
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    finiteTreeInvariantComponentTransfer ends U k c ⊆
        finiteTreeMiddleUnion U c ∧
      sources ends (finiteTreeInvariantComponentTransfer ends U k c) = {k, l} ∧
      (∀ e ∈ finiteTreeInvariantComponentTransfer ends U k c,
        ∀ x ∈ ends e,
          connK ends (finiteTreeInvariantComponentTransfer ends U k c) k x) := by
  have hmiddle : sources ends (finiteTreeMiddleUnion U c) = {k, l} := by
    unfold finiteTreeMiddleUnion
    rw [sources_union_of_disjoint
      (colorClass_disjoint U c (show (1 : Fin 4) ≠ 2 by decide)),
      hmix.2.1, hmix.2.2.1]
    simp
  have hconn1 : connK ends (colorClass U c 1) k l :=
    StatMech.Walls.gc6_pairingPath_abstract ends
      (colorClass U c 1) (colorClass U c 1)
      (fun e he => hloop e (colorClass_subset U c 1 he))
      Finset.Subset.rfl hmix.2.1 hkl
  have hconn : connK ends (finiteTreeMiddleUnion U c) k l := by
    exact connK_mono Finset.subset_union_left hconn1
  have hsrc : sources ends
      (edgeComponent ends (finiteTreeMiddleUnion U c) k) = {k, l} := by
    rw [sources_edgeComponent, hmiddle]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hconn
  unfold finiteTreeInvariantComponentTransfer
  exact ⟨edgeComponent_subset_edges ends (finiteTreeMiddleUnion U c) k,
    hsrc, edgeComponent_endpoint_connK ends (finiteTreeMiddleUnion U c) k⟩



theorem finiteTreeInvariantComponentTransfer_selected_invariant
    (ends : ι -> Sym2 V) (U : Finset ι) (k : V)
    (c : ↑U -> Fin 4)
    (hsub : finiteTreeInvariantComponentTransfer ends U k c ⊆
      finiteTreeMiddleUnion U c) :
    finiteTreeInvariantComponentTransfer ends U k
        (middleSwapOn U
          (finiteTreeInvariantComponentTransfer ends U k c) c) =
      finiteTreeInvariantComponentTransfer ends U k c := by
  exact congrArg (fun M => edgeComponent ends M k)
    (finiteTreeMiddleUnion_middleSwapOn U
      (finiteTreeInvariantComponentTransfer ends U k c) c hsub)

theorem finiteTree_invariantComponentSwitch_separatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    FiniteTreeSeparatedSources ends U i j k l
      (middleSwapOn U
        (finiteTreeInvariantComponentTransfer ends U k c) c) := by
  have hs := finiteTreeInvariantComponentTransfer_spec
    ends U c hloop hkl hmix
  unfold FiniteTreeSeparatedSources
  rw [colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one U _ c hs.1,
    colorClass_middleSwapOn_two U _ c hs.1,
    colorClass_middleSwapOn_three,
    sources_symmDiff, sources_symmDiff,
    hmix.1, hmix.2.1, hmix.2.2.1, hmix.2.2.2.1, hs.2.1]
  simp

theorem finiteTree_invariantComponentSwitch_involutive
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    middleSwapOn U
        (finiteTreeInvariantComponentTransfer ends U k
          (middleSwapOn U
            (finiteTreeInvariantComponentTransfer ends U k c) c))
        (middleSwapOn U
          (finiteTreeInvariantComponentTransfer ends U k c) c) = c := by
  have hs := finiteTreeInvariantComponentTransfer_spec
    ends U c hloop hkl hmix
  rw [finiteTreeInvariantComponentTransfer_selected_invariant
    ends U k c hs.1]
  exact middleSwapOn_involutive U
    (finiteTreeInvariantComponentTransfer ends U k c) c



theorem finiteTree_selectedSwitch_separatedSources
    (ends : ι -> Sym2 V) (U : Finset ι) {i j k l : V}
    (c : ↑U -> Fin 4)
    (hloop : ∀ e ∈ U, ¬(ends e).IsDiag) (hkl : k ≠ l)
    (hmix : FiniteTreeMixedPattern ends U i j k l c) :
    FiniteTreeSeparatedSources ends U i j k l
      (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) := by
  have hex := exists_finiteTreeMiddleTransferWitness_of_mixed
    ends U c hloop hkl hmix
  have hs := finiteTreeMiddleTransfer_spec ends U k l c hex
  unfold FiniteTreeSeparatedSources
  rw [colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one U _ c hs.1,
    colorClass_middleSwapOn_two U _ c hs.1,
    colorClass_middleSwapOn_three,
    sources_symmDiff, sources_symmDiff,
    hmix.1, hmix.2.1, hmix.2.2.1, hmix.2.2.2.1, hs.2.1]
  simp


theorem finiteTree_selectedSwitch_involutive
    (ends : ι -> Sym2 V) (U : Finset ι) (k l : V)
    (c : ↑U -> Fin 4)
    (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
    middleSwapOn U
        (finiteTreeMiddleTransfer ends U k l
          (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c))
        (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) = c := by
  rw [finiteTreeMiddleTransfer_selected_invariant ends U k l c h]
  exact middleSwapOn_involutive U
    (finiteTreeMiddleTransfer ends U k l c) c

end StatMech.FrontierA

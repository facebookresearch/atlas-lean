/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.ProbabilisticTreeDepth

/-!
# Tests for termination within bounded depth

Depths 0, 1, and 2 computed explicitly; strict growth of the events;
descendants below leaves ignored; same-yield distinct trees at depth
3; the depth-2 probability at `p = 2/3`; and the boundary
probabilities `p = 0` and `p = 1`.
-/

@[expose] public section

open MeasureTheory

namespace Cslib.Language

/-- Tests (h = 0): no tree has depth at most zero; the event is empty, has
probability zero, and `cgTotal` is zero there. -/
private theorem test_depth_zero {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    cgTrees 0 = ∅ ∧ terminationByDepth 0 = ∅ ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth 0) = 0 ∧
      cgTotal p (1 - p) 0 = 0 := by
  refine ⟨cgTrees_zero, terminationByDepth_zero, ?_, ?_⟩
  · rw [terminationByDepth_zero]
    exact measure_empty
  · show (∑ t ∈ cgTrees 0, t.weight p (1 - p)) = 0
    rw [cgTrees_zero]
    exact Finset.sum_empty

/-- Tests (h = 1, leaf depth one): only the leaf tree; the event is the root-leaf
event and has probability `1 - p`. -/
private theorem test_depth_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    cgTrees 1 = {CGTree.leaf} ∧
      terminationByDepth 1 = BinaryTreeAddressLaw.leafAt [] ∧
      terminationByDepth 1 = treeCylinder CGTree.leaf ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth 1) =
        ENNReal.ofReal (1 - p) := by
  have h1 : cgTrees 1 = {CGTree.leaf} := by
    have hsucc := cgTrees_succ 0
    rw [cgTrees_zero] at hsucc
    simp at hsucc
    exact hsucc
  have hT1 : terminationByDepth 1 = BinaryTreeAddressLaw.leafAt [] := by
    have hsucc := terminationByDepth_succ 0
    rw [terminationByDepth_zero] at hsucc
    simp at hsucc
    exact hsucc
  have hT1cyl : terminationByDepth 1 = treeCylinder CGTree.leaf :=
    hT1.trans treeCylinder_leaf.symm
  have hcg : cgTotal p (1 - p) 1 = 1 - p := by
    show (∑ t ∈ cgTrees 1, t.weight p (1 - p)) = _
    simp [h1, CGTree.weight]
  have hlaw : BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth 1) =
      ENNReal.ofReal (1 - p) := by
    have h := law_terminationByDepth hp0 hp1 1
    rw [hcg] at h
    exact h
  exact ⟨h1, hT1, hT1cyl, hlaw⟩

/-- Tests (h = 2): the leaf and the cherry; the event is the root leaf, or a root
branch with two leaf children; probability `(1 - p) + p (1 - p)^2`. -/
private theorem test_depth_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    cgTrees 2 = {CGTree.leaf, CGTree.node CGTree.leaf CGTree.leaf} ∧
      terminationByDepth 2 =
        treeCylinder CGTree.leaf ∪ treeCylinder (CGTree.node CGTree.leaf CGTree.leaf) ∧
      terminationByDepth 2 =
        BinaryTreeAddressLaw.leafAt [] ∪
          (BinaryTreeAddressLaw.branchAt [] ∩ BinaryTreeAddressLaw.leafAt [false] ∩
            BinaryTreeAddressLaw.leafAt [true]) ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth 2) =
        ENNReal.ofReal ((1 - p) + p * (1 - p) ^ 2) := by
  have h1 : cgTrees 1 = {CGTree.leaf} := by
    have hsucc := cgTrees_succ 0
    rw [cgTrees_zero] at hsucc
    simp at hsucc
    exact hsucc
  have hT1 : terminationByDepth 1 = BinaryTreeAddressLaw.leafAt [] := by
    have hsucc := terminationByDepth_succ 0
    rw [terminationByDepth_zero] at hsucc
    simp at hsucc
    exact hsucc
  have h2 : cgTrees 2 = {CGTree.leaf, CGTree.node CGTree.leaf CGTree.leaf} := by
    have hsucc := cgTrees_succ 1
    rw [h1] at hsucc
    simp at hsucc
    exact hsucc
  have hT2union : terminationByDepth 2 =
      treeCylinder CGTree.leaf ∪
        treeCylinder (CGTree.node CGTree.leaf CGTree.leaf) := by
    rw [terminationByDepth_eq_biUnion 2, h2]
    ext ω
    constructor
    · intro hmemU
      simp only [Set.mem_iUnion] at hmemU
      obtain ⟨t, ht, hmem⟩ := hmemU
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      cases ht with
      | inl heq =>
          subst heq
          exact Or.inl hmem
      | inr heq =>
          subst heq
          exact Or.inr hmem
    · rintro (h | h)
      · exact Set.mem_biUnion (by simp) h
      · exact Set.mem_biUnion (by simp) h
  have hshiftL : BinaryTreeAddressLaw.shiftLeft ⁻¹' BinaryTreeAddressLaw.leafAt [] =
      BinaryTreeAddressLaw.leafAt [false] := by
    ext ω
    rfl
  have hshiftR : BinaryTreeAddressLaw.shiftRight ⁻¹' BinaryTreeAddressLaw.leafAt [] =
      BinaryTreeAddressLaw.leafAt [true] := by
    ext ω
    rfl
  have hT2eq : terminationByDepth 2 =
      BinaryTreeAddressLaw.leafAt [] ∪
        (BinaryTreeAddressLaw.branchAt [] ∩ BinaryTreeAddressLaw.leafAt [false] ∩
          BinaryTreeAddressLaw.leafAt [true]) := by
    have hsucc := terminationByDepth_succ 1
    rw [hT1, hshiftL, hshiftR] at hsucc
    exact hsucc
  have hcg2 : cgTotal p (1 - p) 2 = (1 - p) + p * (1 - p) ^ 2 := by
    show (∑ t ∈ cgTrees 2, t.weight p (1 - p)) = _
    have hne : CGTree.leaf ∉
        ({CGTree.node CGTree.leaf CGTree.leaf} : Finset CGTree) := by decide
    rw [h2, Finset.sum_insert hne, Finset.sum_singleton]
    show (1 - p) + p * (1 - p) * (1 - p) = _
    ring
  have hlaw : BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth 2) =
      ENNReal.ofReal ((1 - p) + p * (1 - p) ^ 2) := by
    have h := law_terminationByDepth hp0 hp1 2
    rw [hcg2] at h
    exact h
  exact ⟨h2, hT2union, hT2eq, hlaw⟩

/-- Tests (strict growth, not a constant sequence): a root branch with two leaf
children (and branches everywhere deeper) terminates within depth 2 but not 1; the
all-branch point never terminates. -/
private theorem test_strict_and_proper :
    (fun a : List Bool => decide (a.length ≠ 1)) ∈ terminationByDepth 2 ∧
      (fun a : List Bool => decide (a.length ≠ 1)) ∉ terminationByDepth 1 ∧
      ∀ h, (fun _ : List Bool => true) ∉ terminationByDepth h := by
  have hT1 : terminationByDepth 1 = BinaryTreeAddressLaw.leafAt [] := by
    have hsucc := terminationByDepth_succ 0
    rw [terminationByDepth_zero] at hsucc
    simp at hsucc
    exact hsucc
  have hshiftL : BinaryTreeAddressLaw.shiftLeft ⁻¹' BinaryTreeAddressLaw.leafAt [] =
      BinaryTreeAddressLaw.leafAt [false] := by
    ext ω
    rfl
  have hshiftR : BinaryTreeAddressLaw.shiftRight ⁻¹' BinaryTreeAddressLaw.leafAt [] =
      BinaryTreeAddressLaw.leafAt [true] := by
    ext ω
    rfl
  have hT2 : terminationByDepth 2 =
      BinaryTreeAddressLaw.leafAt [] ∪
        (BinaryTreeAddressLaw.branchAt [] ∩ BinaryTreeAddressLaw.leafAt [false] ∩
          BinaryTreeAddressLaw.leafAt [true]) := by
    have hsucc := terminationByDepth_succ 1
    rw [hT1, hshiftL, hshiftR] at hsucc
    exact hsucc
  have hroot : (fun a : List Bool => decide (a.length ≠ 1)) [] = true := rfl
  have hleft : (fun a : List Bool => decide (a.length ≠ 1)) [false] = false := rfl
  have hright : (fun a : List Bool => decide (a.length ≠ 1)) [true] = false := rfl
  have hmem2 : (fun a : List Bool => decide (a.length ≠ 1)) ∈ terminationByDepth 2 := by
    rw [hT2]
    exact Or.inr ⟨⟨hroot, hleft⟩, hright⟩
  have hnot1 : (fun a : List Bool => decide (a.length ≠ 1)) ∉ terminationByDepth 1 := by
    rw [hT1]
    intro hcon
    have hfalse : (fun a : List Bool => decide (a.length ≠ 1)) [] = false := hcon
    rw [hroot] at hfalse
    cases hfalse
  have hall : ∀ h, (fun _ : List Bool => true) ∉ terminationByDepth h := by
    intro h
    induction h with
    | zero =>
        rw [terminationByDepth_zero]
        exact Set.notMem_empty _
    | succ h ih =>
        rw [terminationByDepth_succ h]
        intro hmem
        cases hmem with
        | inl hleaf =>
            have hfalse : (fun _ : List Bool => true) [] = false := hleaf
            cases hfalse
        | inr hbranch =>
            obtain ⟨⟨_, hL⟩, _⟩ := hbranch
            have hshift : BinaryTreeAddressLaw.shiftLeft (fun _ : List Bool => true) =
                (fun _ : List Bool => true) := rfl
            rw [Set.mem_preimage, hshift] at hL
            exact ih hL
  exact ⟨hmem2, hnot1, hall⟩

/-- Tests (ignored descendants below leaves): any point with a root leaf, whatever
its values below the root, lies in every positive-depth event (for example the root
leaf with branches everywhere below it); any point with a root branch and two leaf
children, whatever its values deeper down, lies in the depth-2 event. -/
private theorem test_descendants_ignored :
    (∀ ω : BinaryTreeAddressLaw.Ω, ω [] = false → ∀ h, 1 ≤ h → ω ∈ terminationByDepth h) ∧
      (fun a : List Bool => decide (a ≠ [])) ∈ terminationByDepth 1 ∧
      (∀ ω : BinaryTreeAddressLaw.Ω, ω [] = true → ω [false] = false → ω [true] = false →
        ω ∈ terminationByDepth 2) ∧
      (fun a : List Bool => decide (a = [])) ∈ terminationByDepth 2 := by
  have hT1 : terminationByDepth 1 = BinaryTreeAddressLaw.leafAt [] := by
    have hsucc := terminationByDepth_succ 0
    rw [terminationByDepth_zero] at hsucc
    simp at hsucc
    exact hsucc
  have hshiftL : BinaryTreeAddressLaw.shiftLeft ⁻¹' BinaryTreeAddressLaw.leafAt [] =
      BinaryTreeAddressLaw.leafAt [false] := by
    ext ω
    rfl
  have hshiftR : BinaryTreeAddressLaw.shiftRight ⁻¹' BinaryTreeAddressLaw.leafAt [] =
      BinaryTreeAddressLaw.leafAt [true] := by
    ext ω
    rfl
  have hT2 : terminationByDepth 2 =
      BinaryTreeAddressLaw.leafAt [] ∪
        (BinaryTreeAddressLaw.branchAt [] ∩ BinaryTreeAddressLaw.leafAt [false] ∩
          BinaryTreeAddressLaw.leafAt [true]) := by
    have hsucc := terminationByDepth_succ 1
    rw [hT1, hshiftL, hshiftR] at hsucc
    exact hsucc
  have hsub : ∀ h, 1 ≤ h →
      BinaryTreeAddressLaw.leafAt [] ⊆ terminationByDepth h := by
    intro h hh
    rw [← hT1]
    exact monotone_terminationByDepth hh
  have h1 : ∀ ω : BinaryTreeAddressLaw.Ω, ω [] = false → ∀ h, 1 ≤ h →
      ω ∈ terminationByDepth h := by
    intro ω hroot h hh
    have hmem : ω ∈ BinaryTreeAddressLaw.leafAt [] := hroot
    exact hsub h hh hmem
  have hval1 : (fun a : List Bool => decide (a ≠ [])) [] = false := rfl
  have hmem1 : (fun a : List Bool => decide (a ≠ [])) ∈ terminationByDepth 1 := by
    rw [hT1]
    exact hval1
  have h3 : ∀ ω : BinaryTreeAddressLaw.Ω, ω [] = true → ω [false] = false →
      ω [true] = false → ω ∈ terminationByDepth 2 := by
    intro ω hroot hleft hright
    rw [hT2]
    exact Or.inr ⟨⟨hroot, hleft⟩, hright⟩
  have hv0 : (fun a : List Bool => decide (a = [])) [] = true := rfl
  have hv1 : (fun a : List Bool => decide (a = [])) [false] = false := rfl
  have hv2 : (fun a : List Bool => decide (a = [])) [true] = false := rfl
  have hmem2 : (fun a : List Bool => decide (a = [])) ∈ terminationByDepth 2 :=
    h3 _ hv0 hv1 hv2
  exact ⟨h1, hmem1, h3, hmem2⟩

/-- Tests (same-yield distinct trees): the right- and left-associated three-leaf
trees are distinct, both of depth exactly 3, map under the existing `ofCGTree` to
derivation trees of the same terminal yield `[(), (), ()]`, have disjoint cylinders,
both cylinders lie in the depth-3 event and are disjoint from the depth-2 event. -/
private theorem test_same_yield_distinct :
    CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ≠
        CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf ∧
      CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ∈ cgTrees 3 ∧
      CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf ∈ cgTrees 3 ∧
      CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ∉ cgTrees 2 ∧
      CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf ∉ cgTrees 2 ∧
      (ofCGTree (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf))).yieldOf =
        [(), (), ()] ∧
      (ofCGTree (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf)).yieldOf =
        [(), (), ()] ∧
      Disjoint
        (treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)))
        (treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf)) ∧
      treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)) ⊆
        terminationByDepth 3 ∧
      treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf) ⊆
        terminationByDepth 3 ∧
      Disjoint
        (treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)))
        (terminationByDepth 2) ∧
      Disjoint
        (treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf))
        (terminationByDepth 2) := by
  have hne : CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ≠
      CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf := by decide
  have hmemR : CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ∈
      cgTrees 3 := by decide
  have hmemL : CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf ∈
      cgTrees 3 := by decide
  have hnotR : CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ∉
      cgTrees 2 := by decide
  have hnotL : CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf ∉
      cgTrees 2 := by decide
  have hyR : (ofCGTree (CGTree.node CGTree.leaf
      (CGTree.node CGTree.leaf CGTree.leaf))).yieldOf = [(), (), ()] := rfl
  have hyL : (ofCGTree (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf)
      CGTree.leaf)).yieldOf = [(), (), ()] := rfl
  have hdisj : Disjoint
      (treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)))
      (treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf)
        CGTree.leaf)) :=
    treeCylinder_disjoint_of_ne hne
  have hsubR : treeCylinder (CGTree.node CGTree.leaf
      (CGTree.node CGTree.leaf CGTree.leaf)) ⊆ terminationByDepth 3 := by
    rw [terminationByDepth_eq_biUnion 3]
    intro ω h
    exact Set.mem_biUnion hmemR h
  have hsubL : treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf)
      CGTree.leaf) ⊆ terminationByDepth 3 := by
    rw [terminationByDepth_eq_biUnion 3]
    intro ω h
    exact Set.mem_biUnion hmemL h
  have hdisjR2 : Disjoint
      (treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)))
      (terminationByDepth 2) := by
    rw [Set.disjoint_left]
    intro ω hR hT2
    rw [terminationByDepth_eq_biUnion 2] at hT2
    simp only [Set.mem_iUnion] at hT2
    obtain ⟨t, ht, hmem⟩ := hT2
    have hneq : CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf) ≠ t := by
      intro heq
      subst heq
      exact hnotR ht
    have hd := treeCylinder_disjoint_of_ne hneq
    exact Set.disjoint_left.mp hd hR hmem
  have hdisjL2 : Disjoint
      (treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf)
        CGTree.leaf))
      (terminationByDepth 2) := by
    rw [Set.disjoint_left]
    intro ω hL hT2
    rw [terminationByDepth_eq_biUnion 2] at hT2
    simp only [Set.mem_iUnion] at hT2
    obtain ⟨t, ht, hmem⟩ := hT2
    have hneq : CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf ≠ t := by
      intro heq
      subst heq
      exact hnotL ht
    have hd := treeCylinder_disjoint_of_ne hneq
    exact Set.disjoint_left.mp hd hL hmem
  exact ⟨hne, hmemR, hmemL, hnotR, hnotL, hyR, hyL, hdisj, hsubR, hsubL,
    hdisjR2, hdisjL2⟩

/-- Tests (shifted Chi-Geman index): at `p = 2/3` the depth-2 probability is
`11/27 = chiGemanS (2/3) (1/3) 3`, while the unshifted value `chiGemanS (2/3) (1/3) 2`
is `1/3`; at `p = 1/2` the depth-1 probability is `1/2` while the unshifted
`chiGemanS (1/2) (1/2) 1` is `0`. -/
private theorem test_chiGemanS_shift :
    BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) (terminationByDepth 2) =
        ENNReal.ofReal (11 / 27) ∧
      chiGemanS (2 / 3) (1 - 2 / 3) 3 = 11 / 27 ∧
      chiGemanS (2 / 3) (1 - 2 / 3) 2 = 1 / 3 ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) (terminationByDepth 2) ≠
        ENNReal.ofReal (chiGemanS (2 / 3) (1 - 2 / 3) 2) ∧
      BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num) (terminationByDepth 1) =
        ENNReal.ofReal (1 / 2) ∧
      chiGemanS (1 / 2) (1 - 1 / 2) 1 = 0 ∧
      BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num) (terminationByDepth 1) ≠
        ENNReal.ofReal (chiGemanS (1 / 2) (1 - 1 / 2) 1) := by
  have h1 : cgTrees 1 = {CGTree.leaf} := by
    have hsucc := cgTrees_succ 0
    rw [cgTrees_zero] at hsucc
    simp at hsucc
    exact hsucc
  have h2 : cgTrees 2 = {CGTree.leaf, CGTree.node CGTree.leaf CGTree.leaf} := by
    have hsucc := cgTrees_succ 1
    rw [h1] at hsucc
    simp at hsucc
    exact hsucc
  have hcg1gen : ∀ p : ℝ, cgTotal p (1 - p) 1 = 1 - p := by
    intro p
    show (∑ t ∈ cgTrees 1, t.weight p (1 - p)) = _
    simp [h1, CGTree.weight]
  have hcg2gen : ∀ p : ℝ, cgTotal p (1 - p) 2 = (1 - p) + p * (1 - p) ^ 2 := by
    intro p
    show (∑ t ∈ cgTrees 2, t.weight p (1 - p)) = _
    have hne : CGTree.leaf ∉
        ({CGTree.node CGTree.leaf CGTree.leaf} : Finset CGTree) := by decide
    rw [h2, Finset.sum_insert hne, Finset.sum_singleton]
    show (1 - p) + p * (1 - p) * (1 - p) = _
    ring
  have hcg2c : cgTotal (2 / 3) (1 - 2 / 3) 2 = 11 / 27 := by
    rw [hcg2gen]
    norm_num
  have hlaw2 : BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
      (terminationByDepth 2) = ENNReal.ofReal (11 / 27) := by
    have h := law_terminationByDepth (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 / 3 : ℝ) ≤ 1) 2
    rw [hcg2c] at h
    exact h
  have hchi3 : chiGemanS (2 / 3) (1 - 2 / 3) 3 = 11 / 27 := by
    norm_num [chiGemanS]
  have hchi2 : chiGemanS (2 / 3) (1 - 2 / 3) 2 = 1 / 3 := by
    norm_num [chiGemanS]
  have hne2 : ENNReal.ofReal (11 / 27 : ℝ) ≠ ENNReal.ofReal (1 / 3 : ℝ) := by
    intro hcon
    have h : ENNReal.toReal (ENNReal.ofReal (11 / 27 : ℝ)) =
        ENNReal.toReal (ENNReal.ofReal (1 / 3 : ℝ)) := by rw [hcon]
    rw [ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by norm_num)] at h
    norm_num at h
  have hneLaw2 : BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num)
      (terminationByDepth 2) ≠
      ENNReal.ofReal (chiGemanS (2 / 3) (1 - 2 / 3) 2) := by
    rw [hlaw2, hchi2]
    exact hne2
  have hcg1c : cgTotal (1 / 2) (1 - 1 / 2) 1 = 1 / 2 := by
    rw [hcg1gen]
    norm_num
  have hlaw1 : BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num)
      (terminationByDepth 1) = ENNReal.ofReal (1 / 2) := by
    have h := law_terminationByDepth (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) 1
    rw [hcg1c] at h
    exact h
  have hchi1 : chiGemanS (1 / 2) (1 - 1 / 2) 1 = 0 := by
    norm_num [chiGemanS]
  have hne1 : ENNReal.ofReal (1 / 2 : ℝ) ≠ ENNReal.ofReal (0 : ℝ) := by
    intro hcon
    have h : ENNReal.toReal (ENNReal.ofReal (1 / 2 : ℝ)) =
        ENNReal.toReal (ENNReal.ofReal (0 : ℝ)) := by rw [hcon]
    rw [ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (le_refl 0)] at h
    norm_num at h
  have hneLaw1 : BinaryTreeAddressLaw.law (1 / 2) (by norm_num) (by norm_num)
      (terminationByDepth 1) ≠
      ENNReal.ofReal (chiGemanS (1 / 2) (1 - 1 / 2) 1) := by
    rw [hlaw1, hchi1]
    exact hne1
  exact ⟨hlaw2, hchi3, hchi2, hneLaw2, hlaw1, hchi1, hneLaw1⟩

/-- Tests (boundary): at `p = 0` every positive-depth event has probability one; at
`p = 1` every event has probability zero although the depth-1 event is nonempty. -/
private theorem test_boundary :
    (∀ h, 1 ≤ h →
        BinaryTreeAddressLaw.law 0 le_rfl zero_le_one (terminationByDepth h) = 1) ∧
      (∀ h, BinaryTreeAddressLaw.law 1 zero_le_one le_rfl (terminationByDepth h) = 0) ∧
      (fun _ : List Bool => false) ∈ terminationByDepth 1 := by
  have hT1 : terminationByDepth 1 = BinaryTreeAddressLaw.leafAt [] := by
    have hsucc := terminationByDepth_succ 0
    rw [terminationByDepth_zero] at hsucc
    simp at hsucc
    exact hsucc
  have hcg0 : ∀ h, 1 ≤ h → cgTotal 0 (1 - 0) h = 1 := by
    intro h hh
    cases h with
    | zero =>
        have hfalse : False := by omega
        exact False.elim hfalse
    | succ n =>
        rw [cgTotal_succ]
        simp
  have hlaw0 : ∀ h, 1 ≤ h →
      BinaryTreeAddressLaw.law 0 le_rfl zero_le_one (terminationByDepth h) = 1 := by
    intro h hh
    have hlaw := law_terminationByDepth le_rfl zero_le_one h
    rw [hcg0 h hh, ENNReal.ofReal_one] at hlaw
    exact hlaw
  have hcg1 : ∀ h, cgTotal 1 (1 - 1) h = 0 := by
    intro h
    induction h with
    | zero =>
        show (∑ t ∈ cgTrees 0, t.weight 1 (1 - 1)) = 0
        rw [cgTrees_zero]
        exact Finset.sum_empty
    | succ h ih =>
        rw [cgTotal_succ, ih]
        norm_num
  have hlaw1 : ∀ h,
      BinaryTreeAddressLaw.law 1 zero_le_one le_rfl (terminationByDepth h) = 0 := by
    intro h
    have hlaw := law_terminationByDepth zero_le_one le_rfl h
    rw [hcg1 h, ENNReal.ofReal_zero] at hlaw
    exact hlaw
  have hmem : (fun _ : List Bool => false) ∈ terminationByDepth 1 := by
    rw [hT1]
    rfl
  exact ⟨hlaw0, hlaw1, hmem⟩


end Cslib.Language

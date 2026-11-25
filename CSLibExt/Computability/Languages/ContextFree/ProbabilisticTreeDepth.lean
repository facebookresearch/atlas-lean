/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.ProbabilisticTreeCylinders

/-!
# Termination within bounded depth as a tree-cylinder partition

The event that the random binary tree terminates within depth `h` is
the finite pairwise-disjoint union of the cylinders of the trees of
depth at most `h`, and its probability under the binary address law
is the total `p`/`1 - p` weight of those trees.
-/

@[expose] public section

open MeasureTheory

namespace Cslib.Language

/-- The event that the random binary tree read off `ω` terminates within depth `h`,
counting a leaf as depth one. It is defined operationally: never at depth `0`, and
within depth `h + 1` when the root is a leaf, or the root branches and both the left
and the right subtree (read through the prefix shifts) terminate within depth `h`. -/
def terminationByDepth : ℕ → Set BinaryTreeAddressLaw.Ω
  | 0 => ∅
  | h + 1 => BinaryTreeAddressLaw.leafAt [] ∪
      (BinaryTreeAddressLaw.branchAt [] ∩
        (BinaryTreeAddressLaw.shiftLeft ⁻¹' terminationByDepth h) ∩
          (BinaryTreeAddressLaw.shiftRight ⁻¹' terminationByDepth h))

theorem terminationByDepth_zero : terminationByDepth 0 = ∅ := by rfl

theorem terminationByDepth_succ (h : ℕ) :
    terminationByDepth (h + 1) =
      BinaryTreeAddressLaw.leafAt [] ∪
        (BinaryTreeAddressLaw.branchAt [] ∩
          (BinaryTreeAddressLaw.shiftLeft ⁻¹' terminationByDepth h) ∩
            (BinaryTreeAddressLaw.shiftRight ⁻¹' terminationByDepth h)) := by rfl

/-- Each termination event is measurable: induction on `h`, using measurability of the
root events and of the prefix shifts. -/
theorem measurableSet_terminationByDepth (h : ℕ) :
    MeasurableSet (terminationByDepth h) := by
  induction h with
  | zero =>
      rw [terminationByDepth_zero]
      exact MeasurableSet.empty
  | succ h ih =>
      rw [terminationByDepth_succ]
      exact MeasurableSet.union (BinaryTreeAddressLaw.measurableSet_leafAt [])
        (MeasurableSet.inter
          (MeasurableSet.inter (BinaryTreeAddressLaw.measurableSet_branchAt [])
            ((BinaryTreeAddressLaw.measurable_shift [false]) ih))
          ((BinaryTreeAddressLaw.measurable_shift [true]) ih))

/-- Terminating within depth `h` implies terminating within depth `h + 1`. -/
theorem terminationByDepth_subset_succ (h : ℕ) :
    terminationByDepth h ⊆ terminationByDepth (h + 1) := by
  induction h with
  | zero =>
      rw [terminationByDepth_zero]
      exact Set.empty_subset _
  | succ h ih =>
      rw [terminationByDepth_succ, terminationByDepth_succ]
      exact Set.union_subset_union (Set.Subset.refl _)
        (Set.inter_subset_inter
          (Set.inter_subset_inter (Set.Subset.refl _) (Set.preimage_mono ih))
          (Set.preimage_mono ih))

theorem monotone_terminationByDepth : Monotone terminationByDepth :=
  monotone_nat_of_le_succ terminationByDepth_subset_succ

/-- The termination event is exactly the union of the cylinders of the trees of depth at
most `h`. Induction on `h`, rewriting the successor step with `treeCylinder_leaf`,
`treeCylinder_node` and `cgTrees_succ`. -/
theorem terminationByDepth_eq_biUnion (h : ℕ) :
    terminationByDepth h = ⋃ t ∈ cgTrees h, treeCylinder t := by
  induction h with
  | zero =>
      simp [terminationByDepth_zero, cgTrees_zero]
  | succ h ih =>
      rw [terminationByDepth_succ h, cgTrees_succ h]
      apply Set.Subset.antisymm
      · rintro ω (hleaf | ⟨⟨hbranch, hL⟩, hR⟩)
        · have hmem : ω ∈ treeCylinder CGTree.leaf := by
            rw [treeCylinder_leaf]
            exact hleaf
          have htin : CGTree.leaf ∈
              ({CGTree.leaf} ∪ ((cgTrees h ×ˢ cgTrees h).image
                fun p => CGTree.node p.1 p.2)) := by simp
          exact Set.mem_biUnion htin hmem
        · rw [ih] at hL hR
          simp only [Set.mem_preimage, Set.mem_iUnion] at hL hR
          obtain ⟨l, hlmem, hl⟩ := hL
          obtain ⟨r, hrmem, hr⟩ := hR
          have hprod : (l, r) ∈ cgTrees h ×ˢ cgTrees h :=
            Finset.mem_product.mpr ⟨hlmem, hrmem⟩
          have himg : CGTree.node l r ∈ ((cgTrees h ×ˢ cgTrees h).image
              fun p => CGTree.node p.1 p.2) :=
            Finset.mem_image.mpr ⟨(l, r), hprod, rfl⟩
          have htin : CGTree.node l r ∈
              ({CGTree.leaf} ∪ ((cgTrees h ×ˢ cgTrees h).image
                fun p => CGTree.node p.1 p.2)) :=
            Finset.mem_union_right _ himg
          have hmem : ω ∈ treeCylinder (CGTree.node l r) := by
            rw [treeCylinder_node l r]
            exact ⟨⟨hbranch, hl⟩, hr⟩
          exact Set.mem_biUnion htin hmem
      · intro ω hmemU
        simp only [Set.mem_iUnion] at hmemU
        obtain ⟨t, ht, hmem⟩ := hmemU
        rw [Finset.mem_union] at ht
        cases ht with
        | inl hleaf =>
            rw [Finset.mem_singleton] at hleaf
            subst hleaf
            have h : ω ∈ BinaryTreeAddressLaw.leafAt [] := by
              rw [← treeCylinder_leaf]
              exact hmem
            exact Set.mem_union_left _ h
        | inr himg =>
            rw [Finset.mem_image] at himg
            obtain ⟨p, hprod, rfl⟩ := himg
            rw [Finset.mem_product] at hprod
            obtain ⟨hlmem, hrmem⟩ := hprod
            rw [treeCylinder_node p.1 p.2] at hmem
            obtain ⟨⟨hbranch, hL⟩, hR⟩ := hmem
            have hL' : BinaryTreeAddressLaw.shiftLeft ω ∈ terminationByDepth h := by
              rw [ih]
              exact Set.mem_biUnion hlmem hL
            have hR' : BinaryTreeAddressLaw.shiftRight ω ∈ terminationByDepth h := by
              rw [ih]
              exact Set.mem_biUnion hrmem hR
            exact Set.mem_union_right _ ⟨⟨hbranch, hL'⟩, hR'⟩

/-- The cylinders of the trees of depth at most `h` are pairwise disjoint. -/
theorem pairwiseDisjoint_treeCylinder_cgTrees (h : ℕ) :
    (↑(cgTrees h) : Set CGTree).PairwiseDisjoint treeCylinder := by
  intro t₁ _ t₂ _ hne
  exact treeCylinder_disjoint_of_ne hne

/-- The probability of terminating within depth `h` is the total weight of the trees of
depth at most `h`, with branch weight `p` and leaf weight `1 - p`. -/
theorem law_terminationByDepth {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℕ) :
    BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h) =
      ENNReal.ofReal (cgTotal p (1 - p) h) := by
  rw [terminationByDepth_eq_biUnion h]
  have hmu : BinaryTreeAddressLaw.law p hp0 hp1 (⋃ t ∈ cgTrees h, treeCylinder t) =
      ∑ t ∈ cgTrees h, BinaryTreeAddressLaw.law p hp0 hp1 (treeCylinder t) := by
    apply measure_biUnion_finset
    · exact pairwiseDisjoint_treeCylinder_cgTrees h
    · intro t _
      exact BinaryTreeAddressLaw.measurableSet_cylinder _ _
  rw [hmu]
  simp only [treeCylinder_weight hp0 hp1]
  have hnonneg : ∀ t ∈ cgTrees h, 0 ≤ t.weight p (1 - p) :=
    fun t _ => cgWeight_nonneg p (1 - p) hp0 (sub_nonneg.mpr hp1) t
  have hsum := ENNReal.ofReal_sum_of_nonneg hnonneg
  rw [← hsum]
  rfl

/-- The same probability as a value of the Chi-Geman sequence, at the shifted index
`h + 1`. -/
theorem law_terminationByDepth_eq_chiGemanS {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℕ) :
    BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h) =
      ENNReal.ofReal (chiGemanS p (1 - p) (h + 1)) := by
  rw [law_terminationByDepth hp0 hp1 h, chiGemanS_link]

/-- Termination within depth `h` is a measurable event, monotone in `h`, equal to the
finite disjoint union of the cylinders of the trees of depth at most `h`; hence its
probability is `cgTotal p (1 - p) h`. -/
theorem terminationByDepth_tree_partition {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℕ) :
    MeasurableSet (terminationByDepth h) ∧
      Monotone terminationByDepth ∧
      terminationByDepth h = ⋃ t ∈ cgTrees h, treeCylinder t ∧
      (↑(cgTrees h) : Set CGTree).PairwiseDisjoint treeCylinder ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (terminationByDepth h) =
        ENNReal.ofReal (cgTotal p (1 - p) h) := by
  exact ⟨measurableSet_terminationByDepth h, monotone_terminationByDepth,
    terminationByDepth_eq_biUnion h, pairwiseDisjoint_treeCylinder_cgTrees h,
    law_terminationByDepth hp0 hp1 h⟩

end Cslib.Language

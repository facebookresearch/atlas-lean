/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.DeficiencyZero.API
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Tests for the reaction-network structure API: the empty network (no complexes, no linkage
classes, deficiency `0`), a single self-reaction (an isolated complex, one linkage class, no
edge), two parallel reactions (an edge, one linkage class, not weakly reversible), two
disconnected linkage classes (`0 → A`, `2A → 3A`, deficiency `1`), and a reversible network
(weakly reversible, directed reachability equals linkage-class membership). -/

namespace MathlibExtTest.Biology.Dynamics.DeficiencyZero.API

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork

/-! ### The empty network -/

/-- The network with no reactions on one species. -/
def emptyNet : ReactionNetwork (Fin 1) Empty where
  src := Empty.elim
  prod := Empty.elim

example : emptyNet.complexes = ∅ := complexes_eq_empty
example : emptyNet.numLinkageClasses = 0 := numLinkageClasses_of_isEmpty
example : emptyNet.deficiency = 0 := deficiency_of_isEmpty
example : emptyNet.IsWeaklyReversible := isWeaklyReversible_of_isEmpty

/-! ### A single self-reaction `A → A`: an isolated complex -/

/-- The network with the single reaction `A → A`. -/
def selfNet : ReactionNetwork (Fin 1) Unit where
  src := fun _ => ![1]
  prod := fun _ => ![1]

theorem selfNet_complexes : selfNet.complexes = {![1]} := by
  ext y
  simp [complexes, selfNet]

/-- The only complex. -/
def selfA : selfNet.complexes := ⟨![1], by simp [selfNet_complexes]⟩

/-- Self-reactions give no edge of the linkage graph. -/
theorem selfNet_not_adj (c c' : selfNet.complexes) : ¬ selfNet.linkageGraph.Adj c c' := by
  rw [linkageGraph_adj]
  rintro ⟨hne, ⟨r, h, h'⟩ | ⟨r, h, h'⟩⟩
  · exact hne (Subtype.ext (h.symm.trans h'))
  · exact hne (Subtype.ext (h'.symm.trans h))

example (c : selfNet.complexes) : selfNet.linkageGraph.Reachable selfA c ↔ selfA = c :=
  reachable_iff_eq_of_forall_not_adj (selfNet_not_adj selfA)

theorem selfNet_numLinkageClasses : selfNet.numLinkageClasses = 1 :=
  le_antisymm numLinkageClasses_le_card_reactions numLinkageClasses_pos

theorem selfNet_stoichiometricSubspace : selfNet.stoichiometricSubspace = ⊥ := by
  simp [stoichiometricSubspace, selfNet]
  rfl

theorem selfNet_deficiency : selfNet.deficiency = 0 := by
  have hs : Module.finrank ℝ selfNet.stoichiometricSubspace = 0 := by
    rw [selfNet_stoichiometricSubspace]
    exact finrank_bot ℝ _
  simp [deficiency, selfNet_numLinkageClasses, selfNet_complexes, hs]

example : selfNet.IsWeaklyReversible := fun _ => .refl

/-! ### Parallel reactions `A → B`, `A → B` -/

/-- Two parallel copies of `A → B` on species `Fin 2`. -/
def parallelNet : ReactionNetwork (Fin 2) (Fin 2) where
  src := fun _ => ![1, 0]
  prod := fun _ => ![0, 1]

theorem parallelNet_adj :
    parallelNet.linkageGraph.Adj ⟨_, src_mem_complexes 0⟩ ⟨_, prod_mem_complexes 1⟩ := by
  rw [linkageGraph_adj]
  refine ⟨fun h => ?_, .inl ⟨0, rfl, rfl⟩⟩
  have := congrFun (congrArg Subtype.val h) 0
  simp [parallelNet] at this

theorem parallelNet_numLinkageClasses : parallelNet.numLinkageClasses = 1 := by
  refine le_antisymm (numLinkageClasses_le_card {⟨_, src_mem_complexes 0⟩} fun c => ?_)
    numLinkageClasses_pos
  obtain ⟨y, hy⟩ := c
  obtain ⟨r, rfl | rfl⟩ := mem_complexes.1 hy
  · exact ⟨_, Finset.mem_singleton_self _, .rfl⟩
  · exact ⟨_, Finset.mem_singleton_self _, (src_reachable_prod r).symm⟩

/-- No reaction leaves `B`, so `A → B` cannot be undone. -/
theorem parallelNet_not_isWeaklyReversible : ¬ parallelNet.IsWeaklyReversible := by
  intro h
  rcases Relation.ReflTransGen.cases_head (h 0) with h' | ⟨c, ⟨r, hr, -⟩, -⟩
  · have := congrFun h' 0
    simp [parallelNet] at this
  · have := congrFun hr 0
    simp [parallelNet] at this

/-! ### Two linkage classes: `0 → A` and `2A → 3A` -/

/-- The network `0 → A`, `2A → 3A` on one species. -/
def disconnNet : ReactionNetwork (Fin 1) (Fin 2) where
  src := ![![0], ![2]]
  prod := ![![1], ![3]]

theorem disconnNet_complexes : disconnNet.complexes = {![0], ![1], ![2], ![3]} := by
  ext y
  simp only [complexes, disconnNet, Set.mem_union, Set.mem_range, Fin.exists_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_insert_iff, Set.mem_singleton_iff,
    @eq_comm _ _ y]
  tauto

theorem disconnNet_card_complexes : Nat.card disconnNet.complexes = 4 := by
  rw [disconnNet_complexes, Nat.card_coe_set_eq]
  rw [Set.ncard_eq_toFinset_card']
  decide

/-- Reactions preserve whether the copy number is at most `1`, so `0` and `2A` lie in
different linkage classes. -/
theorem disconnNet_not_reachable :
    ¬ disconnNet.linkageGraph.Reachable ⟨_, src_mem_complexes 0⟩ ⟨_, src_mem_complexes 1⟩ := by
  intro h
  have := reachable_imp_iff_of_reacts (fun y => y 0 ≤ 1) ?_ h
  · simp [disconnNet] at this
  · rintro y y' ⟨r, rfl, rfl⟩
    fin_cases r <;> simp [disconnNet]

theorem disconnNet_numLinkageClasses : disconnNet.numLinkageClasses = 2 := by
  classical
  refine le_antisymm (numLinkageClasses_le_card_reactions.trans (by simp)) ?_
  have hne : (⟨_, src_mem_complexes 0⟩ : disconnNet.complexes) ≠ ⟨_, src_mem_complexes 1⟩ :=
    fun h => disconnNet_not_reachable (h ▸ .rfl)
  have := card_le_numLinkageClasses
    ({⟨_, src_mem_complexes 0⟩, ⟨_, src_mem_complexes 1⟩} : Finset disconnNet.complexes)
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro c (rfl | rfl) c' (rfl | rfl) h
      · rfl
      · exact absurd h disconnNet_not_reachable
      · exact absurd h.symm disconnNet_not_reachable
      · rfl)
  rwa [Finset.card_pair hne] at this

theorem disconnNet_stoichiometricSubspace : disconnNet.stoichiometricSubspace = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = v 0 • fun s => ((disconnNet.prod 0 s : ℝ) - disconnNet.src 0 s) := by
    funext s
    fin_cases s
    simp [disconnNet]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-- A nonzero deficiency: `δ = 4 - 2 - 1 = 1`. -/
theorem disconnNet_deficiency : disconnNet.deficiency = 1 := by
  have hs : Module.finrank ℝ disconnNet.stoichiometricSubspace = 1 := by
    rw [disconnNet_stoichiometricSubspace, finrank_top, Module.finrank_fin_fun]
  rw [deficiency, disconnNet_card_complexes, disconnNet_numLinkageClasses, hs]
  norm_num

/-! ### A reversible network `A ⇌ B` -/

/-- The network `A ⇌ B` on species `Fin 2`. -/
def revNet : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

theorem revNet_isWeaklyReversible : revNet.IsWeaklyReversible :=
  isWeaklyReversible_of_reversible fun r => by
    fin_cases r
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩

/-- In `A ⇌ B`, `B` reaches `A` along reactions, as it does in the linkage graph. -/
example : Relation.ReflTransGen revNet.Reacts (revNet.prod 0) (revNet.src 0) :=
  (revNet_isWeaklyReversible.reflTransGen_iff_reachable
    (c := ⟨_, prod_mem_complexes 0⟩) (c' := ⟨_, src_mem_complexes 0⟩)).2
    (src_reachable_prod 0).symm

example (c c' : revNet.complexes) (h : revNet.linkageGraph.Reachable c c') :
    Relation.ReflTransGen revNet.Reacts c c' :=
  isWeaklyReversible_iff_reachable.1 revNet_isWeaklyReversible c c' h

example (y y' : Fin 2 → ℕ) (h : Relation.ReflTransGen revNet.Reacts y y') :
    Relation.ReflTransGen revNet.Reacts y' y :=
  revNet_isWeaklyReversible.reflTransGen_symm h

end MathlibExtTest.Biology.Dynamics.DeficiencyZero.API

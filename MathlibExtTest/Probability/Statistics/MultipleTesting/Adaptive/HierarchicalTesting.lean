/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalTesting
public import MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni

/-!
# Tests for hierarchical testing

* **Two-level tree** (root `{0, 1, 2}` + three singleton children, `m = 3`): the tree is laminar,
  the adjusted levels are `α` and `α / 3`, the parent of each child is the root, and the rejection
  set for concrete p-values is computed from the definition.
* **FWER with one true null** on the two-level tree: with `α = 1/2`, variable `1` null with a
  `Uniform[0, 1]` p-value and the other nodes rejecting surely, the FWER computed from the
  definition is exactly `1/6 = α |N| / m`, so the bound of
  `measure_meinshausen_familywiseError_le_card` is attained; the theorem also applies
  (non-vacuity).
* **Deep tree** (dyadic tree of depth 3 on `m = 8` variables, 15 nodes): laminar; the levels of
  each depth sum to `α`, the levels of the two children of every internal node sum to the level of
  the node, and the levels along a root-to-leaf path are `α, α/2, α/4, α/8`; a leaf with
  p-value `0` is not rejected when an intermediate ancestor is accepted.
* **No rejections**: if the root is accepted nothing is rejected, even when every child has
  p-value `0` (Bonferroni on the leaves would reject all three).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalTesting

/-! ### Two-level tree: root + three children -/

/-- The root `{0, 1, 2}` with its three singleton children. -/
def tree3 : Finset (Finset (Fin 3)) := {Finset.univ, {0}, {1}, {2}}

theorem tree3_laminar : IsLaminar tree3 := by
  unfold IsLaminar tree3
  decide

/-- The adjusted level of the root is `α`. -/
theorem meinshausenLevel_root3 (α : ℝ) : meinshausenLevel α (Finset.univ : Finset (Fin 3)) = α := by
  simp [meinshausenLevel]

/-- The adjusted level of each child is `α / 3`. -/
theorem meinshausenLevel_child3 (α : ℝ) (i : Fin 3) : meinshausenLevel α {i} = α / 3 := by
  simp [meinshausenLevel]

/-- The levels of the three children sum to the level of the root. -/
theorem sum_children3 (α : ℝ) :
    meinshausenLevel α ({0} : Finset (Fin 3)) + meinshausenLevel α ({1} : Finset (Fin 3)) +
        meinshausenLevel α ({2} : Finset (Fin 3)) =
      meinshausenLevel α (Finset.univ : Finset (Fin 3)) := by
  simp only [meinshausenLevel_child3, meinshausenLevel_root3]
  ring

/-- The root is the parent of each child. -/
theorem isParent_root3 (i : Fin 3) : IsParent tree3 {i} Finset.univ := by
  refine ⟨by fin_cases i <;> simp [tree3], by simp [tree3], ?_, ?_⟩
  · fin_cases i <;> decide
  · unfold tree3
    fin_cases i <;> decide

/-- The root has no strict superset in the tree. -/
theorem root3_isRoot : ∀ E ∈ tree3, ¬ (Finset.univ : Finset (Fin 3)) ⊂ E := by
  unfold tree3
  decide

/-- On the two-level tree, the root is rejected iff its p-value passes `a univ`; a child is
rejected iff the root and the child both pass. Computed from the definition of
`hierRejections`. -/
theorem mem_hierRejections_tree3 (a p : Finset (Fin 3) → ℝ) (C : Finset (Fin 3)) :
    C ∈ hierRejections tree3 a p ↔
      (C = Finset.univ ∧ p Finset.univ ≤ a Finset.univ) ∨
      ((C = {0} ∨ C = {1} ∨ C = {2}) ∧ p Finset.univ ≤ a Finset.univ ∧ p C ≤ a C) := by
  rw [mem_hierRejections]
  simp only [tree3, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Finset.subset_univ, true_imp_iff]
  constructor
  · rintro ⟨hC | hC | hC | hC, hroot, h0, h1, h2⟩ <;> subst hC
    · exact Or.inl ⟨rfl, hroot⟩
    · exact Or.inr ⟨Or.inl rfl, hroot, h0 subset_rfl⟩
    · exact Or.inr ⟨Or.inr (Or.inl rfl), hroot, h1 subset_rfl⟩
    · exact Or.inr ⟨Or.inr (Or.inr rfl), hroot, h2 subset_rfl⟩
  · rintro (⟨rfl, hroot⟩ | ⟨hC | hC | hC, hroot, hpC⟩)
    · refine ⟨Or.inl rfl, hroot, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
    all_goals subst hC
    · refine ⟨Or.inr (Or.inl rfl), hroot, fun _ => hpC, ?_, ?_⟩ <;> intro h <;>
        exact absurd h (by decide)
    · refine ⟨Or.inr (Or.inr (Or.inl rfl)), hroot, ?_, fun _ => hpC, ?_⟩ <;> intro h <;>
        exact absurd h (by decide)
    · refine ⟨Or.inr (Or.inr (Or.inr rfl)), hroot, ?_, ?_, fun _ => hpC⟩ <;> intro h <;>
        exact absurd h (by decide)

/-- The top-down reading agrees with the definition on the two-level tree: the root is tested
unconditionally and child `i` is rejected iff it passes and the root was rejected. -/
theorem hierRejections_tree3_topDown (a p : Finset (Fin 3) → ℝ) (i : Fin 3) :
    (Finset.univ ∈ hierRejections tree3 a p ↔ p Finset.univ ≤ a Finset.univ) ∧
    ({i} ∈ hierRejections tree3 a p ↔
      p {i} ≤ a {i} ∧ Finset.univ ∈ hierRejections tree3 a p) := by
  rw [mem_hierRejections_iff_root root3_isRoot, mem_hierRejections_iff_parent (isParent_root3 i),
    mem_hierRejections_iff_root root3_isRoot]
  have hu : (Finset.univ : Finset (Fin 3)) ∈ tree3 := by simp [tree3]
  simp [hu]

/-- Concrete p-values on the two-level tree. -/
noncomputable def pv3 (C : Finset (Fin 3)) : ℝ :=
  if C = Finset.univ then 1 / 100 else if C = {0} then 1 / 1000 else if C = {1} then 1 / 5
  else 1 / 250

/-- At `α = 1/20` the levels are `1/20` (root) and `1/60` (children): the root and the
children `{0}` (`p = 1/1000`) and `{2}` (`p = 1/250`) are rejected; `{1}` (`p = 1/5`) is not. -/
theorem hierRejections_pv3 :
    hierRejections tree3 (meinshausenLevel (1 / 20)) pv3 = {Finset.univ, {0}, {2}} := by
  ext C
  rw [mem_hierRejections_tree3]
  simp only [meinshausenLevel_root3, Finset.mem_insert, Finset.mem_singleton]
  have hroot : pv3 Finset.univ = 1 / 100 := by simp [pv3]
  have h0 : pv3 {0} = 1 / 1000 := by simp [pv3]
  have h1 : pv3 {1} = 1 / 5 := by simp [pv3]
  have h2 : pv3 {2} = 1 / 250 := by simp [pv3]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨hC | hC | hC, -, hpC⟩) <;> try subst hC
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rw [h1, meinshausenLevel_child3] at hpC
      norm_num at hpC
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨rfl, by rw [hroot]; norm_num⟩
    · exact Or.inr ⟨Or.inl rfl, by rw [hroot]; norm_num, by
        rw [h0, meinshausenLevel_child3]; norm_num⟩
    · exact Or.inr ⟨Or.inr (Or.inr rfl), by rw [hroot]; norm_num, by
        rw [h2, meinshausenLevel_child3]; norm_num⟩

/-! ### FWER on the two-level tree with one true null -/

/-- The probability space: `[0, 1]` with Lebesgue measure. -/
noncomputable def μU : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- Variable `1` is null and its cluster `{1}` has a `Uniform[0, 1]` p-value `ω`; every other
node has p-value `0` (it is rejected surely). -/
noncomputable def pω (C : Finset (Fin 3)) (ω : ℝ) : ℝ := if C = {1} then ω else 0

theorem pω_one : pω {1} = id := by
  funext ω
  simp [pω]

theorem pω_univ (ω : ℝ) : pω Finset.univ ω = 0 := by
  simp only [pω, ite_eq_right_iff]
  intro h
  exact absurd h (by decide)

/-- The family-wise error event, computed from the definition: `{1}` is rejected exactly when
`ω ≤ α / 3 = 1/6`. -/
theorem familywiseError_set_pω :
    {ω | (hierRejections tree3 (meinshausenLevel (1 / 2)) (fun C => pω C ω) ∩ {{1}}).Nonempty} =
      Set.Iic (1 / 6) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Iic, Finset.inter_singleton]
  split_ifs with h
  · rw [mem_hierRejections_tree3, pω_univ, pω_one, meinshausenLevel_root3,
      meinshausenLevel_child3] at h
    simp only [Finset.singleton_nonempty, true_iff]
    rcases h with ⟨h, -⟩ | ⟨-, -, h⟩
    · exact absurd h (by decide)
    · simp only [id] at h
      linarith
  · simp only [Finset.not_nonempty_empty, false_iff, not_le]
    rw [mem_hierRejections_tree3, pω_univ, pω_one, meinshausenLevel_root3,
      meinshausenLevel_child3] at h
    push Not at h
    have := h.2 (Or.inr (Or.inl rfl)) (by norm_num)
    simp only [id] at this
    linarith

/-- **The FWER on this model is exactly `1/6`**, computed from the definition. -/
theorem familywiseError_pω :
    μU {ω | (hierRejections tree3 (meinshausenLevel (1 / 2)) (fun C => pω C ω) ∩
      {{1}}).Nonempty} = ENNReal.ofReal (1 / 6) := by
  have hset : Set.Iic (1 / 6 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 6) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, by linarith⟩
  rw [familywiseError_set_pω, μU, Measure.restrict_apply measurableSet_Iic, hset,
    Real.volume_Icc]
  norm_num

/-- The FWER `1/6` equals the bound `α |N| / m = (1/2) · 1 / 3` (the bound is attained) and is
at most `α = 1/2`. -/
theorem familywiseError_pω_eq_bound :
    μU {ω | (hierRejections tree3 (meinshausenLevel (1 / 2)) (fun C => pω C ω) ∩
      {{1}}).Nonempty} = ENNReal.ofReal ((1 / 2) * ({1} : Finset (Fin 3)).card / 3) ∧
    μU {ω | (hierRejections tree3 (meinshausenLevel (1 / 2)) (fun C => pω C ω) ∩
      {{1}}).Nonempty} ≤ ENNReal.ofReal (1 / 2) := by
  rw [familywiseError_pω]
  refine ⟨by norm_num, ENNReal.ofReal_le_ofReal (by norm_num)⟩

/-- The `Uniform[0, 1]` p-value of the true null is valid. -/
theorem isValidPValue_pω_one : IsValidPValue μU (pω {1}) := by
  rw [pω_one]
  exact isValidPValue_of_hasLaw_uniform HasLaw.id

/-- **Non-vacuity**: the hypotheses of `measure_meinshausen_familywiseError_le_card` hold on this
model, and the theorem yields the bound `α |N| / m = 1/6` that the computation attains. -/
theorem familywiseError_pω_le_of_theorem :
    μU {ω | (hierRejections tree3 (meinshausenLevel (1 / 2)) (fun C => pω C ω) ∩
      {{1}}).Nonempty} ≤ ENNReal.ofReal ((1 / 2) * ({1} : Finset (Fin 3)).card / 3) :=
  measure_meinshausen_familywiseError_le_card μU tree3_laminar pω
    (H0 := {{1}}) (by simp [tree3]) (by simpa using isValidPValue_pω_one)
    (N := {1}) (by simp) (by norm_num) (by norm_num)

/-- The false-null nodes are rejected surely on this model (the procedure has power). -/
theorem mem_hierRejections_pω_zero (ω : ℝ) :
    ({0} : Finset (Fin 3)) ∈ hierRejections tree3 (meinshausenLevel (1 / 2)) (fun C => pω C ω) := by
  rw [mem_hierRejections_tree3, pω_univ, meinshausenLevel_root3, meinshausenLevel_child3]
  refine Or.inr ⟨Or.inl rfl, by norm_num, ?_⟩
  simp only [pω]
  split_ifs with h
  · exact absurd h (by decide)
  · norm_num

/-! ### No rejections: the root gates the whole tree -/

/-- The root is accepted (`p = 9/10 > 1/20`); every child has p-value `0`. -/
noncomputable def pvNone (C : Finset (Fin 3)) : ℝ := if C = Finset.univ then 9 / 10 else 0

/-- **Nothing is rejected** when the root is accepted, even though every child has p-value `0`.
Computed from the definition. -/
theorem hierRejections_pvNone : hierRejections tree3 (meinshausenLevel (1 / 20)) pvNone = ∅ := by
  ext C
  simp only [mem_hierRejections_tree3, meinshausenLevel_root3, Finset.notMem_empty, iff_false]
  have : ¬ pvNone Finset.univ ≤ 1 / 20 := by simp [pvNone]; norm_num
  tauto

/-- For contrast, Bonferroni on the three leaves at the same `α = 1/20` rejects all three. -/
theorem bonferroniRejections_pvNone_leaves :
    bonferroniRejections (1 / 20) (fun i : Fin 3 => pvNone {i}) = Finset.univ := by
  ext i
  simp only [bonferroniRejections, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  have : pvNone {i} = 0 := by
    simp only [pvNone]
    split_ifs with h
    · fin_cases i <;> exact absurd h (by decide)
    · rfl
  rw [this]
  norm_num

/-! ### Deep tree: dyadic tree of depth 3 on eight variables -/

/-- Depth 1: two halves. -/
def depth1 : Finset (Finset (Fin 8)) := {{0, 1, 2, 3}, {4, 5, 6, 7}}

/-- Depth 2: four pairs. -/
def depth2 : Finset (Finset (Fin 8)) := {{0, 1}, {2, 3}, {4, 5}, {6, 7}}

/-- Depth 3: eight singletons. -/
def depth3 : Finset (Finset (Fin 8)) := {{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}}

/-- The dyadic tree: root, two halves, four pairs, eight leaves (15 nodes). -/
def tree8 : Finset (Finset (Fin 8)) := insert Finset.univ (depth1 ∪ depth2 ∪ depth3)

theorem card_tree8 : tree8.card = 15 := by decide

theorem tree8_laminar : IsLaminar tree8 := by
  unfold IsLaminar
  decide +kernel

/-- The levels of each depth sum to `α`: depth 0. -/
theorem sum_depth0 (α : ℝ) : meinshausenLevel α (Finset.univ : Finset (Fin 8)) = α := by
  simp [meinshausenLevel]

/-- Depth 1: `α · 4/8 + α · 4/8 = α`. -/
theorem sum_depth1 (α : ℝ) : ∑ C ∈ depth1, meinshausenLevel α C = α := by
  rw [depth1, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [meinshausenLevel]
  rw [show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 by decide,
    show ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 by decide]
  push_cast
  ring

/-- Depth 2: four pairs, `4 · α · 2/8 = α`. -/
theorem sum_depth2 (α : ℝ) : ∑ C ∈ depth2, meinshausenLevel α C = α := by
  rw [depth2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [meinshausenLevel]
  rw [show ({0, 1} : Finset (Fin 8)).card = 2 by decide,
    show ({2, 3} : Finset (Fin 8)).card = 2 by decide,
    show ({4, 5} : Finset (Fin 8)).card = 2 by decide,
    show ({6, 7} : Finset (Fin 8)).card = 2 by decide]
  push_cast
  ring

/-- Depth 3: eight leaves, `8 · α/8 = α`. -/
theorem sum_depth3 (α : ℝ) : ∑ C ∈ depth3, meinshausenLevel α C = α := by
  rw [depth3]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [meinshausenLevel, Finset.card_singleton]
  push_cast
  ring

/-- The two children of every internal node have levels summing to the level of the node. -/
theorem sum_children8 (α : ℝ) :
    meinshausenLevel α ({0, 1, 2, 3} : Finset (Fin 8)) +
        meinshausenLevel α ({4, 5, 6, 7} : Finset (Fin 8)) =
      meinshausenLevel α (Finset.univ : Finset (Fin 8)) ∧
    meinshausenLevel α ({0, 1} : Finset (Fin 8)) + meinshausenLevel α ({2, 3} : Finset (Fin 8)) =
      meinshausenLevel α ({0, 1, 2, 3} : Finset (Fin 8)) ∧
    meinshausenLevel α ({4, 5} : Finset (Fin 8)) + meinshausenLevel α ({6, 7} : Finset (Fin 8)) =
      meinshausenLevel α ({4, 5, 6, 7} : Finset (Fin 8)) ∧
    ∀ i j : Fin 8, i ≠ j → ({i, j} : Finset (Fin 8)) ∈ depth2 →
      meinshausenLevel α ({i} : Finset (Fin 8)) + meinshausenLevel α {j} =
        meinshausenLevel α {i, j} := by
  refine ⟨?_, ?_, ?_, fun i j hij _ => ?_⟩
  · simp only [meinshausenLevel, Finset.card_univ, Fintype.card_fin]
    rw [show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 by decide,
      show ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 by decide]
    push_cast
    ring
  · simp only [meinshausenLevel]
    rw [show ({0, 1} : Finset (Fin 8)).card = 2 by decide,
      show ({2, 3} : Finset (Fin 8)).card = 2 by decide,
      show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 by decide]
    push_cast
    ring
  · simp only [meinshausenLevel]
    rw [show ({4, 5} : Finset (Fin 8)).card = 2 by decide,
      show ({6, 7} : Finset (Fin 8)).card = 2 by decide,
      show ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 by decide]
    push_cast
    ring
  · simp only [meinshausenLevel, Finset.card_singleton, Finset.card_pair hij]
    push_cast
    ring

/-- Along the path root `⊃ {0,1,2,3} ⊃ {0,1} ⊃ {0}` the levels halve: `α, α/2, α/4, α/8`. -/
theorem meinshausenLevel_path8 (α : ℝ) :
    meinshausenLevel α (Finset.univ : Finset (Fin 8)) = α ∧
    meinshausenLevel α ({0, 1, 2, 3} : Finset (Fin 8)) = α / 2 ∧
    meinshausenLevel α ({0, 1} : Finset (Fin 8)) = α / 4 ∧
    meinshausenLevel α ({0} : Finset (Fin 8)) = α / 8 := by
  refine ⟨sum_depth0 α, ?_, ?_, ?_⟩ <;> simp only [meinshausenLevel]
  · rw [show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 by decide]
    push_cast
    ring
  · rw [show ({0, 1} : Finset (Fin 8)).card = 2 by decide]
    push_cast
    ring
  · simp

/-- `{0, 1}` is the parent of `{0}` in the deep tree. -/
theorem isParent_pair8 : IsParent tree8 {0} {0, 1} := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  unfold tree8
  decide +kernel

/-- In the deep tree, a leaf with p-value `0` is not rejected when an intermediate ancestor
(`{4, 5}`) is accepted. Computed from the definition. -/
theorem leaf_not_rejected_tree8 {α : ℝ} (hα : α ≤ 1) :
    ({5} : Finset (Fin 8)) ∉ hierRejections tree8 (meinshausenLevel α)
      (fun C => if C = {4, 5} then 1 else 0) := by
  intro h
  have h45 := (mem_hierRejections.mp h).2 {4, 5} (by decide) (by decide)
  simp only [↓reduceIte] at h45
  have hle : meinshausenLevel α ({4, 5} : Finset (Fin 8)) = α / 4 := by
    simp only [meinshausenLevel]
    rw [show ({4, 5} : Finset (Fin 8)).card = 2 by decide]
    push_cast
    ring
  rw [hle] at h45
  linarith

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalTesting

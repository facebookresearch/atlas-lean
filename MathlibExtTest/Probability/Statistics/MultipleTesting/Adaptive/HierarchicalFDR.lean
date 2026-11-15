/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalFDR

/-!
# Tests for hierarchical FDR control (Yekutieli)

* **BH index at the extremes**, from the definition: all `k` p-values at most `q` give index `k`;
  all above `q` give index `0`.
* **All p-values below `q`**: Yekutieli's procedure rejects every node of any tree.
* **Two-level tree** (root `{0, 1, 2}` + three singleton children): the strict ancestors and the
  two sibling families, computed from the definitions.
* **Power over Meinshausen**: children with p-values `1/50, 1/40, 1/30` and `q = 1/20` are all
  rejected (BH in the child family has cutoff `1/20`), while Meinshausen's level `α / 3 = 1/60`
  does not reject the child `{0}` (`p = 1/50`), the smallest of the three child p-values.
* **Gating**: if the root has p-value `9/10 > q`, nothing is rejected, though every child has
  p-value `0`.
* **Exact FDR, bound attained** (one node, `Uniform[0, 1]` null p-value): the full-tree FDR
  computed from the definition is exactly `q`, the hypotheses of
  `integral_treeFDP_yekutieliRejections_le` hold (non-vacuity), and its bound evaluates to `q`.
* **Only tree nodes matter**: the mutual-independence corollary applies when every cluster,
  inside the tree or not, carries the same p-value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalFDR

/-! ### The BH index at the extremes -/

/-- If all `k ≥ 1` p-values are at most `q`, the BH index is `k`. -/
theorem bhIndex_eq_of_forall_le {k : ℕ} {q : ℝ} {x : Fin k → ℝ} (hk : 0 < k)
    (h : ∀ i, x i ≤ q) : bhIndex q x = k := by
  have hnum : numBelow x (q * (k : ℝ) / k) = k := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [mul_div_assoc, div_self hk', mul_one]
    unfold numBelow
    rw [Finset.filter_true_of_mem fun i _ => h i, Finset.card_univ, Fintype.card_fin]
  exact le_antisymm (bhIndex_le q x) (le_bhIndex le_rfl hnum.ge)

/-- If all p-values exceed `q ≥ 0`, the BH index is `0`. -/
theorem bhIndex_eq_zero_of_forall_gt {k : ℕ} {q : ℝ} {x : Fin k → ℝ} (hq : 0 ≤ q)
    (h : ∀ i, q < x i) : bhIndex q x = 0 := by
  have h1 := bhIndex_le_numBelow q x
  have hle : q * (bhIndex q x : ℝ) / k ≤ q := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hq]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_le_iff₀ hk']
      have : (bhIndex q x : ℝ) ≤ k := by exact_mod_cast bhIndex_le q x
      nlinarith
  have h0 : numBelow x (q * (bhIndex q x : ℝ) / k) = 0 := by
    unfold numBelow
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact absurd (hi.trans hle) (not_le.mpr (h i))
  omega

/-! ### All p-values below `q` -/

/-- **If every node's p-value is at most `q`, every node is rejected**: each family's BH cutoff
is then `q`, and every node and its ancestors pass it. -/
theorem yekutieliRejections_eq_self_of_forall_le {m : ℕ} {q : ℝ} {T : Finset (Finset (Fin m))}
    {p : Finset (Fin m) → ℝ} (h : ∀ D ∈ T, p D ≤ q) : yekutieliRejections q T p = T := by
  have hlevel : ∀ D ∈ T, yekutieliLevel q T p D = q := by
    intro D hD
    have hpos := card_siblingFamily_pos hD
    have hc : ((siblingFamily T D).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    unfold yekutieliLevel familyBHLevel
    rw [bhIndex_eq_of_forall_le (x := familyPValues p (siblingFamily T D)) hpos fun i =>
      h _ (siblingFamily_subset T D ((siblingFamily T D).equivFin.symm i).2),
      mul_div_assoc, div_self hc, mul_one]
  ext C
  constructor
  · intro hC
    exact hierRejections_subset _ _ _ hC
  · intro hC
    rw [mem_yekutieliRejections_iff hC]
    refine ⟨(h C hC).trans_eq (hlevel C hC).symm, fun E hE => ?_⟩
    have hET := (mem_strictAncestors.mp hE).1
    exact (h E hET).trans_eq (hlevel E hET).symm

/-! ### Two-level tree: root + three children -/

/-- The root `{0, 1, 2}` with its three singleton children. -/
def tree3 : Finset (Finset (Fin 3)) := {Finset.univ, {0}, {1}, {2}}

theorem strictAncestors_tree3_univ : strictAncestors tree3 Finset.univ = ∅ := by
  ext D
  simp only [mem_strictAncestors, Finset.notMem_empty, iff_false, not_and]
  intro _ h
  exact (ssubset_iff_subset_not_subset.mp h).2 (Finset.subset_univ D)

theorem strictAncestors_tree3_child (i : Fin 3) :
    strictAncestors tree3 {i} = {Finset.univ} := by
  ext D
  rw [mem_strictAncestors, Finset.mem_singleton]
  constructor
  · rintro ⟨hD, hlt⟩
    simp only [tree3, Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · rfl
    all_goals exact absurd (Finset.card_lt_card hlt) (by simp)
  · rintro rfl
    exact ⟨by simp [tree3], by fin_cases i <;> decide⟩

/-- The children form one family. -/
theorem siblingFamily_tree3_child (i : Fin 3) :
    siblingFamily tree3 {i} = {{0}, {1}, {2}} := by
  ext D
  rw [mem_siblingFamily, strictAncestors_tree3_child]
  constructor
  · rintro ⟨hD, h⟩
    simp only [tree3, Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · rw [strictAncestors_tree3_univ] at h
      exact absurd h (by simp)
    all_goals simp
  · intro hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    all_goals exact ⟨by simp [tree3], strictAncestors_tree3_child _⟩

/-- The root forms a family on its own. -/
theorem siblingFamily_tree3_univ : siblingFamily tree3 Finset.univ = {Finset.univ} := by
  ext D
  rw [mem_siblingFamily, strictAncestors_tree3_univ, Finset.mem_singleton]
  constructor
  · rintro ⟨hD, h⟩
    simp only [tree3, Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl
    · rfl
    all_goals rw [strictAncestors_tree3_child] at h; exact absurd h (by simp)
  · rintro rfl
    exact ⟨by simp [tree3], strictAncestors_tree3_univ⟩

/-! ### Power over Meinshausen's levels -/

/-- Root p-value `1/100`; children `1/50, 1/40, 1/30`. -/
noncomputable def pvPow (C : Finset (Fin 3)) : ℝ :=
  if C = Finset.univ then 1 / 100 else if C = {0} then 1 / 50 else if C = {1} then 1 / 40
  else 1 / 30

/-- **Yekutieli's procedure at `q = 1/20` rejects all four nodes.** -/
theorem yekutieliRejections_pvPow : yekutieliRejections (1 / 20) tree3 pvPow = tree3 := by
  refine yekutieliRejections_eq_self_of_forall_le fun D hD => ?_
  simp only [tree3, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl <;> norm_num [pvPow]

/-- **Meinshausen's procedure at `α = 1/20` does not reject the child `{0}`**: its level is
`α / 3 = 1/60 < 1/50`. -/
theorem not_mem_hierRejections_meinshausen_pvPow :
    ({0} : Finset (Fin 3)) ∉ hierRejections tree3 (meinshausenLevel (1 / 20)) pvPow := by
  intro h
  have := le_of_mem_hierRejections h
  norm_num [pvPow, meinshausenLevel] at this

/-! ### Gating: an accepted root blocks the tree -/

/-- Root p-value `9/10`; every child has p-value `0`. -/
noncomputable def pvGate (C : Finset (Fin 3)) : ℝ := if C = Finset.univ then 9 / 10 else 0

/-- **Nothing is rejected** when the root fails BH at `q = 1/20`, although every child has
p-value `0`. Computed from the definitions: the root family's BH index is `0`. -/
theorem yekutieliRejections_pvGate : yekutieliRejections (1 / 20) tree3 pvGate = ∅ := by
  have hmem : ∀ D ∈ siblingFamily tree3 Finset.univ, D = Finset.univ := fun D hD => by
    rw [siblingFamily_tree3_univ] at hD
    exact Finset.mem_singleton.mp hD
  have hlevel : yekutieliLevel (1 / 20) tree3 pvGate Finset.univ = 0 := by
    unfold yekutieliLevel familyBHLevel
    rw [bhIndex_eq_zero_of_forall_gt (by norm_num) fun i => ?_]
    · simp
    · unfold familyPValues
      rw [hmem _ ((siblingFamily tree3 Finset.univ).equivFin.symm i).2]
      norm_num [pvGate]
  ext C
  simp only [Finset.notMem_empty, iff_false]
  intro hC
  have hCT : C ∈ tree3 := hierRejections_subset _ _ _ hC
  rw [mem_yekutieliRejections_iff hCT] at hC
  have hroot : pvGate Finset.univ ≤ yekutieliLevel (1 / 20) tree3 pvGate Finset.univ := by
    simp only [tree3, Finset.mem_insert, Finset.mem_singleton] at hCT
    rcases hCT with rfl | rfl | rfl | rfl
    · exact hC.1
    all_goals exact hC.2 _ (by rw [strictAncestors_tree3_child]; exact Finset.mem_singleton_self _)
  rw [hlevel] at hroot
  norm_num [pvGate] at hroot

/-! ### One node: the FDR equals the bound -/

/-- The tree with one node. -/
def tree1 : Finset (Finset (Fin 1)) := {Finset.univ}

/-- The node is a true null. -/
def H1 : Finset (Finset (Fin 1)) := {Finset.univ}

/-- The probability space: `[0, 1]` with Lebesgue measure. -/
noncomputable def μU : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure μU := ⟨by simp [μU]⟩

/-- The node has the `Uniform[0, 1]` p-value `ω`; other clusters (outside the tree) get `0`. -/
noncomputable def p1 (D : Finset (Fin 1)) (ω : ℝ) : ℝ := if D = Finset.univ then ω else 0

theorem p1_univ : p1 Finset.univ = id := by
  funext ω
  simp [p1]

theorem univ_mem_tree1 : (Finset.univ : Finset (Fin 1)) ∈ tree1 := by simp [tree1]

theorem siblingFamily_tree1 : siblingFamily tree1 Finset.univ = {Finset.univ} := by
  ext D
  rw [mem_siblingFamily]
  simp only [tree1, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl, -⟩
    rfl
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- The node is rejected iff `ω ≤ q`, so the full-tree FDP is the indicator of `ω ≤ q`.
Computed from the definitions. -/
theorem treeFDP_tree1 {q : ℝ} (hq : 0 ≤ q) (ω : ℝ) :
    treeFDP H1 (yekutieliRejections q tree1 fun D => p1 D ω) = (Set.Iic q).indicator 1 ω := by
  by_cases hω : ω ≤ q
  · rw [yekutieliRejections_eq_self_of_forall_le, Set.indicator_of_mem (Set.mem_Iic.mpr hω)]
    · simp [treeFDP, tree1, H1]
    · intro D hD
      rw [tree1, Finset.mem_singleton] at hD
      subst hD
      simpa [p1] using hω
  · rw [Set.indicator_of_notMem (fun h => hω (Set.mem_Iic.mp h))]
    have hlevel : yekutieliLevel q tree1 (fun D => p1 D ω) Finset.univ = 0 := by
      unfold yekutieliLevel familyBHLevel
      rw [bhIndex_eq_zero_of_forall_gt hq fun i => ?_]
      · simp
      · unfold familyPValues
        have hmem : ∀ D ∈ siblingFamily tree1 Finset.univ, D = Finset.univ := fun D hD => by
          rw [siblingFamily_tree1] at hD
          exact Finset.mem_singleton.mp hD
        rw [hmem _ ((siblingFamily tree1 Finset.univ).equivFin.symm i).2]
        show q < p1 Finset.univ ω
        rw [p1_univ]
        exact not_le.mp hω
    have hempty : yekutieliRejections q tree1 (fun D => p1 D ω) = ∅ := by
      ext C
      simp only [Finset.notMem_empty, iff_false]
      intro hC
      have hCT : C ∈ tree1 := hierRejections_subset _ _ _ hC
      have hle := ((mem_yekutieliRejections_iff hCT).mp hC).1
      rw [tree1, Finset.mem_singleton] at hCT
      subst hCT
      rw [hlevel, p1_univ] at hle
      exact hω (hle.trans hq)
    simp [hempty, treeFDP]

/-- **The full-tree FDR of the one-node tree is exactly `q`**, computed from the definitions. -/
theorem integral_treeFDP_tree1 {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, treeFDP H1 (yekutieliRejections q tree1 fun D => p1 D ω) ∂μU = q := by
  have hset : Set.Iic q ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 q := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, h2.trans hq₁⟩
  simp_rw [treeFDP_tree1 hq₀]
  rw [integral_indicator_one measurableSet_Iic, measureReal_def, μU,
    Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal hq₀]

/-- **Non-vacuity, bound attained.** The hypotheses of `integral_treeFDP_yekutieliRejections_le`
hold for the one-node tree, and its bound evaluates to `q`, the exact FDR. -/
theorem integral_treeFDP_tree1_le_of_theorem {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, treeFDP H1 (yekutieliRejections q tree1 fun D => p1 D ω) ∂μU ≤ q := by
  have hp : ∀ D, Measurable (p1 D) := by
    intro D
    by_cases h : D = Finset.univ
    · subst h
      rw [p1_univ]
      exact measurable_id
    · have : p1 D = fun _ => 0 := by
        funext ω
        exact ite_eq_right_of_eq_false _ _ (eq_false h)
      rw [this]
      exact measurable_const
  have hindep : ∀ C ∈ tree1, iIndepFun
      (fun i : Fin (siblingFamily tree1 C).card =>
        p1 ((siblingFamily tree1 C).equivFin.symm i).1) μU := by
    intro C _
    have hcard : (siblingFamily tree1 C).card ≤ 1 :=
      (Finset.card_le_card (siblingFamily_subset _ _)).trans (by simp [tree1])
    have : Subsingleton (Fin (siblingFamily tree1 C).card) :=
      ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
    exact iIndepFun.of_subsingleton
  have hnull : ∀ D ∈ tree1, D ∈ H1 → IsValidPValue μU (p1 D) := by
    intro D hD _
    rw [tree1, Finset.mem_singleton] at hD
    subst hD
    rw [p1_univ]
    exact isValidPValue_of_hasLaw_uniform HasLaw.id
  have hout : ∀ C ∈ tree1, IndepFun
      (fun ω (i : Fin (siblingFamily tree1 C).card) =>
        p1 ((siblingFamily tree1 C).equivFin.symm i).1 ω)
      (fun ω => outsideFamily tree1 (fun D => p1 D ω) (siblingFamily tree1 C)) μU := by
    intro C hC
    rw [tree1, Finset.mem_singleton] at hC
    subst hC
    have hconst : (fun ω => outsideFamily tree1 (fun D => p1 D ω)
        (siblingFamily tree1 Finset.univ)) = fun _ => 0 := by
      funext ω D
      show (if D ∈ tree1 \ siblingFamily tree1 Finset.univ then p1 D ω else 0) = 0
      refine ite_eq_right_of_eq_false _ _ (eq_false fun hD => ?_)
      obtain ⟨hDT, hDS⟩ := Finset.mem_sdiff.mp hD
      rw [tree1, Finset.mem_singleton] at hDT
      subst hDT
      exact hDS (self_mem_siblingFamily univ_mem_tree1)
    rw [hconst]
    exact indepFun_const_right _ _
  have h := integral_treeFDP_yekutieliRejections_le μU p1 (fun D _ => hp D) H1 hindep hnull hout
    q hq₀ hq₁
  have himg : tree1.image (siblingFamily tree1) = {{Finset.univ}} := by
    change Finset.image (siblingFamily tree1) {Finset.univ} = _
    rw [Finset.image_singleton, siblingFamily_tree1]
  have hset : {ω | IsTestedFamily q tree1 (fun D => p1 D ω) {Finset.univ}} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro C hC
    rw [Finset.mem_singleton] at hC
    subst hC
    refine isTested_of_root fun E hE hlt => ?_
    exact (ssubset_iff_subset_not_subset.mp hlt).2 (Finset.subset_univ E)
  have h1 : μU.real Set.univ = 1 := by simp [measureReal_def]
  rw [himg, Finset.sum_singleton, hset, h1,
    show ({Finset.univ} : Finset (Finset (Fin 1))) ∩ H1 = {Finset.univ} from Finset.inter_self _,
    Finset.card_singleton] at h
  simpa using h

/-- **Only the nodes of the tree enter the independence corollary.** Here every cluster, in the
tree or not, carries the same `Uniform[0, 1]` p-value `ω`; the corollary needs measurability and
mutual independence only over the single node of `tree1`. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, treeFDP H1 (yekutieliRejections q tree1 fun _ => ω) ∂μU ≤
      ∑ S ∈ tree1.image (siblingFamily tree1),
        q * ((S ∩ H1).card : ℝ) / S.card *
          μU.real {ω | IsTestedFamily q tree1 (fun _ => ω) S} := by
  have : Subsingleton tree1 := ⟨fun a b => Subtype.ext
    ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  exact integral_treeFDP_yekutieliRejections_le_of_iIndepFun μU (fun _ ω => ω)
    (fun _ _ => measurable_id) iIndepFun.of_subsingleton H1
    (fun _ _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id) q hq₀ hq₁

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.HierarchicalFDR

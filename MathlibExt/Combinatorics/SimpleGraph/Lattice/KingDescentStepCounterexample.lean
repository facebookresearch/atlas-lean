/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample

/-!
# A 4-thin walk refuting one-step king descent

`kda_KingDescentStep Vc seed` asks every off-support interior site other than `seed` to have one
of its four lexicographically smaller king neighbours (left, lower left, below, lower right) in the
off-support interior. It implies king connectivity (`kda_kingRowLinked_of_descentStep`), but it is
not necessary.

The walk `kda_stairDR` traces the polygon
`(0, 1) → (0, 3) → (3, 3) → (3, 2) → (4, 2) → (4, 0) → (2, 0) → (2, 1) → (0, 1)`. Its off-support
interior is `{(1, 2), (2, 2), (3, 1)}` (`kda_interior_eq`), with least site `(3, 1)`. The walk is
4-thin and its interior is king row-linked from `(3, 1)`, but all four smaller king neighbours of
`(1, 2)` are on the walk, so one-step descent fails (`kda_descentStep_false_but_theorem_true`).

## Main definitions

* `StatMech.Lattice.kda_stairDR`: the walk described above.
* `StatMech.Lattice.kda_KingDescentStep Vc seed`: one-step king descent.

## Main results

* `StatMech.Lattice.kda_kingRowLinked_of_descentStep`: one-step king descent gives a king
  row-linked seed.
* `StatMech.Lattice.kda_interior_eq`, `StatMech.Lattice.kda_stairDR_fourThin`: the interior of
  `kda_stairDR`, and 4-thinness.
* `StatMech.Lattice.kda_descentStep_lexMinSeed_false`: one-step descent fails at the least seed.
* `StatMech.Lattice.kda_descentStep_false_but_theorem_true`: 4-thin, king row-linked, and
  violating one-step descent.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The walk `(0, 1) → (0, 3) → (3, 3) → (3, 2) → (4, 2) → (4, 0) → (2, 0) → (2, 1) → (0, 1)`. -/
noncomputable def kda_stairDR :
    (hypercubicLattice 2).Walk ![(0 : ℤ), (1 : ℤ)] ![(0 : ℤ), (1 : ℤ)] :=
  let s1 : (hypercubicLattice 2).Walk ![(0 : ℤ), 1] ![0, 3] :=
    (jec_vsegUp 0 1 2).copy rfl (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![(0 : ℤ), 3] ![3, 3] :=
    (jec_hsegRight 3 0 3).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![(3 : ℤ), 3] ![3, 2] :=
    ((jec_vsegUp 3 2 1).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![(3 : ℤ), 2] ![4, 2] :=
    (jec_hsegRight 2 3 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s5 : (hypercubicLattice 2).Walk ![(4 : ℤ), 2] ![4, 0] :=
    ((jec_vsegUp 4 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s6 : (hypercubicLattice 2).Walk ![(4 : ℤ), 0] ![2, 0] :=
    ((jec_hsegRight 0 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let s7 : (hypercubicLattice 2).Walk ![(2 : ℤ), 0] ![2, 1] :=
    (jec_vsegUp 2 0 1).copy rfl (by ext i; fin_cases i <;> simp)
  let s8 : (hypercubicLattice 2).Walk ![(2 : ℤ), 1] ![0, 1] :=
    ((jec_hsegRight 1 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  s1.append (s2.append (s3.append (s4.append (s5.append (s6.append (s7.append s8))))))

/-- The ray count of `kda_stairDR` at `z` counts the vertical sides of the walk that lie left of `z`
and contain the edge between rows `z 1 - 1` and `z 1`. -/
theorem kda_stairDR_raycount (z : Site 2) :
    jec_rayCount z kda_stairDR =
      (if 0 ≤ z 0 - 1 ∧ 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 1 + (2 : ℤ) - 1 then 1 else 0)
      + (if 3 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (1 : ℤ) - 1 then 1 else 0)
      + (if 4 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2 : ℤ) - 1 then 1 else 0)
      + (if 2 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (1 : ℤ) - 1 then 1 else 0) := by
  unfold kda_stairDR
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight]
  push_cast; ring_nf

/-- Every site of `kda_stairDR` lies on one of its eight sides. -/
theorem kda_stairDR_support_locus (p : Site 2) (hp : p ∈ kda_stairDR.support) :
      (p 0 = 0 ∧ 1 ≤ p 1 ∧ p 1 ≤ 3) ∨
      (p 1 = 3 ∧ 0 ≤ p 0 ∧ p 0 ≤ 3) ∨
      (p 0 = 3 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3) ∨
      (p 1 = 2 ∧ 3 ≤ p 0 ∧ p 0 ≤ 4) ∨
      (p 0 = 4 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) ∨
      (p 1 = 0 ∧ 2 ≤ p 0 ∧ p 0 ≤ 4) ∨
      (p 0 = 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ∨
      (p 1 = 1 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) := by
  unfold kda_stairDR at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with h|h|h|h|h|h|h|h
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 0 1 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 3 0 3 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 3 2 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 2 3 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 4 0 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 0 2 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 2 0 1 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 1 0 2 h; push_cast at *; omega

theorem kda_off_12 : (![1, 2] : Site 2) ∉ kda_stairDR.support := by
  intro h; have := kda_stairDR_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega

theorem kda_off_22 : (![2, 2] : Site 2) ∉ kda_stairDR.support := by
  intro h; have := kda_stairDR_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega

theorem kda_off_31 : (![3, 1] : Site 2) ∉ kda_stairDR.support := by
  intro h; have := kda_stairDR_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega

theorem kda_on_02 : (![0, 2] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  left
  exact sdc_vsegUp_mem' 0 1 2 2 (by norm_num) (by norm_num)

theorem kda_on_23 : (![2, 3] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_hsegRight_mem' 3 0 3 2 (by norm_num) (by norm_num)

theorem kda_on_32 : (![3, 2] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; left
  exact sdc_vsegUp_mem' 3 2 1 2 (by norm_num) (by norm_num)

theorem kda_on_21 : (![2, 1] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; right; left
  exact sdc_vsegUp_mem' 2 0 1 1 (by norm_num) (by norm_num)

theorem kda_on_11 : (![1, 1] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; right; right
  exact sdc_hsegRight_mem' 1 0 2 1 (by norm_num) (by norm_num)

theorem kda_on_01 : (![0, 1] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  left
  exact sdc_vsegUp_mem' 0 1 2 1 (by norm_num) (by norm_num)

theorem kda_interior_12 : (![1, 2] : Site 2) ∈ jec_leftRegion kda_stairDR := by
  rw [jec_mem_leftRegion, kda_stairDR_raycount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  decide

theorem kda_interior_22 : (![2, 2] : Site 2) ∈ jec_leftRegion kda_stairDR := by
  rw [jec_mem_leftRegion, kda_stairDR_raycount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  decide

theorem kda_interior_31 : (![3, 1] : Site 2) ∈ jec_leftRegion kda_stairDR := by
  rw [jec_mem_leftRegion, kda_stairDR_raycount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  decide

theorem kda_mem_interior_12 : (![1, 2] : Site 2) ∈ jil_offSupportInterior kda_stairDR :=
  (jil_mem_offSupportInterior kda_stairDR _).mpr ⟨kda_off_12, kda_interior_12⟩

theorem kda_mem_interior_22 : (![2, 2] : Site 2) ∈ jil_offSupportInterior kda_stairDR :=
  (jil_mem_offSupportInterior kda_stairDR _).mpr ⟨kda_off_22, kda_interior_22⟩

theorem kda_mem_interior_31 : (![3, 1] : Site 2) ∈ jil_offSupportInterior kda_stairDR :=
  (jil_mem_offSupportInterior kda_stairDR _).mpr ⟨kda_off_31, kda_interior_31⟩

theorem kda_on_33 : (![3, 3] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_hsegRight_mem' 3 0 3 3 (by norm_num) (by norm_num)

theorem kda_on_13 : (![1, 3] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_hsegRight_mem' 3 0 3 1 (by norm_num) (by norm_num)

theorem kda_on_41 : (![4, 1] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; left
  exact sdc_vsegUp_mem' 4 0 2 1 (by norm_num) (by norm_num)

theorem kda_on_42 : (![4, 2] : Site 2) ∈ kda_stairDR.support := by
  unfold kda_stairDR
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; left
  exact sdc_vsegUp_mem' 4 0 2 2 (by norm_num) (by norm_num)

/-- The off-support interior of `kda_stairDR` is `{(1, 2), (2, 2), (3, 1)}`. -/
theorem kda_interior_eq :
    jil_offSupportInterior kda_stairDR =
      {(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)} := by
  ext z
  rw [jil_mem_offSupportInterior, jec_mem_leftRegion, kda_stairDR_raycount]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have key : (z = (![1, 2] : Site 2) ↔ z 0 = 1 ∧ z 1 = 2) ∧
      (z = (![2, 2] : Site 2) ↔ z 0 = 2 ∧ z 1 = 2) ∧
      (z = (![3, 1] : Site 2) ↔ z 0 = 3 ∧ z 1 = 1) := by
    refine ⟨⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩, ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩,
      ⟨fun h => ?_, fun ⟨h0, h1⟩ => ?_⟩⟩
    · rw [h]; exact ⟨by simp, by simp⟩
    · ext i; fin_cases i <;> simp [h0, h1]
    · rw [h]; exact ⟨by simp, by simp⟩
    · ext i; fin_cases i <;> simp [h0, h1]
    · rw [h]; exact ⟨by simp, by simp⟩
    · ext i; fin_cases i <;> simp [h0, h1]
  rw [key.1, key.2.1, key.2.2]
  have mkEq : ∀ c0 c1 : ℤ, (z = (![c0, c1] : Site 2) ↔ z 0 = c0 ∧ z 1 = c1) := fun c0 c1 =>
    ⟨fun h => ⟨by rw [h]; simp, by rw [h]; simp⟩,
     fun ⟨h0, h1⟩ => by ext i; fin_cases i <;> simp [h0, h1]⟩
  have h13 : ¬ (z 0 = 1 ∧ z 1 = 3 ∧ z ∉ kda_stairDR.support) := fun ⟨a, b, c⟩ =>
    c ((mkEq 1 3).mpr ⟨a, b⟩ ▸ kda_on_13)
  have h23 : ¬ (z 0 = 2 ∧ z 1 = 3 ∧ z ∉ kda_stairDR.support) := fun ⟨a, b, c⟩ =>
    c ((mkEq 2 3).mpr ⟨a, b⟩ ▸ kda_on_23)
  have h32 : ¬ (z 0 = 3 ∧ z 1 = 2 ∧ z ∉ kda_stairDR.support) := fun ⟨a, b, c⟩ =>
    c ((mkEq 3 2).mpr ⟨a, b⟩ ▸ kda_on_32)
  have h33 : ¬ (z 0 = 3 ∧ z 1 = 3 ∧ z ∉ kda_stairDR.support) := fun ⟨a, b, c⟩ =>
    c ((mkEq 3 3).mpr ⟨a, b⟩ ▸ kda_on_33)
  have h41 : ¬ (z 0 = 4 ∧ z 1 = 1 ∧ z ∉ kda_stairDR.support) := fun ⟨a, b, c⟩ =>
    c ((mkEq 4 1).mpr ⟨a, b⟩ ▸ kda_on_41)
  have h42 : ¬ (z 0 = 4 ∧ z 1 = 2 ∧ z ∉ kda_stairDR.support) := fun ⟨a, b, c⟩ =>
    c ((mkEq 4 2).mpr ⟨a, b⟩ ▸ kda_on_42)
  set R : ℤ → ℤ → ℕ := fun a b =>
      (if 0 ≤ a - 1 ∧ 1 ≤ b - 1 ∧ b - 1 ≤ 1 + (2 : ℤ) - 1 then 1 else 0)
      + (if 3 ≤ a - 1 ∧ 2 ≤ b - 1 ∧ b - 1 ≤ 2 + (1 : ℤ) - 1 then 1 else 0)
      + (if 4 ≤ a - 1 ∧ 0 ≤ b - 1 ∧ b - 1 ≤ 0 + (2 : ℤ) - 1 then 1 else 0)
      + (if 2 ≤ a - 1 ∧ 0 ≤ b - 1 ∧ b - 1 ≤ 0 + (1 : ℤ) - 1 then 1 else 0) with hR
  have bounds : ∀ a b : ℤ, ¬ Even (R a b) → (1 ≤ b ∧ b ≤ 3) ∧ 1 ≤ a := by
    intro a b hodd
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    · by_contra hcon
      revert hodd
      simp only [hR]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
      decide
  have evenBig : ∀ a b : ℤ, 1 ≤ b → b ≤ 3 → 5 ≤ a → Even (R a b) := by
    intro a b _ _ ha
    simp only [hR]
    rcases (by omega : b = 1 ∨ b = 2 ∨ b = 3) with hb | hb | hb <;> subst hb
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
          ite_eq_left (by omega)]; decide
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
          ite_eq_right (by omega)]; decide
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]; decide
  constructor
  · rintro ⟨hoff, hodd⟩
    have hoddR : ¬ Even (R (z 0) (z 1)) := by simpa only [hR] using hodd
    obtain ⟨⟨hb1, hb2⟩, ha1⟩ := bounds (z 0) (z 1) hoddR
    have ha2 : z 0 ≤ 4 := by
      by_contra hcon
      exact hoddR (evenBig (z 0) (z 1) hb1 hb2 (by omega))
    rcases (by omega : z 0 = 1 ∨ z 0 = 2 ∨ z 0 = 3 ∨ z 0 = 4) with h0 | h0 | h0 | h0 <;>
      rcases (by omega : z 1 = 1 ∨ z 1 = 2 ∨ z 1 = 3) with h1 | h1 | h1
    · exact absurd (by simp only [hR, h0, h1]; decide) hoddR
    · exact Or.inl ⟨h0, h1⟩
    · exact absurd ⟨h0, h1, hoff⟩ h13
    · exact absurd (by simp only [hR, h0, h1]; decide) hoddR
    · exact Or.inr (Or.inl ⟨h0, h1⟩)
    · exact absurd ⟨h0, h1, hoff⟩ h23
    · exact Or.inr (Or.inr ⟨h0, h1⟩)
    · exact absurd ⟨h0, h1, hoff⟩ h32
    · exact absurd ⟨h0, h1, hoff⟩ h33
    · exact absurd ⟨h0, h1, hoff⟩ h41
    · exact absurd ⟨h0, h1, hoff⟩ h42
    · exact absurd (by simp only [hR, h0, h1]; decide) hoddR
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine ⟨(key.1.mpr ⟨h0, h1⟩) ▸ kda_off_12, ?_⟩
      simp only [h0, h1]; decide
    · refine ⟨(key.2.1.mpr ⟨h0, h1⟩) ▸ kda_off_22, ?_⟩
      simp only [h0, h1]; decide
    · refine ⟨(key.2.2.mpr ⟨h0, h1⟩) ▸ kda_off_31, ?_⟩
      simp only [h0, h1]; decide

/-- The fourteen sites of `kda_stairDR`. -/
theorem kda_support_cells (p : Site 2) (hp : p ∈ kda_stairDR.support) :
    p = (![0, 1] : Site 2) ∨ p = (![0, 2] : Site 2) ∨ p = (![0, 3] : Site 2) ∨
    p = (![1, 3] : Site 2) ∨ p = (![2, 3] : Site 2) ∨ p = (![3, 3] : Site 2) ∨
    p = (![3, 2] : Site 2) ∨ p = (![4, 2] : Site 2) ∨ p = (![4, 1] : Site 2) ∨
    p = (![4, 0] : Site 2) ∨ p = (![3, 0] : Site 2) ∨ p = (![2, 0] : Site 2) ∨
    p = (![2, 1] : Site 2) ∨ p = (![1, 1] : Site 2) := by
  have hl := kda_stairDR_support_locus p hp
  have toCell : ∀ a b : ℤ, p 0 = a → p 1 = b → p = (![a, b] : Site 2) := by
    intro a b h0 h1; ext i; fin_cases i <;> simp [h0, h1]
  have hpair : (p 0 = 0 ∧ p 1 = 1) ∨ (p 0 = 0 ∧ p 1 = 2) ∨ (p 0 = 0 ∧ p 1 = 3) ∨
      (p 0 = 1 ∧ p 1 = 3) ∨ (p 0 = 2 ∧ p 1 = 3) ∨ (p 0 = 3 ∧ p 1 = 3) ∨
      (p 0 = 3 ∧ p 1 = 2) ∨ (p 0 = 4 ∧ p 1 = 2) ∨ (p 0 = 4 ∧ p 1 = 1) ∨
      (p 0 = 4 ∧ p 1 = 0) ∨ (p 0 = 3 ∧ p 1 = 0) ∨ (p 0 = 2 ∧ p 1 = 0) ∨
      (p 0 = 2 ∧ p 1 = 1) ∨ (p 0 = 1 ∧ p 1 = 1) := by
    rcases hl with h|h|h|h|h|h|h|h <;> omega
  rcases hpair with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · rw [toCell _ _ h.1 h.2]; simp

/-- The walk `kda_stairDR` is 4-thin. -/
theorem kda_stairDR_fourThin : mci_FourThin kda_stairDR := by
  intro u v hu hv hadj
  have edges_mem : ∀ e : Sym2 (Site 2),
      (e = s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∨
       e = s((![0, 2] : Site 2), (![0, 3] : Site 2)) ∨
       e = s((![0, 3] : Site 2), (![1, 3] : Site 2)) ∨
       e = s((![1, 3] : Site 2), (![2, 3] : Site 2)) ∨
       e = s((![2, 3] : Site 2), (![3, 3] : Site 2)) ∨
       e = s((![3, 3] : Site 2), (![3, 2] : Site 2)) ∨
       e = s((![3, 2] : Site 2), (![4, 2] : Site 2)) ∨
       e = s((![4, 2] : Site 2), (![4, 1] : Site 2)) ∨
       e = s((![4, 1] : Site 2), (![4, 0] : Site 2)) ∨
       e = s((![4, 0] : Site 2), (![3, 0] : Site 2)) ∨
       e = s((![3, 0] : Site 2), (![2, 0] : Site 2)) ∨
       e = s((![2, 0] : Site 2), (![2, 1] : Site 2)) ∨
       e = s((![2, 1] : Site 2), (![1, 1] : Site 2)) ∨
       e = s((![1, 1] : Site 2), (![0, 1] : Site 2))) →
      e ∈ kda_stairDR.edges := by
    rintro e (h|h|h|h|h|h|h|h|h|h|h|h|h|h) <;> subst h <;> unfold kda_stairDR <;>
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_reverse]
    · left; have := ksd_vsegUp_edge_mem' 0 1 2 1 (by norm_num) (by norm_num); simpa using this
    · left; have := ksd_vsegUp_edge_mem' 0 1 2 2 (by norm_num) (by norm_num); simpa using this
    · right; left; have := ksd_hsegRight_edge_mem' 3 0 3 0 (by norm_num) (by norm_num)
      simpa using this
    · right; left; have := ksd_hsegRight_edge_mem' 3 0 3 1 (by norm_num) (by norm_num)
      simpa using this
    · right; left; have := ksd_hsegRight_edge_mem' 3 0 3 2 (by norm_num) (by norm_num)
      simpa using this
    · right; right; left
      have := ksd_vsegUp_edge_mem' 3 2 1 2 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
    · right; right; right; left
      have := ksd_hsegRight_edge_mem' 2 3 1 3 (by norm_num) (by norm_num); simpa using this
    · right; right; right; right; left
      have := ksd_vsegUp_edge_mem' 4 0 2 1 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
    · right; right; right; right; left
      have := ksd_vsegUp_edge_mem' 4 0 2 0 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
    · right; right; right; right; right; left
      have := ksd_hsegRight_edge_mem' 0 2 2 3 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
    · right; right; right; right; right; left
      have := ksd_hsegRight_edge_mem' 0 2 2 2 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
    · right; right; right; right; right; right; left
      have := ksd_vsegUp_edge_mem' 2 0 1 0 (by norm_num) (by norm_num); simpa using this
    · right; right; right; right; right; right; right
      have := ksd_hsegRight_edge_mem' 1 0 2 1 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
    · right; right; right; right; right; right; right
      have := ksd_hsegRight_edge_mem' 1 0 2 0 (by norm_num) (by norm_num); rw [Sym2.eq_swap]
      simpa using this
  have hu14 := kda_support_cells u hu
  have hv14 := kda_support_cells v hv
  apply edges_mem
  rcases hu14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hv14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first
        | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
        | (revert hadj; decide)

/-- One-step king descent: every off-support interior site `z ≠ seed` has its left, lower-left,
lower, or lower-right neighbour in the off-support interior. -/
def kda_KingDescentStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    (![z 0 - 1, z 1] : Site 2) ∈ jil_offSupportInterior Vc ∨
    (![z 0 - 1, z 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc ∨
    (![z 0, z 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc ∨
    (![z 0 + 1, z 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc

/-- The lower-left neighbour of a site is king-adjacent to it. -/
theorem kda_kingAdj_downLeft (x y : ℤ) :
    mci_kingGraph.Adj (![x, y] : Site 2) ![x - 1, y - 1] := by
  have h := mci_kingAdj_diag x y (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simpa only [show x + (-1) = x - 1 by ring, show y + (-1) = y - 1 by ring] using h

/-- The lower-right neighbour of a site is king-adjacent to it. -/
theorem kda_kingAdj_downRight (x y : ℤ) :
    mci_kingGraph.Adj (![x, y] : Site 2) ![x + 1, y - 1] := by
  have h := mci_kingAdj_diag x y 1 (-1) (Or.inl rfl) (Or.inr rfl)
  simpa only [show y + (-1) = y - 1 by ring] using h

/-- A king neighbour in the off-support interior that is lexicographically smaller gives a descent
step. -/
theorem kda_descentStep_to_neighbour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ} (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    {w : Site 2} (hw : w ∈ jil_offSupportInterior Vc)
    (hadj : mci_kingGraph.Adj (![x, y] : Site 2) w)
    (hlex : w 1 < y ∨ (w 1 = y ∧ w 0 < x)) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ u ∈ p.support, u ∈ jil_offSupportInterior Vc := by
  refine ⟨w, hw, ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hwL := (jil_mem_offSupportInterior Vc _ |>.mp hw).2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hwL
    refine rlc_lexMeasure_lt (z := (![x, y] : Site 2)) (z' := w)
      (by simpa using hb0a) (by simpa using hb0b) (by simpa using hb1a) (by simpa using hb1b)
      hd0a hd0b hd1a hd1b ?_
    simpa using hlex
  · refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro u hu
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h | h
    · subst h; exact hz
    · subst h; exact hw

/-- One-step king descent gives `kif_KingDownLink`. -/
theorem kda_kingDownLink_of_descentStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kda_KingDescentStep Vc seed) :
    kif_KingDownLink Vc seed M := by
  intro z hz hzs
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  rw [hzeq] at hz ⊢
  rcases hres z (hzeq ▸ hz) hzs with hL | hDL | hD | hDR
  · exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hL)
      (by simpa using kif_kingAdj_left (z 0) (z 1)) (Or.inr ⟨by simp, by simp⟩)
  · exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hDL)
      (by simpa using kda_kingAdj_downLeft (z 0) (z 1)) (Or.inl (by simp))
  · exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hD)
      (by simpa using kif_kingAdj_down (z 0) (z 1)) (Or.inl (by simp))
  · exact kda_descentStep_to_neighbour Vc M hMb hz (by simpa using hDR)
      (by simp) (Or.inl (by simp))

/-- One-step king descent gives a king row-linked seed. -/
theorem kda_kingRowLinked_of_descentStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kda_KingDescentStep Vc seed) :
    mci_KingRowLinked Vc seed :=
  kif_kingRowLinked_of_kingDownLink Vc M (kda_kingDownLink_of_descentStep Vc M hMb hres)

/-- The lexicographically least off-support interior site of `kda_stairDR` is `(3, 1)`. -/
theorem kda_seed_is_31 {M : ℤ}
    (hMb : ∀ z ∈ jec_leftRegion kda_stairDR, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {seed : Site 2} (hseed : seed ∈ jil_offSupportInterior kda_stairDR)
    (hmin : ∀ z ∈ jil_offSupportInterior kda_stairDR,
      rlc_lexMeasure M seed ≤ rlc_lexMeasure M z) :
    seed = (![3, 1] : Site 2) := by
  have hmem : seed ∈
      ({(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)} : Set (Site 2)) := by
    rw [← kda_interior_eq]; exact hseed
  have hbox31 := hMb _ kda_interior_31
  obtain ⟨⟨g0a, g0b⟩, ⟨g1a, g1b⟩⟩ := hbox31
  rcases hmem with h | h | h
  · exfalso
    have hbox12 := hMb _ kda_interior_12
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox12
    have hlt : rlc_lexMeasure M (![3, 1] : Site 2) < rlc_lexMeasure M (![1, 2] : Site 2) :=
      rlc_lexMeasure_lt (z := (![1, 2] : Site 2)) (z' := (![3, 1] : Site 2))
        (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
        (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
        (Or.inl (by norm_num))
    have := hmin _ kda_mem_interior_31
    rw [h] at this; omega
  · exfalso
    have hbox22 := hMb _ kda_interior_22
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox22
    have hlt : rlc_lexMeasure M (![3, 1] : Site 2) < rlc_lexMeasure M (![2, 2] : Site 2) :=
      rlc_lexMeasure_lt (z := (![2, 2] : Site 2)) (z' := (![3, 1] : Site 2))
        (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
        (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
        (Or.inl (by norm_num))
    have := hmin _ kda_mem_interior_31
    rw [h] at this; omega
  · exact h

/-- One-step king descent fails for `kda_stairDR` with seed `(3, 1)`: all four smaller king
neighbours of `(1, 2)` are on the walk. -/
theorem kda_stairDR_descentStep_false :
    ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) := by
  intro hres
  have hne : (![1, 2] : Site 2) ≠ (![3, 1] : Site 2) := by
    intro h; have := congrFun h 0; simp at this
  have hcoords : ((![1, 2] : Site 2) 0 = 1) ∧ ((![1, 2] : Site 2) 1 = 2) := ⟨by simp, by simp⟩
  obtain ⟨hc0, hc1⟩ := hcoords
  rcases hres (![1, 2] : Site 2) kda_mem_interior_12 hne with hL | hDL | hD | hDR
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hL).1
      (by simpa only [hc0, hc1, show (1 : ℤ) - 1 = 0 by ring] using kda_on_02)
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hDL).1
      (by simpa only [hc0, hc1, show (1 : ℤ) - 1 = 0 by ring, show (2 : ℤ) - 1 = 1 by ring]
        using kda_on_01)
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hD).1
      (by simpa only [hc0, hc1, show (2 : ℤ) - 1 = 1 by ring] using kda_on_11)
  · exact (jil_mem_offSupportInterior kda_stairDR _ |>.mp hDR).1
      (by simpa only [hc0, hc1, show (1 : ℤ) + 1 = 2 by ring, show (2 : ℤ) - 1 = 1 by ring]
        using kda_on_21)

/-- One-step king descent fails for `kda_stairDR` at its lexicographically least off-support
interior site. -/
theorem kda_descentStep_lexMinSeed_false :
    ∃ seed : Site 2, seed ∈ jil_offSupportInterior kda_stairDR ∧
      ¬ kda_KingDescentStep kda_stairDR seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded kda_stairDR
  obtain ⟨seed, hseed, hmin⟩ :=
    rlc_exists_lexMin_seed kda_stairDR kda_mem_interior_31 M
  refine ⟨seed, hseed, ?_⟩
  rw [kda_seed_is_31 hMb hseed hmin]
  exact kda_stairDR_descentStep_false

/-- The off-support interior of `kda_stairDR` is king row-linked from `(3, 1)`. -/
theorem kda_stairDR_kingRowLinked : mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) := by
  have hadj_r : mci_kingGraph.Adj (![1, 2] : Site 2) (![2, 2] : Site 2) := by
    simp
  have hadj_dr : mci_kingGraph.Adj (![2, 2] : Site 2) (![3, 1] : Site 2) := by
    have h := kda_kingAdj_downRight 2 2
    simpa only [show (2 : ℤ) + 1 = 3 by ring, show (2 : ℤ) - 1 = 1 by ring] using h
  intro z hz
  have hmem : z ∈ ({(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)}
      : Set (Site 2)) := by
    rw [← kda_interior_eq]; exact hz
  rcases hmem with h | h | h
  · subst h
    refine ⟨SimpleGraph.Walk.cons hadj_r (SimpleGraph.Walk.cons hadj_dr SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h
    · subst h; exact kda_mem_interior_12
    · subst h; exact kda_mem_interior_22
    · subst h; exact kda_mem_interior_31
  · subst h
    refine ⟨SimpleGraph.Walk.cons hadj_dr SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact kda_mem_interior_22
    · subst h; exact kda_mem_interior_31
  · subst h
    exact ⟨SimpleGraph.Walk.nil, by
      intro w hw
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      exact hw ▸ kda_mem_interior_31⟩

/-- The walk `kda_stairDR` is 4-thin and king row-linked from `(3, 1)`, but violates one-step king
descent there: one-step descent is not necessary for king connectivity of 4-thin walks. -/
theorem kda_descentStep_false_but_theorem_true :
    mci_FourThin kda_stairDR ∧
    mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) ∧
    ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) :=
  ⟨kda_stairDR_fourThin, kda_stairDR_kingRowLinked, kda_stairDR_descentStep_false⟩

end Lattice

end StatMech

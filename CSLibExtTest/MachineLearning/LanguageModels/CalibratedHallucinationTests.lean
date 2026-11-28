/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.LanguageModels.CalibratedHallucination

/-!
# Tests for the calibrated-hallucination finite core

Closed-instance checks for Kalai and Vempala, *Calibrated Language
Models Must Hallucinate*: the canonical two-point prior, boundary
cases, adaptive faithfulness, the two false source remarks,
regularity worlds, the divided-form bridges, the monofact rate,
instances of `binIndex_spec`, Lemma 2 and the bound form of Theorem 1
(including a weight-zero component whose facts miss the observed
set), the unnormalized `Mis_∞` characterization, and the axiom audit.
-/

namespace Cslib
namespace MachineLearning
namespace CalibratedHallucination

open MathlibExt.Probability.MarkovMixing (tvDist)
open Cslib.InformationRetrieval.PageRank (IsProbVec)

section Helpers

private theorem tri1 : ∀ y : Fin 1, y = 0 := by decide

private theorem tri2 : ∀ y : Fin 2, y = 0 ∨ y = 1 := by decide

private theorem tri3 : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide

private theorem tri4 :
    ∀ y : Fin 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide

private theorem part_top_univ {Y : Type*} [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (y : Y) :
    (⊤ : Finpartition (Finset.univ : Finset Y)).part y = Finset.univ := by
  have huniv :
      Finset.univ ∈ (⊤ : Finpartition (Finset.univ : Finset Y)).parts := by
    obtain ⟨a⟩ := (inferInstance : Nonempty Y)
    obtain ⟨t, ht, _⟩ := (⊤ : Finpartition (Finset.univ : Finset Y)).exists_mem
      (Finset.mem_univ a)
    have hsub := Finpartition.parts_top_subset (Finset.univ : Finset Y) ht
    rw [Finset.mem_singleton] at hsub
    rw [hsub] at ht
    exact ht
  exact (⊤ : Finpartition (Finset.univ : Finset Y)).part_eq_of_mem huniv
    (Finset.mem_univ y)

private theorem part_bot_single {Y : Type*} [Fintype Y] [DecidableEq Y]
    (y : Y) :
    (⊥ : Finpartition (Finset.univ : Finset Y)).part y = {y} :=
  (⊥ : Finpartition (Finset.univ : Finset Y)).part_eq_of_mem
    (Finpartition.mem_bot_iff.mpr ⟨y, Finset.mem_univ y, rfl⟩)
    (Finset.mem_singleton_self y)

private theorem coarsen_bot_eq {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D : Y → ℝ) (y : Y) :
    coarsen ⊥ D y = D y := by
  show (∑ z ∈ (⊥ : Finpartition (Finset.univ : Finset Y)).part y, D z) /
      ((⊥ : Finpartition (Finset.univ : Finset Y)).part y).card = D y
  rw [part_bot_single y, Finset.sum_singleton, Finset.card_singleton]
  norm_num

private theorem coarsen_top_eq {Y : Type*} [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (D : Y → ℝ) (hD : IsProbVec D) (y : Y) :
    coarsen ⊤ D y = 1 / (Fintype.card Y : ℝ) := by
  show (∑ z ∈ (⊤ : Finpartition (Finset.univ : Finset Y)).part y, D z) /
      ((⊤ : Finpartition (Finset.univ : Finset Y)).part y).card = _
  rw [part_top_univ y, hD.2, Finset.card_univ]

end Helpers

section T2

noncomputable def t2g : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 / 4 else 3 / 4

private theorem t2g0 : t2g 0 = 1 / 4 := by simp [t2g]

private theorem t2g1 : t2g 1 = 3 / 4 := by simp [t2g]

private theorem t2g_prob : IsProbVec t2g := by
  constructor
  · intro y
    rcases tri2 y with rfl | rfl
    · rw [t2g0]; norm_num
    · rw [t2g1]; norm_num
  · rw [Fin.sum_univ_two, t2g0, t2g1]
    norm_num

-- T2: coarsening at the bottom partition is the identity.
example (D : Fin 3 → ℝ) (y : Fin 3) : coarsen ⊥ D y = D y :=
  coarsen_bot_eq D y

-- T2: coarsening at the top partition is constant.
example (D : Fin 3 → ℝ) (hD : IsProbVec D) (y : Fin 3) :
    coarsen ⊤ D y = 1 / 3 := by
  have h := coarsen_top_eq D hD y
  rw [h]
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [hcard]

-- T2: every distribution is calibrated to itself.
example (D : Fin 3 → ℝ) : IsCalibratedTo D D :=
  ⟨⊥, by funext y; exact (coarsen_bot_eq D y).symm⟩

-- T2: `mis 1` against the uniform distribution at `(1/4, 3/4)`.
example : mis 1 t2g t2g = 1 / 4 := by
  rw [mis_one t2g_prob t2g_prob]
  show (1 / 2 : ℝ) * ∑ y : Fin 2,
      |(fun _ : Fin 2 => 1 / (Fintype.card (Fin 2) : ℝ)) y - t2g y| = 1 / 4
  rw [Fin.sum_univ_two]
  simp only [t2g0, t2g1]
  norm_num

-- T2: the boundary lemma with everything observed.
example : ∑ _i : Fin 1, (1 : ℝ) * max
    (∑ y ∈ Finset.univ \ Finset.univ, t2g y - tvDist (coarsen ⊤ t2g) t2g
      - ∑ y ∈ Finset.univ \ Finset.univ, t2g y) 0 = 0 :=
  expect_hallucination_gap_eq_zero_of_eq_univ (fun _ => 1) (fun _ => t2g)
    (fun _ => Finset.univ) t2g t2g_prob ⊤

end T2

section T1

noncomputable def t1p1 : Fin 3 → ℝ :=
  fun i => if i = 0 then 1 / 2 else if i = 1 then 1 / 2 else 0

noncomputable def t1p2 : Fin 3 → ℝ :=
  fun i => if i = 0 then 1 / 2 else if i = 1 then 0 else 1 / 2

noncomputable def t1g : Fin 3 → ℝ := fun _ => 1 / 3

noncomputable def t1w : Fin 2 → ℝ := fun _ => 1 / 2

noncomputable def t1p : Fin 2 → Fin 3 → ℝ :=
  fun i => if i = 0 then t1p1 else t1p2

def t1O : Finset (Fin 3) := {0}

noncomputable def t1F : (Fin 3 → ℝ) → Finset (Fin 3) :=
  fun p => Finset.univ.filter (fun y => p y ≠ 0) ∪ t1O

private theorem t1p1_0 : t1p1 0 = 1 / 2 := by simp [t1p1]

private theorem t1p1_1 : t1p1 1 = 1 / 2 := by simp [t1p1]

private theorem t1p1_2 : t1p1 2 = 0 := by simp [t1p1]

private theorem t1p2_0 : t1p2 0 = 1 / 2 := by simp [t1p2]

private theorem t1p2_1 : t1p2 1 = 0 := by simp [t1p2]

private theorem t1p2_2 : t1p2 2 = 1 / 2 := by simp [t1p2]

private theorem t1g_y (y : Fin 3) : t1g y = 1 / 3 := rfl

private theorem t1w0 : t1w 0 = 1 / 2 := rfl

private theorem t1w1 : t1w 1 = 1 / 2 := rfl

private theorem t1p_0 : t1p 0 = t1p1 := by simp [t1p]

private theorem t1p_1 : t1p 1 = t1p2 := by simp [t1p]

private theorem t1p1_prob : IsProbVec t1p1 := by
  constructor
  · intro y
    rcases tri3 y with rfl | rfl | rfl
    · rw [t1p1_0]; norm_num
    · rw [t1p1_1]; norm_num
    · rw [t1p1_2]
  · rw [Fin.sum_univ_three, t1p1_0, t1p1_1, t1p1_2]
    norm_num

private theorem t1p2_prob : IsProbVec t1p2 := by
  constructor
  · intro y
    rcases tri3 y with rfl | rfl | rfl
    · rw [t1p2_0]; norm_num
    · rw [t1p2_1]
    · rw [t1p2_2]; norm_num
  · rw [Fin.sum_univ_three, t1p2_0, t1p2_1, t1p2_2]
    norm_num

private theorem t1g_prob : IsProbVec t1g := by
  constructor
  · intro y
    rw [t1g_y y]; norm_num
  · rw [Fin.sum_univ_three]
    simp only [t1g_y]
    norm_num

private theorem t1w_prob : IsProbVec t1w := by
  constructor
  · intro i
    rcases tri2 i with rfl | rfl
    · rw [t1w0]; norm_num
    · rw [t1w1]; norm_num
  · rw [Fin.sum_univ_two, t1w0, t1w1]
    norm_num

private theorem t1p_prob : ∀ i, IsProbVec (t1p i) := by
  intro i
  rcases tri2 i with rfl | rfl
  · rw [t1p_0]; exact t1p1_prob
  · rw [t1p_1]; exact t1p2_prob

private theorem tvDist_nonneg {Y : Type*} [Fintype Y] (q g : Y → ℝ) :
    0 ≤ tvDist q g := by
  show (0 : ℝ) ≤ (1 / 2 : ℝ) * ∑ y, |q y - g y|
  apply mul_nonneg _ _
  · norm_num
  · apply Finset.sum_nonneg
    intro y _
    exact abs_nonneg _

private theorem t1U : Finset.univ \ t1O = ({1, 2} : Finset (Fin 3)) := by
  decide

private theorem t1F_p1 : t1F t1p1 = ({0, 1} : Finset (Fin 3)) := by
  ext y
  rcases tri3 y with rfl | rfl | rfl
  · simp [t1F, t1O]
  · simp [t1F, t1O, t1p1_1, show (1 : Fin 3) ≠ 0 by decide]
  · simp [t1F, t1O, t1p1_2, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide]

private theorem t1F_p2 : t1F t1p2 = ({0, 2} : Finset (Fin 3)) := by
  ext y
  rcases tri3 y with rfl | rfl | rfl
  · simp [t1F, t1O]
  · simp [t1F, t1O, t1p2_1, show (1 : Fin 3) ≠ 0 by decide,
      show (1 : Fin 3) ≠ 2 by decide]
  · simp [t1F, t1O, t1p2_2, show (2 : Fin 3) ≠ 0 by decide]

private theorem t1hU : (Finset.univ \ t1O).Nonempty := by
  rw [t1U]
  exact ⟨1, by simp⟩

private theorem t1not12 : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide

private theorem t1sumU_p1 : ∑ y ∈ Finset.univ \ t1O, t1p1 y = 1 / 2 := by
  rw [t1U, Finset.sum_insert t1not12, Finset.sum_singleton, t1p1_1, t1p1_2]
  norm_num

private theorem t1sumU_p2 : ∑ y ∈ Finset.univ \ t1O, t1p2 y = 1 / 2 := by
  rw [t1U, Finset.sum_insert t1not12, Finset.sum_singleton, t1p2_1, t1p2_2]
  norm_num

private theorem t1coarsen_top_p1 : coarsen ⊤ t1p1 = t1g := by
  funext y
  have h := coarsen_top_eq t1p1 t1p1_prob y
  rw [h, t1g_y y]
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [hcard]

private theorem t1coarsen_top_p2 : coarsen ⊤ t1p2 = t1g := by
  funext y
  have h := coarsen_top_eq t1p2 t1p2_prob y
  rw [h, t1g_y y]
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [hcard]

private theorem t1tv_p1 : tvDist (coarsen ⊤ t1p1) t1g = 0 := by
  rw [t1coarsen_top_p1]
  exact MathlibExt.Probability.MarkovMixing.tvDist_self t1g

private theorem t1tv_p2 : tvDist (coarsen ⊤ t1p2) t1g = 0 := by
  rw [t1coarsen_top_p2]
  exact MathlibExt.Probability.MarkovMixing.tvDist_self t1g

private theorem t1sumF_p1 : ∑ y ∈ Finset.univ \ t1F t1p1, t1g y = 1 / 3 := by
  rw [t1F_p1]
  have hsub : Finset.univ \ ({0, 1} : Finset (Fin 3)) = ({2} : Finset (Fin 3)) :=
    by decide
  rw [hsub, Finset.sum_singleton, t1g_y]

private theorem t1sumF_p2 : ∑ y ∈ Finset.univ \ t1F t1p2, t1g y = 1 / 3 := by
  rw [t1F_p2]
  have hsub : Finset.univ \ ({0, 2} : Finset (Fin 3)) = ({1} : Finset (Fin 3)) :=
    by decide
  rw [hsub, Finset.sum_singleton, t1g_y]

private theorem t1gap0 : (∑ y ∈ Finset.univ \ t1O, t1p 0 y
      - tvDist (coarsen ⊤ (t1p 0)) t1g
      - ∑ y ∈ Finset.univ \ t1F (t1p 0), t1g y) = 1 / 6 := by
  rw [t1p_0, t1sumU_p1, t1tv_p1, t1sumF_p1]
  norm_num

private theorem t1gap1 : (∑ y ∈ Finset.univ \ t1O, t1p 1 y
      - tvDist (coarsen ⊤ (t1p 1)) t1g
      - ∑ y ∈ Finset.univ \ t1F (t1p 1), t1g y) = 1 / 6 := by
  rw [t1p_1, t1sumU_p2, t1tv_p2, t1sumF_p2]
  norm_num

private theorem t1max0 : max (∑ y ∈ Finset.univ \ t1O, t1p 0 y
      - tvDist (coarsen ⊤ (t1p 0)) t1g
      - ∑ y ∈ Finset.univ \ t1F (t1p 0), t1g y) 0 = 1 / 6 := by
  rw [t1gap0]
  norm_num

private theorem t1max1 : max (∑ y ∈ Finset.univ \ t1O, t1p 1 y
      - tvDist (coarsen ⊤ (t1p 1)) t1g
      - ∑ y ∈ Finset.univ \ t1F (t1p 1), t1g y) 0 = 1 / 6 := by
  rw [t1gap1]
  norm_num

-- T1: the left side of Theorem 1 on the two-point prior is `1/6`.
example : (∑ i, t1w i * max (∑ y ∈ Finset.univ \ t1O, t1p i y
      - tvDist (coarsen ⊤ (t1p i)) t1g
      - ∑ y ∈ Finset.univ \ t1F (t1p i), t1g y) 0) = 1 / 6 := by
  rw [Fin.sum_univ_two, t1w0, t1w1, t1max0, t1max1]
  norm_num

private theorem t1filt1 : Finset.univ.filter (fun i => (1 : Fin 3) ∈ t1F (t1p i))
    = ({0} : Finset (Fin 2)) := by
  ext i
  rcases tri2 i with rfl | rfl
  · simp [t1p_0, t1F_p1, show (1 : Fin 3) ≠ 0 by decide]
  · simp [t1p_1, t1F_p2, show (1 : Fin 3) ≠ 0 by decide,
      show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 2) ≠ 0 by decide]

private theorem t1filt2 : Finset.univ.filter (fun i => (2 : Fin 3) ∈ t1F (t1p i))
    = ({1} : Finset (Fin 2)) := by
  ext i
  rcases tri2 i with rfl | rfl
  · simp [t1p_0, t1F_p1, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 2) ≠ 1 by decide]
  · simp [t1p_1, t1F_p2, show (2 : Fin 3) ≠ 0 by decide]

private theorem t1fA1 : (∑ i ∈ Finset.univ.filter
      (fun i => (1 : Fin 3) ∈ t1F (t1p i)), t1w i) = 1 / 2 := by
  rw [t1filt1, Finset.sum_singleton, t1w0]

private theorem t1fA2 : (∑ i ∈ Finset.univ.filter
      (fun i => (2 : Fin 3) ∈ t1F (t1p i)), t1w i) = 1 / 2 := by
  rw [t1filt2, Finset.sum_singleton, t1w1]

private theorem t1fB1 : (∑ i, t1w i * t1p i 1) = 1 / 4 := by
  rw [Fin.sum_univ_two, t1w0, t1w1, t1p_0, t1p_1, t1p1_1, t1p2_1]
  norm_num

private theorem t1fB2 : (∑ i, t1w i * t1p i 2) = 1 / 4 := by
  rw [Fin.sum_univ_two, t1w0, t1w1, t1p_0, t1p_1, t1p1_2, t1p2_2]
  norm_num

private theorem t1maxA : ((Finset.univ \ t1O).image (fun y =>
      ∑ i ∈ Finset.univ.filter (fun i => y ∈ t1F (t1p i)), t1w i)).max'
      (Finset.image_nonempty.mpr t1hU) = 1 / 2 := by
  rw [Finset.max'_eq_iff]
  constructor
  · rw [Finset.mem_image]
    exact ⟨1, by rw [t1U]; simp, t1fA1⟩
  · intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨y, hyU, rfl⟩ := hb
    rw [t1U] at hyU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyU
    rcases hyU with rfl | rfl
    · exact le_of_eq t1fA1
    · exact le_of_eq t1fA2

private theorem t1maxB : ((Finset.univ \ t1O).image
      (fun y => ∑ i, t1w i * t1p i y)).max'
      (Finset.image_nonempty.mpr t1hU) = 1 / 4 := by
  rw [Finset.max'_eq_iff]
  constructor
  · rw [Finset.mem_image]
    exact ⟨1, by rw [t1U]; simp, t1fB1⟩
  · intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨y, hyU, rfl⟩ := hb
    rw [t1U] at hyU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyU
    rcases hyU with rfl | rfl
    · exact le_of_eq t1fB1
    · exact le_of_eq t1fB2

-- T1: the right side of Theorem 1 on the two-point prior is `3/4`.
example : (((Finset.univ \ t1O).image (fun y =>
          ∑ i ∈ Finset.univ.filter (fun i => y ∈ t1F (t1p i)), t1w i)).max'
          (Finset.image_nonempty.mpr t1hU)
        + t1O.card * ((Finset.univ \ t1O).image
          (fun y => ∑ i, t1w i * t1p i y)).max'
          (Finset.image_nonempty.mpr t1hU)) = 3 / 4 := by
  rw [t1maxA, t1maxB]
  have hc : t1O.card = 1 := by simp [t1O]
  rw [hc]
  norm_num

-- T1: Theorem 1 applied to the canonical two-point prior.
example : (∑ i, t1w i * max (∑ y ∈ Finset.univ \ t1O, t1p i y
        - tvDist (coarsen ⊤ (t1p i)) t1g
        - ∑ y ∈ Finset.univ \ t1F (t1p i), t1g y) 0)
      ≤ (((Finset.univ \ t1O).image (fun y =>
          ∑ i ∈ Finset.univ.filter (fun i => y ∈ t1F (t1p i)), t1w i)).max'
          (Finset.image_nonempty.mpr t1hU)
        + t1O.card * ((Finset.univ \ t1O).image
          (fun y => ∑ i, t1w i * t1p i y)).max'
          (Finset.image_nonempty.mpr t1hU)) :=
  expect_hallucination_gap_le t1w t1w_prob t1p t1p_prob t1O (fun i => t1F (t1p i)) t1g
    t1g_prob ⊤ t1hU

noncomputable def t1d0 : Fin 3 → ℝ := fun y => if y = 0 then 1 else 0

private theorem t1d0_0 : t1d0 0 = 1 := by simp [t1d0]

private theorem t1d0_1 : t1d0 1 = 0 := by simp [t1d0]

private theorem t1d0_2 : t1d0 2 = 0 := by simp [t1d0]

private theorem t1F_d0 : t1F t1d0 = t1O := by
  ext y
  rcases tri3 y with rfl | rfl | rfl
  · simp [t1F, t1O]
  · simp [t1F, t1O, t1d0_1, show (1 : Fin 3) ≠ 0 by decide]
  · simp [t1F, t1O, t1d0_2, show (2 : Fin 3) ≠ 0 by decide]

-- T1 companion: mass at the observed point sees gap `0` under `⊥`.
example : (∑ _i : Fin 1, (1 : ℝ) * max (∑ y ∈ Finset.univ \ t1O, t1d0 y
      - tvDist (coarsen ⊥ t1d0) t1g
      - ∑ y ∈ Finset.univ \ t1F t1d0, t1g y) 0) = 0 := by
  rw [Fin.sum_univ_one]
  have hU : (∑ y ∈ Finset.univ \ t1O, t1d0 y) = 0 := by
    rw [t1U, Finset.sum_insert t1not12, Finset.sum_singleton, t1d0_1, t1d0_2]
    norm_num
  have hF : (∑ y ∈ Finset.univ \ t1F t1d0, t1g y) = 2 / 3 := by
    rw [t1F_d0, t1U, Finset.sum_insert t1not12, Finset.sum_singleton, t1g_y,
      t1g_y]
    norm_num
  have htv : 0 ≤ tvDist (coarsen ⊥ t1d0) t1g := by
    have hc : coarsen ⊥ t1d0 = t1d0 := funext (coarsen_bot_eq t1d0)
    rw [hc]
    exact tvDist_nonneg _ _
  have hgap : (∑ y ∈ Finset.univ \ t1O, t1d0 y
        - tvDist (coarsen ⊥ t1d0) t1g - ∑ y ∈ Finset.univ \ t1F t1d0, t1g y)
        ≤ 0 := by
    rw [hU, hF]
    linarith [htv]
  rw [max_eq_right hgap, mul_zero]

end T1

section T3

private theorem t3set : {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => t2g y ≤ z), t2g y)
        ≤ ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)}
    = Set.Ico (0 : ℝ) (1 / 4) := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ico]
  constructor
  · rintro ⟨⟨hz0, -⟩, hmass⟩
    refine ⟨hz0, ?_⟩
    by_contra hcon
    push Not at hcon
    have h0mem : (0 : Fin 2) ∈ Finset.univ.filter (fun y => t2g y ≤ z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [t2g0]
      exact hcon
    have hle : t2g 0 ≤
        (∑ y ∈ Finset.univ.filter (fun y => t2g y ≤ z), t2g y) :=
      Finset.single_le_sum (fun i _ => t2g_prob.1 i) h0mem
    rw [t2g0] at hle
    have hcon' : (1 / 4 : ℝ) ≤ ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) :=
      le_trans hle hmass
    norm_num at hcon'
  · rintro ⟨hz0, hz4⟩
    refine ⟨⟨hz0, by linarith⟩, ?_⟩
    have hemp : Finset.univ.filter (fun y : Fin 2 => t2g y ≤ z) = ∅ := by
      apply Finset.filter_false_of_mem
      intro y _
      rcases tri2 y with rfl | rfl
      · rw [t2g0]
        linarith
      · rw [t2g1]
        linarith
    rw [hemp, Finset.sum_empty]
    norm_num

private theorem t3thresh1 : binThreshold t2g 5 1 = 1 / 4 := by
  have h := congrArg sSup t3set
  rw [csSup_Ico (by norm_num : (0 : ℝ) < 1 / 4)] at h
  exact h

private theorem t3idx0 : binIndex t2g 5 0 = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  have h0mem : (0 : ℕ) ∈ {i : ℕ | t2g 0 ≤ binThreshold t2g 5 (i + 1)} := by
    simp only [Set.mem_ofPred_eq, t2g0, zero_add, t3thresh1]
    norm_num
  exact Nat.sInf_le h0mem

private theorem t3g01 : t2g 0 ≠ t2g 1 := by
  rw [t2g0, t2g1]
  norm_num

private theorem t3idx1ne : binIndex t2g 5 1 ≠ binIndex t2g 5 0 := by
  rw [t3idx0]
  have h0notin : (0 : ℕ) ∉ {i : ℕ | t2g 1 ≤ binThreshold t2g 5 (i + 1)} := by
    simp only [Set.mem_ofPred_eq, t2g1, zero_add, t3thresh1]
    norm_num
  have ht5 : binThreshold t2g 5 5 = 1 :=
    binThreshold_self t2g_prob (by norm_num)
  have h4mem : (4 : ℕ) ∈ {i : ℕ | t2g 1 ≤ binThreshold t2g 5 (i + 1)} := by
    show t2g 1 ≤ binThreshold t2g 5 (4 + 1)
    rw [show (4 : ℕ) + 1 = 5 from rfl, t2g1, ht5]
    norm_num
  have hmem : binIndex t2g 5 1
      ∈ {i : ℕ | t2g 1 ≤ binThreshold t2g 5 (i + 1)} :=
    Nat.sInf_mem ⟨4, h4mem⟩
  intro hcon
  rw [hcon] at hmem
  exact h0notin hmem

private theorem t3ker : Setoid.ker (binIndex t2g 5) = Setoid.ker t2g := by
  apply Setoid.ext
  intro x y
  show (binIndex t2g 5 x = binIndex t2g 5 y) ↔ (t2g x = t2g y)
  rcases tri2 x with rfl | rfl <;> rcases tri2 y with rfl | rfl
  · exact iff_of_true rfl rfl
  · exact iff_of_false (fun h => t3idx1ne h.symm) t3g01
  · exact iff_of_false t3idx1ne (fun h => t3g01 h.symm)
  · exact iff_of_true rfl rfl

private theorem t3part : adaptivePartition t2g 5 = levelPartition t2g := by
  unfold adaptivePartition levelPartition
  rw [t3ker]

-- T3: the adaptive partition is faithful at `(1/4, 3/4)` with `b = 5`.
example : adaptivePartition t2g 5 = levelPartition t2g := t3part

-- T3: hence `mis 5` agrees with `misInf` there.
example : mis 5 t2g t2g = misInf t2g t2g := by
  unfold mis misInf
  rw [t3part]

end T3

section T6

private theorem t6set : {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => t1p1 y ≤ z), t1p1 y)
        ≤ ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)}
    = Set.Ico (0 : ℝ) (1 / 2) := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ico]
  constructor
  · rintro ⟨⟨hz0, -⟩, hmass⟩
    refine ⟨hz0, ?_⟩
    by_contra hcon
    push Not at hcon
    have hfil : Finset.univ.filter (fun y : Fin 3 => t1p1 y ≤ z)
        = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro y _
      rcases tri3 y with rfl | rfl | rfl
      · rw [t1p1_0]
        exact hcon
      · rw [t1p1_1]
        exact hcon
      · rw [t1p1_2]
        exact hz0
    rw [hfil, t1p1_prob.2] at hmass
    norm_num at hmass
  · rintro ⟨hz0, hz2⟩
    refine ⟨⟨hz0, by linarith⟩, ?_⟩
    have hfil : Finset.univ.filter (fun y : Fin 3 => t1p1 y ≤ z)
        = ({2} : Finset (Fin 3)) := by
      ext y
      rcases tri3 y with rfl | rfl | rfl
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, t1p1_0]
        exact iff_of_false (by linarith) (by decide)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, t1p1_1]
        exact iff_of_false (by linarith) (by decide)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, t1p1_2]
        exact iff_of_true hz0 trivial
    rw [hfil, Finset.sum_singleton, t1p1_2]
    norm_num

private theorem t6thresh1 : binThreshold t1p1 2 1 = 1 / 2 := by
  have h := congrArg sSup t6set
  rw [csSup_Ico (by norm_num : (0 : ℝ) < 1 / 2)] at h
  exact h

private theorem t6idx : ∀ y, binIndex t1p1 2 y = 0 := by
  intro y
  apply le_antisymm _ (Nat.zero_le _)
  have h0mem : (0 : ℕ) ∈ {i : ℕ | t1p1 y ≤ binThreshold t1p1 2 (i + 1)} := by
    simp only [Set.mem_ofPred_eq, zero_add, t6thresh1]
    rcases tri3 y with rfl | rfl | rfl
    · rw [t1p1_0]
    · rw [t1p1_1]
    · rw [t1p1_2]
      norm_num
  exact Nat.sInf_le h0mem

private theorem t6part : ∀ y, (adaptivePartition t1p1 2).part y = Finset.univ := by
  intro y
  ext b
  unfold adaptivePartition
  classical
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  show (binIndex t1p1 2 y = binIndex t1p1 2 b) ↔ b ∈ Finset.univ
  rw [t6idx y, t6idx b]
  simp

private theorem t6coarsen : coarsen (adaptivePartition t1p1 2) t1p1 = t1g := by
  funext y
  show (∑ z ∈ (adaptivePartition t1p1 2).part y, t1p1 z)
      / ((adaptivePartition t1p1 2).part y).card = t1g y
  rw [t6part y, t1p1_prob.2, Finset.card_univ, t1g_y y]
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [hcard]

private theorem t6mis : mis 2 t1p1 t1p1 = 1 / 3 := by
  unfold mis
  rw [t6coarsen]
  show (1 / 2 : ℝ) * ∑ y : Fin 3, |t1g y - t1p1 y| = 1 / 3
  rw [Fin.sum_univ_three]
  simp only [t1g_y, t1p1_0, t1p1_1, t1p1_2]
  norm_num

private theorem t6cal : IsCalibratedTo t1p1 t1p1 :=
  ⟨⊥, by funext y; exact (coarsen_bot_eq t1p1 y).symm⟩

private theorem t6misInf : misInf t1p1 t1p1 = 0 :=
  isCalibratedTo_iff_misInf_eq_zero.mp t6cal

-- T6: `mis 2` is `1/3` on the constant-bin world.
example : mis 2 t1p1 t1p1 = 1 / 3 := t6mis

-- T6: `misInf` vanishes there.
example : misInf t1p1 t1p1 = 0 := t6misInf

-- T6: the world is calibrated to itself.
example : IsCalibratedTo t1p1 t1p1 := t6cal

-- T6: both false source remarks fail (`mis 2 ≠ misInf`, `mis 2 ≠ 0`).
example : mis 2 t1p1 t1p1 ≠ misInf t1p1 t1p1 ∧ mis 2 t1p1 t1p1 ≠ 0 := by
  constructor
  · rw [t6mis, t6misInf]
    norm_num
  · rw [t6mis]
    norm_num

end T6

section T7

private theorem t7push (D : Fin 4 → ℝ) (y : Fin 4) :
    pushforward id D y = D y := by
  unfold pushforward
  have hfil : Finset.univ.filter (fun x : Fin 4 => id x = y) = {y} := by
    ext x
    simp
  rw [hfil, Finset.sum_singleton]

private theorem t7train (D : Fin 4 → ℝ) (x : Fin 1 → Fin 4) :
    trainProb D x = D (x 0) := by
  unfold trainProb
  rw [Fin.prod_univ_one]

private theorem t7obs (x : Fin 1 → Fin 4) :
    observed id 0 x = {x 0, 0} := by
  unfold observed
  have huniv : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  rw [huniv, Finset.image_singleton]
  rfl

noncomputable def t7d1 : Fin 4 → ℝ := fun x => if x = 1 then 1 else 0
noncomputable def t7d2 : Fin 4 → ℝ := fun x => if x = 2 then 1 else 0
noncomputable def t7d3 : Fin 4 → ℝ := fun x => if x = 3 then 1 else 0
noncomputable def t7w : Fin 3 → ℝ := fun _ => 1 / 3
noncomputable def t7D : Fin 3 → Fin 4 → ℝ :=
  fun i => if i = 0 then t7d1 else if i = 1 then t7d2 else t7d3

private theorem t7d1_0 : t7d1 0 = 0 := by simp [t7d1]
private theorem t7d1_1 : t7d1 1 = 1 := by simp [t7d1]
private theorem t7d1_2 : t7d1 2 = 0 := by simp [t7d1]
private theorem t7d1_3 : t7d1 3 = 0 := by simp [t7d1]
private theorem t7d2_0 : t7d2 0 = 0 := by simp [t7d2]
private theorem t7d2_1 : t7d2 1 = 0 := by simp [t7d2]
private theorem t7d2_2 : t7d2 2 = 1 := by simp [t7d2]
private theorem t7d2_3 : t7d2 3 = 0 := by simp [t7d2]
private theorem t7d3_0 : t7d3 0 = 0 := by simp [t7d3]
private theorem t7d3_1 : t7d3 1 = 0 := by simp [t7d3]
private theorem t7d3_2 : t7d3 2 = 0 := by simp [t7d3]
private theorem t7d3_3 : t7d3 3 = 1 := by simp [t7d3]

private theorem t7w0 : t7w 0 = 1 / 3 := rfl
private theorem t7w1 : t7w 1 = 1 / 3 := rfl
private theorem t7w2 : t7w 2 = 1 / 3 := rfl

private theorem t7D_0 : t7D 0 = t7d1 := by simp [t7D]
private theorem t7D_1 : t7D 1 = t7d2 := by simp [t7D]
private theorem t7D_2 : t7D 2 = t7d3 := by simp [t7D]

private theorem t7F_d1 : facts id 0 t7d1 = ({0, 1} : Finset (Fin 4)) := by
  ext y
  rcases tri4 y with rfl | rfl | rfl | rfl
  · simp [facts]
  · simp [facts, t7push, t7d1_1, show (1 : Fin 4) ≠ 0 by decide]
  · simp [facts, t7push, t7d1_2, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide]
  · simp [facts, t7push, t7d1_3, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide]

private theorem t7F_d2 : facts id 0 t7d2 = ({0, 2} : Finset (Fin 4)) := by
  ext y
  rcases tri4 y with rfl | rfl | rfl | rfl
  · simp [facts]
  · simp [facts, t7push, t7d2_1, show (1 : Fin 4) ≠ 0 by decide,
      show (1 : Fin 4) ≠ 2 by decide]
  · simp [facts, t7push, t7d2_2, show (2 : Fin 4) ≠ 0 by decide]
  · simp [facts, t7push, t7d2_3, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 2 by decide]

private theorem t7F_d3 : facts id 0 t7d3 = ({0, 3} : Finset (Fin 4)) := by
  ext y
  rcases tri4 y with rfl | rfl | rfl | rfl
  · simp [facts]
  · simp [facts, t7push, t7d3_1, show (1 : Fin 4) ≠ 0 by decide,
      show (1 : Fin 4) ≠ 3 by decide]
  · simp [facts, t7push, t7d3_2, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 3 by decide]
  · simp [facts, t7push, t7d3_3, show (3 : Fin 4) ≠ 0 by decide]

private theorem t7F0 : facts id 0 (t7D 0) = ({0, 1} : Finset (Fin 4)) := by
  rw [t7D_0]
  exact t7F_d1

private theorem t7F1 : facts id 0 (t7D 1) = ({0, 2} : Finset (Fin 4)) := by
  rw [t7D_1]
  exact t7F_d2

private theorem t7F2 : facts id 0 (t7D 2) = ({0, 3} : Finset (Fin 4)) := by
  rw [t7D_2]
  exact t7F_d3

private theorem t7H0 :
    hallucinations id 0 (t7D 0) = ({2, 3} : Finset (Fin 4)) := by
  unfold hallucinations
  rw [t7F0]
  decide

private theorem t7H1 :
    hallucinations id 0 (t7D 1) = ({1, 3} : Finset (Fin 4)) := by
  unfold hallucinations
  rw [t7F1]
  decide

private theorem t7H2 :
    hallucinations id 0 (t7D 2) = ({1, 2} : Finset (Fin 4)) := by
  unfold hallucinations
  rw [t7F2]
  decide

private theorem t7filt1 :
    Finset.univ.filter (fun i : Fin 3 => (1 : Fin 4) ∈ facts id 0 (t7D i))
      = ({0} : Finset (Fin 3)) := by
  ext i
  rcases tri3 i with rfl | rfl | rfl
  · simp [t7F0, show (1 : Fin 4) ≠ 0 by decide]
  · simp [t7F1, show (1 : Fin 4) ≠ 0 by decide,
      show (1 : Fin 4) ≠ 2 by decide]
  · simp [t7F2, show (1 : Fin 4) ≠ 0 by decide,
      show (1 : Fin 4) ≠ 3 by decide]

private theorem t7filt2 :
    Finset.univ.filter (fun i : Fin 3 => (2 : Fin 4) ∈ facts id 0 (t7D i))
      = ({1} : Finset (Fin 3)) := by
  ext i
  rcases tri3 i with rfl | rfl | rfl
  · simp [t7F0, show (0 : Fin 3) ≠ 1 by decide,
      show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
  · simp [t7F1, show (2 : Fin 4) ≠ 0 by decide]
  · simp [t7F2, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 3 by decide]

private theorem t7filt3 :
    Finset.univ.filter (fun i : Fin 3 => (3 : Fin 4) ∈ facts id 0 (t7D i))
      = ({2} : Finset (Fin 3)) := by
  ext i
  rcases tri3 i with rfl | rfl | rfl
  · simp [t7F0, show (0 : Fin 3) ≠ 2 by decide,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide]
  · simp [t7F1, show (1 : Fin 3) ≠ 2 by decide,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 2 by decide]
  · simp [t7F2, show (3 : Fin 4) ≠ 0 by decide]

private theorem t7sparse : IsSparse id 0 t7w t7D 0 := by
  intro i _
  rcases tri3 i with rfl | rfl | rfl
  · have hFc : (facts id 0 (t7D 0)).card = 2 := by rw [t7F0]; decide
    have hHc : (hallucinations id 0 (t7D 0)).card = 2 := by
      rw [t7H0]
      decide
    rw [hFc, hHc]
    have hexp : Real.exp (-(0 : ℝ)) = 1 := by simp
    rw [hexp]
    norm_num
  · have hFc : (facts id 0 (t7D 1)).card = 2 := by rw [t7F1]; decide
    have hHc : (hallucinations id 0 (t7D 1)).card = 2 := by
      rw [t7H1]
      decide
    rw [hFc, hHc]
    have hexp : Real.exp (-(0 : ℝ)) = 1 := by simp
    rw [hexp]
    norm_num
  · have hFc : (facts id 0 (t7D 2)).card = 2 := by rw [t7F2]; decide
    have hHc : (hallucinations id 0 (t7D 2)).card = 2 := by
      rw [t7H2]
      decide
    rw [hFc, hHc]
    have hexp : Real.exp (-(0 : ℝ)) = 1 := by simp
    rw [hexp]
    norm_num

private theorem t7posFacts : HasRegularFacts id 0 t7w t7D 1 := by
  intro x hpos y hy y' hy'
  have hobs : observed id 0 x = {x 0, 0} := t7obs x
  rcases tri4 (x 0) with h0 | h1 | h2 | h3
  · exfalso
    have hsum : ∑ i, t7w i * trainProb (t7D i) x = 0 := by
      rw [Fin.sum_univ_three]
      have e0 : trainProb (t7D 0) x = 0 := by
        rw [t7train, h0, t7D_0, t7d1_0]
      have e1 : trainProb (t7D 1) x = 0 := by
        rw [t7train, h0, t7D_1, t7d2_0]
      have e2 : trainProb (t7D 2) x = 0 := by
        rw [t7train, h0, t7D_2, t7d3_0]
      rw [e0, e1, e2]
      simp
    rw [hsum] at hpos
    exact lt_irrefl 0 hpos
  · have hobs1 : observed id 0 x = ({0, 1} : Finset (Fin 4)) := by
      rw [hobs, h1]
      decide
    rw [hobs1] at hy hy'
    have hNum : ∀ z, z ∉ ({0, 1} : Finset (Fin 4)) →
        (∑ i ∈ Finset.univ.filter (fun i => z ∈ facts id 0 (t7D i)),
          t7w i * trainProb (t7D i) x) = 0 := by
      intro z hz
      rcases tri4 z with rfl | rfl | rfl | rfl
      · have hm : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · have hm : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [t7filt2, Finset.sum_singleton]
        have e : trainProb (t7D 1) x = 0 := by
          rw [t7train, h1, t7D_1, t7d2_1]
        rw [e, mul_zero]
      · rw [t7filt3, Finset.sum_singleton]
        have e : trainProb (t7D 2) x = 0 := by
          rw [t7train, h1, t7D_2, t7d3_1]
        rw [e, mul_zero]
    rw [hNum y hy, hNum y' hy']
  · have hobs2 : observed id 0 x = ({0, 2} : Finset (Fin 4)) := by
      rw [hobs, h2]
      decide
    rw [hobs2] at hy hy'
    have hNum : ∀ z, z ∉ ({0, 2} : Finset (Fin 4)) →
        (∑ i ∈ Finset.univ.filter (fun i => z ∈ facts id 0 (t7D i)),
          t7w i * trainProb (t7D i) x) = 0 := by
      intro z hz
      rcases tri4 z with rfl | rfl | rfl | rfl
      · have hm : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [t7filt1, Finset.sum_singleton]
        have e : trainProb (t7D 0) x = 0 := by
          rw [t7train, h2, t7D_0, t7d1_2]
        rw [e, mul_zero]
      · have hm : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [t7filt3, Finset.sum_singleton]
        have e : trainProb (t7D 2) x = 0 := by
          rw [t7train, h2, t7D_2, t7d3_2]
        rw [e, mul_zero]
    rw [hNum y hy, hNum y' hy']
  · have hobs3 : observed id 0 x = ({0, 3} : Finset (Fin 4)) := by
      rw [hobs, h3]
      decide
    rw [hobs3] at hy hy'
    have hNum : ∀ z, z ∉ ({0, 3} : Finset (Fin 4)) →
        (∑ i ∈ Finset.univ.filter (fun i => z ∈ facts id 0 (t7D i)),
          t7w i * trainProb (t7D i) x) = 0 := by
      intro z hz
      rcases tri4 z with rfl | rfl | rfl | rfl
      · have hm : (0 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [t7filt1, Finset.sum_singleton]
        have e : trainProb (t7D 0) x = 0 := by
          rw [t7train, h3, t7D_0, t7d1_3]
        rw [e, mul_zero]
      · rw [t7filt2, Finset.sum_singleton]
        have e : trainProb (t7D 1) x = 0 := by
          rw [t7train, h3, t7D_1, t7d2_3]
        rw [e, mul_zero]
      · have hm : (3 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by simp
        exact absurd hm hz
    rw [hNum y hy, hNum y' hy']

private theorem t7posProbs : HasRegularProbabilities id 0 t7w t7D 1 := by
  intro x hpos y hy y' hy'
  have hobs : observed id 0 x = {x 0, 0} := t7obs x
  rcases tri4 (x 0) with h0 | h1 | h2 | h3
  · exfalso
    have hsum : ∑ i, t7w i * trainProb (t7D i) x = 0 := by
      rw [Fin.sum_univ_three]
      have e0 : trainProb (t7D 0) x = 0 := by
        rw [t7train, h0, t7D_0, t7d1_0]
      have e1 : trainProb (t7D 1) x = 0 := by
        rw [t7train, h0, t7D_1, t7d2_0]
      have e2 : trainProb (t7D 2) x = 0 := by
        rw [t7train, h0, t7D_2, t7d3_0]
      rw [e0, e1, e2]
      simp
    rw [hsum] at hpos
    exact lt_irrefl 0 hpos
  · have hobs1 : observed id 0 x = ({0, 1} : Finset (Fin 4)) := by
      rw [hobs, h1]
      decide
    rw [hobs1] at hy hy'
    have hSum : ∀ z, z ∉ ({0, 1} : Finset (Fin 4)) →
        (∑ i, t7w i * trainProb (t7D i) x * pushforward id (t7D i) z)
          = 0 := by
      intro z hz
      rcases tri4 z with rfl | rfl | rfl | rfl
      · have hm : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · have hm : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [Fin.sum_univ_three]
        have e0 : t7w 0 * trainProb (t7D 0) x
            * pushforward id (t7D 0) 2 = 0 := by
          rw [t7train, h1, t7D_0, t7d1_1, t7push, t7d1_2, t7w0]
          norm_num
        have e1 : t7w 1 * trainProb (t7D 1) x
            * pushforward id (t7D 1) 2 = 0 := by
          rw [t7train, h1, t7D_1, t7d2_1, t7push, t7d2_2, t7w1]
          norm_num
        have e2 : t7w 2 * trainProb (t7D 2) x
            * pushforward id (t7D 2) 2 = 0 := by
          rw [t7train, h1, t7D_2, t7d3_1, t7push, t7d3_2, t7w2]
          norm_num
        rw [e0, e1, e2]
        norm_num
      · rw [Fin.sum_univ_three]
        have e0 : t7w 0 * trainProb (t7D 0) x
            * pushforward id (t7D 0) 3 = 0 := by
          rw [t7train, h1, t7D_0, t7d1_1, t7push, t7d1_3, t7w0]
          norm_num
        have e1 : t7w 1 * trainProb (t7D 1) x
            * pushforward id (t7D 1) 3 = 0 := by
          rw [t7train, h1, t7D_1, t7d2_1, t7push, t7d2_3, t7w1]
          norm_num
        have e2 : t7w 2 * trainProb (t7D 2) x
            * pushforward id (t7D 2) 3 = 0 := by
          rw [t7train, h1, t7D_2, t7d3_1, t7push, t7d3_3, t7w2]
          norm_num
        rw [e0, e1, e2]
        norm_num
    rw [hSum y hy, hSum y' hy']
  · have hobs2 : observed id 0 x = ({0, 2} : Finset (Fin 4)) := by
      rw [hobs, h2]
      decide
    rw [hobs2] at hy hy'
    have hSum : ∀ z, z ∉ ({0, 2} : Finset (Fin 4)) →
        (∑ i, t7w i * trainProb (t7D i) x * pushforward id (t7D i) z)
          = 0 := by
      intro z hz
      rcases tri4 z with rfl | rfl | rfl | rfl
      · have hm : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [Fin.sum_univ_three]
        have e0 : t7w 0 * trainProb (t7D 0) x
            * pushforward id (t7D 0) 1 = 0 := by
          rw [t7train, h2, t7D_0, t7d1_2, t7push, t7d1_1, t7w0]
          norm_num
        have e1 : t7w 1 * trainProb (t7D 1) x
            * pushforward id (t7D 1) 1 = 0 := by
          rw [t7train, h2, t7D_1, t7d2_2, t7push, t7d2_1, t7w1]
          norm_num
        have e2 : t7w 2 * trainProb (t7D 2) x
            * pushforward id (t7D 2) 1 = 0 := by
          rw [t7train, h2, t7D_2, t7d3_2, t7push, t7d3_1, t7w2]
          norm_num
        rw [e0, e1, e2]
        norm_num
      · have hm : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [Fin.sum_univ_three]
        have e0 : t7w 0 * trainProb (t7D 0) x
            * pushforward id (t7D 0) 3 = 0 := by
          rw [t7train, h2, t7D_0, t7d1_2, t7push, t7d1_3, t7w0]
          norm_num
        have e1 : t7w 1 * trainProb (t7D 1) x
            * pushforward id (t7D 1) 3 = 0 := by
          rw [t7train, h2, t7D_1, t7d2_2, t7push, t7d2_3, t7w1]
          norm_num
        have e2 : t7w 2 * trainProb (t7D 2) x
            * pushforward id (t7D 2) 3 = 0 := by
          rw [t7train, h2, t7D_2, t7d3_2, t7push, t7d3_3, t7w2]
          norm_num
        rw [e0, e1, e2]
        norm_num
    rw [hSum y hy, hSum y' hy']
  · have hobs3 : observed id 0 x = ({0, 3} : Finset (Fin 4)) := by
      rw [hobs, h3]
      decide
    rw [hobs3] at hy hy'
    have hSum : ∀ z, z ∉ ({0, 3} : Finset (Fin 4)) →
        (∑ i, t7w i * trainProb (t7D i) x * pushforward id (t7D i) z)
          = 0 := by
      intro z hz
      rcases tri4 z with rfl | rfl | rfl | rfl
      · have hm : (0 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by simp
        exact absurd hm hz
      · rw [Fin.sum_univ_three]
        have e0 : t7w 0 * trainProb (t7D 0) x
            * pushforward id (t7D 0) 1 = 0 := by
          rw [t7train, h3, t7D_0, t7d1_3, t7push, t7d1_1, t7w0]
          norm_num
        have e1 : t7w 1 * trainProb (t7D 1) x
            * pushforward id (t7D 1) 1 = 0 := by
          rw [t7train, h3, t7D_1, t7d2_3, t7push, t7d2_1, t7w1]
          norm_num
        have e2 : t7w 2 * trainProb (t7D 2) x
            * pushforward id (t7D 2) 1 = 0 := by
          rw [t7train, h3, t7D_2, t7d3_3, t7push, t7d3_1, t7w2]
          norm_num
        rw [e0, e1, e2]
        norm_num
      · rw [Fin.sum_univ_three]
        have e0 : t7w 0 * trainProb (t7D 0) x
            * pushforward id (t7D 0) 2 = 0 := by
          rw [t7train, h3, t7D_0, t7d1_3, t7push, t7d1_2, t7w0]
          norm_num
        have e1 : t7w 1 * trainProb (t7D 1) x
            * pushforward id (t7D 1) 2 = 0 := by
          rw [t7train, h3, t7D_1, t7d2_3, t7push, t7d2_2, t7w1]
          norm_num
        have e2 : t7w 2 * trainProb (t7D 2) x
            * pushforward id (t7D 2) 2 = 0 := by
          rw [t7train, h3, t7D_2, t7d3_3, t7push, t7d3_2, t7w2]
          norm_num
        rw [e0, e1, e2]
        norm_num
      · have hm : (3 : Fin 4) ∈ ({0, 3} : Finset (Fin 4)) := by simp
        exact absurd hm hz
    rw [hSum y hy, hSum y' hy']

private theorem t7posReg : IsRegular id 0 t7w t7D 1 :=
  ⟨t7posFacts, t7posProbs⟩

noncomputable def t7nw : Fin 2 → ℝ := fun i => if i = 0 then 3 / 4 else 1 / 4

noncomputable def t7nd0 : Fin 4 → ℝ :=
  fun x => if x = 1 then 1 / 2 else if x = 2 then 1 / 2 else 0

noncomputable def t7nd1 : Fin 4 → ℝ :=
  fun x => if x = 1 then 1 / 2 else if x = 3 then 1 / 2 else 0

noncomputable def t7nD : Fin 2 → Fin 4 → ℝ :=
  fun i => if i = 0 then t7nd0 else t7nd1

noncomputable def t7nx : Fin 1 → Fin 4 := fun _ => 1

private theorem t7nx0 : t7nx 0 = 1 := rfl

private theorem t7nw0 : t7nw 0 = 3 / 4 := by simp [t7nw]
private theorem t7nw1 : t7nw 1 = 1 / 4 := by simp [t7nw]

private theorem t7nd0_0 : t7nd0 0 = 0 := by simp [t7nd0]
private theorem t7nd0_1 : t7nd0 1 = 1 / 2 := by simp [t7nd0]
private theorem t7nd0_2 : t7nd0 2 = 1 / 2 := by simp [t7nd0]
private theorem t7nd0_3 : t7nd0 3 = 0 := by simp [t7nd0]
private theorem t7nd1_0 : t7nd1 0 = 0 := by simp [t7nd1]
private theorem t7nd1_1 : t7nd1 1 = 1 / 2 := by simp [t7nd1]
private theorem t7nd1_2 : t7nd1 2 = 0 := by simp [t7nd1]
private theorem t7nd1_3 : t7nd1 3 = 1 / 2 := by simp [t7nd1]

private theorem t7nD_0 : t7nD 0 = t7nd0 := by simp [t7nD]
private theorem t7nD_1 : t7nD 1 = t7nd1 := by simp [t7nD]

private theorem t7nF0 :
    facts id 0 (t7nD 0) = ({0, 1, 2} : Finset (Fin 4)) := by
  rw [t7nD_0]
  ext y
  rcases tri4 y with rfl | rfl | rfl | rfl
  · simp [facts]
  · simp [facts, t7push, t7nd0_1, show (1 : Fin 4) ≠ 0 by decide]
  · simp [facts, t7push, t7nd0_2, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide]
  · simp [facts, t7push, t7nd0_3, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide]

private theorem t7nF1 :
    facts id 0 (t7nD 1) = ({0, 1, 3} : Finset (Fin 4)) := by
  rw [t7nD_1]
  ext y
  rcases tri4 y with rfl | rfl | rfl | rfl
  · simp [facts]
  · simp [facts, t7push, t7nd1_1, show (1 : Fin 4) ≠ 0 by decide]
  · simp [facts, t7push, t7nd1_2, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide, show (2 : Fin 4) ≠ 3 by decide]
  · simp [facts, t7push, t7nd1_3, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide]

private theorem t7npos : 0 < ∑ i, t7nw i * trainProb (t7nD i) t7nx := by
  rw [Fin.sum_univ_two, t7train, t7train, t7nD_0, t7nD_1, t7nx0, t7nd0_1,
    t7nd1_1, t7nw0, t7nw1]
  norm_num

private theorem t7nobs : observed id 0 t7nx = ({0, 1} : Finset (Fin 4)) := by
  unfold observed
  have huniv : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  rw [huniv, Finset.image_singleton]
  show ({(id ∘ t7nx) 0, 0} : Finset (Fin 4)) = {0, 1}
  have hx0 : (id ∘ t7nx) 0 = 1 := rfl
  rw [hx0]
  decide

private theorem t7nfilt2 : Finset.univ.filter
      (fun i : Fin 2 => (2 : Fin 4) ∈ facts id 0 (t7nD i))
      = ({0} : Finset (Fin 2)) := by
  ext i
  rcases tri2 i with rfl | rfl
  · simp [t7nF0, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide]
  · simp [t7nF1, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide, show (2 : Fin 4) ≠ 3 by decide]

private theorem t7nfilt3 : Finset.univ.filter
      (fun i : Fin 2 => (3 : Fin 4) ∈ facts id 0 (t7nD i))
      = ({1} : Finset (Fin 2)) := by
  ext i
  rcases tri2 i with rfl | rfl
  · simp [t7nF0, show (0 : Fin 2) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide]
  · simp [t7nF1, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide]

private theorem t7nN2 : (∑ i ∈ Finset.univ.filter
      (fun i : Fin 2 => (2 : Fin 4) ∈ facts id 0 (t7nD i)),
      t7nw i * trainProb (t7nD i) t7nx) = 3 / 8 := by
  rw [t7nfilt2, Finset.sum_singleton, t7train, t7nD_0, t7nx0, t7nd0_1,
    t7nw0]
  norm_num

private theorem t7nN3 : (∑ i ∈ Finset.univ.filter
      (fun i : Fin 2 => (3 : Fin 4) ∈ facts id 0 (t7nD i)),
      t7nw i * trainProb (t7nD i) t7nx) = 1 / 8 := by
  rw [t7nfilt3, Finset.sum_singleton, t7train, t7nD_1, t7nx0, t7nd1_1,
    t7nw1]
  norm_num

private theorem t7nneg : ¬ HasRegularFacts id 0 t7nw t7nD 1 := by
  intro hreg
  have hy2 : (2 : Fin 4) ∉ observed id 0 t7nx := by
    rw [t7nobs]
    decide
  have hy3 : (3 : Fin 4) ∉ observed id 0 t7nx := by
    rw [t7nobs]
    decide
  have heq := hreg t7nx t7npos 2 hy2 3 hy3
  rw [t7nN2, t7nN3] at heq
  norm_num at heq

-- T7: the point-mass world is sparse at `s = 0`.
example : IsSparse id 0 t7w t7D 0 := t7sparse

-- T7: the point-mass world is regular at `n = 1`.
example : IsRegular id 0 t7w t7D 1 := t7posReg

-- T7: the two-uniform world breaks regularity (`3/8` vs `1/8`).
example : ¬ HasRegularFacts id 0 t7nw t7nD 1 := t7nneg

-- T7: numerator at `2` is `3/8` on the sample `(1)`.
example : (∑ i ∈ Finset.univ.filter
      (fun i : Fin 2 => (2 : Fin 4) ∈ facts id 0 (t7nD i)),
      t7nw i * trainProb (t7nD i) t7nx) = 3 / 8 := t7nN2

-- T7: numerator at `3` is `1/8` on the sample `(1)`.
example : (∑ i ∈ Finset.univ.filter
      (fun i : Fin 2 => (3 : Fin 4) ∈ facts id 0 (t7nD i)),
      t7nw i * trainProb (t7nD i) t7nx) = 1 / 8 := t7nN3

end T7

section T8

-- T8: divided facts form on the regular world.
example : ∀ x : Fin 1 → Fin 4, 0 < ∑ i, t7w i * trainProb (t7D i) x →
    ∀ y ∉ observed id 0 x, ∀ y' ∉ observed id 0 x,
      (∑ i ∈ Finset.univ.filter (fun i => y ∈ facts id 0 (t7D i)),
        t7w i * trainProb (t7D i) x) / (∑ i, t7w i * trainProb (t7D i) x)
      = (∑ i ∈ Finset.univ.filter (fun i => y' ∈ facts id 0 (t7D i)),
        t7w i * trainProb (t7D i) x) / (∑ i, t7w i * trainProb (t7D i) x) :=
  (hasRegularFacts_iff id 0 t7w t7D 1).mp t7posFacts

-- T8: divided probabilities form on the regular world.
example : ∀ x : Fin 1 → Fin 4, 0 < ∑ i, t7w i * trainProb (t7D i) x →
    ∀ y ∉ observed id 0 x, ∀ y' ∉ observed id 0 x,
      (∑ i, t7w i * trainProb (t7D i) x * pushforward id (t7D i) y)
        / (∑ i, t7w i * trainProb (t7D i) x)
      = (∑ i, t7w i * trainProb (t7D i) x * pushforward id (t7D i) y')
        / (∑ i, t7w i * trainProb (t7D i) x) :=
  (hasRegularProbabilities_iff id 0 t7w t7D 1).mp t7posProbs

-- T8: divided facts form fails on the irregular world.
example : ¬ ∀ x : Fin 1 → Fin 4, 0 < ∑ i, t7nw i * trainProb (t7nD i) x →
    ∀ y ∉ observed id 0 x, ∀ y' ∉ observed id 0 x,
      (∑ i ∈ Finset.univ.filter (fun i => y ∈ facts id 0 (t7nD i)),
        t7nw i * trainProb (t7nD i) x) / (∑ i, t7nw i * trainProb (t7nD i) x)
      = (∑ i ∈ Finset.univ.filter (fun i => y' ∈ facts id 0 (t7nD i)),
        t7nw i * trainProb (t7nD i) x)
        / (∑ i, t7nw i * trainProb (t7nD i) x) :=
  mt (hasRegularFacts_iff id 0 t7nw t7nD 1).mpr t7nneg

private theorem t7nP2 : (∑ i, t7nw i * trainProb (t7nD i) t7nx
    * pushforward id (t7nD i) 2) = 3 / 16 := by
  rw [Fin.sum_univ_two, t7train, t7train, t7nD_0, t7nD_1, t7nx0, t7nd0_1,
    t7nd1_1, t7push, t7push, t7nd0_2, t7nd1_2, t7nw0, t7nw1]
  norm_num

private theorem t7nP3 : (∑ i, t7nw i * trainProb (t7nD i) t7nx
    * pushforward id (t7nD i) 3) = 1 / 16 := by
  rw [Fin.sum_univ_two, t7train, t7train, t7nD_0, t7nD_1, t7nx0, t7nd0_1,
    t7nd1_1, t7push, t7push, t7nd0_3, t7nd1_3, t7nw0, t7nw1]
  norm_num

private theorem t7nnegProbs : ¬ HasRegularProbabilities id 0 t7nw t7nD 1 := by
  intro hreg
  have hy2 : (2 : Fin 4) ∉ observed id 0 t7nx := by
    rw [t7nobs]
    decide
  have hy3 : (3 : Fin 4) ∉ observed id 0 t7nx := by
    rw [t7nobs]
    decide
  have heq := hreg t7nx t7npos 2 hy2 3 hy3
  rw [t7nP2, t7nP3] at heq
  norm_num at heq

private theorem t7nnegDiv : ¬ ∀ x : Fin 1 → Fin 4,
    0 < ∑ i, t7nw i * trainProb (t7nD i) x →
    ∀ y ∉ observed id 0 x, ∀ y' ∉ observed id 0 x,
      (∑ i, t7nw i * trainProb (t7nD i) x * pushforward id (t7nD i) y)
        / (∑ i, t7nw i * trainProb (t7nD i) x)
      = (∑ i, t7nw i * trainProb (t7nD i) x * pushforward id (t7nD i) y')
        / (∑ i, t7nw i * trainProb (t7nD i) x) := by
  intro hdiv
  have hy2 : (2 : Fin 4) ∉ observed id 0 t7nx := by
    rw [t7nobs]
    decide
  have hy3 : (3 : Fin 4) ∉ observed id 0 t7nx := by
    rw [t7nobs]
    decide
  have heq := hdiv t7nx t7npos 2 hy2 3 hy3
  rw [t7nP2, t7nP3] at heq
  have hden : (∑ i, t7nw i * trainProb (t7nD i) t7nx) ≠ 0 :=
    ne_of_gt t7npos
  have h2 : ((3 / 16 : ℝ) / (∑ i, t7nw i * trainProb (t7nD i) t7nx))
      * (∑ i, t7nw i * trainProb (t7nD i) t7nx)
      = ((1 / 16 : ℝ) / (∑ i, t7nw i * trainProb (t7nD i) t7nx))
      * (∑ i, t7nw i * trainProb (t7nD i) t7nx) := by
    rw [heq]
  rw [div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden] at h2
  norm_num at h2

-- T8: divided probabilities form fails on the irregular world.
example : ¬ ∀ x : Fin 1 → Fin 4, 0 < ∑ i, t7nw i * trainProb (t7nD i) x →
    ∀ y ∉ observed id 0 x, ∀ y' ∉ observed id 0 x,
      (∑ i, t7nw i * trainProb (t7nD i) x * pushforward id (t7nD i) y)
        / (∑ i, t7nw i * trainProb (t7nD i) x)
      = (∑ i, t7nw i * trainProb (t7nD i) x * pushforward id (t7nD i) y')
        / (∑ i, t7nw i * trainProb (t7nD i) x) :=
  mt (hasRegularProbabilities_iff id 0 t7nw t7nD 1).mpr t7nnegProbs

-- T8: divided-form failure breaks regularity on the irregular world.
example : ¬ HasRegularProbabilities id 0 t7nw t7nD 1 :=
  mt (hasRegularProbabilities_iff id 0 t7nw t7nD 1).mp t7nnegDiv

end T8

section T10

-- T10: with one bin, `binIndex_spec` puts every point in bin `0`.
example (y : Fin 2) : binIndex t2g 1 y = 0 :=
  Nat.lt_one_iff.mp (binIndex_spec t2g_prob le_rfl y).1

-- T10: `binIndex_spec` at `(1/4, 3/4)` with `b = 5`: the point `1` is not in
-- the first bin, so its index is below `5` and its lower threshold is below `3/4`.
example : binIndex t2g 5 1 < 5 ∧ binThreshold t2g 5 (binIndex t2g 5 1) < 3 / 4 := by
  have hspec := binIndex_spec t2g_prob (b := 5) (by norm_num) 1
  have hpos : 0 < binIndex t2g 5 1 := by
    have h := t3idx1ne
    rw [t3idx0] at h
    exact Nat.pos_of_ne_zero h
  refine ⟨hspec.1, ?_⟩
  have h := hspec.2.2 hpos
  rwa [t2g1] at h

private theorem t10B0 : (∑ i, t1w i * t1p i 0) = 1 / 2 := by
  rw [Fin.sum_univ_two, t1w0, t1w1, t1p_0, t1p_1, t1p1_0, t1p2_0]
  norm_num

-- T10: Lemma 2 on the two-point prior with `S = {0}` and the top partition:
-- the left side is `1/6`.
private theorem t10L2lhs : (∑ i, t1w i * max (∑ y ∈ ({0} : Finset (Fin 3)), t1p i y
    - ∑ y ∈ ({0} : Finset (Fin 3)), coarsen ⊤ (t1p i) y) 0) = 1 / 6 := by
  rw [Fin.sum_univ_two, t1w0, t1w1, t1p_0, t1p_1, t1coarsen_top_p1, t1coarsen_top_p2]
  simp only [Finset.sum_singleton, t1p1_0, t1p2_0, t1g_y]
  rw [max_eq_left (by norm_num)]
  norm_num

-- T10: the right side is `|Y \ S| * max_{y ∈ S} E[p y] = 2 * (1/2) = 1`.
private theorem t10L2rhs : (((Finset.univ \ ({0} : Finset (Fin 3))).card : ℝ) *
    (({0} : Finset (Fin 3)).image (fun y => ∑ i, t1w i * t1p i y)).max'
      (Finset.image_nonempty.mpr (Finset.singleton_nonempty 0))) = 1 := by
  have hc : (Finset.univ \ ({0} : Finset (Fin 3))).card = 2 := by decide
  have hm : (({0} : Finset (Fin 3)).image (fun y => ∑ i, t1w i * t1p i y)).max'
      (Finset.image_nonempty.mpr (Finset.singleton_nonempty 0)) = 1 / 2 := by
    rw [Finset.max'_eq_iff]
    constructor
    · rw [Finset.mem_image]
      exact ⟨0, Finset.mem_singleton_self 0, t10B0⟩
    · intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨y, hy, rfl⟩ := hb
      rw [Finset.mem_singleton] at hy
      subst hy
      exact le_of_eq t10B0
  rw [hc, hm]
  norm_num

-- T10: Lemma 2 itself on that instance gives `1/6 ≤ 1`.
example : (1 / 6 : ℝ) ≤ 1 := by
  have h := expect_posPart_mass_sub_coarsen_le t1w t1w_prob t1p t1p_prob ⊤
    ({0} : Finset (Fin 3)) (Finset.singleton_nonempty 0)
  rwa [t10L2lhs, t10L2rhs] at h

noncomputable def t10w : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

def t10F : Fin 2 → Finset (Fin 3) := fun i => if i = 0 then {0, 1} else {2}

private theorem t10w0 : t10w 0 = 1 := by simp [t10w]

private theorem t10w1 : t10w 1 = 0 := by simp [t10w]

private theorem t10w_prob : IsProbVec t10w := by
  constructor
  · intro i
    rcases tri2 i with rfl | rfl
    · rw [t10w0]; norm_num
    · rw [t10w1]
  · rw [Fin.sum_univ_two, t10w0, t10w1]
    norm_num

-- T10: the weight-zero component's facts `{2}` miss the observed set `{0}`.
example : ¬ t1O ⊆ t10F 1 := by decide

-- T10: the bound form of Theorem 1 still applies to that mixture, with
-- per-component facts `t10F`, `α = 1` and `β = 1/2`.
example : (∑ i, t10w i * max (∑ y ∈ Finset.univ \ t1O, t1p i y
      - tvDist (coarsen ⊤ (t1p i)) t1g - ∑ y ∈ Finset.univ \ t10F i, t1g y) 0)
    ≤ 1 + t1O.card * (1 / 2) := by
  refine expect_hallucination_gap_le_of_bounds t10w t10w_prob t1p t1p_prob t1O t10F t1g
    t1g_prob ⊤ 1 (1 / 2) zero_le_one (by norm_num) ?_ ?_
  · intro y _
    calc ∑ i ∈ Finset.univ.filter (fun i => y ∈ t10F i), t10w i
        ≤ ∑ i, t10w i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => t10w_prob.1 i)
      _ = 1 := t10w_prob.2
  · intro y hy
    rw [t1U] at hy
    rw [Fin.sum_univ_two, t10w0, t10w1, t1p_0, t1p_1]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · rw [t1p1_1, t1p2_1]; norm_num
    · rw [t1p1_2, t1p2_2]; norm_num

private def t10x : Fin 4 → Fin 4 := ![1, 1, 2, 0]

-- T10: Eq. (5) on the sample `(1, 1, 2, 0)` with `⊥ = 0`: only the fact `2`
-- occurs exactly once (`1` occurs twice, and `⊥` does not count), so the
-- monofact rate is `1/4`.
example : monofactRate (id : Fin 4 → Fin 4) 0 t10x = 1 / 4 := by
  have hc : (Finset.univ.filter (fun y : Fin 4 => y ≠ 0 ∧
      (Finset.univ.filter (fun k : Fin 4 => id (t10x k) = y)).card = 1)).card = 1 := by
    decide
  unfold monofactRate
  rw [hc]
  norm_num

-- T10: the `Mis_∞` characterization needs no normalization (here the mass is `2`).
example : misInf (fun y => 2 * t2g y) (fun y => 2 * t2g y) = 0 :=
  isCalibratedTo_iff_misInf_eq_zero.mp
    ⟨⊥, by funext y; exact (coarsen_bot_eq (fun y => 2 * t2g y) y).symm⟩

end T10

section T9

#print axioms sum_coarsen
#print axioms isCalibratedTo_iff_misInf_eq_zero
#print axioms binThreshold_mono
#print axioms binThreshold_self
#print axioms binIndex_spec
#print axioms sub_le_tvDist_of_sum_eq
#print axioms isCalibratedTo_of_mis_eq_zero
#print axioms mis_one
#print axioms expect_posPart_mass_sub_coarsen_le
#print axioms expect_hallucination_gap_le
#print axioms expect_hallucination_gap_le_of_bounds
#print axioms expect_hallucination_gap_eq_zero_of_eq_univ
#print axioms hasRegularFacts_iff
#print axioms hasRegularProbabilities_iff

end T9

end CalibratedHallucination
end MachineLearning
end Cslib

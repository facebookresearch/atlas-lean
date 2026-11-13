/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalCrossMomentClose

open scoped BigOperators

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]



theorem decisionTree_atom_step_le_flip_sum
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmono : IsMonotonicMeasure mu) (T : DecisionTree E) (t : ℕ)
    (hf : Monotone T.evalR) (base : ConfigSpace E) :
    let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
    (∑ left, ∑ right, |T.evalR right - T.evalR left| *
      tripleJointProb mu ∅ base left right S) ≤
      ∑ e,
        ((if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e left +
              T.evalR right * Lindeberg.coord e right) *
              tripleJointProb mu ∅ base left right S) -
         (if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e right +
              T.evalR right * Lindeberg.coord e left) *
              crossTripleJointProb mu ∅ base left right S)) := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  by_cases hex : ∃ e, tripleModeAt S base e = .flip
  · obtain ⟨e, he⟩ := hex
    have hmain := decisionTree_flip_atom_step_le mu hpos hmono T t hf base e he
    rw [Finset.sum_eq_single e]
    · simpa [S, he] using hmain
    · intro z _ hze
      have hz : tripleModeAt S base z ≠ .flip := by
        intro hz
        exact hze (tripleModeAt_extendDecisionTreeTriple_flip_unique
          t T base base Finset.univ z e hz he)
      have hz' : tripleModeAt
          (extendDecisionTreeTriple (some t) T base Finset.univ) base z ≠ .flip := by
        simpa [S] using hz
      simp [hz']
    · simp
  · have hno : ∀ e, tripleModeAt S base e ≠ .flip := by
      simpa only [not_exists] using hex
    rw [no_flip_causal_atom_eq_zero mu hpos S base hno T.evalR]
    apply Finset.sum_nonneg
    intro e _
    have he' : tripleModeAt
        (extendDecisionTreeTriple (some t) T base Finset.univ) base e ≠ .flip := by
      simpa [S] using hno e
    simp [he']



theorem common_flip_moment_extendDecisionTreeTriple
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmu : ∑ ω, mu ω = 1) (T : DecisionTree E) (seed : ConfigSpace E)
    (t : ℕ) (e : E) :
    let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)
    (∑ base,
      (if tripleModeAt S base e = .flip then 1 else 0) *
        (∑ left, ∑ right,
          (T.evalR left * Lindeberg.coord e left +
            T.evalR right * Lindeberg.coord e right) *
            tripleJointProb mu ∅ base left right S)) =
      2 * Lindeberg.mean mu (fun ω => T.evalR ω * Lindeberg.coord e ω) *
        flipBaseProb mu ∅ seed e S := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)
  have hkernel :
      (∑ base,
        (if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e left +
              T.evalR right * Lindeberg.coord e right) *
              tripleJointProb mu ∅ base left right S)) =
      ∑ left, ∑ right,
        (T.evalR left * Lindeberg.coord e left +
          T.evalR right * Lindeberg.coord e right) *
          flipTripleProb mu ∅ seed left right e S := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro right _
    calc
      _ = (T.evalR left * Lindeberg.coord e left +
            T.evalR right * Lindeberg.coord e right) *
          (∑ base,
            (if tripleModeAt S base e = .flip then 1 else 0) *
              tripleJointProb mu ∅ base left right S) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        ring
      _ = _ := by
        rw [← baseSum_flip_tripleJointProb_eq_flipTripleProb
          mu ∅ seed left right e S (by simp)]
        simp [baseSum, Agree]
  rw [hkernel]
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  have hr (left : ConfigSpace E) :
      (∑ right, flipTripleProb mu ∅ seed left right e S) =
        mu left * flipBaseProb mu ∅ seed e S := by
    simpa [S] using sum_flipTripleProb_right_extendDecisionTreeTriple
      mu hpos hmu seed left seed e t T seed
  have hl (right : ConfigSpace E) :
      (∑ left, flipTripleProb mu ∅ seed left right e S) =
        mu right * flipBaseProb mu ∅ seed e S := by
    simpa [S] using sum_flipTripleProb_left_extendDecisionTreeTriple
      mu hpos hmu seed seed right e t T seed
  have hfirst :
      (∑ left, ∑ right,
        T.evalR left * Lindeberg.coord e left *
          flipTripleProb mu ∅ seed left right e S) =
      (∑ left, T.evalR left * Lindeberg.coord e left * mu left) *
        flipBaseProb mu ∅ seed e S := by
    calc
      _ = ∑ left, (T.evalR left * Lindeberg.coord e left) *
          (mu left * flipBaseProb mu ∅ seed e S) := by
        apply Finset.sum_congr rfl
        intro left _
        rw [← Finset.mul_sum, hr]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro left _
        ring
  have hsecond :
      (∑ left, ∑ right,
        T.evalR right * Lindeberg.coord e right *
          flipTripleProb mu ∅ seed left right e S) =
      (∑ right, T.evalR right * Lindeberg.coord e right * mu right) *
        flipBaseProb mu ∅ seed e S := by
    calc
      _ = ∑ right, (T.evalR right * Lindeberg.coord e right) *
          (mu right * flipBaseProb mu ∅ seed e S) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro right _
        rw [← Finset.mul_sum, hl]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro right _
        ring
  rw [hfirst, hsecond]
  unfold Lindeberg.mean
  dsimp only [S]
  ring



theorem causalTripleJump_le_of_cross_flip_moment
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmu : ∑ ω, mu ω = 1) (hmono : IsMonotonicMeasure mu)
    (T : DecisionTree E) (hf : Monotone T.evalR) (seed : ConfigSpace E)
    (t : ℕ)
    (hcross : ∀ e,
      let S := extendDecisionTreeTriple (some t) T seed
        (Finset.univ : Finset E)
      2 * (Lindeberg.mean mu T.evalR *
        Lindeberg.mean mu (Lindeberg.coord e)) *
          flipBaseProb mu ∅ seed e S ≤
        ∑ base,
          (if tripleModeAt S base e = .flip then 1 else 0) *
            (∑ left, ∑ right,
              (T.evalR left * Lindeberg.coord e right +
                T.evalR right * Lindeberg.coord e left) *
                crossTripleJointProb mu ∅ base left right S)) :
    causalTripleJump mu T t seed ≤
      2 * ∑ e, Lindeberg.cov mu T.evalR (Lindeberg.coord e) *
        Lindeberg.mean mu (fun base => sharedStepIndicator T base t e) := by
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)
  have hbase (base : ConfigSpace E) :
      (∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb mu ∅ base left right S) ≤
      ∑ e,
        ((if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e left +
              T.evalR right * Lindeberg.coord e right) *
              tripleJointProb mu ∅ base left right S) -
         (if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e right +
              T.evalR right * Lindeberg.coord e left) *
              crossTripleJointProb mu ∅ base left right S)) := by
    have h := decisionTree_atom_step_le_flip_sum
      mu hpos hmono T t hf base
    rw [extendDecisionTreeTriple_univ_seed_congr (some t) T base seed] at h
    simpa only [S] using h
  calc
    causalTripleJump mu T t seed =
        ∑ base, ∑ left, ∑ right, |T.evalR right - T.evalR left| *
          tripleJointProb mu ∅ base left right S := by rfl
    _ ≤ ∑ base, ∑ e,
        ((if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e left +
              T.evalR right * Lindeberg.coord e right) *
              tripleJointProb mu ∅ base left right S) -
         (if tripleModeAt S base e = .flip then 1 else 0) *
          (∑ left, ∑ right,
            (T.evalR left * Lindeberg.coord e right +
              T.evalR right * Lindeberg.coord e left) *
              crossTripleJointProb mu ∅ base left right S)) :=
      Finset.sum_le_sum (fun base _ => hbase base)
    _ = ∑ e,
        ((∑ base,
          (if tripleModeAt S base e = .flip then 1 else 0) *
            (∑ left, ∑ right,
              (T.evalR left * Lindeberg.coord e left +
                T.evalR right * Lindeberg.coord e right) *
                tripleJointProb mu ∅ base left right S)) -
         (∑ base,
          (if tripleModeAt S base e = .flip then 1 else 0) *
            (∑ left, ∑ right,
              (T.evalR left * Lindeberg.coord e right +
                T.evalR right * Lindeberg.coord e left) *
                crossTripleJointProb mu ∅ base left right S))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ e,
        (2 * Lindeberg.mean mu
            (fun ω => T.evalR ω * Lindeberg.coord e ω) *
              flipBaseProb mu ∅ seed e S -
         2 * (Lindeberg.mean mu T.evalR *
            Lindeberg.mean mu (Lindeberg.coord e)) *
              flipBaseProb mu ∅ seed e S) := by
      apply Finset.sum_le_sum
      intro e _
      rw [common_flip_moment_extendDecisionTreeTriple mu hpos hmu T seed t e]
      exact sub_le_sub_left (hcross e) _
    _ = 2 * ∑ e, Lindeberg.cov mu T.evalR (Lindeberg.coord e) *
        Lindeberg.mean mu (fun base => sharedStepIndicator T base t e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [← flipBaseProb_extendDecisionTreeTriple_eq_mean_sharedStep
        mu hpos hmu T seed t e]
      unfold Lindeberg.cov
      dsimp only [S]
      ring



theorem causalTripleJump_le_cov_sharedStep
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmu : ∑ ω, mu ω = 1) (hmono : IsMonotonicMeasure mu)
    (T : DecisionTree E) (hf : Monotone T.evalR)
    (seed : ConfigSpace E) (t : ℕ) :
    causalTripleJump mu T t seed ≤
      2 * ∑ e, Lindeberg.cov mu T.evalR (Lindeberg.coord e) *
        Lindeberg.mean mu (fun base => sharedStepIndicator T base t e) := by
  apply causalTripleJump_le_of_cross_flip_moment
    mu hpos hmu hmono T hf seed t
  intro e
  exact le_of_eq
    (cross_flip_moment_extendDecisionTreeTriple_eq mu hpos hmu T seed t e).symm


theorem adaptive_tree_osss
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmu : ∑ ω, mu ω = 1) (hmono : IsMonotonicMeasure mu)
    (T : DecisionTree E) (hf : Monotone T.evalR) :
    Lindeberg.var mu T.evalR ≤
      ∑ e, LindebergTree.revealmentMu mu T e *
        Lindeberg.cov mu T.evalR (Lindeberg.coord e) := by
  let seed : ConfigSpace E := fun _ => false
  apply adaptive_tree_osss_of_causalTripleJump_le mu hpos hmu T seed
  intro t _
  exact causalTripleJump_le_cov_sharedStep mu hpos hmu hmono T hf seed t

end AdaptiveCausalKernel
end OSSS
end StatMech

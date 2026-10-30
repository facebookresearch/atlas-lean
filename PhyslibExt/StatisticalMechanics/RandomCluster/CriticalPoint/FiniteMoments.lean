/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.RussoHamming

/-!
# Moments of the Hamming distance to an event

Polynomial and exponential moments of the Hamming distance to an event under the product Bernoulli
measure on a finite set.

## i. Overview

On a finite edge set the Hamming distance to an event is bounded by the number of edges, so all its
moments are finite and bounded explicitly. All results are unconditional.

## ii. Key results

- `hammingMoment_le`: `E[d(ω, A) ^ d] ≤ |E| ^ d`.
- `exp_hammingMoment_le`: exponential moment bound.

## iii. Table of contents

- A. Bounds on the Hamming distance
- B. Moments

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Bounds on the Hamming distance -/

omit [DecidableEq E] in
lemma hammingToSet_le_card (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    hammingToSet A ω ≤ Fintype.card E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [hammingToSet]
  · obtain ⟨a, _, ha⟩ := exists_realizer A hne ω
    rw [← ha]
    exact hammingDist_le_card_fintype

omit [DecidableEq E] in
lemma hammingToSet_real_le_card (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    (hammingToSet A ω : ℝ) ≤ (Fintype.card E : ℝ) := by
  exact_mod_cast hammingToSet_le_card A ω

lemma expect_const (p : ℝ) (c : ℝ) :
    expect p (fun _ : ConfigSpace E => c) = c := by
  unfold expect
  simp only []
  rw [← Finset.mul_sum, configWeight_sum_one, mul_one]

lemma expect_le_const {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ}
    {f : ConfigSpace E → ℝ} (h : ∀ ω, f ω ≤ c) : expect p f ≤ c :=
  (expect_mono hp0 hp1 h).trans_eq (expect_const p c)

/-! ## B. Moments -/

/-- The `d`-th moment of the Hamming distance from `ω` to `A` under the Bernoulli(`p`) product
  measure. -/
noncomputable def hammingMoment (p : ℝ) (A : Set (ConfigSpace E)) (d : ℕ) : ℝ :=
  expect p (fun ω => (hammingToSet A ω : ℝ) ^ d)

lemma hammingMoment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) : 0 ≤ hammingMoment p A d :=
  expect_nonneg hp0 hp1 (fun ω => by positivity)

lemma hammingMoment_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) :
    hammingMoment p A d ≤ (Fintype.card E : ℝ) ^ d := by
  unfold hammingMoment
  refine expect_le_const hp0 hp1 (fun ω => ?_)
  exact pow_le_pow_left₀ (by positivity) (hammingToSet_real_le_card A ω) d

lemma hammingMoment_lt_top {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) :
    hammingMoment p A d < (Fintype.card E : ℝ) ^ d + 1 :=
  lt_of_le_of_lt (hammingMoment_le hp0 hp1 A d) (by linarith)

lemma hammingMoment_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (hcard : Fintype.card E ≤ 1) (d : ℕ) :
    hammingMoment p A d ≤ 1 := by
  refine (hammingMoment_le hp0 hp1 A d).trans ?_
  have : (Fintype.card E : ℝ) ≤ 1 := by exact_mod_cast hcard
  calc (Fintype.card E : ℝ) ^ d ≤ (1 : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) this d
    _ = 1 := one_pow d

/-- The exponential moment `E[exp (t d(ω, A))]` of the Hamming distance to `A`. -/
noncomputable def expHammingMoment (p : ℝ) (A : Set (ConfigSpace E)) (t : ℝ) : ℝ :=
  expect p (fun ω => Real.exp (t * (hammingToSet A ω : ℝ)))

lemma expHammingMoment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (t : ℝ) : 0 ≤ expHammingMoment p A t :=
  expect_nonneg hp0 hp1 (fun _ => (Real.exp_pos _).le)

lemma exp_hammingMoment_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) {t : ℝ} (ht : 0 ≤ t) :
    expHammingMoment p A t ≤ Real.exp (t * (Fintype.card E : ℝ)) := by
  unfold expHammingMoment
  refine expect_le_const hp0 hp1 (fun ω => ?_)
  refine Real.exp_le_exp.mpr ?_
  exact mul_le_mul_of_nonneg_left (hammingToSet_real_le_card A ω) ht

lemma hammingMoment_one (p : ℝ) (A : Set (ConfigSpace E)) :
    hammingMoment p A 1 = expect p (fun ω => (hammingToSet A ω : ℝ)) := by
  unfold hammingMoment
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only [pow_one]

end BeffaraDC

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Code.BeffaraDC.RussoHamming

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]



omit [DecidableEq E] in





theorem hammingToSet_le_card (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    hammingToSet A ω ≤ Fintype.card E := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [hammingToSet]
  · obtain ⟨a, _, ha⟩ := exists_realizer A hne ω
    rw [← ha]
    exact hammingDist_le_card_fintype

omit [DecidableEq E] in

theorem hammingToSet_real_le_card (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    (hammingToSet A ω : ℝ) ≤ (Fintype.card E : ℝ) := by
  exact_mod_cast hammingToSet_le_card A ω





theorem expect_const (p : ℝ) (c : ℝ) :
    expect p (fun _ : ConfigSpace E => c) = c := by
  unfold expect
  simp only []
  rw [← Finset.mul_sum, configWeight_sum_one, mul_one]



theorem expect_le_const {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ}
    {f : ConfigSpace E → ℝ} (h : ∀ ω, f ω ≤ c) : expect p f ≤ c :=
  (expect_mono hp0 hp1 h).trans_eq (expect_const p c)








noncomputable def hammingMoment (p : ℝ) (A : Set (ConfigSpace E)) (d : ℕ) : ℝ :=
  expect p (fun ω => (hammingToSet A ω : ℝ) ^ d)


theorem hammingMoment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) : 0 ≤ hammingMoment p A d :=
  expect_nonneg hp0 hp1 (fun ω => by positivity)









theorem hammingMoment_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) :
    hammingMoment p A d ≤ (Fintype.card E : ℝ) ^ d := by
  unfold hammingMoment
  refine expect_le_const hp0 hp1 (fun ω => ?_)
  exact pow_le_pow_left₀ (by positivity) (hammingToSet_real_le_card A ω) d




theorem hammingMoment_lt_top {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) :
    hammingMoment p A d < (Fintype.card E : ℝ) ^ d + 1 :=
  lt_of_le_of_lt (hammingMoment_le hp0 hp1 A d) (by linarith)





theorem hammingMoment_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (hcard : Fintype.card E ≤ 1) (d : ℕ) :
    hammingMoment p A d ≤ 1 := by
  refine (hammingMoment_le hp0 hp1 A d).trans ?_
  have : (Fintype.card E : ℝ) ≤ 1 := by exact_mod_cast hcard
  calc (Fintype.card E : ℝ) ^ d ≤ (1 : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) this d
    _ = 1 := one_pow d





noncomputable def expHammingMoment (p : ℝ) (A : Set (ConfigSpace E)) (t : ℝ) : ℝ :=
  expect p (fun ω => Real.exp (t * (hammingToSet A ω : ℝ)))



theorem expHammingMoment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (t : ℝ) : 0 ≤ expHammingMoment p A t :=
  expect_nonneg hp0 hp1 (fun _ => (Real.exp_pos _).le)









theorem exp_hammingMoment_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) {t : ℝ} (ht : 0 ≤ t) :
    expHammingMoment p A t ≤ Real.exp (t * (Fintype.card E : ℝ)) := by
  unfold expHammingMoment
  refine expect_le_const hp0 hp1 (fun ω => ?_)
  refine Real.exp_le_exp.mpr ?_
  exact mul_le_mul_of_nonneg_left (hammingToSet_real_le_card A ω) ht











theorem hammingMoment_one (p : ℝ) (A : Set (ConfigSpace E)) :
    hammingMoment p A 1 = expect p (fun ω => (hammingToSet A ω : ℝ)) := by
  unfold hammingMoment
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only [pow_one]


theorem first_moment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) :
    0 ≤ expect p (fun ω => (hammingToSet A ω : ℝ)) :=
  expect_nonneg hp0 hp1 (fun ω => by positivity)










theorem prob_le_first_moment {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ < p₂) (hp2 : p₂ < 1)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    prob p₁ A ≤ prob p₂ A *
      Real.exp (- 4 * (p₂ - p₁) * expect p₂ (fun ω => (hammingToSet A ω : ℝ))) :=
  russoHammingIntegrated hp1 hp12 hp2 A hA

end BeffaraDC

end StatMech

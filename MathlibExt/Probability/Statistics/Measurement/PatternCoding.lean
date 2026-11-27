/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemResponse

/-!
# Deterministic pattern coding

For any law on finite response patterns, the locally independent
mixture whose latent state is the pattern itself, with component
success probabilities the zero/one coordinates of that pattern,
reproduces the law exactly. No restriction on the law is needed.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.Statistics.Measurement

/-- Zero/one coordinate probabilities are nonnegative. Private helper for the production statement. -/
private theorem zeroOneCoord_nonneg {ι : Type*} (s : ι → Bool) :
    ∀ i, 0 ≤ (if s i then (1 : ℝ) else 0) := by
  intro i
  by_cases h : s i
  · simp only [if_pos h]
    exact zero_le_one
  · simp only [if_neg h]
    exact le_refl _

/-- Zero/one coordinate probabilities are at most one. Private helper for the production statement. -/
private theorem zeroOneCoord_le_one {ι : Type*} (s : ι → Bool) :
    ∀ i, (if s i then (1 : ℝ) else 0) ≤ 1 := by
  intro i
  by_cases h : s i
  · simp only [if_pos h]
    exact le_refl _
  · simp only [if_neg h]
    exact zero_le_one

/-- Deterministic pattern coding. For any law `p` on finite response
patterns, the locally independent mixture whose latent state is the
pattern itself, and whose component at latent pattern `s` uses the
zero/one coordinates of `s` as success probabilities, reproduces `p`
exactly. The mixture is formed with `PMF.bind`; no support, positivity,
or independence assumption on `p` is imposed. -/
theorem deterministic_pattern_coding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : PMF (ι → Bool)) :
    p.bind (fun s => localIndepPMF (fun i => if s i then (1 : ℝ) else 0)
        (fun i => by by_cases h : s i <;> simp [h])
        (fun i => by by_cases h : s i <;> simp [h])) = p := by
  ext x
  rw [PMF.bind_apply]
  have hdirac : ∀ s : ι → Bool,
      localIndepPMF (fun i => if s i then (1 : ℝ) else 0)
          (zeroOneCoord_nonneg s) (zeroOneCoord_le_one s) x
        = (if s = x then 1 else 0) := by
    intro s
    rw [localIndepPMF_apply]
    by_cases hsx : s = x
    · subst hsx
      have hone : ∀ i,
          (if s i then ENNReal.ofReal (if s i then (1 : ℝ) else 0)
            else ENNReal.ofReal (1 - (if s i then (1 : ℝ) else 0))) = 1 := by
        intro i
        cases hx : s i <;> simp [hx]
      simp [hone]
    · have hex : ∃ i, s i ≠ x i := by
        by_contra hnone
        push_neg at hnone
        apply hsx
        funext i
        exact hnone i
      obtain ⟨i, hi⟩ := hex
      have hzero : (if x i then ENNReal.ofReal (if s i then (1 : ℝ) else 0)
          else ENNReal.ofReal (1 - (if s i then (1 : ℝ) else 0))) = 0 := by
        cases hx : x i <;> cases hs : s i
        · exfalso
          exact hi (by rw [hs, hx])
        · simp [hx, hs]
        · simp [hx, hs]
        · exfalso
          exact hi (by rw [hs, hx])
      have hprod : (∏ i, if x i then ENNReal.ofReal (if s i then (1 : ℝ) else 0)
          else ENNReal.ofReal (1 - (if s i then (1 : ℝ) else 0))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      rw [hprod]
      simp [hsx]
  simp_rw [hdirac]
  have hmul : ∀ s : ι → Bool,
      p s * (if s = x then 1 else 0) = (if s = x then p s else 0) := by
    intro s
    by_cases h : s = x <;> simp [h]
  simp_rw [hmul]
  rw [tsum_fintype]
  rw [Finset.sum_ite_eq' Finset.univ x (fun s => p s)]
  simp

end MathlibExt.Probability.Statistics.Measurement

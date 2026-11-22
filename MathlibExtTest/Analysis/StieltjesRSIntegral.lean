/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegral
import Mathlib.Tactic

namespace MetaMathlibExt

open MathlibExt.Analysis.Integration Set

/-! ### Riemann–Stieltjes sums, computed from the definition -/

/-- Against the identity integrator, the Riemann–Stieltjes sum is the Riemann sum. -/
example {a b : ℝ} (f : ℝ → ℝ) (T : TaggedPartition a b) :
    rsSum f id T = riemannSum f T := rfl

/-- The tagged partition `0 < 1 < 2` of `[0, 2]` with left-endpoint tags. -/
noncomputable def testPartition : TaggedPartition 0 2 where
  n := 2
  points := ![0, 1, 2]
  ordered := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> simp
  first := rfl
  last := rfl
  tags := ![0, 1]
  tag_mem i := by fin_cases i <;> simp

/-- `∑ ξₖ (xₖ₊₁² - xₖ²) = 0 · (1 - 0) + 1 · (4 - 1) = 3`, by unfolding `rsSum`. -/
example : rsSum id (fun x => x ^ 2) testPartition = 3 := by
  rw [rsSum]
  change ∑ i : Fin 2, _ = _
  simp [Fin.sum_univ_two, testPartition]
  norm_num

/-- `Partition.ofFinset` has exactly the given points, and `Partition.common` refines both
partitions. -/
example : (Partition.ofFinset ({0, 1, 3} : Finset ℝ) (by norm_num) (by simp) (by simp)
    : Partition 0 3).pointSet = {0, 1, 3} := by
  rw [Partition.pointSet_ofFinset]; simp

example {a b : ℝ} (P Q : Partition a b) :
    (P.common Q).IsRefinement P ∧ (P.common Q).IsRefinement Q :=
  ⟨P.common_isRefinement_left Q, P.common_isRefinement_right Q⟩

/-! ### A jump integrator: `∫₀³ x d𝟙[2, ∞)(x) = 2` -/

/-- The unit jump at `2`, a regulated integrator that is not continuous. -/
noncomputable def jump2 (x : ℝ) : ℝ := if 2 ≤ x then 1 else 0

theorem jump2_monotone : Monotone jump2 := by
  intro x y hxy
  unfold jump2
  split_ifs <;> linarith

/-- The uniform partition of `[0, 3]` into `3 (N + 1)` pieces of length `1 / (N + 1)`. -/
noncomputable def U3 (N : ℕ) : Partition 0 3 :=
  Partition.uniform (by norm_num) (3 * (N + 1)) (by positivity)

theorem U3_n (N : ℕ) : (U3 N).n = 3 * (N + 1) := rfl

theorem U3_pointN (N : ℕ) {k : ℕ} (hk : k ≤ 3 * (N + 1)) : (U3 N).pointN k = k / (N + 1) := by
  rw [U3, Partition.uniform_pointN _ _ _ hk]
  push_cast
  field_simp
  ring

/-- On the uniform partition with right-endpoint tags the sum is exactly `2`: only the
subinterval `[(2N+1)/(N+1), 2]` sees the jump, and its tag is `2`. -/
theorem rsSum_U3_rightTag (N : ℕ) : rsSum id jump2 (U3 N).rightTag = 2 := by
  rw [rsSum_eq_sum_range]
  change ∑ k ∈ Finset.range (3 * (N + 1)), _ = _
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [Finset.sum_eq_single (2 * N + 1)]
  · rw [show (U3 N).rightTag.tagN (2 * N + 1) = (U3 N).pointN (2 * N + 1 + 1) from
      (U3 N).rightTag_tagN (by rw [U3_n]; omega)]
    change (U3 N).pointN (2 * N + 1 + 1) *
      (jump2 ((U3 N).pointN (2 * N + 1 + 1)) - jump2 ((U3 N).pointN (2 * N + 1))) = 2
    rw [U3_pointN N (by omega), U3_pointN N (by omega)]
    have h2 : ((2 * N + 1 + 1 : ℕ) : ℝ) / (N + 1) = 2 := by
      push_cast; field_simp; ring
    have hlt : ¬ (2 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) / (N + 1) := by
      rw [not_le, div_lt_iff₀ hN]; push_cast; linarith
    simp only [jump2, h2, le_refl, ite_true, hlt, ite_false]
    norm_num
  · intro k hk hne
    rw [Finset.mem_range] at hk
    change _ * (jump2 ((U3 N).pointN (k + 1)) - jump2 ((U3 N).pointN k)) = 0
    rw [U3_pointN N (by omega), U3_pointN N (by omega)]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · push_cast
      have h1 : ¬ (2 : ℝ) ≤ ((k : ℝ) + 1) / (N + 1) := by
        rw [not_le, div_lt_iff₀ hN]
        have : (k : ℝ) + 1 ≤ 2 * N + 1 := by exact_mod_cast (show k + 1 ≤ 2 * N + 1 by omega)
        linarith
      have h0 : ¬ (2 : ℝ) ≤ ((k : ℕ) : ℝ) / (N + 1) := by
        rw [not_le, div_lt_iff₀ hN]
        have : (k : ℝ) ≤ 2 * N := by exact_mod_cast (show k ≤ 2 * N by omega)
        linarith
      simp [jump2, h1, h0]
    · push_cast
      have h1 : (2 : ℝ) ≤ ((k : ℝ) + 1) / (N + 1) := by
        rw [le_div_iff₀ hN]
        have : (2 * N + 2 : ℝ) ≤ k := by exact_mod_cast (show 2 * N + 2 ≤ k by omega)
        linarith
      have h0 : (2 : ℝ) ≤ ((k : ℕ) : ℝ) / (N + 1) := by
        rw [le_div_iff₀ hN]
        have : (2 * N + 2 : ℝ) ≤ k := by exact_mod_cast (show 2 * N + 2 ≤ k by omega)
        linarith
      simp [jump2, h1, h0]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

/-- Left-endpoint tags on `0 < 1 < 2 < 3`: `0 · (1 - 0) + 1 · (4 - 1) + 2 · (9 - 4) = 13`. -/
example : rsSum id (fun x => x ^ 2) (U3 0).leftTag = 13 := by
  rw [rsSum_eq_sum_range]
  change ∑ k ∈ Finset.range 3, _ = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [(U3 0).leftTag_tagN (by rw [U3_n]; norm_num), (U3 0).leftTag_tagN (by rw [U3_n]; norm_num),
    (U3 0).leftTag_tagN (by rw [U3_n]; norm_num)]
  change 0 + (U3 0).pointN 0 * ((U3 0).pointN 1 ^ 2 - (U3 0).pointN 0 ^ 2) +
    (U3 0).pointN 1 * ((U3 0).pointN 2 ^ 2 - (U3 0).pointN 1 ^ 2) +
    (U3 0).pointN 2 * ((U3 0).pointN 3 ^ 2 - (U3 0).pointN 2 ^ 2) = 13
  rw [U3_pointN 0 (by norm_num), U3_pointN 0 (by norm_num), U3_pointN 0 (by norm_num),
    U3_pointN 0 (by norm_num)]
  norm_num

/-- `∫₀³ x d𝟙[2, ∞)(x) = 2`: integrating against the unit jump at `2` evaluates the integrand at
the jump. This is not `f · (h 3 - h 0)` for a constant `f`: that would require the constant `2`,
whereas `x` takes the value `2` only at the jump. The value `2` comes from the explicit sums
above; the refinement estimate only bounds how far a refinement can move them. -/
theorem hasRSIntegral_id_jump2 : HasRSIntegral id jump2 0 3 2 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨U3 N, fun T hT => ?_⟩
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  have hest := abs_rsSum_sub_le_of_isRefinement (f := id) (ω := 1 / (N + 1))
    (jump2_monotone.monotoneOn _) (U3 N).rightTag T hT (fun k hk x hx => by
      change k < 3 * (N + 1) at hk
      change x ∈ Icc ((U3 N).pointN k) ((U3 N).pointN (k + 1)) at hx
      rw [(U3 N).rightTag_tagN hk]
      rw [U3_pointN N (by omega), U3_pointN N (by omega)] at hx
      rw [U3_pointN N (by omega)]
      rw [id, id, abs_of_nonneg (by linarith [hx.2])]
      have : ((k + 1 : ℕ) : ℝ) / (N + 1) - (k : ℕ) / (N + 1) = 1 / (N + 1) := by
        push_cast; field_simp; ring
      linarith [hx.1])
  rw [rsSum_U3_rightTag] at hest
  have hj : jump2 3 - jump2 0 = 1 := by norm_num [jump2]
  rw [hj, mul_one, abs_sub_comm] at hest
  exact hest.trans_lt hN

example : rsIntegral id jump2 0 3 = 2 := hasRSIntegral_id_jump2.rsIntegral_eq

/-- The monotone-integrator bound `|∫ f dh| ≤ M (h b - h a)` with `M = 3`, `h 3 - h 0 = 1`. -/
example : |rsIntegral id jump2 0 3| ≤ 3 * (jump2 3 - jump2 0) :=
  (hasRSIntegral_id_jump2.rsIntegrable.hasRSIntegral).abs_le_of_monotoneOn
    (fun x hx => by rw [id, abs_of_nonneg hx.1]; exact hx.2) (jump2_monotone.monotoneOn _)

/-! ### Constants, linearity, boundary cases -/

/-- Constant integrand: `∫ₐᵇ c dh = c (h b - h a)` for an arbitrary integrator. -/
example (c : ℝ) (h : ℝ → ℝ) : rsIntegral (fun _ => c) h 0 1 = c * (h 1 - h 0) :=
  (hasRSIntegral_const c h zero_le_one).rsIntegral_eq

/-- The constant integrand attains the monotone-integrator bound with equality. -/
example : |rsIntegral (fun _ => (1 : ℝ)) jump2 0 3| = 1 * (jump2 3 - jump2 0) := by
  rw [(hasRSIntegral_const 1 jump2 (by norm_num)).rsIntegral_eq]
  norm_num [jump2]

/-- Linearity in the integrator, with values: `∫₀³ x d(2 • 𝟙[2,∞)) = 4`. -/
example : rsIntegral id ((2 : ℝ) • jump2) 0 3 = 4 := by
  rw [(hasRSIntegral_id_jump2.smul_right 2).rsIntegral_eq]; norm_num

/-- Linearity in the integrand: `∫₀³ (x + 1) d𝟙[2,∞) = 2 + 1`. -/
example : rsIntegral (id + fun _ => 1) jump2 0 3 = 3 := by
  rw [(hasRSIntegral_id_jump2.add_left (hasRSIntegral_const 1 jump2 (by norm_num))).rsIntegral_eq]
  norm_num [jump2]

/-- Degenerate interval: every integral over `[a, a]` is `0`. -/
example (f h : ℝ → ℝ) (a : ℝ) : HasRSIntegral f h a a 0 := by
  intro ε hε
  refine ⟨Partition.ofFinset {a} (by simp) (by simp) (by simp), fun T _ => ?_⟩
  have hn : T.n = 0 := by
    by_contra hn
    have hlt : (0 : Fin (T.n + 1)) < Fin.last T.n := Fin.lt_def.mpr (by simp; omega)
    have := T.ordered hlt
    rw [T.first, T.last] at this
    exact lt_irrefl _ this
  rw [rsSum_eq_sum_range, hn]
  simpa using hε

/-- Reversed interval: there are no partitions, so nothing is integrable and the integral is `0`. -/
example (f h : ℝ → ℝ) : ¬ RSIntegrable f h 1 0 ∧ rsIntegral f h 1 0 = 0 := by
  have hnot : ¬ RSIntegrable f h 1 0 := by
    rintro ⟨I, hI⟩
    obtain ⟨P, -⟩ := hI 1 one_pos
    linarith [P.a_le_b]
  exact ⟨hnot, by simp [rsIntegral, hnot]⟩

/-! ### Non-existence at a common jump -/

/-- The unit jump at `1`. -/
noncomputable def step1 (x : ℝ) : ℝ := if 1 ≤ x then 1 else 0

/-- `∫₀² 𝟙[1,∞) d𝟙[1,∞)` does not exist: on every partition the right-tagged and left-tagged sums
differ by `∑ (Δh)² = ∑ Δh = 1`, so no value is within `1/2` of both. -/
theorem not_rsIntegrable_step1_step1 : ¬ RSIntegrable step1 step1 0 2 := by
  rintro ⟨I, hI⟩
  obtain ⟨P, hP⟩ := hI (1 / 2) (by norm_num)
  have hdiff : rsSum step1 step1 P.rightTag - rsSum step1 step1 P.leftTag = 1 := by
    rw [rsSum_eq_sum_range, rsSum_eq_sum_range]
    change ∑ k ∈ Finset.range P.n, _ - ∑ k ∈ Finset.range P.n, _ = _
    rw [← Finset.sum_sub_distrib]
    rw [← (show step1 2 - step1 0 = 1 by norm_num [step1]), ← P.sum_range_sub_pointN step1]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [P.rightTag_tagN hk, P.leftTag_tagN hk]
    change step1 (P.pointN (k + 1)) * (step1 (P.pointN (k + 1)) - step1 (P.pointN k)) -
      step1 (P.pointN k) * (step1 (P.pointN (k + 1)) - step1 (P.pointN k)) =
        step1 (P.pointN (k + 1)) - step1 (P.pointN k)
    have hle : P.pointN k ≤ P.pointN (k + 1) := P.monotone_pointN (Nat.le_succ k)
    unfold step1
    split_ifs <;> first | (exfalso; linarith) | norm_num
  have h1 := hP P.rightTag P.isRefinement_refl
  have h2 := hP P.leftTag P.isRefinement_refl
  rw [abs_lt] at h1 h2
  linarith

/-! ### Existence and the uniform-norm bound -/

/-- Stieltjes's theorem: `x` is integrable against the monotone integrator `x²` on `[0, 1]`. -/
example : RSIntegrable id (fun x => x ^ 2) 0 1 :=
  rsIntegrable_of_continuousOn_of_monotoneOn zero_le_one continuousOn_id
    (fun x hx y _ hxy => by nlinarith [hx.1])

/-- A continuous integrand against the (discontinuous) bounded-variation jump integrator. -/
example : RSIntegrable (fun x => Real.exp x) jump2 0 3 :=
  rsIntegrable_of_continuousOn_of_monotoneOn (by norm_num) Real.continuous_exp.continuousOn
    (jump2_monotone.monotoneOn _)

/-- Lipschitz dependence on the integrator for the uniform norm: changing the integrator by at
most `δ` on `[0, 1]` moves `∫ 1 dh` by at most `δ (2 · 1 + V(1)) = 2δ`. -/
example (g h : ℝ → ℝ) (δ : ℝ) (hgh : ∀ x ∈ Icc (0 : ℝ) 1, |g x - h x| ≤ δ) :
    |rsIntegral (fun _ => (1 : ℝ)) g 0 1 - rsIntegral (fun _ => 1) h 0 1| ≤ δ * 2 := by
  have hsub : ((fun _ : ℝ => (1 : ℝ)) '' Icc 0 1).Subsingleton :=
    (Set.subsingleton_singleton (a := (1 : ℝ))).anti (by rintro _ ⟨x, -, rfl⟩; rfl)
  have hbv : BoundedVariationOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 1) := by
    unfold BoundedVariationOn; rw [eVariationOn.constant_on hsub]; exact ENNReal.zero_ne_top
  have h := HasRSIntegral.abs_sub_le_of_abs_sub_le (M := 1)
    (hasRSIntegral_const 1 g zero_le_one).rsIntegrable.hasRSIntegral
    (hasRSIntegral_const 1 h zero_le_one).rsIntegrable.hasRSIntegral hgh (by simp) hbv
  rwa [eVariationOn.constant_on hsub, ENNReal.toReal_zero, add_zero, mul_one] at h

/-! ### Axioms -/

#print axioms HasRSIntegral.unique
#print axioms HasRSIntegral.add_left
#print axioms HasRSIntegral.add_right
#print axioms HasRSIntegral.abs_le_mul_variation
#print axioms HasRSIntegral.abs_le_of_monotoneOn
#print axioms HasRSIntegral.abs_le_of_abs_le
#print axioms HasRSIntegral.abs_sub_le_of_abs_sub_le
#print axioms abs_rsSum_sub_le_of_isRefinement
#print axioms rsIntegrable_of_cauchy
#print axioms rsIntegrable_of_continuousOn_of_monotoneOn
#print axioms rsIntegrable_of_continuousOn_of_boundedVariationOn
#print axioms hasRSIntegral_id_jump2
#print axioms not_rsIntegrable_step1_step1
#print axioms rsIntegral_sub_right

end MetaMathlibExt

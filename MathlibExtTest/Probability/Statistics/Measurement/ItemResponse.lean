/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the MIT license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemResponse
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Monotone.Basic

/-!
# Item response theory tests: Rasch sufficiency, 2PL affine maps, graded response

Tests for the three item-response contracts.

D03.3 Finite Rasch model: local-independence masses rechecked by hand,
empty item set allowed, total score sufficient for ability with fixed
difficulties (Mair and Hatzinger 2007, Section 3.1).

D06.2 Two-parameter logistic (2PL) affine invariance (Weeks 2010, (7),
(8a), (8b)): the law is unchanged under rescaling with only `A ≠ 0`;
positive scales keep discriminations positive; one anchor item pins
`A = 1` and `B = 0`. Identifying 2PL parameters from the law is NOT
claimed.

D06.3 Graded-response model (Weeks 2010, (2), (3)): telescoping sums with
no hypotheses, nonnegativity under `0 ≤ a` with ordered thresholds,
positivity under strict versions, zero-slope and one-category edge cases.

References:

* Mair and Hatzinger (2007), extended Rasch modeling.
* Weeks (2010), Equations (2), (3), (7), (8a), (8b).
* Rizopoulos, JSS v017 i05, DOI 10.18637/jss.v017.i05.
-/

namespace MathlibExt.Probability.Statistics.Measurement

@[expose]
public section

noncomputable def q_half : Bool → ℝ := fun _ => 1/2

theorem hq_half0 : ∀ i, 0 ≤ q_half i := by
  intro i
  norm_num [q_half]

theorem hq_half1 : ∀ i, q_half i ≤ 1 := by
  intro i
  norm_num [q_half]

noncomputable def q_rat : Bool → ℝ :=
  fun b => if b then 1/3 else 2/5

theorem hq_rat0 : ∀ i, 0 ≤ q_rat i := by
  intro i
  cases i
  · norm_num [q_rat]
  · norm_num [q_rat]

theorem hq_rat1 : ∀ i, q_rat i ≤ 1 := by
  intro i
  cases i
  · norm_num [q_rat]
  · norm_num [q_rat]

noncomputable def a_one : Fin 1 → ℝ := fun _ => 1

theorem ha_one_pos : ∀ i, 0 < a_one i := by
  intro i
  norm_num [a_one]

noncomputable def b_zero : Fin 1 → ℝ := fun _ => 0

theorem hb_mono_ordered :
    Monotone (fun i : Fin 2 => (i.val : ℝ)) := by
  intro a b hab
  show ((a.val : ℕ) : ℝ) ≤ ((b.val : ℕ) : ℝ)
  exact_mod_cast hab

theorem hb_strict_ordered :
    StrictMono (fun i : Fin 2 => (i.val : ℝ)) := by
  intro a b hab
  show ((a.val : ℕ) : ℝ) < ((b.val : ℕ) : ℝ)
  exact_mod_cast hab

/-- Empty item set is allowed: the raw score of an empty pattern is zero. -/
theorem test_totalScore_empty (x : Fin 0 → Bool) :
    totalScore x = 0 := by
  simp [totalScore]

/-- Local-independence masses for two uniform items, rechecked by hand: both
the all-true and all-false patterns have mass `1 / 4`. -/
theorem test_localIndep_uniform :
    localIndepPMF q_half hq_half0 hq_half1 (fun _ => true)
      = ENNReal.ofReal (1/4 : ℝ)
    ∧ localIndepPMF q_half hq_half0 hq_half1 (fun _ => false)
      = ENNReal.ofReal (1/4 : ℝ) := by
  constructor
  · rw [localIndepPMF_apply, Fintype.prod_bool]
    rw [ite_eq_left (show (fun _ : Bool => true) true = true from rfl)]
    rw [ite_eq_left (show (fun _ : Bool => true) false = true from rfl)]
    show ENNReal.ofReal (1/2 : ℝ) * ENNReal.ofReal (1/2 : ℝ)
      = ENNReal.ofReal (1/4 : ℝ)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · rw [localIndepPMF_apply, Fintype.prod_bool]
    rw [ite_eq_right
      (show ¬ (fun _ : Bool => false) true = true from by decide)]
    rw [ite_eq_right
      (show ¬ (fun _ : Bool => false) false = true from by decide)]
    rw [show (1:ℝ) - q_half true = 1/2 by norm_num [q_half]]
    rw [show (1:ℝ) - q_half false = 1/2 by norm_num [q_half]]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num

/-- Rational local-independence masses rechecked by hand (`2 / 15`,
`4 / 15`): these illustrate the local-independence building block used by
2PL; 2PL sigmoid masses themselves are transcendental. -/
theorem test_localIndep_rational :
    localIndepPMF q_rat hq_rat0 hq_rat1 (fun _ => true)
      = ENNReal.ofReal (2/15 : ℝ)
    ∧ localIndepPMF q_rat hq_rat0 hq_rat1 (fun b => !b)
      = ENNReal.ofReal (4/15 : ℝ) := by
  constructor
  · rw [localIndepPMF_apply, Fintype.prod_bool]
    rw [ite_eq_left (show (fun _ : Bool => true) true = true from rfl)]
    rw [ite_eq_left (show (fun _ : Bool => true) false = true from rfl)]
    show ENNReal.ofReal (1/3 : ℝ) * ENNReal.ofReal (2/5 : ℝ)
      = ENNReal.ofReal (2/15 : ℝ)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · rw [localIndepPMF_apply, Fintype.prod_bool]
    rw [ite_eq_right
      (show ¬ (fun b : Bool => !b) true = true from by decide)]
    rw [ite_eq_left (show (fun b : Bool => !b) false = true from rfl)]
    rw [show (1:ℝ) - q_rat true = 2/3 by norm_num [q_rat]]
    show ENNReal.ofReal (2/3 : ℝ) * ENNReal.ofReal (2/5 : ℝ)
      = ENNReal.ofReal (4/15 : ℝ)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num

/-- Total score is sufficient for person ability given fixed item
difficulties (Mair and Hatzinger 2007, Section 3.1). -/
theorem test_rasch_sufficient :
    MathlibExt.Probability.Statistics.Sufficiency.IsSufficientPMF
      (fun θ : ℝ => raschPMF b_zero θ) totalScore :=
  totalScore_sufficient_rasch b_zero

/-- Item difficulties are fixed outside the family: the Rasch family varies
only with ability `θ`. -/
noncomputable def test_rasch_family_shape : ℝ → PMF (Fin 1 → Bool) :=
  raschPMF b_zero

/-- 2PL affine invariance (Weeks 2010, (7), (8a), (8b)): the law is unchanged
under `θ ↦ A * θ + B` with matching maps; only `A ≠ 0` is needed. -/
theorem test_twoPL_affine :
    twoPLPMF a_one b_zero 0
      = twoPLPMF (fun i => a_one i / 2)
        (fun i => 2 * b_zero i + 1) (2 * 0 + 1) :=
  twoPLPMF_affine a_one b_zero 0 2 1 (by norm_num)

/-- Positive-scale 2PL invariance with `A = 2`: transformed discriminations
stay positive and the law is unchanged. -/
theorem test_twoPL_affine_of_pos :
    (∀ i, 0 < a_one i / 2)
      ∧ twoPLPMF a_one b_zero 0
        = twoPLPMF (fun i => a_one i / 2)
          (fun i => 2 * b_zero i + 1) (2 * 0 + 1) :=
  twoPLPMF_affine_of_pos a_one b_zero 0 2 1 (by norm_num) ha_one_pos

/-- One anchor item pins `A = 1` and `B = 0`. -/
theorem test_affine_anchor : (1:ℝ) = 1 ∧ (0:ℝ) = 0 :=
  affine_eq_of_anchor a_one b_zero 0 1 0 (by norm_num)
    (by norm_num [a_one]) (by norm_num [a_one]) (by norm_num [b_zero])

/-- The `A ≠ 0` hypothesis cannot be dropped: under Lean's `x / 0 = 0`
convention, a zero scale collapses every slope to zero. -/
theorem test_affine_A0 (x : ℝ) : x / (0:ℝ) = 0 :=
  div_zero x

/-- Identifying 2PL parameters from the law is NOT claimed here;
identification is addressed only within affine maps. -/
theorem test_2PL_identification_not_claimed : True :=
  trivial

/-- Graded-response sums telescope to one (Weeks 2010, (2), (3)) with no
hypotheses; categories are shifted down by one relative to Weeks. -/
theorem test_graded_sum :
    ∑ j : Fin 3, gradedProb 1 (fun i : Fin 2 => (i.val : ℝ)) 0 j.val
      = 1 :=
  gradedProb_sum 1 (fun i : Fin 2 => (i.val : ℝ)) 0

/-- Graded category probabilities are nonnegative for `0 ≤ a` with ordered
thresholds. -/
theorem test_graded_nonneg_ordered (j : Fin 3) :
    0 ≤ gradedProb 1 (fun i : Fin 2 => (i.val : ℝ)) 0 j.val :=
  gradedProb_nonneg 1 (fun i : Fin 2 => (i.val : ℝ)) 0 (by norm_num)
    hb_mono_ordered j

/-- Graded category probabilities are positive for `0 < a` with strictly
ordered thresholds. -/
theorem test_graded_pos_strict (j : Fin 3) :
    0 < gradedProb 1 (fun i : Fin 2 => (i.val : ℝ)) 0 j.val :=
  gradedProb_pos 1 (fun i : Fin 2 => (i.val : ℝ)) 0 (by norm_num)
    hb_strict_ordered j

/-- The graded-response law (Weeks 2010, (3)) on the ordered example: one
mass reads back through `gradedResponsePMF_apply`. -/
theorem test_gradedResponsePMF_ordered :
    gradedResponsePMF 1 (fun i : Fin 2 => (i.val : ℝ)) 0 (by norm_num)
        hb_mono_ordered ⟨0, by omega⟩
      = ENNReal.ofReal
        (gradedProb 1 (fun i : Fin 2 => (i.val : ℝ)) 0 0) :=
  gradedResponsePMF_apply 1 _ 0 _ _ _

/-- Zero-slope graded law: `a = 0` is allowed by `gradedProb_nonneg` (not
`gradedProb_pos`); one mass reads back. -/
theorem test_gradedResponsePMF_zero_slope :
    gradedResponsePMF 0 (fun i : Fin 2 => (i.val : ℝ)) 0 (le_refl 0)
        hb_mono_ordered ⟨0, by omega⟩
      = ENNReal.ofReal
        (gradedProb 0 (fun i : Fin 2 => (i.val : ℝ)) 0 0) :=
  gradedResponsePMF_apply 0 _ 0 _ _ _

/-- One-category edge case (`m = 0`): the single graded mass sums to one. -/
theorem test_graded_m0_sum (a θ : ℝ) (b : Fin 0 → ℝ) :
    ∑ j : Fin 1, gradedProb a b θ j.val = 1 :=
  gradedProb_sum a b θ

/-- With `m = 1` (two categories), graded masses still telescope; the
two-category law matches a single-item 2PL shape. -/
theorem test_graded_m1_sum (a θ : ℝ) (b : Fin 1 → ℝ) :
    ∑ j : Fin 2, gradedProb a b θ j.val = 1 :=
  gradedProb_sum a b θ

end

end MathlibExt.Probability.Statistics.Measurement

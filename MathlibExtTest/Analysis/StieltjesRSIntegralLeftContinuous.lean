/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
import Mathlib.Tactic

namespace MetaMathlibExt

open Filter Topology Finset MathlibExt.Analysis.StieltjesProductIntegral
  MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous

/-! ### Explicit sums, computed from the definition -/

/-- The left-endpoint sum over `{0, 1, 2}` tags each cell at its left endpoint. -/
example (f h : ℝ → ℝ) :
    leftSum f h {0, 1, 2} = f 0 * (h 1 - h 0) + f 1 * (h 2 - h 1) := by
  have p0 : prev ({0, 1, 2} : Finset ℝ) 0 = 0 := prev_eq_self (by simp)
  have p1 : prev ({0, 1, 2} : Finset ℝ) 1 = 0 :=
    prev_eq_of (by simp) (by norm_num) (by simp)
  have p2 : prev ({0, 1, 2} : Finset ℝ) 2 = 1 :=
    prev_eq_of (by simp) (by norm_num) (by simp)
  rw [leftSum, sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
  ring

/-- The coarsest partition of `[a, b]` gives the single term `f a (h b - h a)`. -/
example (f h : ℝ → ℝ) : leftPartitionSum f h 0 1 ∅ = f 0 * (h 1 - h 0) := by
  have p0 : prev ({0, 1} : Finset ℝ) 0 = 0 := prev_eq_self (by simp)
  have p1 : prev ({0, 1} : Finset ℝ) 1 = 0 := prev_eq_of (by simp) (by norm_num) (by simp)
  rw [leftPartitionSum, partitionPts_empty, leftSum, sum_pair (by norm_num), p0, p1]
  ring

/-- The insertion formula on an explicit set: inserting `1` into `{0, 2}`. -/
example (f h : ℝ → ℝ) :
    leftSum f h {1, 0, 2} - leftSum f h {0, 2} = (f 1 - f 0) * (h 2 - h 1) := by
  have := leftSum_insert_sub f h (P := {0, 2}) (p := 1) (v := 2) (by norm_num) (by simp)
    (by norm_num) (by simp) ⟨0, by simp, by norm_num⟩
  rwa [prev_eq_of (P := {0, 2}) (x := 1) (y := 0) (by simp) (by norm_num)
    (by simp)] at this

/-! ### Same-side jumps: the motivating example

For `f = h = 1_{[c, ∞)}` both functions jump from the left at `c`, and the refinement integral with
free tags does not exist. Every left-endpoint sum is `0`, computed term by term from the
definition, so the left-endpoint integral exists and is `0`. -/

/-- Every left-endpoint sum of `1_{[c, ∞)}` against itself vanishes. -/
theorem leftSum_step_step (c : ℝ) (P : Finset ℝ) :
    leftSum (fun x => if c ≤ x then (1 : ℝ) else 0) (fun x => if c ≤ x then 1 else 0) P = 0 := by
  refine sum_eq_zero fun x _ => ?_
  by_cases hp : c ≤ prev P x
  · have hx : c ≤ x := hp.trans (prev_le P x)
    simp [hp, hx]
  · simp [hp]

example (c a b : ℝ) :
    HasLeftRSIntegral (fun x => if c ≤ x then (1 : ℝ) else 0)
      (fun x => if c ≤ x then 1 else 0) a b 0 := by
  rw [HasLeftRSIntegral, show leftPartitionSum (fun x => if c ≤ x then (1 : ℝ) else 0)
      (fun x => if c ≤ x then 1 else 0) a b = fun _ => 0 from
    funext fun s => leftSum_step_step c _]
  exact tendsto_const_nhds

/-- On an explicit partition containing the jump point, the integrand `1_{[1, ∞)}` against
`1_{(1, ∞)}` picks up the value `f 1 = 1` from the cell `(1, 2]`. -/
example : leftPartitionSum (fun x => if (1 : ℝ) ≤ x then (1 : ℝ) else 0)
    (fun x => if (1 : ℝ) < x then 1 else 0) 0 2 {1} = 1 := by
  have hP : partitionPts (0 : ℝ) 2 {1} = {0, 2, 1} := by
    ext x; simp [mem_partitionPts]; constructor <;> rintro (h | h | h) <;> simp_all
  have p0 : prev ({0, 2, 1} : Finset ℝ) 0 = 0 := prev_eq_self (by simp)
  have p1 : prev ({0, 2, 1} : Finset ℝ) 1 = 0 :=
    prev_eq_of (by simp) (by norm_num) (by simp)
  have p2 : prev ({0, 2, 1} : Finset ℝ) 2 = 1 :=
    prev_eq_of (by simp) (by norm_num) (by simp)
  rw [leftPartitionSum, hP, leftSum, sum_insert (by norm_num), sum_insert (by norm_num),
    sum_singleton, p0, p1, p2]
  norm_num

/-! ### Step integrators -/

/-- `1_{[1, ∞)}` against `1_{(1, ∞)}`: the jump from the right is weighted by `f 1 = 1`. -/
example : HasLeftRSIntegral (fun x => if (1 : ℝ) ≤ x then (1 : ℝ) else 0)
    (fun x => if (1 : ℝ) < x then 1 else 0) 0 2 1 := by
  have := hasLeftRSIntegral_ite_lt (f := fun x => if (1 : ℝ) ≤ x then (1 : ℝ) else 0)
    (a := 0) (b := 2) (c := 1) (by norm_num) (by norm_num)
  simpa using this

/-- `1_{[1, ∞)}` against `1_{[1, ∞)}`: the jump from the left is weighted by the left limit `0`,
not by the value `f 1 = 1`. -/
example : HasLeftRSIntegral (fun x => if (1 : ℝ) ≤ x then (1 : ℝ) else 0)
    (fun x => if (1 : ℝ) ≤ x then 1 else 0) 0 2 0 := by
  refine hasLeftRSIntegral_ite_le (by norm_num) (by norm_num) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : x < 1)
  simp [not_le.2 hx]

/-- For the left-continuous `1_{(1, ∞)}` the left limit at `1` is the value `0`. -/
example : HasLeftRSIntegral (fun x => if (1 : ℝ) < x then (1 : ℝ) else 0)
    (fun x => if (1 : ℝ) ≤ x then 1 else 0) 0 2 0 := by
  have hcont : ContinuousWithinAt (fun x => if (1 : ℝ) < x then (1 : ℝ) else 0) (Set.Iic 1) 1 := by
    refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun x (hx : x ≤ 1) => ?_) (by simp)
    simp [not_lt.2 hx]
  have := hasLeftRSIntegral_ite_le_of_continuousWithinAt (a := 0) (b := 2) (by norm_num)
    (by norm_num) hcont
  simpa using this

/-- A continuous integrand against a unit jump at `c` integrates to its value at `c`. -/
example : HasLeftRSIntegral id (fun x => if (1 / 2 : ℝ) ≤ x then 1 else 0) 0 1 (1 / 2) :=
  hasLeftRSIntegral_ite_le_of_continuousWithinAt (by norm_num) (by norm_num)
    continuous_id.continuousWithinAt

/-! ### Constants, uniqueness, linearity -/

example (h : ℝ → ℝ) : HasLeftRSIntegral (fun _ => 3) h 0 1 (3 * (h 1 - h 0)) :=
  hasLeftRSIntegral_const zero_le_one 3 h

example (h : ℝ → ℝ) : leftRSIntegral (fun _ => 3) h 0 1 = 3 * (h 1 - h 0) :=
  (hasLeftRSIntegral_const zero_le_one 3 h).leftRSIntegral_eq

/-- Linearity in the integrator, applied to the two step integrators above. -/
example : HasLeftRSIntegral id ((fun x => if (1 / 2 : ℝ) ≤ x then 1 else 0) +
    (fun x => if (1 / 2 : ℝ) < x then 1 else 0)) 0 1 (1 / 2 + 1 / 2) :=
  (hasLeftRSIntegral_ite_le_of_continuousWithinAt (by norm_num) (by norm_num)
    continuous_id.continuousWithinAt).add_right
    (hasLeftRSIntegral_ite_lt (f := id) (by norm_num) (by norm_num))

/-! ### Existence -/

theorem boundedVariationOn_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Set.Icc a b)) : BoundedVariationOn f (Set.Icc a b) := by
  have := hf.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [Set.inter_self] at this

/-- Both functions discontinuous at the same point: existence for bounded variation. -/
example : LeftRSIntegrable (fun x => if (1 / 2 : ℝ) ≤ x then (1 : ℝ) else 0)
    (fun x => if (1 / 2 : ℝ) ≤ x then 1 else 0) 0 1 := by
  have hm : MonotoneOn (fun x : ℝ => if (1 / 2 : ℝ) ≤ x then (1 : ℝ) else 0) (Set.Icc 0 1) :=
    fun x _ y _ hxy => by
      dsimp only
      split_ifs <;> linarith
  exact leftRSIntegrable_of_boundedVariationOn zero_le_one
    (boundedVariationOn_of_monotoneOn zero_le_one hm)
    (boundedVariationOn_of_monotoneOn zero_le_one hm)

/-- Existence for a continuous integrator, through `leftRSIntegrable_of_continuousOn`; here
`sin` on `[0, 1]`. This exercises only the continuous-integrator route: `sin` is itself of
bounded variation on `[0, 1]`. -/
example : LeftRSIntegrable id Real.sin 0 1 :=
  leftRSIntegrable_of_continuousOn zero_le_one
    (boundedVariationOn_of_monotoneOn zero_le_one (monotone_id.monotoneOn _))
    Real.continuous_sin.continuousOn

/-! ### Bounds -/

/-- The uniform-norm bound on a single explicit sum. -/
example (h : ℝ → ℝ) (hh : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ 1) (s : Finset ℝ) :
    |leftPartitionSum id h 0 1 s| ≤ 1 * (2 * 1 + (id 1 - id 0)) :=
  abs_leftPartitionSum_le_of_abs_le zero_le_one hh
    (fun x hx => by rw [id, abs_of_nonneg hx.1]; exact hx.2)
    (isControl_self_of_monotoneOn (monotone_id.monotoneOn _)) s

/-- The bound for a monotone integrator, applied to the step integrator: the integral `1 / 2` is
at most `1 * (h 1 - h 0) = 1`. The bound is not attained here; the example only demonstrates
it. -/
example : |(1 / 2 : ℝ)| ≤ 1 * ((fun x => if (1 / 2 : ℝ) ≤ x then (1 : ℝ) else 0) 1 -
    (fun x => if (1 / 2 : ℝ) ≤ x then (1 : ℝ) else 0) 0) := by
  have hI : HasLeftRSIntegral id (fun x => if (1 / 2 : ℝ) ≤ x then 1 else 0) 0 1 (1 / 2) :=
    hasLeftRSIntegral_ite_le_of_continuousWithinAt (by norm_num) (by norm_num)
      continuous_id.continuousWithinAt
  refine hI.abs_le_of_monotoneOn zero_le_one (fun x _ y _ hxy => ?_) fun x hx => ?_
  · dsimp only
    split_ifs <;> linarith
  · rw [id, abs_of_nonneg hx.1]; exact hx.2

/-! ### Agreement with the free-tag integral -/

/-- The left-endpoint sum over the points of any partition is the left-tagged `rsSum`. -/
example (f h : ℝ → ℝ) (P : MathlibExt.Analysis.Integration.Partition 0 1) :
    leftSum f h (univ.image P.points) = MathlibExt.Analysis.Integration.rsSum f h P.leftTag :=
  leftSum_image_points_eq_rsSum_leftTag f h P

/-- A free-tag integral transfers with its value: the free-tag `∫₀¹ c dh = c (h 1 - h 0)` gives
the left-endpoint integral, the value of `hasLeftRSIntegral_const`. -/
example (c : ℝ) (h : ℝ → ℝ) : HasLeftRSIntegral (fun _ => c) h 0 1 (c * (h 1 - h 0)) :=
  hasLeftRSIntegral_of_hasRSIntegral
    (MathlibExt.Analysis.Integration.hasRSIntegral_const c h zero_le_one)

/-- The two integrals agree: for `f = id` (continuous) against `h = id` (monotone) on `[0, 1]`,
the left-endpoint integral is the free-tag `rsIntegral`. -/
example : leftRSIntegral id id 0 1 = MathlibExt.Analysis.Integration.rsIntegral id id 0 1 :=
  (hasLeftRSIntegral_of_hasRSIntegral
    (MathlibExt.Analysis.Integration.rsIntegrable_of_continuousOn_of_monotoneOn zero_le_one
      continuous_id.continuousOn (monotone_id.monotoneOn _)).hasRSIntegral).leftRSIntegral_eq

/-! ### Axioms -/

#print axioms leftRSIntegrable_of_boundedVariationOn
#print axioms leftRSIntegrable_of_uniform_approx
#print axioms leftRSIntegrable_of_continuousOn
#print axioms HasLeftRSIntegral.tendsto_rightSum
#print axioms HasLeftRSIntegral.abs_le_mul_variation
#print axioms HasLeftRSIntegral.abs_le_of_abs_le
#print axioms HasLeftRSIntegral.abs_sub_le_of_abs_sub_le
#print axioms hasLeftRSIntegral_ite_le
#print axioms hasLeftRSIntegral_ite_lt
#print axioms leftSum_image_points_eq_rsSum_leftTag
#print axioms hasLeftRSIntegral_of_hasRSIntegral

end MetaMathlibExt

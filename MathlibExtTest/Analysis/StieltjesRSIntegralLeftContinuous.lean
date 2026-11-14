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

/-! ### The implication on a computed instance

`f₃ = 3 · 1_{(-∞, 1]}` is left-continuous and jumps from the right at `1`; `step₁ = 1_{[1, ∞)}`
jumps from the left there. The jumps are on opposite sides, so the free-tag integral exists. Its
value `3` is computed below from `HasRSIntegral` itself, independently of the left-endpoint
integral. -/

/-- `3` up to and including `1`, `0` after it. -/
noncomputable def f₃ (x : ℝ) : ℝ := if x ≤ 1 then 3 else 0

/-- The unit jump at `1`, closed on the right. -/
noncomputable def step₁ (x : ℝ) : ℝ := if 1 ≤ x then 1 else 0

/-- `∫₀² f₃ dstep₁ = 3` in the free-tag sense, from the definition: on every tagged refinement of
`{0, 1, 2}` each cell either ends at or before `1` (where `step₁` is flat or `f₃ = 3` at the
tag) or starts at or after `1` (where `step₁` is flat), so the sum equals
`3 (step₁ 2 - step₁ 0) = 3`. -/
theorem hasRSIntegral_f₃_step₁ : MathlibExt.Analysis.Integration.HasRSIntegral f₃ step₁ 0 2 3 := by
  intro ε hε
  refine ⟨MathlibExt.Analysis.Integration.Partition.ofFinset {0, 1, 2} (by norm_num) (by simp)
    (by simp), fun T hT => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, T.points j = 1 :=
    hT (by rw [MathlibExt.Analysis.Integration.Partition.pointSet_ofFinset]; simp)
  have hsum : MathlibExt.Analysis.Integration.rsSum f₃ step₁ T =
      MathlibExt.Analysis.Integration.rsSum (fun _ => 3) step₁ T := by
    refine sum_congr rfl fun i _ => ?_
    by_cases hξ : T.tags i ≤ 1
    · simp only [f₃, hξ, ite_true]
    · have hu : 1 ≤ T.points i.castSucc := by
        by_contra hu
        rw [not_le] at hu hξ
        have a1 : i.castSucc < j := T.ordered.lt_iff_lt.1 (by rw [hj]; exact hu)
        have a2 : j < i.succ :=
          T.ordered.lt_iff_lt.1 (by rw [hj]; exact hξ.trans_le (T.tag_mem i).2)
        rw [Fin.lt_def, Fin.val_castSucc] at a1
        rw [Fin.lt_def, Fin.val_succ] at a2
        omega
      have hv : 1 ≤ T.points i.succ := hu.trans (T.ordered.monotone Fin.castSucc_lt_succ.le)
      simp only [step₁, hu, hv, ite_true, sub_self, mul_zero]
  rw [hsum, MathlibExt.Analysis.Integration.rsSum_const]
  norm_num [step₁]
  exact hε

/-- The left-endpoint sums of `f₃` against `step₁`, computed directly: every one is `3`, because
the only cell that sees the jump is `(prev P 1, 1]` and `f₃ (prev P 1) = 3`. -/
theorem leftPartitionSum_f₃_step₁ (s : Finset ℝ) : leftPartitionSum f₃ step₁ 0 2 s = 3 := by
  rw [show step₁ = fun x => if 1 ≤ x then 1 else 0 from rfl,
    leftPartitionSum_ite_le f₃ (by norm_num) (by norm_num) s]
  have : prev (partitionPts 0 2 s) 1 < 1 :=
    (prev_spec ⟨0, left_mem_partitionPts s, by norm_num⟩).2.1
  simp [f₃, this.le]

/-- The implication instantiated: the free-tag integral transfers to the left-endpoint integral. -/
example : HasLeftRSIntegral f₃ step₁ 0 2 3 :=
  hasLeftRSIntegral_of_hasRSIntegral hasRSIntegral_f₃_step₁

/-- The value the implication transfers agrees with the limit of the directly computed
left-endpoint sums; so any free-tag value must be `3`. -/
example (I : ℝ) (hI : MathlibExt.Analysis.Integration.HasRSIntegral f₃ step₁ 0 2 I) : I = 3 := by
  have hdirect : HasLeftRSIntegral f₃ step₁ 0 2 3 := by
    rw [HasLeftRSIntegral, funext leftPartitionSum_f₃_step₁]
    exact tendsto_const_nhds
  exact (hasLeftRSIntegral_of_hasRSIntegral hI).unique hdirect

/-! ### Where the implication is vacuous

For `f = h = step₁` on `[0, 2]` both functions jump from the left at `1`: every left-tagged sum is
`0` and every right-tagged sum is `1`, so the free-tag integral does not exist and
`hasLeftRSIntegral_of_hasRSIntegral` says nothing. The left-endpoint integral exists anyway. -/

theorem not_exists_hasRSIntegral_step₁ :
    ¬ ∃ I, MathlibExt.Analysis.Integration.HasRSIntegral step₁ step₁ 0 2 I := by
  rintro ⟨I, hI⟩
  obtain ⟨P, hP⟩ := hI (1 / 2) (by norm_num)
  have hL : MathlibExt.Analysis.Integration.rsSum step₁ step₁ P.leftTag = 0 := by
    rw [← leftSum_image_points_eq_rsSum_leftTag]
    exact leftSum_step_step 1 _
  have hR : MathlibExt.Analysis.Integration.rsSum step₁ step₁ P.rightTag = 1 := by
    have e : MathlibExt.Analysis.Integration.rsSum step₁ step₁ P.rightTag =
        MathlibExt.Analysis.Integration.rsSum (fun _ => 1) step₁ P.rightTag := by
      refine sum_congr rfl fun i _ => ?_
      change step₁ (P.points i.succ) * (step₁ (P.points i.succ) - step₁ (P.points i.castSucc)) =
        1 * (step₁ (P.points i.succ) - step₁ (P.points i.castSucc))
      have hle : P.points i.castSucc ≤ P.points i.succ :=
        P.ordered.monotone Fin.castSucc_lt_succ.le
      unfold step₁
      split_ifs <;> first | (exfalso; linarith) | norm_num
    rw [e, MathlibExt.Analysis.Integration.rsSum_const]
    norm_num [step₁]
  have h1 := hP P.leftTag P.isRefinement_refl
  have h2 := hP P.rightTag P.isRefinement_refl
  rw [hL, abs_lt] at h1
  rw [hR, abs_lt] at h2
  linarith

example : (¬ ∃ I, MathlibExt.Analysis.Integration.HasRSIntegral step₁ step₁ 0 2 I) ∧
    HasLeftRSIntegral step₁ step₁ 0 2 0 := by
  refine ⟨not_exists_hasRSIntegral_step₁, ?_⟩
  rw [HasLeftRSIntegral, show leftPartitionSum step₁ step₁ 0 2 = fun _ => 0 from
    funext fun s => leftSum_step_step 1 _]
  exact tendsto_const_nhds

/-! ### Two-tag sums

Left tags for `F`, right tags for `G`, on the explicit partition `{0, 1, 2}`. -/

theorem prev_012 :
    prev ({0, 1, 2} : Finset ℝ) 0 = 0 ∧ prev ({0, 1, 2} : Finset ℝ) 1 = 0 ∧
      prev ({0, 1, 2} : Finset ℝ) 2 = 1 :=
  ⟨prev_eq_self (by simp), prev_eq_of (by simp) (by norm_num) (by simp),
    prev_eq_of (by simp) (by norm_num) (by simp)⟩

/-- `F = id`, `G = x + 1`, `h = x²`: `0 · 1 · 2 + 1 · 3 · 3 = 9`, computed from the definition. -/
example : twoTagSum id (· + 1) (· ^ 2) {0, 1, 2} = 9 := by
  obtain ⟨p0, p1, p2⟩ := prev_012
  rw [twoTagSum, sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
  norm_num

/-- The left-endpoint sum of `F G = x (x + 1)` is `0 · 1 + 2 · 3 = 6`, so by
`twoTagSum_eq_leftSum_add` the second-order term `∑ F(u) Δh ΔG = 1 · 3 · 1` is `3`. -/
example : leftSum (id * (· + 1)) (· ^ 2) {0, 1, 2} = 6 ∧
    ∑ x ∈ ({0, 1, 2} : Finset ℝ), id (prev {0, 1, 2} x) * (x ^ 2 - prev {0, 1, 2} x ^ 2) *
      ((x + 1) - (prev {0, 1, 2} x + 1)) = 3 := by
  obtain ⟨p0, p1, p2⟩ := prev_012
  constructor
  · rw [leftSum, sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
    norm_num
  · rw [sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
    norm_num

/-- The right-endpoint sum of `F G` is `2 · 1 + 6 · 3 = 20` and the right second-order term
`∑ G(x) Δh ΔF` is `2 · 1 · 1 + 3 · 3 · 1 = 11`; `20 - 11 = 9`. -/
example : rightSum (id * (· + 1)) (· ^ 2) {0, 1, 2} = 20 ∧
    ∑ x ∈ ({0, 1, 2} : Finset ℝ), (x + 1) * (x ^ 2 - prev {0, 1, 2} x ^ 2) *
      (id x - id (prev {0, 1, 2} x)) = 11 := by
  obtain ⟨p0, p1, p2⟩ := prev_012
  constructor
  · rw [rightSum, sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
    norm_num
  · rw [sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
    norm_num

/-- With a common same-side jump the two taggings differ: for `F = 1`, `G = h = step₁` the
two-tag sum is `1` (the right tag of `(0, 1]` sees `G 1 = 1`) while the left-endpoint sum of `F G`
is `0`; the difference is the product of the jumps `ΔG · Δh = 1`. -/
example : twoTagSum (fun _ => 1) step₁ step₁ {0, 1, 2} = 1 ∧
    leftSum ((fun _ => 1) * step₁) step₁ {0, 1, 2} = 0 := by
  obtain ⟨p0, p1, p2⟩ := prev_012
  constructor
  · rw [twoTagSum, sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
    norm_num [step₁]
  · rw [leftSum, sum_insert (by norm_num), sum_insert (by norm_num), sum_singleton, p0, p1, p2]
    norm_num [step₁]

/-- The uniform bound applied to the jump example: `|S| ≤ 1 · (2 · 1 · 1 + 1 · 0 + 3 · 1 · 1)`. -/
example (s : Finset ℝ) : |twoTagSum (fun _ => 1) step₁ step₁ (partitionPts 0 2 s)| ≤ 5 := by
  have hmono : MonotoneOn step₁ (Set.Icc 0 2) := fun x _ y _ hxy => by
    unfold step₁; split_ifs <;> linarith
  have hb : ∀ x ∈ Set.Icc (0 : ℝ) 2, |step₁ x| ≤ 1 := fun x _ => by
    unfold step₁; split_ifs <;> norm_num
  have := abs_twoTagSum_le_of_abs_le (F := fun _ => 1) (G := step₁) (h := step₁)
    (V := fun _ => 0) (B := 1) (M := 1) (N := 1) zero_le_two
    hb (fun _ _ => by norm_num) hb (fun _ _ _ _ _ => by simp) (isControl_self_of_monotoneOn hmono) s
  norm_num [step₁] at this
  linarith

/-- The Duhamel sum is a two-tag sum. -/
example (A B : ℝ → ℝ) (s : Finset ℝ) :
    duhamelSum A B 0 1 s = twoTagSum (productIntegral A 0) (fun x => productIntegral B x 1)
      (B - A) (partitionPts 0 1 s) :=
  duhamelSum_eq_twoTagSum A B 0 1 s

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
#print axioms twoTagSum_image_points
#print axioms twoTagSum_eq_leftSum_add
#print axioms twoTagSum_eq_rightSum_sub
#print axioms duhamelSum_eq_twoTagSum
#print axioms abs_twoTagSum_le_of_abs_le
#print axioms abs_twoTagSum_sub_le
#print axioms hasRSIntegral_f₃_step₁
#print axioms not_exists_hasRSIntegral_step₁

end MetaMathlibExt

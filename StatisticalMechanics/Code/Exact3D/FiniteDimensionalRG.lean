/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Exact3D.Certificate
import Code.Exact3D.RGBridgeCriteria
import Code.Exact3D.MatrixCertificate











namespace StatMech
namespace Exact3D



structure IntervalLipschitzConstant where
  interval : RatInterval
  nonnegative : interval.Nonnegative

namespace IntervalLipschitzConstant


def upper (L : IntervalLipschitzConstant) : ℚ :=
  L.interval.upper


theorem upper_nonneg (L : IntervalLipschitzConstant) : 0 ≤ L.upper :=
  le_trans L.nonnegative L.interval.lower_le_upper


def zero : IntervalLipschitzConstant where
  interval := RatInterval.point 0
  nonnegative := by norm_num [RatInterval.point, RatInterval.Nonnegative]

@[simp] theorem zero_upper : zero.upper = 0 := by
  rfl

end IntervalLipschitzConstant



structure StableBlockWithRemainder (n : ℕ) where
  linear : Fin n → Fin n → ℝ
  enclosure : RatInterval.IntervalMatrix n n
  enclosure_sound : RatInterval.MatrixMem linear enclosure
  linear_contraction : RatInterval.RowSumContraction enclosure
  remainder : (Fin n → ℝ) → Fin n → ℝ
  remainder_lipschitz : IntervalLipschitzConstant
  remainder_bound :
    ∀ x i, |remainder x i| ≤
      (remainder_lipschitz.upper : ℝ) * RatInterval.supNormVec x
  total_lt_one : linear_contraction.c + remainder_lipschitz.upper < 1

namespace StableBlockWithRemainder



noncomputable def ofLinearRowSum {n : ℕ}
    (linear : Fin n → Fin n → ℝ) {enclosure : RatInterval.IntervalMatrix n n}
    (enclosure_sound : RatInterval.MatrixMem linear enclosure)
    (linear_contraction : RatInterval.RowSumContraction enclosure) :
    StableBlockWithRemainder n where
  linear := linear
  enclosure := enclosure
  enclosure_sound := enclosure_sound
  linear_contraction := linear_contraction
  remainder := fun _ _ => 0
  remainder_lipschitz := IntervalLipschitzConstant.zero
  remainder_bound := by
    intro x i
    have h :
        0 ≤ ((IntervalLipschitzConstant.zero.upper : ℚ) : ℝ) *
          RatInterval.supNormVec x := by
      exact mul_nonneg
        (by norm_num [IntervalLipschitzConstant.zero,
          IntervalLipschitzConstant.upper, RatInterval.point])
        (RatInterval.supNormVec_nonneg x)
    simpa [IntervalLipschitzConstant.upper] using h
  total_lt_one := by
    simpa [IntervalLipschitzConstant.zero, IntervalLipschitzConstant.upper,
      RatInterval.point] using linear_contraction.c_lt_one



noncomputable def step {n : ℕ} (S : StableBlockWithRemainder n)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  RatInterval.matVec S.linear x i + S.remainder x i



theorem ofLinearRowSum_step {n : ℕ}
    (linear : Fin n → Fin n → ℝ) {enclosure : RatInterval.IntervalMatrix n n}
    (enclosure_sound : RatInterval.MatrixMem linear enclosure)
    (linear_contraction : RatInterval.RowSumContraction enclosure)
    (x : Fin n → ℝ) :
    (ofLinearRowSum linear enclosure_sound linear_contraction).step x =
      fun i => RatInterval.matVec linear x i := by
  funext i
  simp [ofLinearRowSum, step]


noncomputable def coordinateConstant {n : ℕ} (S : StableBlockWithRemainder n) : ℝ :=
  ((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ)



noncomputable def l1StepConstant {n : ℕ} (S : StableBlockWithRemainder n) : ℝ :=
  (n : ℝ) * S.coordinateConstant


noncomputable def iterate {n : ℕ} (S : StableBlockWithRemainder n) :
    ℕ → (Fin n → ℝ) → Fin n → ℝ
  | 0, x => x
  | k + 1, x => S.step (S.iterate k x)


theorem remainder_zero {n : ℕ} (S : StableBlockWithRemainder n) :
    S.remainder (0 : Fin n → ℝ) = 0 := by
  funext i
  have hle : |S.remainder (0 : Fin n → ℝ) i| ≤ 0 := by
    simpa [RatInterval.supNormVec] using
      S.remainder_bound (0 : Fin n → ℝ) i
  have habs : |S.remainder (0 : Fin n → ℝ) i| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp habs


theorem step_zero {n : ℕ} (S : StableBlockWithRemainder n) :
    S.step (0 : Fin n → ℝ) = 0 := by
  funext i
  have hrem := congrFun S.remainder_zero i
  simp [step, RatInterval.matVec, hrem]


theorem iterate_zero {n : ℕ} (S : StableBlockWithRemainder n) (k : ℕ) :
    S.iterate k (0 : Fin n → ℝ) = 0 := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, S.step_zero]



theorem apply_bound {n : ℕ} (S : StableBlockWithRemainder n)
    (x : Fin n → ℝ) (i : Fin n) :
    |S.step x i| ≤ S.coordinateConstant * RatInterval.supNormVec x := by
  have hlinear :
      |RatInterval.matVec S.linear x i| ≤
        (S.linear_contraction.c : ℝ) * RatInterval.supNormVec x :=
    S.linear_contraction.apply_bound S.enclosure_sound x i
  have hrem :
      |S.remainder x i| ≤
        (S.remainder_lipschitz.upper : ℝ) * RatInterval.supNormVec x :=
    S.remainder_bound x i
  calc
    |S.step x i| = |RatInterval.matVec S.linear x i + S.remainder x i| := rfl
    _ ≤ |RatInterval.matVec S.linear x i| + |S.remainder x i| := abs_add_le _ _
    _ ≤ (S.linear_contraction.c : ℝ) * RatInterval.supNormVec x +
        (S.remainder_lipschitz.upper : ℝ) * RatInterval.supNormVec x := by
      exact add_le_add hlinear hrem
    _ = ((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ) *
        RatInterval.supNormVec x := by
      norm_num [IntervalLipschitzConstant.upper]
      ring


theorem coordinateConstant_nonneg {n : ℕ} (S : StableBlockWithRemainder n) :
    0 ≤ S.coordinateConstant := by
  have hq :
      0 ≤ S.linear_contraction.c + S.remainder_lipschitz.upper :=
    add_nonneg S.linear_contraction.c_nonneg
      S.remainder_lipschitz.upper_nonneg
  have hqℝ :
      (0 : ℝ) ≤
        ((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [coordinateConstant] using hqℝ


theorem contraction_constant_lt_one {n : ℕ} (S : StableBlockWithRemainder n) :
    S.coordinateConstant < 1 := by
  have hqℝ :
      (((S.linear_contraction.c + S.remainder_lipschitz.upper : ℚ) : ℝ) <
        (1 : ℝ)) := by
    exact_mod_cast S.total_lt_one
  simpa [coordinateConstant] using hqℝ


theorem l1StepConstant_nonneg {n : ℕ} (S : StableBlockWithRemainder n) :
    0 ≤ S.l1StepConstant := by
  exact mul_nonneg (Nat.cast_nonneg n) S.coordinateConstant_nonneg



theorem ofLinearRowSum_l1StepConstant {n : ℕ}
    (linear : Fin n → Fin n → ℝ) {enclosure : RatInterval.IntervalMatrix n n}
    (enclosure_sound : RatInterval.MatrixMem linear enclosure)
    (linear_contraction : RatInterval.RowSumContraction enclosure) :
    (ofLinearRowSum linear enclosure_sound linear_contraction).l1StepConstant =
      (n : ℝ) * (linear_contraction.c : ℝ) := by
  simp [l1StepConstant, coordinateConstant, ofLinearRowSum,
    IntervalLipschitzConstant.zero, IntervalLipschitzConstant.upper,
    RatInterval.point]



theorem step_supNormVec_bound {n : ℕ} (S : StableBlockWithRemainder n)
    (x : Fin n → ℝ) :
    RatInterval.supNormVec (S.step x) ≤
      S.l1StepConstant * RatInterval.supNormVec x := by
  classical
  calc
    RatInterval.supNormVec (S.step x) =
        ∑ i : Fin n, |S.step x i| := rfl
    _ ≤ ∑ _i : Fin n, S.coordinateConstant * RatInterval.supNormVec x := by
      exact Finset.sum_le_sum fun i _ => S.apply_bound x i
    _ = S.l1StepConstant * RatInterval.supNormVec x := by
      simp [l1StepConstant, Finset.sum_const, nsmul_eq_mul]
      ring



theorem step_mem_l1_ball_of_l1StepConstant_le_one {n : ℕ}
    (S : StableBlockWithRemainder n) {r : ℝ}
    (hS : S.l1StepConstant ≤ 1) (hr : 0 ≤ r) {x : Fin n → ℝ}
    (hx : RatInterval.supNormVec x ≤ r) :
    RatInterval.supNormVec (S.step x) ≤ r := by
  calc
    RatInterval.supNormVec (S.step x) ≤
        S.l1StepConstant * RatInterval.supNormVec x :=
      S.step_supNormVec_bound x
    _ ≤ S.l1StepConstant * r := by
      exact mul_le_mul_of_nonneg_left hx S.l1StepConstant_nonneg
    _ ≤ 1 * r := by
      exact mul_le_mul_of_nonneg_right hS hr
    _ = r := by ring



theorem iterate_supNormVec_bound {n : ℕ} (S : StableBlockWithRemainder n)
    (k : ℕ) (x : Fin n → ℝ) :
    RatInterval.supNormVec (S.iterate k x) ≤
      S.l1StepConstant ^ k * RatInterval.supNormVec x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      calc
        RatInterval.supNormVec (S.iterate (k + 1) x) =
            RatInterval.supNormVec (S.step (S.iterate k x)) := rfl
        _ ≤ S.l1StepConstant * RatInterval.supNormVec (S.iterate k x) :=
          S.step_supNormVec_bound (S.iterate k x)
        _ ≤ S.l1StepConstant *
            (S.l1StepConstant ^ k * RatInterval.supNormVec x) := by
          exact mul_le_mul_of_nonneg_left ih S.l1StepConstant_nonneg
        _ = S.l1StepConstant ^ (k + 1) * RatInterval.supNormVec x := by
          rw [pow_succ']
          ring



theorem tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one {n : ℕ}
    (S : StableBlockWithRemainder n)
    (hS : S.l1StepConstant < 1) (x : Fin n → ℝ) :
    Filter.Tendsto (fun k : ℕ => RatInterval.supNormVec (S.iterate k x))
      Filter.atTop (nhds 0) := by
  have hpow :
      Filter.Tendsto (fun k : ℕ => S.l1StepConstant ^ k) Filter.atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one S.l1StepConstant_nonneg hS
  have hupper :
      Filter.Tendsto
        (fun k : ℕ =>
          S.l1StepConstant ^ k * RatInterval.supNormVec x)
        Filter.atTop (nhds 0) := by
    simpa using
      hpow.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => RatInterval.supNormVec x)
          Filter.atTop (nhds (RatInterval.supNormVec x)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds 0)) hupper ?_ ?_
  · intro k
    exact RatInterval.supNormVec_nonneg (S.iterate k x)
  · intro k
    exact S.iterate_supNormVec_bound k x



theorem iterate_mem_l1_ball_of_l1StepConstant_le_one {n : ℕ}
    (S : StableBlockWithRemainder n) {r : ℝ}
    (hS : S.l1StepConstant ≤ 1) (hr : 0 ≤ r) {x : Fin n → ℝ}
    (hx : RatInterval.supNormVec x ≤ r) (k : ℕ) :
    RatInterval.supNormVec (S.iterate k x) ≤ r := by
  induction k with
  | zero =>
      simpa [iterate] using hx
  | succ k ih =>
      exact S.step_mem_l1_ball_of_l1StepConstant_le_one hS hr ih


def ThermalStableCone {n : ℕ} (η t : ℝ) (s : Fin n → ℝ) : Prop :=
  RatInterval.supNormVec s ≤ η * |t|


theorem step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
    {n : ℕ} (S : StableBlockWithRemainder n)
    {thermal η t : ℝ} {s : Fin n → ℝ}
    (hη : 0 ≤ η)
    (hdom : S.l1StepConstant ≤ |thermal|)
    (hs : ThermalStableCone η t s) :
    ThermalStableCone η (thermal * t) (S.step s) := by
  have hK_nonneg : 0 ≤ S.l1StepConstant := S.l1StepConstant_nonneg
  have hcone_rhs_nonneg : 0 ≤ η * |t| :=
    mul_nonneg hη (abs_nonneg t)
  calc
    RatInterval.supNormVec (S.step s)
        ≤ S.l1StepConstant * RatInterval.supNormVec s :=
      S.step_supNormVec_bound s
    _ ≤ S.l1StepConstant * (η * |t|) :=
      mul_le_mul_of_nonneg_left hs hK_nonneg
    _ ≤ |thermal| * (η * |t|) :=
      mul_le_mul_of_nonneg_right hdom hcone_rhs_nonneg
    _ = η * |thermal * t| := by
      rw [abs_mul]
      ring



theorem iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
    {n : ℕ} (S : StableBlockWithRemainder n)
    {thermal η t : ℝ} {s : Fin n → ℝ}
    (hη : 0 ≤ η)
    (hdom : S.l1StepConstant ≤ |thermal|)
    (hs : ThermalStableCone η t s) (k : ℕ) :
    ThermalStableCone η (thermal ^ k * t) (S.iterate k s) := by
  induction k with
  | zero =>
      simpa [iterate] using hs
  | succ k ih =>
      have hstep :=
        S.step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
          hη hdom ih
      simpa [iterate, pow_succ', mul_assoc] using hstep

end StableBlockWithRemainder




structure FiniteHyperbolicSplitting (n : ℕ) where
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : StableBlockWithRemainder n
  stable_dominated : stable.l1StepConstant ≤ |thermal|

namespace FiniteHyperbolicSplitting



noncomputable def ofLinearStableRowSum {n : ℕ}
    (thermal : ℝ) (thermal_gt_one : 1 < thermal)
    (stableLinear : Fin n → Fin n → ℝ)
    {stableEnclosure : RatInterval.IntervalMatrix n n}
    (stable_enclosure_sound : RatInterval.MatrixMem stableLinear stableEnclosure)
    (stable_contraction : RatInterval.RowSumContraction stableEnclosure)
    (stable_dominated :
      (n : ℝ) * (stable_contraction.c : ℝ) ≤ |thermal|) :
    FiniteHyperbolicSplitting n where
  thermal := thermal
  thermal_gt_one := thermal_gt_one
  stable :=
    StableBlockWithRemainder.ofLinearRowSum stableLinear
      stable_enclosure_sound stable_contraction
  stable_dominated := by
    simpa [StableBlockWithRemainder.ofLinearRowSum_l1StepConstant] using
      stable_dominated


abbrev State (n : ℕ) : Type :=
  ℝ × (Fin n → ℝ)


def origin {n : ℕ} : State n :=
  (0, 0)



noncomputable def step {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (x : State n) : State n :=
  (H.thermal * x.1, H.stable.step x.2)


noncomputable def iterate {n : ℕ} (H : FiniteHyperbolicSplitting n) :
    ℕ → State n → State n
  | 0, x => x
  | k + 1, x => H.step (H.iterate k x)


theorem step_origin {n : ℕ} (H : FiniteHyperbolicSplitting n) :
    H.step origin = origin := by
  apply Prod.ext
  · simp [origin, step]
  · simpa [origin, step] using H.stable.step_zero


theorem iterate_origin {n : ℕ} (H : FiniteHyperbolicSplitting n) (k : ℕ) :
    H.iterate k origin = origin := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, ih, H.step_origin]


abbrev hamiltonian {n : ℕ} (_H : FiniteHyperbolicSplitting n) :
    EffectiveHamiltonian where
  carrier := State n



noncomputable def rgMap {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) : BlockSpinMap H.hamiltonian where
  scale := scale
  map := H.step


noncomputable def fixedPointData {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) : RGFixedPointData H.hamiltonian (H.rgMap scale) where
  fixedPoint := origin
  fixedPoint_eq := H.step_origin
  thermalEigenvalue := H.thermal
  thermal_gt_one := H.thermal_gt_one



noncomputable def certificate {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) : RGCertificate M where
  H := H.hamiltonian
  R := H.rgMap scale
  fixedPointData := H.fixedPointData scale

@[simp] theorem certificate_retarget {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ) :
    H.certificate scale N = (H.certificate scale M).retarget N :=
  rfl

@[simp] theorem certificate_thermalEigenvalue_eq {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).thermalEigenvalue = H.thermal :=
  rfl

@[simp] theorem certificate_scale_eq {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).scale = scale :=
  rfl



theorem certificate_predictedExponent_eq {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).predictedExponent =
      predictedNu scale H.thermal :=
  rfl


theorem certificate_fixedPointEnclosure {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).FixedPointEnclosure :=
  H.step_origin

theorem certificate_finiteCaseChecks {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).FiniteCaseChecks :=
  trivial

theorem certificate_tailBounds {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).TailBounds :=
  trivial

theorem certificate_linearizationEnclosure {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).LinearizationEnclosure :=
  (H.certificate scale M).linearizationEnclosure_of_thermal_gt_one

theorem certificate_hyperbolicSplitting {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).HyperbolicSplitting :=
  (H.certificate scale M).hyperbolicSplitting_of_thermal_gt_one

theorem certificate_orbitEntry {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).OrbitEntry :=
  trivial


theorem iterate_fst_eq {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (k : ℕ) (x : State n) :
    (H.iterate k x).1 = H.thermal ^ k * x.1 := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      simp [iterate, step, ih, pow_succ', mul_assoc]


theorem iterate_snd_eq {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (k : ℕ) (x : State n) :
    (H.iterate k x).2 = H.stable.iterate k x.2 := by
  induction k with
  | zero =>
      simp [iterate, StableBlockWithRemainder.iterate]
  | succ k ih =>
      simp [iterate, StableBlockWithRemainder.iterate, step, ih]



theorem tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one
    {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (hS : H.stable.l1StepConstant < 1) (x : State n) :
    Filter.Tendsto
      (fun k : ℕ => RatInterval.supNormVec (H.iterate k x).2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_
    (H.stable.tendsto_iterate_supNormVec_zero_of_l1StepConstant_lt_one
      hS x.2)
  exact Filter.Eventually.of_forall fun k => by
    exact congrArg RatInterval.supNormVec (H.iterate_snd_eq k x).symm


def cone {n : ℕ} (_H : FiniteHyperbolicSplitting n)
    (η : ℝ) (x : State n) : Prop :=
  StableBlockWithRemainder.ThermalStableCone η x.1 x.2


theorem cone_step {n : ℕ} (H : FiniteHyperbolicSplitting n)
    {η : ℝ} (hη : 0 ≤ η) {x : State n} (hx : H.cone η x) :
    H.cone η (H.step x) :=
  H.stable.step_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
    hη H.stable_dominated hx



theorem cone_iterate {n : ℕ} (H : FiniteHyperbolicSplitting n)
    {η : ℝ} (hη : 0 ≤ η) {x : State n} (hx : H.cone η x)
    (k : ℕ) :
    H.cone η (H.iterate k x) := by
  unfold cone
  rw [H.iterate_fst_eq k x, H.iterate_snd_eq k x]
  exact
    H.stable.iterate_mem_thermalStableCone_of_l1StepConstant_le_abs_thermal
      hη H.stable_dominated hx k


theorem rgMap_iterate_eq {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) (k : ℕ) (x : State n) :
    ((H.rgMap scale).map^[k]) x = H.iterate k x := by
  induction k with
  | zero =>
      simp [iterate]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simpa [iterate, rgMap] using congrArg H.step ih



theorem rgMap_cone_iterate {n : ℕ} (H : FiniteHyperbolicSplitting n)
    (scale : BlockScale) {η : ℝ} (hη : 0 ≤ η) {x : State n}
    (hx : H.cone η x) (k : ℕ) :
    H.cone η (((H.rgMap scale).map^[k]) x) := by
  rw [H.rgMap_iterate_eq scale k x]
  exact H.cone_iterate hη hx k



theorem tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one
    {n : ℕ} (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (hS : H.stable.l1StepConstant < 1) (x : State n) :
    Filter.Tendsto
      (fun k : ℕ =>
        RatInterval.supNormVec ((((H.rgMap scale).map^[k]) x).2))
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_
    (H.tendsto_iterate_stable_supNormVec_zero_of_l1StepConstant_lt_one hS x)
  exact Filter.Eventually.of_forall fun k => by
    exact congrArg (fun y : State n => RatInterval.supNormVec y.2)
      (H.rgMap_iterate_eq scale k x).symm



theorem certificate_cone_iterate {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {η : ℝ} (hη : 0 ≤ η)
    {x : (H.certificate scale M).H.carrier} (hx : H.cone η x) (k : ℕ) :
    H.cone η ((((H.certificate scale M).R.map)^[k]) x) := by
  simpa [certificate] using H.rgMap_cone_iterate scale hη hx k


theorem tendsto_certificate_stable_supNormVec_zero_of_l1StepConstant_lt_one
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι)
    (hS : H.stable.l1StepConstant < 1)
    (x : (H.certificate scale M).H.carrier) :
    Filter.Tendsto
      (fun k : ℕ =>
        RatInterval.supNormVec ((((H.certificate scale M).R.map)^[k]) x).2)
      Filter.atTop (nhds 0) := by
  simpa [certificate] using
    H.tendsto_rgMap_stable_supNormVec_zero_of_l1StepConstant_lt_one
      scale hS x



theorem certificate_valid_of_bridge {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
    (H.certificate scale M).Valid correlationLength :=
  (H.certificate scale M).valid_of_bridge correlationLength
    (H.certificate_finiteCaseChecks scale M)
    (H.certificate_tailBounds scale M)
    (H.certificate_fixedPointEnclosure scale M)
    (H.certificate_linearizationEnclosure scale M)
    (H.certificate_hyperbolicSplitting scale M)
    (H.certificate_orbitEntry scale M)
    hbridge



theorem certificate_rgToExponentBridge_of_hasCriticalNu
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  (H.certificate scale M).bridge_of_hasCriticalNu correlationLength hν



theorem certificate_valid_of_hasCriticalNu {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_hasCriticalNu
      scale M correlationLength hν)


theorem certificate_hasCriticalNu_of_bridge {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (correlationLength : ℝ → ℝ)
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_bridge scale M correlationLength hbridge).hasCriticalNu




noncomputable def exactScaleObservable {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) : ℝ → ℝ :=
  fun β : ℝ =>
    Real.exp (-(H.certificate scale M).predictedExponent *
      Real.log (M.betaC - β))

@[simp] theorem exactScaleObservable_eq_power {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (β : ℝ) :
    H.exactScaleObservable scale M β =
      Real.exp (-(H.certificate scale M).predictedExponent *
        Real.log (M.betaC - β)) :=
  rfl



theorem certificate_rgToExponentBridge_exactScaleObservable
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).RGToExponentBridge
      (H.exactScaleObservable scale M) := by
  refine (H.certificate scale M).rgToExponentBridge_of_exact_power_on_Ioo
    (H.exactScaleObservable scale M) 1 (by norm_num) ?_
  intro β _hβ
  exact H.exactScaleObservable_eq_power scale M β



theorem certificate_valid_exactScaleObservable {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    (H.certificate scale M).Valid (H.exactScaleObservable scale M) :=
  H.certificate_valid_of_bridge scale M (H.exactScaleObservable scale M)
    (H.certificate_rgToExponentBridge_exactScaleObservable scale M)



theorem certificate_hasCriticalNu_exactScaleObservable
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) :
    HasCriticalNu M (H.exactScaleObservable scale M)
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_exactScaleObservable scale M).hasCriticalNu



theorem certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (H.certificate scale M).RGToExponentBridge correlationLength :=
  RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred



theorem certificate_valid_of_bridge_congr_predictedExponent
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    (H.certificate scale M).Valid correlationLength :=
  H.certificate_valid_of_bridge scale M correlationLength
    (H.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent
      scale M hpred hbridge)



theorem certificate_hasCriticalNu_of_bridge_congr_predictedExponent
    {n : ℕ} {ι : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) {D : RGCertificate M}
    {correlationLength : ℝ → ℝ}
    (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
    (hbridge : D.RGToExponentBridge correlationLength) :
    HasCriticalNu M correlationLength
      (H.certificate scale M).predictedExponent :=
  (H.certificate_valid_of_bridge_congr_predictedExponent
    scale M hpred hbridge).hasCriticalNu



theorem certificate_retarget_rgToExponentBridge {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC)
    (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength) :
    (H.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using RGCertificate.retarget_rgToExponentBridge hbridge hβc



theorem certificate_retarget_valid {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC)
    (hvalid : (H.certificate scale M).Valid correlationLength) :
    (H.certificate scale N).Valid correlationLength := by
  simpa using hvalid.retarget hβc



theorem certificate_retarget_hasCriticalNu {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC)
    (hν :
      HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent) :
    HasCriticalNu N correlationLength
      (H.certificate scale N).predictedExponent := by
  simpa using RGCertificate.retarget_hasCriticalNu hν hβc


theorem certificate_retarget_rgToExponentBridge_iff
    {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    (H.certificate scale M).RGToExponentBridge correlationLength ↔
      (H.certificate scale N).RGToExponentBridge correlationLength := by
  simpa using
    (RGCertificate.retarget_rgToExponentBridge_iff
      (C := H.certificate scale M) (N := N) hβc)


theorem certificate_retarget_valid_iff {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    (H.certificate scale M).Valid correlationLength ↔
      (H.certificate scale N).Valid correlationLength := by
  simpa using
    (RGCertificate.Valid.retarget_iff
      (C := H.certificate scale M) (N := N) hβc)


theorem certificate_retarget_hasCriticalNu_iff {n : ℕ} {ι κ : Type*}
    (H : FiniteHyperbolicSplitting n) (scale : BlockScale)
    (M : CriticalModel ι) (N : CriticalModel κ)
    {correlationLength : ℝ → ℝ} (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength
        (H.certificate scale M).predictedExponent ↔
      HasCriticalNu N correlationLength
        (H.certificate scale N).predictedExponent := by
  simpa using
    (RGCertificate.retarget_hasCriticalNu_iff
      (C := H.certificate scale M) (N := N) hβc)

end FiniteHyperbolicSplitting

namespace FiniteHyperbolicSplittingExample


noncomputable def stableLinear : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => (1 : ℝ) / 2


def stableEnclosure : RatInterval.IntervalMatrix 1 1 :=
  fun _ _ => RatInterval.point (1 / 2)


theorem stableLinear_mem_enclosure :
    RatInterval.MatrixMem stableLinear stableEnclosure := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [stableLinear, stableEnclosure, RatInterval.point, RatInterval.MemR]


def stableRowSumContraction :
    RatInterval.RowSumContraction stableEnclosure where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i
    norm_num [RatInterval.MatrixAbsRowSum, stableEnclosure,
      RatInterval.point, RatInterval.absUpper]


def zeroRemainderLipschitz : IntervalLipschitzConstant where
  interval := RatInterval.point 0
  nonnegative := by norm_num [RatInterval.point, RatInterval.Nonnegative]


noncomputable def stableBlock : StableBlockWithRemainder 1 where
  linear := stableLinear
  enclosure := stableEnclosure
  enclosure_sound := stableLinear_mem_enclosure
  linear_contraction := stableRowSumContraction
  remainder := fun _ _ => 0
  remainder_lipschitz := zeroRemainderLipschitz
  remainder_bound := by
    intro x i
    simp [zeroRemainderLipschitz, IntervalLipschitzConstant.upper,
      RatInterval.point]
  total_lt_one := by
    norm_num [stableRowSumContraction, zeroRemainderLipschitz,
      IntervalLipschitzConstant.upper, RatInterval.point]


theorem stableBlock_linear_contraction_c :
    stableBlock.linear_contraction.c = (1 / 2 : ℚ) := by
  rfl


theorem stableBlock_remainder_lipschitz_upper :
    stableBlock.remainder_lipschitz.upper = 0 := by
  rfl


theorem stableBlock_l1StepConstant :
    stableBlock.l1StepConstant = (1 : ℝ) / 2 := by
  simp [StableBlockWithRemainder.l1StepConstant,
    StableBlockWithRemainder.coordinateConstant,
    stableBlock_linear_contraction_c,
    stableBlock_remainder_lipschitz_upper]



noncomputable def splitting : FiniteHyperbolicSplitting 1 where
  thermal := 3
  thermal_gt_one := by norm_num
  stable := stableBlock
  stable_dominated := by
    rw [stableBlock_l1StepConstant]
    norm_num



noncomputable def splittingFromRowSum : FiniteHyperbolicSplitting 1 :=
  FiniteHyperbolicSplitting.ofLinearStableRowSum
    (n := 1) (thermal := 3) (by norm_num) stableLinear
    stableLinear_mem_enclosure stableRowSumContraction (by
      norm_num [stableRowSumContraction])



theorem splitting_cone_iterate {η : ℝ} (hη : 0 ≤ η)
    {x : FiniteHyperbolicSplitting.State 1} (hx : splitting.cone η x)
    (k : ℕ) :
    splitting.cone η (splitting.iterate k x) :=
  splitting.cone_iterate hη hx k


def scale : BlockScale where
  L := 2
  one_lt := by norm_num



noncomputable def model : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


noncomputable def certificate : RGCertificate model :=
  splitting.certificate scale model



theorem splittingFromRowSum_certificate_cone_iterate {η : ℝ} (hη : 0 ≤ η)
    {x : (splittingFromRowSum.certificate scale model).H.carrier}
    (hx : splittingFromRowSum.cone η x) (k : ℕ) :
    splittingFromRowSum.cone η
      ((((splittingFromRowSum.certificate scale model).R.map)^[k]) x) :=
  splittingFromRowSum.certificate_cone_iterate scale model hη hx k



theorem certificate_fixedPointEnclosure :
    certificate.FixedPointEnclosure :=
  splitting.certificate_fixedPointEnclosure scale model

end FiniteHyperbolicSplittingExample



structure TwoCoordinateRGData where
  scale : BlockScale
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : ℝ
  stable_abs_lt_one : |stable| < 1

namespace TwoCoordinateRGData


abbrev hamiltonian (_D : TwoCoordinateRGData) : EffectiveHamiltonian where
  carrier := ℝ × ℝ


noncomputable def rgMap (D : TwoCoordinateRGData) : BlockSpinMap D.hamiltonian where
  scale := D.scale
  map := fun x => (D.thermal * x.1, D.stable * x.2)


noncomputable def fixedPointData (D : TwoCoordinateRGData) :
    RGFixedPointData D.hamiltonian D.rgMap where
  fixedPoint := (0, 0)
  fixedPoint_eq := by
    simp [rgMap]
  thermalEigenvalue := D.thermal
  thermal_gt_one := D.thermal_gt_one


noncomputable def model (_D : TwoCoordinateRGData) : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


noncomputable def certificate (D : TwoCoordinateRGData) : RGCertificate D.model where
  H := D.hamiltonian
  R := D.rgMap
  fixedPointData := D.fixedPointData


noncomputable def nu (D : TwoCoordinateRGData) : ℝ :=
  D.certificate.predictedExponent


noncomputable def exactScaleObservable (D : TwoCoordinateRGData) (β : ℝ) : ℝ :=
  Real.exp (-D.nu * Real.log (-β))


noncomputable def iterate (D : TwoCoordinateRGData) :
    ℕ → (ℝ × ℝ) → (ℝ × ℝ)
  | 0, x => x
  | n + 1, x => D.rgMap.map (D.iterate n x)


theorem iterate_eq (D : TwoCoordinateRGData) (n : ℕ) (x : ℝ × ℝ) :
    D.iterate n x = (D.thermal ^ n * x.1, D.stable ^ n * x.2) := by
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      simp [iterate, ih, rgMap, pow_succ', mul_assoc]


theorem stable_iterate_abs_eq (D : TwoCoordinateRGData) (n : ℕ) (s : ℝ) :
    |(D.iterate n (0, s)).2| = |D.stable| ^ n * |s| := by
  simp [iterate_eq, abs_mul, abs_pow]


theorem stable_multiplier_lt_one (D : TwoCoordinateRGData) :
    |D.stable| < 1 :=
  D.stable_abs_lt_one



def thermalCone (_D : TwoCoordinateRGData) (K : ℝ) (x : ℝ × ℝ) : Prop :=
  |x.2| ≤ K * |x.1|


theorem thermal_pos (D : TwoCoordinateRGData) : 0 < D.thermal :=
  lt_trans zero_lt_one D.thermal_gt_one


theorem abs_thermal_eq (D : TwoCoordinateRGData) : |D.thermal| = D.thermal :=
  abs_of_pos D.thermal_pos



theorem stable_abs_le_thermal_abs (D : TwoCoordinateRGData) :
    |D.stable| ≤ |D.thermal| := by
  rw [D.abs_thermal_eq]
  exact (lt_trans D.stable_abs_lt_one D.thermal_gt_one).le



theorem thermalCone_step {D : TwoCoordinateRGData} {K : ℝ} (hK : 0 ≤ K)
    {x : ℝ × ℝ} (hx : D.thermalCone K x) :
    D.thermalCone K (D.rgMap.map x) := by
  unfold thermalCone
  change |D.stable * x.2| ≤ K * |D.thermal * x.1|
  calc
    |D.stable * x.2| = |D.stable| * |x.2| := abs_mul _ _
    _ ≤ |D.stable| * (K * |x.1|) := by
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg D.stable)
    _ = K * (|D.stable| * |x.1|) := by ring
    _ ≤ K * (|D.thermal| * |x.1|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right D.stable_abs_le_thermal_abs
          (abs_nonneg x.1)) hK
    _ = K * |D.thermal * x.1| := by
      rw [abs_mul]


theorem thermalCone_iterate {D : TwoCoordinateRGData} {K : ℝ} (hK : 0 ≤ K)
    {x : ℝ × ℝ} (hx : D.thermalCone K x) (n : ℕ) :
    D.thermalCone K (D.iterate n x) := by
  induction n with
  | zero =>
      simpa [iterate] using hx
  | succ _ ih =>
      exact thermalCone_step hK ih


theorem exactScaleObservable_eq_power (D : TwoCoordinateRGData) (β : ℝ) :
    D.exactScaleObservable β =
      Real.exp (-D.certificate.predictedExponent *
        Real.log (D.model.betaC - β)) := by
  simp [exactScaleObservable, nu, model]



theorem bridge (D : TwoCoordinateRGData) :
    D.certificate.RGToExponentBridge D.exactScaleObservable := by
  refine D.certificate.rgToExponentBridge_of_exact_power_on_Ioo
    D.exactScaleObservable 1 (by norm_num) ?_
  intro β _hβ
  exact D.exactScaleObservable_eq_power β


theorem certificate_valid (D : TwoCoordinateRGData) :
    D.certificate.Valid D.exactScaleObservable := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact D.fixedPointData.fixedPoint_eq
  · exact D.certificate.linearizationEnclosure_of_thermal_gt_one
  · exact D.certificate.hyperbolicSplitting_of_thermal_gt_one
  · exact D.bridge



theorem hasCriticalNu_eq_predicted (D : TwoCoordinateRGData) :
    HasCriticalNu D.model D.exactScaleObservable D.certificate.predictedExponent :=
  D.certificate_valid.hasCriticalNu

end TwoCoordinateRGData

end Exact3D
end StatMech

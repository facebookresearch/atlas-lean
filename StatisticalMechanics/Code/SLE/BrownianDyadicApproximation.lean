/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianDyadicControl
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal









open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatMech.SLE



noncomputable def brownianDyadicApproxIndex (N n : Nat) (t : Real) : Nat :=
  Nat.floor ((t + N) * brownianDyadicDenominator n)


noncomputable def brownianDyadicApproxPoint (N n : Nat) (t : Real) : Real :=
  brownianDyadicPoint N n (brownianDyadicApproxIndex N n t)

@[simp]
theorem brownianDyadicDenominator_succ (n : Nat) :
    brownianDyadicDenominator (n + 1) =
      brownianDyadicDenominator n * 256 := by
  simp [brownianDyadicDenominator, pow_succ]

theorem brownianDyadicApproxIndex_le (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N) :
    brownianDyadicApproxIndex N n t <=
      2 * N * brownianDyadicDenominator n := by
  have hnonneg : 0 <= (t + N) * brownianDyadicDenominator n :=
    mul_nonneg (by linarith) (by positivity)
  have hfloor := Nat.floor_le hnonneg
  have hupper : (t + N) * brownianDyadicDenominator n <=
      ((2 * N * brownianDyadicDenominator n : Nat) : Real) := by
    push_cast
    have hdenom : (0 : Real) <= brownianDyadicDenominator n := by positivity
    nlinarith
  unfold brownianDyadicApproxIndex
  exact_mod_cast hfloor.trans hupper

theorem brownianDyadicApproxPoint_le (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) :
    brownianDyadicApproxPoint N n t <= t := by
  have hnonneg : 0 <= (t + N) * brownianDyadicDenominator n :=
    mul_nonneg (by linarith) (by positivity)
  have hfloor := Nat.floor_le hnonneg
  have hdenom : (0 : Real) < brownianDyadicDenominator n := by
    exact_mod_cast brownianDyadicDenominator_pos n
  unfold brownianDyadicApproxPoint brownianDyadicPoint
  dsimp only [brownianDyadicApproxIndex]
  push_cast at hfloor
  have hdiv := (div_le_iff₀ hdenom).2 hfloor
  nlinarith

theorem brownianDyadicApproxPoint_lt_add_mesh (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) :
    t < brownianDyadicApproxPoint N n t +
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
  have hnonneg : 0 <= (t + N) * brownianDyadicDenominator n :=
    mul_nonneg (by linarith) (by positivity)
  have hfloor := Nat.lt_floor_add_one ((t + N) * brownianDyadicDenominator n)
  have hdenom : (0 : Real) < brownianDyadicDenominator n := by
    exact_mod_cast brownianDyadicDenominator_pos n
  unfold brownianDyadicApproxPoint brownianDyadicPoint
  dsimp only [brownianDyadicApproxIndex]
  push_cast at hfloor
  rw [inv_eq_one_div]
  have hdiv := (lt_div_iff₀ hdenom).2 hfloor
  rw [add_div] at hdiv
  nlinarith


theorem dist_brownianDyadicApproxPoint_lt_mesh (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) :
    dist (brownianDyadicApproxPoint N n t) t <
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
  rw [Real.dist_eq, abs_of_nonpos
    (sub_nonpos.mpr (brownianDyadicApproxPoint_le N n htLower))]
  linarith [brownianDyadicApproxPoint_lt_add_mesh N n htLower]


theorem brownianDyadicApproxIndex_mono (N n : Nat) {s t : Real}
    (hst : s <= t) :
    brownianDyadicApproxIndex N n s <= brownianDyadicApproxIndex N n t := by
  unfold brownianDyadicApproxIndex
  apply Nat.floor_mono
  gcongr



theorem brownianDyadicApproxIndex_lt_add_two (N n : Nat) {s t : Real}
    (hsLower : -(N : Real) <= s) (hst : s <= t)
    (hclose : t - s < ((brownianDyadicDenominator n : Nat) : Real)⁻¹) :
    brownianDyadicApproxIndex N n t <
      brownianDyadicApproxIndex N n s + 2 := by
  let D : Real := brownianDyadicDenominator n
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast brownianDyadicDenominator_pos n
  have hsNonneg : 0 <= (s + N) * D :=
    mul_nonneg (by linarith) hD.le
  have htNonneg : 0 <= (t + N) * D :=
    mul_nonneg (by linarith) hD.le
  have hsFloor := Nat.lt_floor_add_one ((s + N) * D)
  unfold brownianDyadicApproxIndex
  change Nat.floor ((t + N) * D) < Nat.floor ((s + N) * D) + 2
  rw [Nat.floor_lt htNonneg]
  push_cast
  have hcloseMul : (t - s) * D < 1 := by
    rw [inv_eq_one_div] at hclose
    exact (lt_div_iff₀ hD).mp hclose
  nlinarith



theorem brownianDyadicApproxIndex_mul_le_succ (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) :
    brownianDyadicApproxIndex N n t * 256 <=
      brownianDyadicApproxIndex N (n + 1) t := by
  let x : Real := t + N
  have hx : 0 <= x := by dsimp [x]; linarith
  have hcoarseNonneg : 0 <= x * brownianDyadicDenominator n :=
    mul_nonneg hx (by positivity)
  have hfineNonneg : 0 <= x * brownianDyadicDenominator (n + 1) :=
    mul_nonneg hx (by positivity)
  have hcoarse := (Nat.floor_eq_iff hcoarseNonneg).1 rfl
  unfold brownianDyadicApproxIndex
  change Nat.floor (x * brownianDyadicDenominator n) * 256 <=
    Nat.floor (x * brownianDyadicDenominator (n + 1))
  rw [Nat.le_floor_iff hfineNonneg]
  push_cast
  rw [brownianDyadicDenominator_succ]
  push_cast
  nlinarith [hcoarse.1]



theorem brownianDyadicApproxIndex_succ_lt (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) :
    brownianDyadicApproxIndex N (n + 1) t <
      (brownianDyadicApproxIndex N n t + 1) * 256 := by
  let x : Real := t + N
  have hx : 0 <= x := by dsimp [x]; linarith
  have hcoarseNonneg : 0 <= x * brownianDyadicDenominator n :=
    mul_nonneg hx (by positivity)
  have hfineNonneg : 0 <= x * brownianDyadicDenominator (n + 1) :=
    mul_nonneg hx (by positivity)
  have hcoarse := (Nat.floor_eq_iff hcoarseNonneg).1 rfl
  unfold brownianDyadicApproxIndex
  change Nat.floor (x * brownianDyadicDenominator (n + 1)) <
    (Nat.floor (x * brownianDyadicDenominator n) + 1) * 256
  rw [Nat.floor_lt hfineNonneg]
  push_cast
  rw [brownianDyadicDenominator_succ]
  push_cast
  nlinarith [hcoarse.2]



theorem brownianDyadicPoint_succ_mul (N n k : Nat) :
    brownianDyadicPoint N (n + 1) (k * 256) =
      brownianDyadicPoint N n k := by
  have hdenom : Ne ((brownianDyadicDenominator n : Nat) : Real) 0 := by
    exact_mod_cast (brownianDyadicDenominator_pos n).ne'
  unfold brownianDyadicPoint
  rw [brownianDyadicDenominator_succ]
  push_cast
  field_simp



theorem edist_brownianCoordinateProcess_approxPoint_succ_le
    (omega : Real -> Real) (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hedge : ∀ k ∈ Finset.range
        (2 * N * brownianDyadicDenominator (n + 1)),
      edist
        (brownianCoordinateProcess (brownianDyadicPoint N (n + 1) k) omega)
        (brownianCoordinateProcess (brownianDyadicPoint N (n + 1) (k + 1)) omega) <
          brownianDyadicThreshold (n + 1)) :
    edist
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)
        (brownianCoordinateProcess (brownianDyadicApproxPoint N (n + 1) t) omega) <=
      (256 : ENNReal) * brownianDyadicThreshold (n + 1) := by
  let a : Nat := brownianDyadicApproxIndex N n t * 256
  let b : Nat := brownianDyadicApproxIndex N (n + 1) t
  have hab : a <= b := brownianDyadicApproxIndex_mul_le_succ N n htLower
  have hb : b <= 2 * N * brownianDyadicDenominator (n + 1) :=
    brownianDyadicApproxIndex_le N (n + 1) htLower htUpper
  have hbBlock : b < a + 256 := by
    dsimp only [a, b]
    have h := brownianDyadicApproxIndex_succ_lt N n htLower
    omega
  have hchain := edist_brownianCoordinateProcess_dyadicPoint_le
    omega N (n + 1) a b hedge hab hb
  have hdiff : b - a <= 256 := by omega
  change edist
      (brownianCoordinateProcess
        (brownianDyadicPoint N n (brownianDyadicApproxIndex N n t)) omega)
      (brownianCoordinateProcess
        (brownianDyadicPoint N (n + 1)
          (brownianDyadicApproxIndex N (n + 1) t)) omega) <= _
  rw [← brownianDyadicPoint_succ_mul N n]
  change edist
      (brownianCoordinateProcess (brownianDyadicPoint N (n + 1) a) omega)
      (brownianCoordinateProcess (brownianDyadicPoint N (n + 1) b) omega) <= _
  have hdiff' : ((b - a : Nat) : ENNReal) <= 256 := by
    exact_mod_cast hdiff
  exact hchain.trans (by
    simpa using mul_le_mul_left hdiff' (brownianDyadicThreshold (n + 1)))



theorem edist_brownianCoordinateProcess_approxPoint_le_of_le
    (omega : Real -> Real) (N n : Nat) {s t : Real}
    (hsLower : -(N : Real) <= s) (htUpper : t <= N)
    (hst : s <= t)
    (hclose : t - s < ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
    (hedge : ∀ k ∈ Finset.range
        (2 * N * brownianDyadicDenominator n),
      edist
        (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
        (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
          brownianDyadicThreshold n) :
    edist
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n s) omega)
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) <=
      brownianDyadicThreshold n := by
  let a := brownianDyadicApproxIndex N n s
  let b := brownianDyadicApproxIndex N n t
  have hab : a <= b := brownianDyadicApproxIndex_mono N n hst
  have hb : b <= 2 * N * brownianDyadicDenominator n :=
    brownianDyadicApproxIndex_le N n (hsLower.trans hst) htUpper
  have hgap : b < a + 2 :=
    brownianDyadicApproxIndex_lt_add_two N n hsLower hst hclose
  have hchain := edist_brownianCoordinateProcess_dyadicPoint_le
    omega N n a b hedge hab hb
  have hdiff : b - a <= 1 := by omega
  have hdiff' : ((b - a : Nat) : ENNReal) <= 1 := by exact_mod_cast hdiff
  exact hchain.trans (by
    simpa using mul_le_mul_left hdiff' (brownianDyadicThreshold n))



theorem edist_brownianCoordinateProcess_approxPoint_le
    (omega : Real -> Real) (N n : Nat) {s t : Real}
    (hsLower : -(N : Real) <= s) (hsUpper : s <= N)
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hclose : dist s t <
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
    (hedge : ∀ k ∈ Finset.range
        (2 * N * brownianDyadicDenominator n),
      edist
        (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
        (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
          brownianDyadicThreshold n) :
    edist
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n s) omega)
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) <=
      brownianDyadicThreshold n := by
  rcases le_total s t with hst | hts
  · refine edist_brownianCoordinateProcess_approxPoint_le_of_le
      omega N n hsLower htUpper hst ?_ hedge
    simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] using hclose
  · rw [edist_comm]
    refine edist_brownianCoordinateProcess_approxPoint_le_of_le
      omega N n htLower hsUpper hts ?_ hedge
    simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] using hclose



theorem cauchySeq_brownianCoordinateProcess_brownianDyadicApproxPoint
    (omega : Real -> Real) (N : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hgood : ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    CauchySeq (fun n =>
      brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) := by
  rw [Filter.eventually_atTop] at hgood
  obtain ⟨n0, hn0⟩ := hgood
  rw [← cauchySeq_shift n0]
  let d : Nat -> ENNReal := fun m =>
    (256 : ENNReal) * brownianDyadicThreshold (m + n0 + 1)
  apply cauchySeq_of_edist_le_of_tsum_ne_top d
  · intro m
    rw [show m.succ + n0 = (m + n0) + 1 by omega]
    change edist
        (brownianCoordinateProcess (brownianDyadicApproxPoint N (m + n0) t) omega)
        (brownianCoordinateProcess (brownianDyadicApproxPoint N (m + n0 + 1) t) omega) <=
      (256 : ENNReal) * brownianDyadicThreshold (m + n0 + 1)
    exact edist_brownianCoordinateProcess_approxPoint_succ_le
      omega N (m + n0) htLower htUpper (hn0 _ (by omega))
  · dsimp only [d, brownianDyadicThreshold]
    have hfun : (fun m : Nat =>
        (256 : ENNReal) * (2 : ENNReal)⁻¹ ^ (m + n0 + 1)) =
        fun m => ((256 : ENNReal) * (2 : ENNReal)⁻¹ ^ (n0 + 1)) *
          (2 : ENNReal)⁻¹ ^ m := by
      funext m
      rw [show m + n0 + 1 = m + (n0 + 1) by omega, pow_add]
      ac_rfl
    rw [hfun]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top <|
        ENNReal.pow_ne_top <| ENNReal.inv_ne_top.mpr <| by norm_num)
      (ENNReal.inv_ne_top.mpr <| ne_of_gt <|
        tsub_pos_iff_lt.mpr <| ENNReal.inv_lt_one.2 <| by norm_num)



noncomputable def brownianDyadicLimit (N : Nat) (t : Real)
    (omega : Real -> Real) : Real :=
  limUnder atTop (fun n =>
    brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)



theorem tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint
    (omega : Real -> Real) (N : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hgood : ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    Tendsto (fun n =>
      brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)
      atTop (nhds (brownianDyadicLimit N t omega)) := by
  exact (cauchySeq_brownianCoordinateProcess_brownianDyadicApproxPoint
    omega N htLower htUpper hgood).tendsto_limUnder



theorem edist_brownianCoordinateProcess_approxPoint_limit_le
    (omega : Real -> Real) (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hgoodFrom : ∀ m, n <= m ->
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m),
        edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) <
            brownianDyadicThreshold m) :
    edist
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)
        (brownianDyadicLimit N t omega) <=
      (256 : ENNReal) * brownianDyadicThreshold n := by
  have hgood : ∀ᶠ m in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m),
        edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) <
            brownianDyadicThreshold m := by
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hgoodFrom m hm
  let f : Nat -> Real := fun m =>
    brownianCoordinateProcess (brownianDyadicApproxPoint N m t) omega
  let g : Nat -> Real := fun m => f (m + n)
  let d : Nat -> ENNReal := fun m =>
    (256 : ENNReal) * brownianDyadicThreshold (m + n + 1)
  have hg : Tendsto g atTop (nhds (brownianDyadicLimit N t omega)) := by
    simpa only [g, f, Function.comp_def, Nat.add_comm] using
      (tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint
        omega N htLower htUpper hgood).comp (tendsto_add_atTop_nat n)
  have hstep (m : Nat) : edist (g m) (g m.succ) <= d m := by
    dsimp only [g, f, d]
    rw [show m.succ + n = (m + n) + 1 by omega]
    exact edist_brownianCoordinateProcess_approxPoint_succ_le
      omega N (m + n) htLower htUpper (hgoodFrom _ (by omega))
  have htsum : (∑' m : Nat, d m) =
      (256 : ENNReal) * brownianDyadicThreshold n := by
    dsimp only [d, brownianDyadicThreshold]
    have hfun : (fun m : Nat =>
        (256 : ENNReal) * (2 : ENNReal)⁻¹ ^ (m + n + 1)) =
        fun m => ((256 : ENNReal) * (2 : ENNReal)⁻¹ ^ (n + 1)) *
          (2 : ENNReal)⁻¹ ^ m := by
      funext m
      rw [show m + n + 1 = m + (n + 1) by omega, pow_add]
      ac_rfl
    rw [hfun, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, pow_succ]
    calc
      (256 : ENNReal) * ((2 : ENNReal)⁻¹ ^ n * (2 : ENNReal)⁻¹) * 2 =
          ((256 : ENNReal) * (2 : ENNReal)⁻¹ ^ n) *
            ((2 : ENNReal)⁻¹ * 2) := by ac_rfl
      _ = (256 : ENNReal) * (2 : ENNReal)⁻¹ ^ n := by
        rw [ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, mul_one]
  have hbound := edist_le_tsum_of_edist_le_of_tendsto₀ d hstep hg
  change edist (f n) (brownianDyadicLimit N t omega) <= _
  simpa [g, htsum] using hbound



theorem edist_brownianDyadicLimit_le
    (omega : Real -> Real) (N n : Nat) {s t : Real}
    (hsLower : -(N : Real) <= s) (hsUpper : s <= N)
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hclose : dist s t <
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
    (hgoodFrom : ∀ m, n <= m ->
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m),
        edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) <
            brownianDyadicThreshold m) :
    edist (brownianDyadicLimit N s omega) (brownianDyadicLimit N t omega) <=
      (513 : ENNReal) * brownianDyadicThreshold n := by
  let Bs := brownianCoordinateProcess (brownianDyadicApproxPoint N n s) omega
  let Bt := brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega
  have hsTail : edist Bs (brownianDyadicLimit N s omega) <=
      (256 : ENNReal) * brownianDyadicThreshold n :=
    edist_brownianCoordinateProcess_approxPoint_limit_le
      omega N n hsLower hsUpper hgoodFrom
  have htTail : edist Bt (brownianDyadicLimit N t omega) <=
      (256 : ENNReal) * brownianDyadicThreshold n :=
    edist_brownianCoordinateProcess_approxPoint_limit_le
      omega N n htLower htUpper hgoodFrom
  have hmiddle : edist Bs Bt <= brownianDyadicThreshold n :=
    edist_brownianCoordinateProcess_approxPoint_le omega N n
      hsLower hsUpper htLower htUpper hclose (hgoodFrom n le_rfl)
  calc
    edist (brownianDyadicLimit N s omega) (brownianDyadicLimit N t omega) <=
        edist (brownianDyadicLimit N s omega) Bs +
          edist Bs (brownianDyadicLimit N t omega) := edist_triangle _ _ _
    _ <= edist (brownianDyadicLimit N s omega) Bs +
        (edist Bs Bt + edist Bt (brownianDyadicLimit N t omega)) :=
      add_le_add_right (edist_triangle Bs Bt _) _
    _ <= ((256 : ENNReal) * brownianDyadicThreshold n) +
        (brownianDyadicThreshold n +
          ((256 : ENNReal) * brownianDyadicThreshold n)) := by
      apply add_le_add
      · simpa [edist_comm] using hsTail
      · exact add_le_add hmiddle htTail
    _ = (513 : ENNReal) * brownianDyadicThreshold n := by
      let x := brownianDyadicThreshold n
      change (256 : ENNReal) * x + (x + 256 * x) = 513 * x
      calc
        (256 : ENNReal) * x + (x + 256 * x) =
            256 * x + (1 * x + 256 * x) := by simp only [one_mul]
        _ = (256 + (1 + 256)) * x := by simp only [add_mul]
        _ = 513 * x := by norm_num



theorem continuousOn_brownianDyadicLimit
    (omega : Real -> Real) (N : Nat)
    (hgood : ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    ContinuousOn (fun t => brownianDyadicLimit N t omega)
      (Set.Icc (-(N : Real)) N) := by
  rw [Filter.eventually_atTop] at hgood
  obtain ⟨n0, hn0⟩ := hgood
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (K := Real) (x := eps / 513) (y := (1 / 2 : Real))
      (by positivity) (by norm_num)
  let n := k + n0
  have hn0n : n0 <= n := by dsimp only [n]; omega
  have hpowN : (1 / 2 : Real) ^ n0 <= 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hpowK : 0 <= (1 / 2 : Real) ^ k := by positivity
  have hpow : 513 * (1 / 2 : Real) ^ n < eps := by
    have hk' : 513 * (1 / 2 : Real) ^ k < eps := by nlinarith
    have hprod : (1 / 2 : Real) ^ k * (1 / 2 : Real) ^ n0 <=
        (1 / 2 : Real) ^ k :=
      mul_le_of_le_one_right hpowK hpowN
    dsimp only [n]
    rw [pow_add]
    nlinarith
  let delta : Real := ((brownianDyadicDenominator n : Nat) : Real)⁻¹
  have hdelta : 0 < delta := by
    dsimp only [delta]
    apply inv_pos.mpr
    exact_mod_cast brownianDyadicDenominator_pos n
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hst
  have hed := edist_brownianDyadicLimit_le omega N n
    hs.1 hs.2 ht.1 ht.2 hst
    (fun m hm => hn0 m (hn0n.trans hm))
  rw [dist_edist]
  have hfinite : (513 : ENNReal) * brownianDyadicThreshold n ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    unfold brownianDyadicThreshold
    exact ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (by norm_num))
  calc
    (edist (brownianDyadicLimit N s omega)
      (brownianDyadicLimit N t omega)).toReal <=
        ((513 : ENNReal) * brownianDyadicThreshold n).toReal :=
      (ENNReal.toReal_le_toReal (edist_ne_top _ _) hfinite).2 hed
    _ = 513 * (1 / 2 : Real) ^ n := by
      simp [brownianDyadicThreshold, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_inv]
    _ < eps := hpow

end StatMech.SLE

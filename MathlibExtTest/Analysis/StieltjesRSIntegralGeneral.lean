/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegralGeneral
import Mathlib.Tactic

/-!
# Tests for the Duhamel operator `Ψ A B` on `ℓ^∞`

1. **A computed `Ψ` with its norm bound.** For `A = B = 0` every Duhamel sum telescopes, so
   `Ψ h t = h t - h 0` for every `h ∈ ℓ^∞([0, 1])`, computed from the sums. For `h = id` this gives
   `Ψ h = h`, `‖Ψ h‖ = ‖h‖ = 1`, and the bound `‖Ψ h‖ ≤ 6 exp 0 exp 0 ‖h‖ = 6` is exhibited.
   For `A = 0` and `B` with a jump of `1` at `1/2`, the Duhamel sums of the step `h = B` are
   computed from the definitions (the kernel `P(B)(x, 1]` from `productIntegral_step`), giving
   `Ψ A B h 1 = 1 = P(B)(0, 1] - P(A)(0, 1]`.
2. **An `h ∈ ℓ^∞` with no integral.** For the same `A`, `B` and the indicator `h` of the rationals,
   the Duhamel integral on `[0, 1]` does not exist: the sums are `h(prev c) + const`, and refining
   puts a rational or an irrational point just below the jump `c = 1/2`. So
   `psi_apply_eq_of_hasDuhamelIntegral` does not apply and no value of `Ψ A B h 1` is claimed;
   only the norm bound, which holds for every `h`, is stated.
3. **A non-`ℓ^∞` input.** `h x = x⁻¹` (`h 0 = 0`) is unbounded on `[0, 1]`, so it is not an element
   of `ℓ^∞([0, 1])` and `Ψ` cannot be applied to it, although its Duhamel integral for
   `A = B = 0` exists (it is `h 1 - h 0 = 1`). The continuous linear map is not claimed there.
-/

namespace MetaMathlibExt.StieltjesRSIntegralGeneralTest

open Filter Topology Finset MathlibExt.Analysis.StieltjesProductIntegral
  MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
  MathlibExt.Analysis.StieltjesRSIntegralGeneral

open scoped ENNReal

local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

/-! ### Shared facts -/

theorem eVariationOn_zero (τ : ℝ) : eVariationOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 τ) = 0 :=
  eVariationOn.constant_on (Set.subsingleton_of_forall_eq 0 fun _ ⟨_, _, hx⟩ => hx.symm)

theorem bv_zero (τ : ℝ) : BoundedVariationOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc 0 τ) := by
  change eVariationOn _ _ ≠ ⊤
  rw [eVariationOn_zero]
  exact ENNReal.zero_ne_top

/-- With `A = B = 0` both kernel factors are `1` and every Duhamel sum telescopes. -/
theorem twoTagSum_zero_zero (h : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (s : Finset ℝ) :
    twoTagSum (productIntegral (fun _ => (0 : ℝ)) 0)
      (fun x => productIntegral (fun _ => (0 : ℝ)) x t) h (partitionPts 0 t s) = h t - h 0 := by
  simp only [twoTagSum, productIntegral_const, one_mul, mul_one]
  exact sum_increments_partitionPts ht h s

/-! ### 1. `A = B = 0`: `Ψ h t = h t - h 0`, and the norm bound -/

/-- `Ψ 0 0 h t = h t - h 0` for every `h ∈ ℓ^∞([0, 1])`, from the telescoped sums. -/
theorem psi_zero_zero (h : 𝔻[1]) (t : Set.Icc (0 : ℝ) 1) :
    psi 1 (fun _ => 0) (fun _ => 0) h t = h t - h ⟨0, by norm_num⟩ := by
  refine psi_apply_eq_of_hasDuhamelIntegral (bv_zero 1) (bv_zero 1) h t ?_
  refine tendsto_const_nhds.congr fun s => ?_
  rw [twoTagSum_zero_zero _ t.2.1, extendIcc_coe,
    extendIcc_of_mem h (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]

/-- The identity on `[0, 1]` as an element of `ℓ^∞([0, 1])`. -/
noncomputable def idD : 𝔻[1] :=
  ⟨fun t => (t : ℝ), memℓp_infty ⟨1, by
    rintro _ ⟨t, rfl⟩
    change ‖(t : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg t.2.1]
    exact t.2.2⟩⟩

theorem psi_zero_zero_idD : psi 1 (fun _ => 0) (fun _ => 0) idD = idD :=
  lp.ext <| funext fun t => by
    rw [psi_zero_zero]
    exact sub_zero _

theorem norm_idD : ‖idD‖ = 1 := by
  refine le_antisymm (lp.norm_le_of_forall_le zero_le_one fun t => ?_) ?_
  · change ‖(t : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg t.2.1]
    exact t.2.2
  · have := lp.norm_apply_le_norm ENNReal.top_ne_zero idD ⟨1, by norm_num⟩
    change ‖(1 : ℝ)‖ ≤ ‖idD‖ at this
    simpa using this

/-- The norm bound `‖Ψ h‖ ≤ 6 exp (V(A)) exp (V(B)) ‖h‖` for `A = B = 0`, `h = id`: here
`‖Ψ h‖ = 1` and the bound is `6`. -/
example : ‖psi 1 (fun _ => 0) (fun _ => 0) idD‖ = 1 ∧
    psiConst 1 (fun _ => 0) (fun _ => 0) * ‖idD‖ = 6 ∧
    ‖psi 1 (fun _ => 0) (fun _ => 0) idD‖ ≤ psiConst 1 (fun _ => 0) (fun _ => 0) * ‖idD‖ := by
  have hc : psiConst 1 (fun _ => 0) (fun _ => 0) = 6 := by
    rw [psiConst, eVariationOn_zero, ENNReal.toReal_zero, Real.exp_zero, mul_one, mul_one]
  refine ⟨by rw [psi_zero_zero_idD, norm_idD], by rw [hc, norm_idD, mul_one],
    norm_psi_apply_le (bv_zero 1) (bv_zero 1) idD⟩

/-! ### A kernel with a jump -/

/-- `B` jumps by `1` at `1/2`. -/
noncomputable def jumpB : ℝ → ℝ := fun x => if (1 / 2 : ℝ) ≤ x then 1 else 0

/-- The indicator of `(-∞, 1/2)`. -/
noncomputable def below : ℝ → ℝ := fun x => if x < 1 / 2 then 1 else 0

theorem bv_jumpB : BoundedVariationOn jumpB (Set.Icc 0 1) := by
  refine MonotoneOn.boundedVariationOn (C := 1) (fun x _ y _ hxy => ?_) fun x _ => ?_
  · simp only [jumpB]
    split_ifs <;> linarith
  · simp only [jumpB]
    split_ifs <;> norm_num

/-- The right kernel factor `P(B)(x, 1] = 1 + 1_{x < 1/2}` on `[0, 1]`, from
`productIntegral_step` and `productIntegral_const`. -/
theorem productIntegral_jumpB {x : ℝ} (hx1 : x ≤ 1) :
    productIntegral jumpB x 1 = 1 + below x := by
  by_cases hx : x < 1 / 2
  · rw [show below x = 1 from ite_eq_left hx]
    change productIntegral (fun t => if (1 / 2 : ℝ) ≤ t then (1 : ℝ) else 0) x 1 = 1 + 1
    rw [productIntegral_step hx (by norm_num)]
    norm_num
  · have e := productIntegral_congr (A := jumpB) (B := fun _ => (1 : ℝ)) hx1 fun y hy => by
      change (if (1 / 2 : ℝ) ≤ y then (1 : ℝ) else 0) = 1
      exact ite_eq_left ((not_lt.1 hx).trans hy.1)
    rw [show below x = 0 from ite_eq_right hx, e, productIntegral_const, add_zero]

/-- **The Duhamel sums for `A = 0` and the jump `B`, computed from the definitions**: on every
partition of `[0, 1]` the sum of `e` is `(e 1 - e 0) + (e u - e 0)`, where `u` is the partition
point just below the jump `1/2`. -/
theorem twoTagSum_jump (e : ℝ → ℝ) (s : Finset ℝ) :
    twoTagSum (productIntegral (fun _ => (0 : ℝ)) 0) (fun x => productIntegral jumpB x 1) e
      (partitionPts 0 1 s) =
      (e 1 - e 0) + (e (prev (partitionPts 0 1 s) (1 / 2)) - e 0) := by
  have h1 : twoTagSum (productIntegral (fun _ => (0 : ℝ)) 0) (fun x => productIntegral jumpB x 1)
      e (partitionPts 0 1 s) = ∑ x ∈ partitionPts 0 1 s, (e x - e (prev (partitionPts 0 1 s) x)) +
        rightSum below e (partitionPts 0 1 s) := by
    rw [twoTagSum, rightSum, ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    rw [productIntegral_const, productIntegral_jumpB (mem_Icc_of_mem_partitionPts zero_le_one hx).2]
    ring
  have h2 := sum_increments_partitionPts zero_le_one e s
  have h3 := leftPartitionSum_add_rightSum zero_le_one e below s
  have hsplit : below = (fun _ => (1 : ℝ)) - fun x => if (1 / 2 : ℝ) ≤ x then 1 else 0 := by
    funext x
    simp only [below, Pi.sub_apply]
    split_ifs <;> linarith
  have hstep := leftPartitionSum_ite_le e (a := 0) (b := 1) (c := 1 / 2) (by norm_num)
    (by norm_num) s
  have hone : leftSum e (fun _ => (1 : ℝ)) (partitionPts 0 1 s) = 0 := by simp [leftSum]
  rw [leftPartitionSum] at hstep
  have h4 : leftPartitionSum e below 0 1 s = -e (prev (partitionPts 0 1 s) (1 / 2)) := by
    rw [hsplit, leftPartitionSum, leftSum_sub_right, hone, hstep, zero_sub]
  have hb1 : below 1 = 0 := ite_eq_right (by norm_num)
  have hb0 : below 0 = 1 := ite_eq_left (by norm_num)
  rw [hb1, hb0, h4] at h3
  rw [h1, h2]
  linarith

/-- The step `B` itself as an element of `ℓ^∞([0, 1])`. -/
noncomputable def jumpD : 𝔻[1] :=
  ⟨fun t => jumpB t, memℓp_infty ⟨1, by
    rintro _ ⟨t, rfl⟩
    change ‖jumpB t‖ ≤ 1
    simp only [jumpB]
    split_ifs <;> norm_num⟩⟩

/-- **`Ψ A B` on the jump, from the sums**: for `A = 0` and `h = B`, `Ψ A B h 1 = 1`, and this is
`P(B)(0, 1] - P(A)(0, 1] = 2 - 1`, each side computed independently of the Duhamel theorem. -/
example : psi 1 (fun _ => 0) jumpB jumpD ⟨1, by norm_num⟩ = 1 ∧
    productIntegral jumpB 0 1 - productIntegral (fun _ => (0 : ℝ)) 0 1 = 1 := by
  refine ⟨psi_apply_eq_of_hasDuhamelIntegral (bv_zero 1) bv_jumpB jumpD _ ?_, ?_⟩
  · refine tendsto_const_nhds.congr fun s => ?_
    rw [twoTagSum_partitionPts_congr zero_le_one (g := jumpB)
      (fun x hx => extendIcc_of_mem jumpD hx) s, twoTagSum_jump]
    have hlt : prev (partitionPts 0 1 s) (1 / 2) < 1 / 2 :=
      (prev_spec ⟨0, left_mem_partitionPts s, by norm_num⟩).2.1
    simp only [jumpB, ite_eq_right (not_le.2 hlt)]
    norm_num
  · rw [productIntegral_jumpB (by norm_num : (0 : ℝ) ≤ 1), productIntegral_const,
      show below 0 = 1 from ite_eq_left (by norm_num)]
    norm_num

/-! ### 2. A bounded `h` whose Duhamel integral does not exist -/

open Classical in
/-- The indicator of the rationals. -/
noncomputable def ratInd (x : ℝ) : ℝ := if x ∈ Set.range ((↑) : ℚ → ℝ) then 1 else 0

/-- The indicator of the rationals on `[0, 1]`, an element of `ℓ^∞([0, 1])`. -/
noncomputable def ratD : 𝔻[1] :=
  ⟨fun t => ratInd t, memℓp_infty ⟨1, by
    rintro _ ⟨t, rfl⟩
    change ‖ratInd t‖ ≤ 1
    simp only [ratInd]
    split_ifs <;> norm_num⟩⟩

/-- Inserting a point `q` between the partition point below `1/2` and `1/2` makes `q` the new
partition point below `1/2`. -/
theorem prev_refine (s₀ : Finset ℝ) {q : ℝ}
    (hq : prev (partitionPts 0 1 (insert (1 / 2) s₀)) (1 / 2) < q) (hqc : q < 1 / 2) :
    prev (partitionPts 0 1 (insert q (insert (1 / 2) s₀))) (1 / 2) = q := by
  obtain ⟨hmP, -, hmax⟩ := prev_spec (P := partitionPts 0 1 (insert (1 / 2) s₀)) (x := 1 / 2)
    ⟨0, left_mem_partitionPts _, by norm_num⟩
  have hm0 := (mem_Icc_of_mem_partitionPts zero_le_one hmP).1
  refine prev_eq_of (mem_partitionPts.2 (Or.inr (Or.inr ⟨mem_insert_self _ _, by linarith,
    by linarith⟩))) hqc fun z hz hzc => ?_
  rcases mem_partitionPts.1 hz with rfl | rfl | ⟨hzs, hz0, hz1⟩
  · linarith
  · norm_num at hzc
  · rcases mem_insert.1 hzs with rfl | hzs'
    · exact le_rfl
    · exact (hmax z (mem_partitionPts.2 (Or.inr (Or.inr ⟨hzs', hz0, hz1⟩))) hzc).trans hq.le

/-- **No Duhamel integral for the indicator of the rationals.** With `A = 0` and the jump `B`, the
Duhamel sums of `ratD` on `[0, 1]` are `const + ratInd u` with `u` the partition point below `1/2`;
every partition has a refinement with `u` rational and one with `u` irrational, so the sums do not
converge. Hence `psi_apply_eq_of_hasDuhamelIntegral` does not apply to `Ψ A B ratD 1`. -/
theorem not_hasDuhamelIntegral_ratD :
    ¬ ∃ I, HasDuhamelIntegral (fun _ => (0 : ℝ)) jumpB (extendIcc ratD) 0 1 I := by
  rintro ⟨I, hI⟩
  unfold HasDuhamelIntegral HasTwoTagRSIntegral at hI
  have hu : Tendsto (fun s => ratInd (prev (partitionPts 0 1 s) (1 / 2))) atTop
      (𝓝 (I - (ratInd 1 - ratInd 0) + ratInd 0)) := by
    refine ((hI.sub_const (ratInd 1 - ratInd 0)).add_const (ratInd 0)).congr fun s => ?_
    rw [twoTagSum_partitionPts_congr zero_le_one (g := ratInd)
      (fun x hx => extendIcc_of_mem ratD hx) s, twoTagSum_jump]
    ring
  obtain ⟨s₀, hs₀⟩ := Metric.tendsto_atTop.1 hu (1 / 2) (by norm_num)
  have hmc : prev (partitionPts 0 1 (insert (1 / 2) s₀)) (1 / 2) < 1 / 2 :=
    (prev_spec ⟨0, left_mem_partitionPts _, by norm_num⟩).2.1
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hmc
  obtain ⟨r, hr, hr1, hr2⟩ := exists_irrational_btwn hmc
  have hsub : ∀ p : ℝ, s₀ ≤ insert p (insert (1 / 2) s₀) := fun p =>
    (subset_insert _ _).trans (subset_insert _ _)
  have e1 := hs₀ _ (hsub q)
  have e2 := hs₀ _ (hsub r)
  beta_reduce at e1 e2
  rw [prev_refine s₀ hq1 hq2, show ratInd (q : ℝ) = 1 from ite_eq_left ⟨q, rfl⟩, Real.dist_eq,
    abs_lt] at e1
  rw [prev_refine s₀ hr1 hr2, show ratInd r = 0 from ite_eq_right hr, Real.dist_eq, abs_lt] at e2
  linarith [e1.1, e2.2]

/-- The same statement at the point `t = 1` of `[0, 1]`, in the form taken by
`psi_apply_eq_of_hasDuhamelIntegral`. -/
example : ¬ ∃ I, HasDuhamelIntegral (fun _ => (0 : ℝ)) jumpB (extendIcc ratD) 0
    ((⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ) I :=
  not_hasDuhamelIntegral_ratD

/-- What is claimed about `Ψ A B ratD`: only the bound, which holds for every `h ∈ ℓ^∞`. -/
example : ‖psi 1 (fun _ => 0) jumpB ratD‖ ≤ psiConst 1 (fun _ => 0) jumpB * ‖ratD‖ :=
  norm_psi_apply_le (bv_zero 1) bv_jumpB ratD

/-! ### 3. A non-`ℓ^∞` input -/

/-- The Duhamel integral of `x ↦ x⁻¹` for `A = B = 0` exists on `[0, 1]` and equals `1`. -/
theorem hasDuhamelIntegral_inv :
    HasDuhamelIntegral (fun _ => (0 : ℝ)) (fun _ => 0) (fun x => x⁻¹) 0 1 1 := by
  refine tendsto_const_nhds.congr fun s => ?_
  rw [twoTagSum_zero_zero _ zero_le_one]
  norm_num

/-- `x ↦ x⁻¹` is not bounded on `[0, 1]`: no element of `ℓ^∞([0, 1])` agrees with it, so `Ψ` (a
map on `ℓ^∞`) is not applied to it and the bound is not claimed for it. -/
theorem not_exists_lp_inv : ¬ ∃ g : 𝔻[1], ∀ t : Set.Icc (0 : ℝ) 1, g t = (t : ℝ)⁻¹ := by
  rintro ⟨g, hg⟩
  have hR := norm_nonneg g
  have ht : (‖g‖ + 2)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, inv_le_one_of_one_le₀ (by linarith)⟩
  have h := lp.norm_apply_le_norm ENNReal.top_ne_zero g ⟨_, ht⟩
  rw [hg] at h
  change ‖(‖g‖ + 2)⁻¹⁻¹‖ ≤ ‖g‖ at h
  rw [inv_inv, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  linarith

/-! ### The interface -/

example : IsPsiCLM 1 (psi 1) := isPsiCLM_psi 1

/-- With `G = 1` the two-tag integral is the left-endpoint integral. -/
example (F h : ℝ → ℝ) (I : ℝ) :
    HasTwoTagRSIntegral F (fun _ => 1) h 0 1 I ↔ HasLeftRSIntegral F h 0 1 I :=
  hasTwoTagRSIntegral_one_iff

end MetaMathlibExt.StieltjesRSIntegralGeneralTest

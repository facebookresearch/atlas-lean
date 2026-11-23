/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.WoldDecomposition
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the Wold decomposition

Two examples are checked:

* the identity isometry on `ℂ`: wandering subspace `⊥`, residual subspace `⊤`;
* the unilateral shift `S` on `ℓ²(ℕ, ℂ)`: `S` is an isometry, its powers
  shift coordinates (`shiftIsometry_pow_apply`), `S` sends the `n`-th basis
  vector to the `(n+1)`-st (`shiftIsometry_single`), the wandering subspace
  is the span of `e₀` (`wanderingSub_shiftIsometry`), the residual subspace
  is trivial (`residualSub_shiftIsometry`), and the explicit Wold
  decomposition of `e₀ + 2 • e₁` at level `2` has squared norm `5`
  (`wold_norm_sq_shift_example`).
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.WoldDecompositionTests

open scoped _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.WoldDecomposition

/-- The identity isometry has trivial wandering subspace. -/
theorem wanderingSub_one : wanderingSub (1 : ℂ →ₗᵢ[ℂ] ℂ) = ⊥ := by
  have h : LinearMap.range ((1 : ℂ →ₗᵢ[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) = ⊤ :=
    LinearMap.range_eq_top.mpr fun y => ⟨y, by simp⟩
  show (LinearMap.range ((1 : ℂ →ₗᵢ[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ))ᗮ = ⊥
  rw [h, Submodule.top_orthogonal_eq_bot]

/-- The identity isometry has full residual subspace. -/
theorem residualSub_one : residualSub (1 : ℂ →ₗᵢ[ℂ] ℂ) = ⊤ := by
  show (⨅ _n, LinearMap.range (((1 : ℂ →ₗᵢ[ℂ] ℂ) ^ _n : ℂ →ₗᵢ[ℂ] ℂ) :
      ℂ →ₗ[ℂ] ℂ)) = ⊤
  simp only [one_pow]
  have h : LinearMap.range ((1 : ℂ →ₗᵢ[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) = ⊤ :=
    LinearMap.range_eq_top.mpr fun y => ⟨y, by simp⟩
  simp [h]

/-- The residual unitary of the identity isometry acts as the identity. -/
theorem woldResidualEquiv_one_apply :
    ((woldResidualEquiv (1 : ℂ →ₗᵢ[ℂ] ℂ) ⟨(2 : ℂ),
      by rw [residualSub_one]; trivial⟩ : residualSub (1 : ℂ →ₗᵢ[ℂ] ℂ)) : ℂ) =
      2 := by
  rw [woldResidualEquiv_apply_coe]
  simp

/-- The right shift on sequences: `(0, x₀, x₁, …)`. -/
noncomputable def shiftFun (x : PreLp (fun _ : ℕ => ℂ)) : PreLp (fun _ : ℕ => ℂ) :=
  fun n => if n = 0 then 0 else x (n - 1)

/-- The shift of a sequence is zero at coordinate `0`. -/
theorem shiftFun_zero (x : PreLp (fun _ : ℕ => ℂ)) : shiftFun x 0 = 0 := by
  simp [shiftFun]

/-- The shift of a sequence at coordinate `n + 1` is the original at `n`. -/
theorem shiftFun_succ (x : PreLp (fun _ : ℕ => ℂ)) (n : ℕ) : shiftFun x (n + 1) = x n := by
  simp [shiftFun]

/-- The shift of a sequence at a positive coordinate `k` is the original at `k - 1`. -/
theorem shiftFun_sub_one (x : PreLp (fun _ : ℕ => ℂ)) {k : ℕ} (hk : 1 ≤ k) :
    shiftFun x k = x (k - 1) := by
  simp only [shiftFun, show k ≠ 0 by omega, ite_false]

/-- Applying a scalar multiple of a sequence coordinatewise. -/
theorem preLp_smul_apply {c : ℂ} {f : PreLp (fun _ : ℕ => ℂ)} {i : ℕ} :
    (c • f) i = c • f i := rfl

/-- The shift of an `ℓ²` sequence is again in `ℓ²`. -/
theorem shiftFun_memℓp (x : lp (fun _ : ℕ => ℂ) 2) : Memℓp (shiftFun x.val) 2 := by
  apply memℓp_gen
  have hsumm : Summable (fun i => ‖x.val i‖ ^ (2 : ENNReal).toReal) :=
    x.property.summable (by simp)
  have hshift : Summable (fun i => ‖shiftFun x.val (i + 1)‖ ^ (2 : ENNReal).toReal) := by
    simpa only [shiftFun_succ] using hsumm
  exact (summable_nat_add_iff 1).mp hshift

/-- The unilateral shift as a bounded linear map on `ℓ²(ℕ, ℂ)`. -/
noncomputable def shiftCLM : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toFun x := ⟨shiftFun x.val, shiftFun_memℓp x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    show shiftFun (x + y).val n = (shiftFun x.val + shiftFun y.val) n
    rw [PreLp.add_apply]
    by_cases hn : n = 0
    · subst hn
      rw [shiftFun_zero, shiftFun_zero, shiftFun_zero, add_zero]
    · rw [shiftFun_sub_one _ (by omega : 1 ≤ n), shiftFun_sub_one _ (by omega : 1 ≤ n),
        shiftFun_sub_one _ (by omega : 1 ≤ n)]
      rfl
  map_smul' c x := by
    apply lp.ext
    funext n
    show shiftFun (c • x).val n = (c • shiftFun x.val) n
    by_cases hn : n = 0
    · subst hn
      show (0 : ℂ) = c • (shiftFun x.val 0)
      rw [shiftFun_zero, smul_zero]
    · rw [shiftFun_sub_one _ (by omega : 1 ≤ n)]
      show (c • x.val) (n - 1) = c • (shiftFun x.val n)
      rw [preLp_smul_apply, shiftFun_sub_one _ (by omega : 1 ≤ n)]

/-- Applying the shift: `(S x) n = shiftFun x n`. -/
theorem shiftCLM_apply (x : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (shiftCLM x).val n = shiftFun x.val n := rfl

/-- The shift preserves inner products. -/
theorem inner_shiftCLM (x y : lp (fun _ : ℕ => ℂ) 2) :
    ⟪shiftCLM x, shiftCLM y⟫_ℂ = ⟪x, y⟫_ℂ := by
  have h1 : HasSum (fun n => ⟪(shiftCLM x).val (n + 1), (shiftCLM y).val (n + 1)⟫_ℂ)
      ⟪x, y⟫_ℂ := by
    simpa only [shiftCLM_apply, shiftFun_succ] using lp.hasSum_inner x y
  have h0 : (fun n => ⟪(shiftCLM x).val n, (shiftCLM y).val n⟫_ℂ) 0 = 0 := by
    simp only [shiftCLM_apply, shiftFun_zero, inner_zero_left]
  have h2 : HasSum (fun n => ⟪(shiftCLM x).val n, (shiftCLM y).val n⟫_ℂ)
      ⟪x, y⟫_ℂ := by
    have h := (hasSum_nat_add_iff 1 (f := fun n => ⟪(shiftCLM x).val n,
      (shiftCLM y).val n⟫_ℂ)).mp h1
    simp only [Finset.sum_range_one, h0, add_zero] at h
    exact h
  exact (lp.hasSum_inner (shiftCLM x) (shiftCLM y)).unique h2

/-- The unilateral shift as a linear isometry on `ℓ²(ℕ, ℂ)`. -/
noncomputable def shiftIsometry : lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  LinearMap.isometryOfInner shiftCLM inner_shiftCLM

/-- Applying the shift isometry: `(S x) n = shiftFun x n`. -/
theorem shiftIsometry_apply (x : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (shiftIsometry x).val n = shiftFun x.val n := rfl

/-- Powers of the shift move coordinates: `(S ^ n x) k = 0` for `k < n` and
`(S ^ n x) k = x (k - n)` otherwise. -/
theorem shiftIsometry_pow_apply (n k : ℕ) (x : lp (fun _ : ℕ => ℂ) 2) :
    ((shiftIsometry ^ n) x).val k = if k < n then 0 else x.val (k - n) := by
  induction n generalizing x k with
  | zero => simp
  | succ n ih =>
    have hpow : (shiftIsometry ^ (n + 1)) x =
        shiftIsometry ((shiftIsometry ^ n) x) := by
      rw [pow_succ', LinearIsometry.coe_mul, Function.comp_apply]
    rw [hpow, shiftIsometry_apply]
    by_cases hk0 : k = 0
    · subst hk0
      rw [shiftFun_zero]
      simp
    · rw [shiftFun_sub_one _ (by omega : 1 ≤ k), ih]
      by_cases hkn' : k - 1 < n
      · have hkn : k < n + 1 := by omega
        simp only [hkn', hkn, ite_true]
      · have hkn : ¬ k < n + 1 := by omega
        have h2 : k - 1 - n = k - (n + 1) := by omega
        simp only [hkn', hkn, ite_false]
        rw [h2]

/-- The shift sends the `n`-th basis vector to the `(n+1)`-st. -/
theorem shiftIsometry_single (n : ℕ) :
    shiftIsometry (lp.single 2 n (1 : ℂ)) = lp.single 2 (n + 1) (1 : ℂ) := by
  apply lp.ext
  funext k
  show (shiftIsometry (lp.single 2 n (1 : ℂ))).val k =
    ((lp.single 2 (n + 1) (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)).val k
  rw [shiftIsometry_apply]
  by_cases hk : k = n + 1
  · subst hk
    rw [shiftFun_succ]
    show Pi.single (M := fun _ : ℕ => ℂ) n (1 : ℂ) n =
      Pi.single (M := fun _ : ℕ => ℂ) (n + 1) (1 : ℂ) (n + 1)
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · by_cases hk0 : k = 0
    · subst hk0
      rw [shiftFun_zero]
      show (0 : ℂ) = Pi.single (M := fun _ : ℕ => ℂ) (n + 1) (1 : ℂ) 0
      rw [Pi.single_eq_of_ne (show (0 : ℕ) ≠ n + 1 by omega)]
    · rw [shiftFun_sub_one _ (by omega : 1 ≤ k)]
      show Pi.single (M := fun _ : ℕ => ℂ) n (1 : ℂ) (k - 1) =
        Pi.single (M := fun _ : ℕ => ℂ) (n + 1) (1 : ℂ) k
      rw [Pi.single_eq_of_ne (show k - 1 ≠ n by omega), Pi.single_eq_of_ne hk]

/-- The `n`-th basis vector has unit norm in `ℓ²(ℕ, ℂ)`. -/
theorem norm_single_lp (n : ℕ) :
    ‖(lp.single 2 n (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)‖ = 1 := by
  rw [lp.norm_single (show (0 : ENNReal) < 2 by norm_num)]
  simp

/-- The wandering subspace of the shift is the span of `e₀`. -/
theorem wanderingSub_shiftIsometry :
    wanderingSub shiftIsometry =
      Submodule.span ℂ ({lp.single 2 0 (1 : ℂ)} : Set (lp (fun _ : ℕ => ℂ) 2)) := by
  apply le_antisymm
  · intro a ha
    rw [Submodule.mem_span_singleton]
    refine ⟨a.val 0, ?_⟩
    apply lp.ext
    funext k
    show (a.val 0) • ((lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)).val k = a.val k
    by_cases hk0 : k = 0
    · subst hk0
      show (a.val 0) • Pi.single (M := fun _ : ℕ => ℂ) 0 (1 : ℂ) 0 = a.val 0
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · have hak : a.val k = 0 := by
        have hmem : (shiftIsometry (lp.single 2 (k - 1) (1 : ℂ))) ∈
            LinearMap.range (shiftIsometry : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
              lp (fun _ : ℕ => ℂ) 2) := ⟨_, rfl⟩
        have h0 := (Submodule.mem_orthogonal _ _).mp ha _ hmem
        have hS : shiftIsometry (lp.single 2 (k - 1) (1 : ℂ)) =
            lp.single 2 k (1 : ℂ) := by
          have hkk : k - 1 + 1 = k := by omega
          rw [← hkk]
          exact shiftIsometry_single (k - 1)
        rw [hS, lp.inner_single_left] at h0
        have h0' : ⟪(1 : ℂ), a.val k⟫_ℂ = 0 := h0
        simpa using h0'
      show (a.val 0) • Pi.single (M := fun _ : ℕ => ℂ) 0 (1 : ℂ) k = a.val k
      rw [Pi.single_eq_of_ne hk0, smul_zero, hak]
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show lp.single 2 0 (1 : ℂ) ∈
      (LinearMap.range (shiftIsometry : lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ]
        lp (fun _ : ℕ => ℂ) 2))ᗮ
    rw [Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨w, hw⟩ := hz
    rw [← hw, lp.inner_single_right]
    show ⟪shiftFun w.val 0, (1 : ℂ)⟫_ℂ = 0
    rw [shiftFun_zero]
    exact inner_zero_left _

/-- The first basis vector is a wandering vector for the shift. -/
theorem single_zero_mem_wandering :
    lp.single 2 0 (1 : ℂ) ∈ wanderingSub shiftIsometry := by
  rw [wanderingSub_shiftIsometry]
  exact Submodule.mem_span_singleton_self _

/-- The wandering vector `e₀` is orthogonal to `S e₀ = e₁`. -/
theorem inner_wandering_shift_example :
    ⟪(shiftIsometry ^ 0) (lp.single 2 0 (1 : ℂ)),
      (shiftIsometry ^ 1) (lp.single 2 0 (1 : ℂ))⟫_ℂ = 0 :=
  inner_pow_wandering shiftIsometry (by norm_num : (0 : ℕ) < 1) _
    single_zero_mem_wandering _

/-- The residual subspace of the shift is trivial. -/
theorem residualSub_shiftIsometry : residualSub shiftIsometry = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hzero : ∀ k, x.val k = 0 := by
    intro k
    have hxk : x ∈ LinearMap.range ((shiftIsometry ^ (k + 1) :
        lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
        lp (fun _ : ℕ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2) :=
      (Submodule.mem_iInf _).mp hx (k + 1)
    obtain ⟨z, hz⟩ := hxk
    have hz' : (shiftIsometry ^ (k + 1)) z = x := hz
    have h2 : ((shiftIsometry ^ (k + 1)) z).val k = 0 := by
      rw [shiftIsometry_pow_apply]
      simp
    rw [← hz']
    exact h2
  apply lp.ext
  funext k
  show x.val k = 0
  exact hzero k

/-- The vector `e₀ + 2 • e₁` in `ℓ²(ℕ, ℂ)`. -/
noncomputable def testVec : lp (fun _ : ℕ => ℂ) 2 :=
  lp.single 2 0 (1 : ℂ) + (2 : ℂ) • lp.single 2 1 (1 : ℂ)

/-- The wandering coefficients of the explicit Wold decomposition of `testVec`:
`e₀` at `0`, `2 • e₀` at `1`, and `0` elsewhere. -/
noncomputable def testCoeffs : ℕ → lp (fun _ : ℕ => ℂ) 2 :=
  fun k => if k = 0 then lp.single 2 0 (1 : ℂ)
    else if k = 1 then (2 : ℂ) • lp.single 2 0 (1 : ℂ) else 0

/-- The explicit Wold decomposition of `testVec` at level `2`: the wandering
coefficients are `e₀` and `2 • e₀` and the remainder is `0`. -/
theorem testVec_wold_decomposition :
    testVec = (∑ k ∈ Finset.range 2, (shiftIsometry ^ k) (testCoeffs k)) +
      (shiftIsometry ^ 2) 0 := by
  rw [map_zero, add_zero]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [testVec, testCoeffs, shiftIsometry_single]

/-- Pythagoras for the explicit Wold decomposition: `‖e₀ + 2 • e₁‖² = 5`. -/
theorem wold_norm_sq_shift_example :
    ‖testVec‖ ^ 2 = 5 := by
  have hw : ∀ k, testCoeffs k ∈ wanderingSub shiftIsometry := by
    intro k
    show (if k = 0 then lp.single 2 0 (1 : ℂ)
      else if k = 1 then (2 : ℂ) • lp.single 2 0 (1 : ℂ) else 0) ∈
      wanderingSub shiftIsometry
    by_cases hk0 : k = 0
    · rw [ite_eq_left hk0]
      exact single_zero_mem_wandering
    · by_cases hk1 : k = 1
      · rw [ite_eq_right hk0, ite_eq_left hk1]
        exact Submodule.smul_mem _ (2 : ℂ) single_zero_mem_wandering
      · rw [ite_eq_right hk0, ite_eq_right hk1]
        exact Submodule.zero_mem _
  have hnorm := wold_norm_sq shiftIsometry 2 testCoeffs hw 0 testVec
    testVec_wold_decomposition
  have h1 : ‖(lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)‖ = 1 := norm_single_lp 0
  have h2 : ‖(2 : ℂ) • (lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)‖ = 2 := by
    rw [norm_smul, norm_single_lp]
    simp
  have h0 : testCoeffs 0 = lp.single 2 0 (1 : ℂ) := by simp [testCoeffs]
  have h1' : testCoeffs 1 = (2 : ℂ) • lp.single 2 0 (1 : ℂ) := by simp [testCoeffs]
  have hsum : (∑ k ∈ Finset.range 2, ‖testCoeffs k‖ ^ 2) = 5 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1', h1, h2]
    norm_num
  rw [hsum] at hnorm
  simpa using hnorm

end MathlibExtTest.Analysis.InnerProductSpace.WoldDecompositionTests

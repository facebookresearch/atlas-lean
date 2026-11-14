/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FunctionalDeltaContinuous

/-!
# Tests for continuous-time product-integral differentiability

The values below are computed from the definitions (T77's `productIntegral_const` and
`productIntegral_step`, the telescoping of increments), not through the Hadamard theorem.

* The Duhamel derivative at the zero integrator is `h ↦ h τ - h 0` for **every** path `h`.
* For the unit jump path `1_{[c, τ]}` (`0 < c ≤ τ`), the difference quotient
  `t⁻¹ (P(t · 1_{[c, τ]}) - P(0))` equals `1` for every `t > 0`, and so does the Duhamel derivative
  in that direction: the derivative formula agrees with the exact quotients.
* Non-vacuity of the hypotheses: `0` lies in every total-variation ball of radius `≥ 0`; the
  discontinuous jump path and every continuous path lie in the tangent set; the theorems
  instantiate at `θ = 0`.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal
open MathlibExt.Analysis.StieltjesProductIntegral
open MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
open MathlibExt.Probability.Statistics.FunctionalDeltaContinuous

namespace MathlibExtTest.FunctionalDeltaContinuous

local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

variable {τ : ℝ}

theorem toFun_zero (τ : ℝ) : toFun (0 : 𝔻[τ]) = fun _ => 0 := by
  funext t
  simp [toFun]

/-- The zero path lies in every total-variation ball of nonnegative radius. -/
theorem zero_mem_tvBall {M : ℝ} (hM : 0 ≤ M) : (0 : 𝔻[τ]) ∈ tvBall τ M :=
  ⟨fun _ => 0, by rw [toFun_zero]; exact isControl_zero, by simpa using hM⟩

/-- **The Duhamel derivative at `0`**, from the definitions: both factors are the product
integral of the zero integrator, which is `1`, and the two-tag sums telescope to `h τ - h 0`. -/
theorem duhamelDeriv_zero (hτ : 0 ≤ τ) (h : 𝔻[τ]) :
    duhamelDeriv 0 h = toFun h τ - toFun h 0 := by
  unfold duhamelDeriv duhamelDerivFun
  rw [toFun_zero]
  refine (tendsto_const_nhds.congr fun s => ?_).limUnder_eq
  rw [twoTagSum, ← sum_increments_partitionPts hτ (toFun h) s]
  refine sum_congr rfl fun x _ => ?_
  simp only [productIntegral_const, one_mul, mul_one]

/-- The unit jump path `1_{[c, τ]}` on `[0, τ]`. -/
noncomputable def jumpPath (τ c : ℝ) : 𝔻[τ] :=
  ⟨fun t => if c ≤ (t : ℝ) then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨t, rfl⟩
    dsimp only
    split_ifs <;> simp⟩⟩

theorem toFun_jumpPath {c t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    toFun (jumpPath τ c) t = if c ≤ t then 1 else 0 := by
  rw [toFun_of_mem _ ht]
  rfl

theorem toFun_smul_jumpPath {c s t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    toFun ((0 : 𝔻[τ]) + s • jumpPath τ c) t = if c ≤ t then s else 0 := by
  rw [zero_add, toFun_smul, toFun_jumpPath ht]
  split_ifs <;> simp

/-- The product integral of `s · 1_{[c, τ]}` is `1 + s` (one jump of size `s`, T77). -/
theorem prodIntegralEnd_smul_jumpPath {c s : ℝ} (hc : 0 < c) (hcτ : c ≤ τ) :
    prodIntegralEnd ((0 : 𝔻[τ]) + s • jumpPath τ c) = 1 + s := by
  rw [prodIntegralEnd, productIntegral_congr (hc.le.trans hcτ)
    (B := fun t => if c ≤ t then s else 0) fun t ht => toFun_smul_jumpPath ht,
    productIntegral_step hc hcτ, sub_zero]

theorem prodIntegralEnd_zero : prodIntegralEnd (0 : 𝔻[τ]) = 1 := by
  rw [prodIntegralEnd, toFun_zero, productIntegral_const]

/-- **The exact difference quotient in the jump direction is `1`.** -/
theorem quotient_jumpPath {c t : ℝ} (hc : 0 < c) (hcτ : c ≤ τ) (ht : 0 < t) :
    t⁻¹ • (prodIntegralEnd ((0 : 𝔻[τ]) + t • jumpPath τ c) - prodIntegralEnd (0 : 𝔻[τ])) = 1 := by
  rw [prodIntegralEnd_smul_jumpPath hc hcτ, prodIntegralEnd_zero, smul_eq_mul, add_sub_cancel_left,
    inv_mul_cancel₀ ht.ne']

/-- **The Duhamel derivative in the jump direction is `1`**, matching the exact quotients. -/
theorem duhamelDeriv_zero_jumpPath {c : ℝ} (hc : 0 < c) (hcτ : c ≤ τ) :
    duhamelDeriv 0 (jumpPath τ c) = 1 := by
  have hτ : 0 ≤ τ := hc.le.trans hcτ
  rw [duhamelDeriv_zero hτ, toFun_jumpPath ⟨hτ, le_rfl⟩, toFun_jumpPath ⟨le_rfl, hτ⟩]
  simp [hcτ, not_le.2 hc]

example {c t : ℝ} (hc : 0 < c) (hcτ : c ≤ τ) (ht : 0 < t) :
    t⁻¹ • (prodIntegralEnd ((0 : 𝔻[τ]) + t • jumpPath τ c) - prodIntegralEnd (0 : 𝔻[τ])) =
      duhamelDeriv 0 (jumpPath τ c) := by
  rw [quotient_jumpPath hc hcτ ht, duhamelDeriv_zero_jumpPath hc hcτ]

/-- The discontinuous jump path has bounded variation, so it lies in the tangent set. -/
theorem jumpPath_mem_bvPaths (c : ℝ) : jumpPath τ c ∈ bvPaths τ := by
  refine ⟨fun t => if c ≤ t then 1 else 0, IsControl.congr (isControl_self_of_monotoneOn ?_)
    fun t ht => (toFun_jumpPath ht).symm⟩
  intro x _ y _ hxy
  dsimp only
  split_ifs <;> linarith

example (c : ℝ) : jumpPath τ c ∈ closure (bvPaths τ) :=
  subset_closure (jumpPath_mem_bvPaths c)

/-- A constant path is continuous, so it lies in the tangent set. -/
example (hτ : 0 ≤ τ) : (0 : 𝔻[τ]) ∈ closure (bvPaths τ) :=
  continuous_mem_closure_bvPaths hτ (by simpa using continuous_const)

/-- The Hadamard theorem instantiates at `θ = 0` on the unit total-variation ball. -/
example (hτ : 0 ≤ τ) :
    HasHadamardDerivWithinAt prodIntegralEnd (duhamelDeriv (0 : 𝔻[τ])) (tvBall τ 1)
      (closure (bvPaths τ)) 0 :=
  hasHadamardDerivWithinAt_prodIntegralEnd hτ (zero_mem_tvBall zero_le_one)

/-- The survival-map theorem instantiates at `Λ = 0`. -/
example (hτ : 0 ≤ τ) :
    HasHadamardDerivWithinAt (fun x : 𝔻[τ] => prodIntegralEnd (-x))
      (fun h => duhamelDeriv (-0) (-h)) {x | -x ∈ tvBall τ 1}
      {h | -h ∈ closure (bvPaths τ)} 0 :=
  hasHadamardDerivWithinAt_survivalEnd hτ (by simpa using zero_mem_tvBall zero_le_one)

end MathlibExtTest.FunctionalDeltaContinuous

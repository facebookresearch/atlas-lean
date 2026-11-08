/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Semigroup

/-!
# Tests for the Wright–Fisher diffusion semigroup

The one-generation second moment `E_x[(X₁)^2] = x/M + (1 - 1/M) x²`; the `M = 0` junk value of
the chain operator; the dual block-counting entries for two lineages; preservation of the mean
and the exact decay `E_x[H(X_t)] = e^{-t} H(x)` of heterozygosity `H(x) = 2x(1 - x)` under the
diffusion semigroup; the semigroup at `t = 0` and the junk value at `t < 0`; positivity,
contraction and the convergence of the chain for a concrete continuous function.
-/

@[expose] public section

open Filter Topology Matrix Polynomial
open scoped unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.Semigroup

open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting
open MathlibExt.Biology.PopulationGenetics.Diffusion.ChainLimit
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

/-- One-generation second moment of the frequency: `E_x[(X₁)^2] = x / M + (1 - 1/M) x²`. -/
example (M : ℕ) (hM : M ≠ 0) (x : I) :
    ∫ i, ((i : ℝ) / M) ^ 2 ∂(ProbabilityTheory.binomial M x) =
      (x : ℝ) / M + (1 - 1 / (M : ℝ)) * (x : ℝ) ^ 2 := by
  rw [integral_binomial_div_pow M 2 hM]
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hd : ((M.descFactorial 2 : ℕ) : ℝ) = M * (M - 1) := by
    rcases M with _ | M
    · exact absurd rfl hM
    · simp [Nat.descFactorial]
      ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, wfLineageProb, hd]
  simp [Nat.stirlingSecond]
  field_simp

/-- Boundary `M = 0` (no population): the chain operator evaluates at frequency `0`, a junk value
of the totalized `k / 0 = 0`. -/
example (f : C(I, ℝ)) (x : I) : wfStep 0 f x = f 0 := by
  simp [wfStep_apply, bernsteinApproximation.apply, bernstein_apply, bernstein.z]

/-- One neutral Wright–Fisher generation fixes the constant function one. Removing the public
one-step unit theorem, or reversing its equality, breaks this consumer-level check. -/
example (M : ℕ) : wfStep M 1 = 1 :=
  wfStep_apply_one M

/-- One neutral Wright–Fisher generation preserves the pointwise nonnegative cone. -/
example (M : ℕ) {f : C(I, ℝ)} (hf : 0 ≤ f) : 0 ≤ wfStep M f :=
  wfStep_nonneg M hf

/-- The generic unital-power helper applies to the real neutral chain operator. -/
example (M m : ℕ) : (wfStep M ^ m) 1 = 1 :=
  ContinuousLinearMap.pow_apply_one (wfStep M) (wfStep_apply_one M) m

/-- The generic positive-power helper applies to the real neutral chain operator. -/
example (M m : ℕ) {f : C(I, ℝ)} (hf : 0 ≤ f) : 0 ≤ (wfStep M ^ m) f :=
  ContinuousLinearMap.pow_nonneg (wfStep M) (fun h => wfStep_nonneg M h) m hf

/-- Public one-generation monomial duality is available to downstream chain constructions. -/
example (M n : ℕ) (hM : M ≠ 0) :
    wfStep M ((X ^ n : ℝ[X]).toContinuousMapOn I) =
      (∑ k ∈ Finset.range (n + 1), C (wfLineageProb M n k) * X ^ k).toContinuousMapOn I :=
  wfStep_X_pow M n hM

/-- The block-counting process with one lineage stays put: `P_t(1 → 1) = 1`. -/
example (t : ℝ) : NormedSpace.exp (t • blockCountingGenerator 1) 1 1 = 1 := by
  rw [exp_blockCountingGenerator_apply 1 t 1 1 (by decide) le_rfl]
  simp [tavareProb, Nat.descFactorial, Nat.factorial]
  norm_num

/-- Two lineages never jump to zero lineages: `P_t(2 → 0) = 0`. -/
example (t : ℝ) : NormedSpace.exp (t • blockCountingGenerator 2) 2 0 = 0 := by
  rw [exp_smul_blockCountingGenerator]
  simp [Matrix.mul_apply, Fin.sum_univ_three, blockCountingRightEigen, blockCountingLeftEigen,
    Nat.ascFactorial, Nat.descFactorial, blockCountingEigenvalue]
  norm_num

/-- Truncation consistency, a concrete instance: the `(1, 1)` entry is the same for the
block-counting process on `{0, 1}` and on `{0, 1, 2}`. -/
example (t : ℝ) :
    NormedSpace.exp (t • blockCountingGenerator 2) 1 1 =
      NormedSpace.exp (t • blockCountingGenerator 1) 1 1 :=
  exp_smul_blockCountingGenerator_castLE (n := 1) (N := 2) (by norm_num) t 1 1

/-- At time `0` the diffusion semigroup is the identity. -/
example (f : C(I, ℝ)) : wfSemigroup 0 f = f := by simp

/-- Boundary `t < 0`, outside the domain: the definition returns the identity (junk value). -/
example : wfSemigroup (-1) = 1 := wfSemigroup_of_nonpos (by norm_num)

/-- The diffusion preserves the mean allele frequency: `E_x[X_t] = x` (neutrality). -/
example {t : ℝ} (ht : 0 ≤ t) (x : I) :
    wfSemigroup t ((X ^ 1 : ℝ[X]).toContinuousMapOn I) x = x := by
  rw [wfSemigroup_X_pow ht]
  have hG : blockCountingGenerator 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockCountingGenerator]
  simp [hG, Fin.sum_univ_two]

/-- **Heterozygosity decays exactly at rate one** under the diffusion semigroup:
`E_x[2 X_t (1 - X_t)] = e^{-t} · 2x(1 - x)` (time in units of `2N` generations). -/
example {t : ℝ} (ht : 0 ≤ t) (x : I) :
    wfSemigroup t ((2 * X * (1 - X) : ℝ[X]).toContinuousMapOn I) x =
      Real.exp (-t) * (2 * x * (1 - x)) := by
  have h21 : NormedSpace.exp (t • blockCountingGenerator 2) 2 1 = 1 - Real.exp (-t) := by
    rw [exp_blockCountingGenerator_apply 2 t 2 1 (by decide) (by decide)]
    change tavareProb 2 1 t = _
    rw [tavareProb, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]
    simp [Nat.ascFactorial, Nat.descFactorial, Nat.factorial]
    ring_nf
  have h22 : NormedSpace.exp (t • blockCountingGenerator 2) 2 2 = Real.exp (-t) := by
    rw [exp_blockCountingGenerator_apply 2 t 2 2 (by decide) le_rfl]
    change tavareProb 2 2 t = _
    simp [tavareProb, Nat.ascFactorial, Nat.descFactorial, Nat.factorial]
    ring_nf
  have h20 : NormedSpace.exp (t • blockCountingGenerator 2) 2 0 = 0 := by
    rw [exp_smul_blockCountingGenerator]
    simp [Matrix.mul_apply, Fin.sum_univ_three, blockCountingRightEigen, blockCountingLeftEigen,
      Nat.ascFactorial, Nat.descFactorial, blockCountingEigenvalue]
    norm_num
  have hX1 := wfSemigroup_X_pow ht 1 x
  have hX2 := wfSemigroup_X_pow ht 2 x
  have hG : blockCountingGenerator 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockCountingGenerator]
  have hp : (2 * X * (1 - X) : ℝ[X]).toContinuousMapOn I =
      (2 : ℝ) • (X ^ 1 : ℝ[X]).toContinuousMapOn I -
        (2 : ℝ) • (X ^ 2 : ℝ[X]).toContinuousMapOn I := by
    ext y
    simp
    ring
  rw [hp, map_sub, map_smul, map_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.smul_apply, hX1, hX2]
  simp [hG, Fin.sum_univ_two, Fin.sum_univ_three, h20, h21, h22]
  ring

/-- Positivity and contraction of the diffusion semigroup on a concrete function. -/
example (t : ℝ) (f : C(I, ℝ)) (hf : 0 ≤ f) :
    0 ≤ wfSemigroup t f ∧ ‖wfSemigroup t f‖ ≤ ‖f‖ :=
  ⟨wfSemigroup_nonneg t hf, ((wfSemigroup t).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg f) (norm_wfSemigroup_le t))⟩

/-- The chain converges for a non-polynomial test function, e.g. `x ↦ |x - 1/2|`. -/
example : Tendsto (fun M : ℕ => (wfStep M ^ ⌊(1 : ℝ) * M⌋₊)
    ⟨fun x : I => |(x : ℝ) - 1 / 2|, by fun_prop⟩) atTop
    (𝓝 (wfSemigroup 1 ⟨fun x : I => |(x : ℝ) - 1 / 2|, by fun_prop⟩)) :=
  tendsto_wfStep_pow_floor 1 _

/-- The generator on `x ↦ x²` is `x (1 - x)`, i.e. `(T_t x² - x²) / t → x (1 - x)`. -/
example (x : ℝ) : (polyGenerator (X ^ 2)).eval x = x * (1 - x) := by
  simp [polyGenerator]
  ring

#print axioms tendsto_wfStep_pow_floor
#print axioms wfSemigroup_add
#print axioms tendsto_wfSemigroup_sub_div
#print axioms ContinuousLinearMap.pow_apply_one
#print axioms ContinuousLinearMap.pow_nonneg
#print axioms cauchySeq_apply_of_dense
#print axioms tendsto_apply_of_dense
#print axioms dense_polynomialFunctions
#print axioms floor_mul_eq_zero
#print axioms wfStep_apply_one
#print axioms wfStep_nonneg
#print axioms wfStep_X_pow

#check @Polynomial.toContinuousMapOnAlgHom
#check @Polynomial.toContinuousMapOnAlgHom_apply
#check @cauchySeq_apply_of_dense
#check @tendsto_apply_of_dense
#check @dense_polynomialFunctions
#check @floor_mul_eq_zero
#check @ContinuousLinearMap.pow_apply_one
#check @ContinuousLinearMap.pow_nonneg
#check @wfStep
#check @wfStep_apply
#check @norm_wfStep_le
#check @wfStep_apply_one
#check @wfStep_nonneg
#check @norm_wfStep_pow_le
#check @sum_binomial_mul_div_pow
#check @integral_binomial_div_pow
#check @wfStep_X_pow
#check @wfStep_pow_X_pow
#check @dualMomentPoly
#check @polySemigroup
#check @polySemigroup_X_pow
#check @polySemigroup_zero
#check @polySemigroup_add
#check @polySemigroup_one
#check @tendsto_wfStep_pow_floor_toContinuousMapOn
#check @cauchySeq_wfStep_pow_floor
#check @wfSemigroup
#check @tendsto_wfStep_pow_floor
#check @norm_wfSemigroup_le
#check @wfSemigroup_toContinuousMapOn
#check @wfSemigroup_of_nonpos
#check @wfSemigroup_zero
#check @wfSemigroup_X_pow
#check @wfSemigroup_add
#check @wfSemigroup_apply_one
#check @wfSemigroup_nonneg
#check @tendsto_wfSemigroup_nhdsGE_zero
#check @polyGenerator
#check @eval_polyGenerator
#check @tendsto_wfSemigroup_sub_div

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.Semigroup

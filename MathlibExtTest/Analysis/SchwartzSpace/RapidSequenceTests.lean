/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SchwartzSpace.RapidSequence.Finsupp
public import MathlibExt.Analysis.SchwartzSpace.RapidSequence.Seminorm
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.Defs

/-!
# Complex examples of rapidly decreasing sequences

The finitely supported sequence has coefficients `I` at zero and `2 * I` at two.
Its weighted supremum seminorm is `2 * 3 ^ k`. Cancelling its second coefficient
leaves a sequence whose every weighted seminorm is one. The sequence
`n ↦ exp (-(n + 1)) * I` supplies an example with infinitely many nonzero terms.
-/

@[expose] public noncomputable section

open scoped NNReal Topology

namespace MathlibExtTest.Analysis.SchwartzSpace.RapidSequenceTests

private def coefficients : ℕ →₀ ℂ :=
  Finsupp.single 0 Complex.I + Finsupp.single 2 (2 * Complex.I)

private theorem coefficients_support : coefficients.support = {0, 2} := by
  exact Finsupp.support_single_add_single (by decide) Complex.I_ne_zero
    (mul_ne_zero (by norm_num) Complex.I_ne_zero)

private def packet : RapidSequence ℂ ℂ := RapidSequence.ofFinsupp coefficients

private theorem packet_zero : packet 0 = Complex.I := by
  simp only [packet, coefficients, map_add, RapidSequence.ofFinsupp_single,
    RapidSequence.add_apply, RapidSequence.single_apply_self,
    RapidSequence.single_apply_ne 2 (2 * Complex.I) (by decide : (0 : ℕ) ≠ 2), add_zero]

private theorem packet_two : packet 2 = 2 * Complex.I := by
  simp only [packet, coefficients, map_add, RapidSequence.ofFinsupp_single,
    RapidSequence.add_apply,
    RapidSequence.single_apply_ne 0 Complex.I (by decide : (2 : ℕ) ≠ 0),
    RapidSequence.single_apply_self, zero_add]

private theorem packet_off {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) : packet n = 0 := by
  simp only [packet, coefficients, map_add, RapidSequence.ofFinsupp_single,
    RapidSequence.add_apply, RapidSequence.single_apply_ne 0 Complex.I h0,
    RapidSequence.single_apply_ne 2 (2 * Complex.I) h2, zero_add]

private theorem packet_two_norm : ‖packet 2‖ = 2 := by
  simp [packet_two]

-- The finite-support supremum formula computes every weighted seminorm of the packet.
private theorem packet_seminorm (k : ℕ) :
    RapidSequence.seminorm k packet = 2 * (3 : ℝ) ^ k := by
  have hmono := RapidSequence.seminorm_monotone (𝕜 := ℂ) (E := ℂ) (Nat.zero_le k)
    (RapidSequence.single (𝕜 := ℂ) 2 (1 : ℂ))
  have hp : (1 : ℝ) ≤ 3 ^ k := by
    simpa [RapidSequence.seminorm_single] using hmono
  have hc0 : coefficients 0 = Complex.I := by
    simpa only [packet, RapidSequence.ofFinsupp_apply] using packet_zero
  have hc2 : coefficients 2 = 2 * Complex.I := by
    simpa only [packet, RapidSequence.ofFinsupp_apply] using packet_two
  rw [packet, RapidSequence.seminorm_ofFinsupp, coefficients_support]
  simp only [Finset.sup_insert, Finset.sup_singleton]
  change ((max (((0 + 1 : ℕ) : ℝ≥0) ^ k * ‖coefficients 0‖₊)
    (((2 + 1 : ℕ) : ℝ≥0) ^ k * ‖coefficients 2‖₊) : ℝ≥0) : ℝ) = 2 * (3 : ℝ) ^ k
  rw [NNReal.coe_max]
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, coe_nnNorm]
  simp only [hc0, hc2, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  norm_num only
  simp only [one_pow]
  rw [max_eq_right (by linarith)]; ring

-- Continuous evaluation distinguishes the two nonreal coefficients from an absent one.
example : RapidSequence.evalCLM 0 packet = Complex.I := by
  simpa only [RapidSequence.evalCLM_apply] using packet_zero

example : RapidSequence.evalCLM 2 packet = 2 * Complex.I := by
  simpa only [RapidSequence.evalCLM_apply] using packet_two

example : RapidSequence.evalCLM 1 packet = 0 := by
  simpa only [RapidSequence.evalCLM_apply] using
    packet_off (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) ≠ 2)

example : packet ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : RapidSequence ℂ ℂ ↦ f 0) h
  exact Complex.I_ne_zero (by
    simpa only [packet_zero, RapidSequence.zero_apply] using h0)

example : RapidSequence.seminorm 0 packet = 2 := by
  rw [packet_seminorm]
  norm_num

example : RapidSequence.seminorm 1 packet = 6 := by
  rw [packet_seminorm]
  norm_num

example : RapidSequence.seminorm 2 packet = 18 := by
  rw [packet_seminorm]
  norm_num

example : ‖RapidSequence.evalCLM 2 packet‖ ≤ 2 := by
  simpa [RapidSequence.evalCLM_apply, packet_seminorm] using
    RapidSequence.norm_apply_le_seminorm_zero packet 2

-- A polynomial weight acts on the coefficient before taking its complex norm.
example : RapidSequence.weightedCLM 2 packet 2 = 18 * Complex.I := by
  rw [RapidSequence.weightedCLM_apply, packet_two, smul_eq_mul]
  norm_num; ring

-- A phase rotation preserves each seminorm; multiplying by 2 * I doubles it.
example (k : ℕ) :
    RapidSequence.seminorm k (Complex.I • packet) = 2 * (3 : ℝ) ^ k := by
  rw [map_smul_eq_mul, Complex.norm_I, one_mul, packet_seminorm]

example (k : ℕ) :
    RapidSequence.seminorm k ((2 * Complex.I) • packet) = 4 * (3 : ℝ) ^ k := by
  rw [map_smul_eq_mul, packet_seminorm]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  ring

example : (Complex.I • packet) 2 = (-2 : ℂ) := by
  have h2 : coefficients 2 = 2 * Complex.I := by
    simpa only [packet, RapidSequence.ofFinsupp_apply] using packet_two
  change (Complex.I • RapidSequence.ofFinsupp (𝕜 := ℂ) coefficients) 2 = (-2 : ℂ)
  rw [← map_smul, RapidSequence.ofFinsupp_apply, Finsupp.smul_apply, smul_eq_mul, h2]
  calc
    Complex.I * (2 * Complex.I) = 2 * (Complex.I * Complex.I) := by ring
    _ = -2 := by simp

-- Addition can remove the coordinate which determines the supremum seminorm.
private theorem packet_cancel :
    packet + RapidSequence.single 2 (-(2 * Complex.I)) =
      RapidSequence.single (𝕜 := ℂ) 0 Complex.I := by
  have hc : coefficients + Finsupp.single 2 (-(2 * Complex.I)) =
      Finsupp.single 0 Complex.I := by
    rw [coefficients, add_assoc, ← Finsupp.single_add]
    simp
  calc
    packet + RapidSequence.single 2 (-(2 * Complex.I)) =
        RapidSequence.ofFinsupp (𝕜 := ℂ)
          (coefficients + Finsupp.single 2 (-(2 * Complex.I))) := by
      simp only [packet, map_add, RapidSequence.ofFinsupp_single]
    _ = RapidSequence.single 0 Complex.I := by
      rw [hc, RapidSequence.ofFinsupp_single]

example (k : ℕ) :
    RapidSequence.seminorm k (packet + RapidSequence.single 2 (-(2 * Complex.I))) = 1 := by
  rw [packet_cancel, RapidSequence.seminorm_single]
  simp

-- The n + 1 weight stays nonzero at the first coordinate, for every exponent.
example (k : ℕ) :
    RapidSequence.seminorm k (RapidSequence.single (𝕜 := ℂ) 0 Complex.I) = 1 := by
  rw [RapidSequence.seminorm_single]
  simp

example : RapidSequence.ofFinsupp (𝕜 := ℂ) (0 : ℕ →₀ ℂ) = 0 := by
  simp

example (k : ℕ) : RapidSequence.seminorm k ((0 : ℂ) • packet) = 0 := by
  simp

-- The zero sequence also satisfies the seminorm bound with the endpoint C = 0.
example (k : ℕ) : RapidSequence.seminorm (𝕜 := ℂ) (E := ℂ) k 0 ≤ 0 := by
  apply RapidSequence.seminorm_le_of_forall_le k 0
  intro n
  simp

private def exponentialCoefficients (n : ℕ) : ℂ :=
  (Real.exp (-((n + 1 : ℕ) : ℝ)) : ℂ) * Complex.I

private theorem exponential_norm (n : ℕ) :
    ‖exponentialCoefficients n‖ = Real.exp (-((n + 1 : ℕ) : ℝ)) := by
  rw [exponentialCoefficients, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg (Real.exp_pos _).le]

-- Exponential decay dominates every polynomial weight along n + 1.
private theorem exponentialDecay :
    Asymptotics.SuperpolynomialDecay Filter.atTop
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) (fun n ↦ ‖exponentialCoefficients n‖) := by
  intro k
  have hcast : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
  have hlimit := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hcast
  have hfun :
      ((fun x : ℝ ↦ x ^ k * Real.exp (-x)) ∘
        fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) =
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ k * ‖exponentialCoefficients n‖) := by
    funext n
    rw [Function.comp_apply, exponential_norm]
  exact hfun ▸ hlimit

private def exponential : RapidSequence ℂ ℂ :=
  RapidSequence.ofFunction exponentialCoefficients exponentialDecay

private theorem exponential_nonzero (n : ℕ) : exponential n ≠ 0 := by
  change exponentialCoefficients n ≠ 0
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) Complex.I_ne_zero

example : ¬ Function.HasFiniteSupport (fun n ↦ exponential n) := by
  intro h
  have hs : Function.support (fun n ↦ exponential n) = Set.univ := by
    ext n
    simp [Function.support, exponential_nonzero n]
  have hf : (Set.univ : Set ℕ).Finite := by
    simpa only [Function.HasFiniteSupport, hs] using h
  exact Set.infinite_univ hf

example (k : ℕ) : Filter.Tendsto
    (fun n : ℕ ↦ (((n + 1 : ℕ) : ℂ) ^ k) * exponentialCoefficients n)
      Filter.atTop (𝓝 0) := by
  simpa only [exponential, RapidSequence.ofFunction_apply, smul_eq_mul] using
    exponential.tendsto_weighted k

example (k : ℕ) :
    Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ k *
      Real.exp (-((n + 1 : ℕ) : ℝ))) := by
  simpa only [exponential, RapidSequence.ofFunction_apply, exponential_norm] using
    exponential.summable_weight_mul_norm k

-- The nonzero coefficient at two gives a bound for every higher seminorm of this infinite sequence.
example (k : ℕ) :
    9 * Real.exp (-3) ≤ RapidSequence.seminorm (k + 2) exponential := by
  have hpoint := RapidSequence.weight_mul_norm_le_seminorm 2 2 exponential
  have hmono := RapidSequence.seminorm_monotone (𝕜 := ℂ) (E := ℂ)
    (Nat.le_add_left 2 k) exponential
  have h := hpoint.trans hmono
  norm_num only [exponential, RapidSequence.ofFunction_apply, exponential_norm] at h
  exact h

section UniformityRegression

open Filter

example :
    (inferInstance : UniformSpace (RapidSequence ℂ ℂ)).toTopologicalSpace =
      (inferInstance : TopologicalSpace (RapidSequence ℂ ℂ)) := by
  with_reducible_and_instances rfl

example (s : Set (RapidSequence ℂ ℂ)) (x : RapidSequence ℂ ℂ) :
    s ∈ 𝓝 x ↔
      {p : RapidSequence ℂ ℂ × RapidSequence ℂ ℂ | p.1 = x → p.2 ∈ s} ∈
        uniformity (RapidSequence ℂ ℂ) := by
  with_reducible_and_instances
    rw [mem_nhds_uniformity_iff_right]

example (s : Set (RapidSequence ℂ ℂ)) :
    s ∈ 𝓝 packet ↔
      {p : RapidSequence ℂ ℂ × RapidSequence ℂ ℂ | p.1 = packet → p.2 ∈ s} ∈
        uniformity (RapidSequence ℂ ℂ) := by
  with_reducible_and_instances
    simp only [mem_nhds_uniformity_iff_right]

end UniformityRegression

end MathlibExtTest.Analysis.SchwartzSpace.RapidSequenceTests

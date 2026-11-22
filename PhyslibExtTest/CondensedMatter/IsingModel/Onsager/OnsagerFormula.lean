/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.OnsagerFormula

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Onsager.Onsanger`

* Infinite temperature, computed directly: at `β = 0` every torus pressure `log Z_L(0) / L²` is
  `log 2` (`Z_L(0) = 2^{L²}`), so the sequence converges to `log 2`.
* `main_free_energy` at `β = 0`: the Onsager integrand is `log 1 = 0`, so the theorem gives the
  limit `log 2`, in agreement with the direct computation.
* `main_free_energy` applies at the critical point `β_c` and at `β = 1`.
* `main_critical_beta_value`, `main_critical_beta_unique`: `sinh 2β_c = 1`, `β_c > 0`, and
  `β = 1` is not critical.
* `main_high_temperature_expansion` on the single edge: `Z(β) = 4 cosh β` (the only even subgraph
  is empty).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Onsager.Onsanger

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Onsager

/-- At `β = 0` the torus pressure is `log 2` for every `L > 2`. -/
lemma torusPressureSeq_zero (L : ℕ) (hL : 2 < L) : ons_torusPressureSeq 0 L = Real.log 2 := by
  have : Fact (2 < L) := ⟨hL⟩
  have : NeZero L := ⟨by omega⟩
  have hL0 : (L : ℝ) ^ 2 ≠ 0 := by positivity
  rw [ons_torusPressureSeq, dite_eq_left_of_eq_true (eq_true hL), ons_pressureFinite, ons_Z]
  simp only [isingZ, isingWeight, neg_zero, zero_mul, Real.exp_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun, Fintype.card_bool,
    onsTorus_card_verts]
  push_cast
  rw [Real.log_pow, Nat.cast_pow]
  field_simp

-- Direct computation: the `β = 0` torus pressures converge to `log 2`.
example : Filter.Tendsto (ons_torusPressureSeq 0) Filter.atTop (nhds (Real.log 2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 2] with L hL
  exact (torusPressureSeq_zero L hL).symm

-- Onsager's formula at `β = 0` gives the same limit `log 2`.
example : Filter.Tendsto (ons_torusPressureSeq 0) Filter.atTop (nhds (Real.log 2)) := by
  have h := main_free_energy 0 le_rfl
  simpa using h

-- Onsager's formula applies at the critical point and at `β = 1`.
example : Filter.Tendsto (ons_torusPressureSeq ons_betaC) Filter.atTop
    (nhds (Real.log 2 + (1 / (8 * Real.pi ^ 2)) *
      ∫ k₁ in (-Real.pi)..Real.pi, ∫ k₂ in (-Real.pi)..Real.pi,
        Real.log (Real.cosh (2 * ons_betaC) ^ 2 -
          Real.sinh (2 * ons_betaC) * (Real.cos k₁ + Real.cos k₂)))) :=
  main_free_energy ons_betaC ons_betaC_pos.le

-- The Kramers–Wannier critical point: `sinh 2β_c = 1` and `β_c > 0`.
example : Real.sinh (2 * ons_betaC) = 1 ∧ 0 < ons_betaC :=
  ⟨main_critical_beta_value, ons_betaC_pos⟩

-- `β = 1` is not the critical point: `sinh 2 ≠ 1`.
example : (1 : ℝ) ≠ ons_betaC := by
  intro h
  have h2 := (main_critical_beta_unique 1 one_pos).mpr h
  have hs : (1 : ℝ) < Real.sinh 2 := by
    have h3 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
    have h4 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    rw [Real.sinh_eq]
    linarith
  norm_num at h2
  linarith

/-- The single edge, the complete graph on two vertices. -/
abbrev edge : SimpleGraph (Fin 2) := ⊤

-- The high-temperature expansion on the single edge: `Z(β) = 2² cosh β · X(tanh β)` with
-- `X = 1`.
example (β : ℝ) : ons_Z edge β = 4 * Real.cosh β := by
  have hE : edge.edgeFinset = {s(0, 1)} := by decide
  have hX : ons_X edge (Real.tanh β) = 1 := by
    have : edge.edgeFinset.powerset.filter IsEvenSubgraph = {∅} := by rw [hE]; decide
    rw [ons_X, this]
    simp
  rw [main_high_temperature_expansion, hX, hE]
  simp
  norm_num

end PhyslibExtTest.CondensedMatter.IsingModel.Onsager.Onsanger

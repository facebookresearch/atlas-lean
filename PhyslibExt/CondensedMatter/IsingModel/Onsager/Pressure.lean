/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.HighTemp

/-!

# Finite-volume pressure

The finite-volume pressure `log Z / |V|` and its decomposition through the high-temperature
expansion.

## i. Overview

The finite-volume pressure of the zero-field Ising model is `p_G(β) = log Z_G(β) / |V|`. The
even-subgraph generating function `X(x)` contains the empty subgraph, so it is positive for `x ≥ 0`,
and the high-temperature expansion gives
`p_G(β) = log 2 + (|E| / |V|) log cosh β + log X(tanh β) / |V|` for `β ≥ 0`.

## ii. Key results

- `ons_X_pos` : `X(x) > 0` for `x ≥ 0`
- `ons_pressureFinite` : the finite-volume pressure
- `ons_pressureFinite_eq` : its decomposition

## iii. Table of contents

- A. Positivity of the even-subgraph sum
- B. The finite-volume pressure

## iv. References

- B. L. van der Waerden, *Die lange Reichweite der regelmässigen Atomanordnung in Mischkristallen*,
  Z. Physik 118 (1941) 473-488

-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Positivity of the even-subgraph sum -/

lemma ons_X_pos (x : ℝ) (hx : 0 ≤ x) : 0 < ons_X G x := by
  unfold ons_X
  have hmem : (∅ : Finset (Sym2 V)) ∈
      G.edgeFinset.powerset.filter IsEvenSubgraph := by
    rw [Finset.mem_filter]
    refine ⟨Finset.empty_mem_powerset _, ?_⟩
    intro v
    have : incCount (∅ : Finset (Sym2 V)) v = 0 := by
      unfold incCount
      simp
    rw [this]
    exact ⟨0, rfl⟩
  have hle : (1 : ℝ) ≤
      ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card := by
    have hterm : x ^ (∅ : Finset (Sym2 V)).card = 1 := by simp
    calc (1 : ℝ) = x ^ (∅ : Finset (Sym2 V)).card := hterm.symm
      _ ≤ ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card := by
          apply Finset.single_le_sum (f := fun F => x ^ F.card) ?_ hmem
          intro F _
          exact pow_nonneg hx _
  exact lt_of_lt_of_le zero_lt_one hle

/-! ## B. The finite-volume pressure -/

/-- The finite-volume pressure `log Z_G(β) / |V|` (the negative of `β` times the free energy per
site). -/
noncomputable def ons_pressureFinite (β : ℝ) : ℝ :=
  Real.log (ons_Z G β) / (Fintype.card V : ℝ)

lemma ons_pressureFinite_eq (β : ℝ) (hβ : 0 ≤ β) (hV : 0 < Fintype.card V) :
    ons_pressureFinite G β
      = Real.log 2
        + (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) * Real.log (Real.cosh β)
        + Real.log (ons_X G (Real.tanh β)) / (Fintype.card V : ℝ) := by
  unfold ons_pressureFinite
  rw [ons_hte G β]
  have h2 : ((2 : ℝ) ^ Fintype.card V) ≠ 0 := by positivity
  have hcosh : ((Real.cosh β) ^ G.edgeFinset.card) ≠ 0 :=
    pow_ne_zero _ (Real.cosh_pos β).ne'
  have htanh : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos β).le
  have hX : ons_X G (Real.tanh β) ≠ 0 :=
    (ons_X_pos G (Real.tanh β) htanh).ne'
  rw [Real.log_mul (mul_ne_zero h2 hcosh) hX, Real.log_mul h2 hcosh,
    Real.log_pow, Real.log_pow]
  have hVne : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hV.ne'
  field_simp

end Onsager

end StatMech

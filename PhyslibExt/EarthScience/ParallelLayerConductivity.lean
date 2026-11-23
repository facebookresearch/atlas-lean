/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Parallel-layer effective conductivity

## i. Overview

For an ordered family of layers with thicknesses `L i` and
conductivities `K i`, flow parallel to the layering sees the
thickness-weighted arithmetic mean of the conductivities,
while flow in series across the layering sees total
thickness over summed layer resistances. For the same
nonempty family of positive thicknesses and conductivities,
the parallel value is positive and the series value is at
most the parallel value; this is the arithmetic/harmonic
mean comparison for the layered medium. No anisotropic
tensor law or new flow model is introduced.

## ii. Key results

- `EarthScience.parallelEffectiveConductivity_pos`: positivity
  of the parallel effective conductivity.
- `EarthScience.series_le_parallel`: the series effective
  conductivity is at most the parallel effective
  conductivity.

## iii. Table of contents

- A. Parallel and series effective conductivities

## iv. References

- J. Bear, *Dynamics of Fluids in Porous Media*, 1972
  (effective conductivity of layered media parallel and
  normal to the layering).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Parallel and series effective conductivities -/

/-- Effective conductivity for flow parallel to the layering:
the thickness-weighted arithmetic mean of layer conductivities.
Outside a nonempty family of positive thicknesses this is only
Lean's totalized quotient. -/
noncomputable def parallelEffectiveConductivity {n : ℕ}
    (L K : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, L i * K i) / (∑ i ∈ Finset.range n, L i)

/-- Effective conductivity for flow in series across the
layering: total thickness over summed layer resistances (the
same formula as the layered-series package). -/
noncomputable def seriesEffectiveConductivity {n : ℕ}
    (L K : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, L i) / (∑ i ∈ Finset.range n, L i / K i)

/-- The parallel effective conductivity is positive for at
least one layer with positive thicknesses and conductivities. -/
theorem parallelEffectiveConductivity_pos {n : ℕ} (hn : 1 ≤ n)
    (L K : ℕ → ℝ) (hL : ∀ i < n, 0 < L i)
    (hK : ∀ i < n, 0 < K i) :
    0 < parallelEffectiveConductivity (n := n) L K := by
  unfold parallelEffectiveConductivity
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  apply div_pos
  · exact Finset.sum_pos
      (fun i hi => mul_pos (hL i (Finset.mem_range.mp hi))
        (hK i (Finset.mem_range.mp hi))) hne
  · exact Finset.sum_pos (fun i hi => hL i (Finset.mem_range.mp hi)) hne

/-- Directional comparison: for the same positive layer family,
the series (across-layer) effective conductivity is at most
the parallel (along-layer) effective conductivity. -/
theorem series_le_parallel {n : ℕ} (hn : 1 ≤ n)
    (L K : ℕ → ℝ) (hL : ∀ i < n, 0 < L i)
    (hK : ∀ i < n, 0 < K i) :
    seriesEffectiveConductivity (n := n) L K
      ≤ parallelEffectiveConductivity (n := n) L K := by
  unfold seriesEffectiveConductivity parallelEffectiveConductivity
  have hne : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hT : 0 < ∑ i ∈ Finset.range n, L i :=
    Finset.sum_pos (fun i hi => hL i (Finset.mem_range.mp hi)) hne
  have hS : 0 < ∑ i ∈ Finset.range n, L i / K i :=
    Finset.sum_pos
      (fun i hi => div_pos (hL i (Finset.mem_range.mp hi))
        (hK i (Finset.mem_range.mp hi))) hne
  have hCS := Finset.sq_sum_div_le_sum_sq_div (Finset.range n) L
    (g := fun i => L i / K i)
    (fun i hi => div_pos (hL i (Finset.mem_range.mp hi)) (hK i (Finset.mem_range.mp hi)))
  have hEq : (∑ i ∈ Finset.range n, L i ^ 2 / (L i / K i))
      = ∑ i ∈ Finset.range n, L i * K i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hLi : 0 < L i := hL i hi'
    have hKi : 0 < K i := hK i hi'
    field_simp
  have hCS2 : (∑ i ∈ Finset.range n, L i) ^ 2 / ∑ i ∈ Finset.range n, L i / K i
      ≤ ∑ i ∈ Finset.range n, L i * K i := hCS.trans_eq hEq
  rw [div_le_div_iff₀ hS hT, ← pow_two]
  exact (div_le_iff₀ hS).mp hCS2

end EarthScience

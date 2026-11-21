/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Circuits.NetworkStorageBalance
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.NetworkStorageBalance

namespace PhyslibExtTest.Circuits.NetworkStorageBalance

/-- Tellegen at one node and one branch: `v = 5`, `iB = 3`, so both
sides are `15`, through the public lemma. -/
example : dotProduct (![5] : Fin 1 → ℝ) ![3]
    = dotProduct (![5] : Fin 1 → ℝ) ![3] :=
  branch_power_eq_node_power 1 1 !![1] ![5] ![3] ![5] ![3]
    (by ext i; fin_cases i; norm_num [Matrix.mulVec, dotProduct])
    (by ext i; fin_cases i; norm_num [Matrix.mulVec, dotProduct])

/-- Stored energy of one capacitor branch: `C = 2`, `v = 3` gives
`2 * 3^2 / 2 = 9`, and nonnegativity through the public lemma. -/
example : storedEnergy 1 {0} ∅ ![2] ![0] ![3] ![5] = 9 := by
  norm_num [storedEnergy, Finset.sum_singleton]

example : 0 ≤ storedEnergy 1 {0} ∅ ![2] ![0] ![3] ![5] :=
  storedEnergy_nonneg 1 {0} ∅ ![2] ![0] ![3] ![5]
    (by intro e _; fin_cases e; norm_num) (by intro e h; simp at h)

/-- The stored-energy derivative on a ramping capacitor voltage:
`v(s) = s`, `C = 2`, so `E(s) = s^2` and `E'(t) = 2t`, through
`hasDerivAt_storedEnergy`. -/
example (t : ℝ) : HasDerivAt
    (fun s => storedEnergy 1 {0} ∅ ![2] ![0] (fun _ => s) (fun _ => 2))
    (t * 2) t := by
  have h := hasDerivAt_storedEnergy 1 {0} ∅ ![2] ![0] (fun s _ => s)
    (fun _ _ => 2) t
    (by intro e _; simp)
    (by intro e h; simp at h)
    (by intro e _; fun_prop)
    (by intro e h; simp at h)
  simpa using h

/-- A three-branch parallel network at constant values: branch 0 a
capacitor (`C = 2`, `v = 4`, `iB = 0` since the voltage is
constant), branch 1 a resistor (`R = 2`, `v = 4`, `iB = 2`), branch
2 a source branch (`v = 4`, `iB = 1`), one node with `phi = 4` and
injection `j = 3`. Supplied power is `phi * j = 12`, source
absorbed power is `4`, resistive loss is `8`, and the stored
energy is constant, so the headline balance reads `0 = 12 - 4 - 8`
and the finite-horizon inequality is `0 ≤ ∫₀¹ 8`. -/
private theorem threeBranch_partition :
    IsBranchPartition 3 {1} ∅ {0} {2} := by
  unfold IsBranchPartition
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

example (t : ℝ) :
    deriv (fun s => storedEnergy 3 {0} ∅ ![2, 0, 0] ![0, 0, 0]
      ![4, 4, 4] ![0, 2, 1]) t
      = dotProduct ![4] ![3]
        - sourceAbsorbedPower 3 {2} ![4, 4, 4] ![0, 2, 1]
        - resistiveLoss 3 {1} ![0, 2, 0] ![0, 2, 1] :=
  network_storage_deriv_eq_supplied_minus_losses 1 3 !![1, 1, 1]
    {1} ∅ {0} {2} threeBranch_partition ![0, 2, 0] ![0, 0, 0] ![2, 0, 0]
    (by intro e he; fin_cases e <;> simp_all <;> norm_num) (by intro e h; simp at h)
    (by intro e he; fin_cases e <;> simp_all <;> norm_num)
    (fun _ => ![4]) (fun _ => ![3]) (fun _ => ![4, 4, 4]) (fun _ => ![0, 2, 1]) t
    (by ext i; fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
    (by ext i; fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
    (by intro e he; fin_cases e <;> simp_all <;> norm_num)
    (by intro e he; simp only [Finset.mem_singleton] at he; subst he; simp)
    (by intro e h; simp at h)
    (by intro e _; exact differentiableAt_const _)
    (by intro e h; simp at h)

example : storedEnergy 3 {0} ∅ ![2, 0, 0] ![0, 0, 0] ![4, 4, 4] ![0, 2, 1]
    - storedEnergy 3 {0} ∅ ![2, 0, 0] ![0, 0, 0] ![4, 4, 4] ![0, 2, 1]
    ≤ ∫ s in (0:ℝ)..1, (dotProduct (![4] : Fin 1 → ℝ) ![3]
      - sourceAbsorbedPower 3 {2} ![4, 4, 4] ![0, 2, 1]) :=
  network_energy_sub_le_integral_supplied 1 3 !![1, 1, 1]
    {1} ∅ {0} {2} threeBranch_partition ![0, 2, 0] ![0, 0, 0] ![2, 0, 0]
    (by intro e he; fin_cases e <;> simp_all <;> norm_num) (by intro e h; simp at h)
    (by intro e he; fin_cases e <;> simp_all <;> norm_num)
    (fun _ => ![4]) (fun _ => ![3]) (fun _ => ![4, 4, 4]) (fun _ => ![0, 2, 1])
    0 1 (by norm_num)
    (by intro s _; ext i; fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
    (by intro s _; ext i; fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three])
    (by intro s _ e he; fin_cases e <;> simp_all <;> norm_num)
    (by intro s _ e he; simp only [Finset.mem_singleton] at he; subst he; simp)
    (by intro s _ e h; simp at h)
    (by intro s _ e _; exact differentiableAt_const _)
    (by intro s _ e h; simp at h)
    continuousOn_const
    intervalIntegrable_const

end PhyslibExtTest.Circuits.NetworkStorageBalance

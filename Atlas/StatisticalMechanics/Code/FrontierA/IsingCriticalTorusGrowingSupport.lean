/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.FiniteFamilyDiagonalSelection
import Code.FrontierA.IsingCriticalTorusLocalObservables










open Filter Finset Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}

private def growingRowOrderFamily (n : Nat) : Finset (Nat × Nat) :=
  {n} ×ˢ Finset.range (n + 1)



theorem exists_criticalTorusGrowingCompactCumulant_diagonal
    (hd : 2 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real) :
    ∃ scale : Nat → Nat,
      Tendsto scale atTop atTop ∧
      ∀ n order, order ≤ n →
        |criticalTorusCompactWeightedCumulant
              (A n) (a n) (scale n) order -
            criticalFreeCompactWeightedCumulant (A n) (a n) order| <
          1 / (n + 1 : Real) := by
  let torus : Nat × Nat → Nat → Real := fun p k ↦
    criticalTorusCompactWeightedCumulant (A p.1) (a p.1) k p.2
  let infinite : Nat × Nat → Real := fun p ↦
    criticalFreeCompactWeightedCumulant (A p.1) (a p.1) p.2
  have hpoint (p : Nat × Nat) :
      Tendsto (torus p) atTop (nhds (infinite p)) := by
    exact criticalTorusCompactWeightedCumulant_tendsto
      hd (A p.1) (a p.1) p.2
  obtain ⟨scale, hscale, hclose⟩ :=
    exists_diagonal_close_on_finiteFamilies
      torus infinite hpoint growingRowOrderFamily
  refine ⟨scale, hscale, ?_⟩
  intro n order horder
  have hmem : (n, order) ∈ growingRowOrderFamily n := by
    simp only [growingRowOrderFamily, mem_product, mem_singleton,
      mem_range, true_and]
    omega
  simpa only [torus, infinite] using hclose n (n, order) hmem



theorem exists_criticalTorusGrowingCompactCumulant_tendsto
    (hd : 2 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real) :
    ∃ scale : Nat → Nat,
      Tendsto scale atTop atTop ∧
      ∀ order,
        Tendsto
          (fun n ↦ criticalTorusCompactWeightedCumulant
              (A n) (a n) (scale n) order -
            criticalFreeCompactWeightedCumulant (A n) (a n) order)
          atTop (nhds 0) := by
  obtain ⟨scale, hscale, hclose⟩ :=
    exists_criticalTorusGrowingCompactCumulant_diagonal hd A a
  refine ⟨scale, hscale, ?_⟩
  intro order
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop order] with n hn
    exact (hclose n order hn).le
  · simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat ↦ (1 : Real) / (n + 1)) atTop (nhds 0))

end

end StatMech.FrontierA

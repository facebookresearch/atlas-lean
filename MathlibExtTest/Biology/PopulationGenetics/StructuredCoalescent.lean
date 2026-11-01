/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.StructuredCoalescent
import MathlibExt.Biology.PopulationGenetics.IslandModel

/-! Tests for the two-lineage structured coalescent in the finite island model: the closed-form
mean coalescence times on concrete parameters (the smallest model `d = 2`), the first-step
equations, Slatkin's `F_ST`, its domain boundaries (one deme, no migration: junk values), and the
agreement of the many-demes limit with Wright's infinite-island limit. -/

open Filter
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.StructuredCoalescent

open MathlibExt.Biology.PopulationGenetics.StructuredCoalescent
open MathlibExt.Biology.PopulationGenetics.StructuredCoalescent.PairState
open MathlibExt.Biology.PopulationGenetics.IslandModel (islandEquilibrium tendsto_islandEquilibrium)

/-! ### Mean coalescence times -/

/-- Two demes, `M = 1`: `T₀ = 2`, `T₁ = 3`. -/
example : meanCoalescenceTime 2 1 same = 2 ∧ meanCoalescenceTime 2 1 different = 3 := by
  norm_num [meanCoalescenceTime, withinTime, betweenTime]

/-- Ten demes, `M = 1/2`: `T₁ = 10 + 9 / (1/2) = 28`. -/
example : betweenTime 10 (1 / 2) = 28 := by norm_num [betweenTime]

/-- The closed form solves the first-step equations (`d = 5`, `M = 3`). -/
example : FirstStepEquations 5 3 (meanCoalescenceTime 5 3) :=
  (firstStepEquations_iff (by norm_num) (by norm_num) _).2 rfl

/-- Any solution of the first-step equations has `T₀ = d`, for every migration rate
(Strobeck 1987). -/
example (h : PairState → ℝ) (hh : FirstStepEquations 7 (1 / 100) h) : h same = 7 := by
  rw [(firstStepEquations_iff (by norm_num) (by norm_num) h).1 hh]
  norm_num [meanCoalescenceTime, withinTime]

/-- A function violating the equations is not a solution: `T₀ = 1` is wrong for `d = 2`. -/
example : ¬ FirstStepEquations 2 1 (fun s => if s = coalesced then 0 else 1) := by
  intro h
  have := congrFun ((firstStepEquations_iff (by norm_num) (by norm_num) _).1 h) same
  norm_num [meanCoalescenceTime, withinTime] at this

/-- The exit rates for `d = 3`, `M = 2`: `1 + M = 3` from the same deme, `M / (d - 1) = 1` from
different demes, and `0` from the absorbing state. -/
example : exitRate 3 2 same = 3 ∧ exitRate 3 2 different = 1 ∧ exitRate 3 2 coalesced = 0 := by
  norm_num [exitRate, PairState.sum_eq, rate]

/-- Jump-chain form of the first step from different demes (`d = 3`, `M = 2`). -/
example : meanCoalescenceTime 3 2 different =
    1 / exitRate 3 2 different +
      ∑ t, rate 3 2 different t / exitRate 3 2 different * meanCoalescenceTime 3 2 t :=
  (meanCoalescenceTime_eq_firstStep (by norm_num) (by norm_num) (by decide)).2

/-! ### Slatkin's `F_ST` -/

/-- Two demes, `M = 1`: `T̄ = 5/2`, `F_ST = (5/2 - 2) / (5/2) = 1/5 = 1 / (1 + 1 · 4 / 1)`. -/
example : totalTime 2 1 = 5 / 2 ∧ slatkinFST 2 1 = 1 / 5 := by
  norm_num [totalTime, slatkinFST, withinTime, betweenTime]

example : slatkinFST 2 1 = 1 / (1 + 1 * (2 : ℝ) ^ 2 / ((2 : ℝ) - 1) ^ 2) := by
  have := slatkinFST_eq (d := 2) (M := 1) (by norm_num) (by norm_num)
  push_cast at this
  exact this

/-- `F_ST ∈ (0, 1)` on the model's domain. -/
example : slatkinFST 4 (1 / 3) ∈ Set.Ioo (0 : ℝ) 1 := slatkinFST_mem_Ioo (by norm_num) (by norm_num)

/-- Boundary `d = 1` (a single panmictic deme, outside the theorems' domain `d ≥ 2`): `T̄ = T₀`
and the definition gives `F_ST = 0`, as it should; the closed form `1 / (1 + M d² / (d - 1)²)`
would give the junk value `1` there (from `/ 0`). -/
example : slatkinFST 1 1 = 0 := by norm_num [slatkinFST, totalTime, withinTime, betweenTime]

example : (1 : ℝ) / (1 + 1 * (1 : ℝ) ^ 2 / ((1 : ℝ) - 1) ^ 2) = 1 := by norm_num

/-- Boundary `M = 0` (isolated demes, outside the domain `M > 0`): the true mean `T₁` is
infinite; the definition returns the junk value `betweenTime d 0 = d`. -/
example : betweenTime 3 0 = 3 := by norm_num [betweenTime]

/-! ### Many demes -/

/-- `F_ST → 1 / (1 + M)` as `d → ∞` (here `M = 4Nm = 2`). -/
example : Tendsto (fun d : ℕ => slatkinFST d 2) atTop (𝓝 (1 / 3)) := by
  have := tendsto_slatkinFST (M := 2) (by norm_num)
  norm_num at this ⊢
  exact this

/-- The many-demes limit of Slatkin's `F_ST` and the large-deme limit of Wright's infinite-island
equilibrium (merged `IslandModel`) agree: both are `1 / (1 + 4Nm)`. -/
example (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun d : ℕ => slatkinFST d κ) atTop (𝓝 (1 / (1 + κ))) ∧
      Tendsto (fun N : ℕ => islandEquilibrium (2 * N) (κ / (4 * N))) atTop
        (𝓝 (1 / (1 + κ))) :=
  ⟨tendsto_slatkinFST hκ, tendsto_islandEquilibrium hκ.le⟩

end MathlibExtTest.Biology.PopulationGenetics.StructuredCoalescent

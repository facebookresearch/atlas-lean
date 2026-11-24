/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Subgroup decomposability of the Foster–Greer–Thorbecke measure

At poverty line `z` and poverty-aversion parameter `α`, an individual with income `y < z`
contributes the normalized shortfall `((z - y) / z) ^ α` and others contribute `0`; the
FGT measure of a finite population is the average contribution (`α = 0`: headcount ratio,
`α = 1`: poverty-gap index, `α = 2`: squared poverty gap).

For any assignment of the population to groups, the population FGT is the sum of the groups'
FGT weighted by population shares (`fgt_eq_sum_groups`). No condition on `z`, `α`, or the
groups is needed; empty groups get weight `0`, and an empty population has FGT `0`.

## Main results

* `MathlibExt.Economics.Poverty.fgt_eq_sum_groups`

## References

* J. Foster, J. Greer, E. Thorbecke, "A Class of Decomposable Poverty Measures",
  Econometrica 52 (1984), 761–766.

Atlas roadmap target AP05.T03.
-/

namespace MathlibExt.Economics.Poverty

open Finset

/-- Individual Foster–Greer–Thorbecke contribution at poverty line `z` and poverty-aversion
parameter `α`: the normalized shortfall `((z - y) / z) ^ α` if income `y` is below the line,
and `0` otherwise. It is the FGT contribution for `0 < z` and `0 ≤ α`; outside that domain the
value is Lean's totalized junk (e.g. `z = 0` divides by zero). The decomposition theorem below
is an identity of finite averages and holds for every `z` and `α`, so it carries no domain
hypothesis. -/
noncomputable def fgtTerm (z α y : ℝ) : ℝ :=
  if y < z then ((z - y) / z) ^ α else 0

/-- Foster–Greer–Thorbecke measure `FGT_α` of the finite population `s` with incomes `x`:
the population average of `fgtTerm z α`. It is `0` for an empty population. -/
noncomputable def fgt {ι : Type*} (z α : ℝ) (x : ι → ℝ) (s : Finset ι) : ℝ :=
  (∑ i ∈ s, fgtTerm z α (x i)) / s.card

/-- **Subgroup decomposability of FGT.** If every member of the population `s` is assigned by
`g` to a group in `t`, then `FGT_α` of `s` is the population-share-weighted sum of the
groups' `FGT_α`. Empty groups get weight `0`. -/
theorem fgt_eq_sum_groups {ι κ : Type*} [DecidableEq κ] (z α : ℝ) (x : ι → ℝ)
    (s : Finset ι) (t : Finset κ) (g : ι → κ) (hg : ∀ i ∈ s, g i ∈ t) :
    fgt z α x s =
      ∑ k ∈ t, ((s.filter (fun i => g i = k)).card / s.card : ℝ) *
        fgt z α x (s.filter (fun i => g i = k)) := by
  unfold fgt
  have hfib : (∑ k ∈ t, ∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i))
      = ∑ i ∈ s, fgtTerm z α (x i) :=
    Finset.sum_fiberwise_of_maps_to hg _
  have hterm : ∀ k ∈ t, (((s.filter (fun i => g i = k)).card / s.card : ℝ) *
      ((∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i)) /
        (s.filter (fun i => g i = k)).card)
      = (∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i)) / s.card) := by
    intro k _
    by_cases hk : (s.filter (fun i => g i = k)).card = 0
    · have h_empty : s.filter (fun i => g i = k) = ∅ := Finset.card_eq_zero.mp hk
      have h_sum : ∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i) = 0 := by
        rw [h_empty, Finset.sum_empty]
      simp [h_sum, hk]
    · have hk' : ((s.filter (fun i => g i = k)).card : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr hk
      rw [mul_comm, div_mul_div_cancel₀ hk']
  calc (∑ i ∈ s, fgtTerm z α (x i)) / s.card
      = (∑ k ∈ t, ∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i)) / s.card := by
        rw [← hfib]
    _ = ∑ k ∈ t, (∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i)) / s.card := by
        rw [Finset.sum_div]
    _ = ∑ k ∈ t, ((s.filter (fun i => g i = k)).card / s.card : ℝ) *
          ((∑ i ∈ s.filter (fun i => g i = k), fgtTerm z α (x i)) /
            (s.filter (fun i => g i = k)).card) := by
        apply Finset.sum_congr rfl
        intro k hk_mem
        rw [← hterm k hk_mem]

end MathlibExt.Economics.Poverty

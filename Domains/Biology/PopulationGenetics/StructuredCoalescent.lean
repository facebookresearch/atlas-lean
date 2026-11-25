/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The structured coalescent in the finite island model

In the finite island model there are `d` demes of `N` diploid individuals (`2N` gene copies)
each, and every generation a fraction `m` of the genes of each deme are migrants from the other
demes, each of the other `d - 1` demes being equally likely. With time measured in units of `2N`
generations and `M = 4Nm`, the ancestral lineages of a sample follow the structured coalescent
(Notohara 1990): two lineages in the same deme coalesce at rate `1`, and each lineage moves to
another deme at rate `M / 2`, to each of the `d - 1` other demes with probability `1 / (d - 1)`.

For two lineages this is a continuous-time Markov chain on three states (`PairState`): the
lineages are in the same deme, in different demes, or have coalesced (absorbing). Its rates
(`rate`) are

* same deme → coalesced: `1`;
* same deme → different demes: `M` (either lineage migrates);
* different demes → same deme: `M / (d - 1)` (either lineage migrates, into the other's deme).

The mean times to coalescence `T₀` (same deme) and `T₁` (different demes) are characterized by
the first-step (backward Kolmogorov) equations `∑ₜ q(s, t) (h t - h s) = -1` at the transient
states and `h = 0` at the absorbing state (`FirstStepEquations`). For `d ≥ 2` and `M > 0` they
have the unique solution (`firstStepEquations_iff`)

  `T₀ = d`, `T₁ = d + (d - 1) / M`.

Thus the mean coalescence time of two genes from the same deme does not depend on the migration
rate (Strobeck 1987): it equals the total number `2Nd` of genes, in units of `2N` generations.
Slatkin's (1991) `F_ST = (T̄ - T₀) / T̄`, where `T̄ = T₀ / d + (d - 1) T₁ / d` is the mean
coalescence time of two genes drawn from two demes chosen independently and uniformly, equals

  `F_ST = 1 / (1 + M d² / (d - 1)²)`,

which tends to `1 / (1 + M) = 1 / (1 + 4Nm)` as `d → ∞`, Wright's value for the infinite island
model (`MathlibExt.Biology.PopulationGenetics.IslandModel.tendsto_islandEquilibrium` reaches the
same limit along `N → ∞`).

The model's domain is `d ≥ 2` and `M > 0`. For `d = 1` the state "different demes" does not
exist and the rate `M / (d - 1)` is Lean's junk value `M / 0 = 0`; for `M = 0` two lineages in
different demes never meet, the mean time `T₁` is infinite, and `betweenTime d 0` is the junk value
`d` (from `(d - 1) / 0 = 0`). This file characterizes the mean coalescence times by the
first-step equations; it does not construct the Markov chain.

## Main results

* `rate`, `FirstStepEquations`: the two-lineage structured coalescent and its first-step
  equations.
* `firstStepEquations_iff`: the unique solution `T₀ = d`, `T₁ = d + (d - 1) / M`.
* `meanCoalescenceTime_eq_firstStep`: the same equations in jump-chain form,
  `h s = 1 / qₛ + ∑ₜ (q(s, t) / qₛ) h t`.
* `slatkinFST_eq`: `F_ST = 1 / (1 + M d² / (d - 1)²)`.
* `tendsto_slatkinFST`: `F_ST → 1 / (1 + M)` as `d → ∞`.

## References

* C. Strobeck, *Average number of nucleotide differences in a sample from a single
  subpopulation: a test for population subdivision*, Genetics 117 (1987), 149–153.
* M. Slatkin, *Inbreeding coefficients and coalescence times*, Genet. Res. 58 (1991), 167–175.
* T. Notohara, *The coalescent and the genealogical process in geographically structured
  population*, J. Math. Biol. 29 (1990), 59–75.
* J. Wakeley, *Coalescent Theory: An Introduction*, Roberts & Company (2009), ch. 5.
-/

@[expose] public section

open Filter
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.StructuredCoalescent

/-- The state of two ancestral lineages in the island model: in the same deme, in different
demes, or coalesced (absorbing). -/
inductive PairState
  /-- Both lineages are in the same deme. -/
  | same
  /-- The lineages are in different demes. -/
  | different
  /-- The lineages have coalesced. -/
  | coalesced
  deriving DecidableEq

namespace PairState

instance : Fintype PairState :=
  ⟨{same, different, coalesced}, fun x => by cases x <;> simp⟩

/-- A sum over the three states. -/
theorem sum_eq {β : Type*} [AddCommMonoid β] (f : PairState → β) :
    ∑ t, f t = f same + f different + f coalesced := by
  change ∑ t ∈ {same, different, coalesced}, f t = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

end PairState

open PairState

/-- The transition rates `q(s, t)` (`s ≠ t`) of the two-lineage structured coalescent in the
finite island model with `d` demes and `M = 4Nm`, time in units of `2N` generations: same deme →
coalesced at rate `1`, same deme → different demes at rate `M`, different demes → same deme at
rate `M / (d - 1)`; all other rates (and the diagonal) are `0`. Meaningful for `d ≥ 2` and
`M ≥ 0`. -/
noncomputable def rate (d : ℕ) (M : ℝ) : PairState → PairState → ℝ
  | same, coalesced => 1
  | same, different => M
  | different, same => M / (d - 1)
  | _, _ => 0

/-- The total rate `qₛ = ∑ₜ q(s, t)` of leaving the state `s`. -/
noncomputable def exitRate (d : ℕ) (M : ℝ) (s : PairState) : ℝ := ∑ t, rate d M s t

/-- The first-step (backward Kolmogorov) equations for the mean time to coalescence:
`h coalesced = 0`, and at each transient state `s`, `∑ₜ q(s, t) (h t - h s) = -1`. (The vector
of mean absorption times of a finite absorbing continuous-time Markov chain satisfies these
equations; this file does not construct the chain.) -/
def FirstStepEquations (d : ℕ) (M : ℝ) (h : PairState → ℝ) : Prop :=
  h coalesced = 0 ∧ ∀ s, s ≠ coalesced → ∑ t, rate d M s t * (h t - h s) = -1

/-- The mean coalescence time `T₀ = d` of two lineages in the same deme (units of `2N`
generations). -/
def withinTime (d : ℕ) : ℝ := d

/-- The mean coalescence time `T₁ = d + (d - 1) / M` of two lineages in different demes (units of
`2N` generations). Meaningful for `M > 0`; `betweenTime d 0 = d` is a junk value (the true mean
is infinite). -/
noncomputable def betweenTime (d : ℕ) (M : ℝ) : ℝ := d + (d - 1) / M

/-- The closed-form mean time to coalescence from each state: `T₀`, `T₁`, and `0` once
coalesced. `firstStepEquations_iff` shows it is the unique solution of the first-step
equations. -/
noncomputable def meanCoalescenceTime (d : ℕ) (M : ℝ) : PairState → ℝ
  | same => withinTime d
  | different => betweenTime d M
  | coalesced => 0

/-- **Mean coalescence times in the finite island model (Strobeck 1987; Slatkin 1991).** For
`d ≥ 2` demes and `M = 4Nm > 0`, the first-step equations have the unique solution
`T₀ = d`, `T₁ = d + (d - 1) / M`. In particular `T₀` does not depend on the migration rate. -/
theorem firstStepEquations_iff {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M)
    (h : PairState → ℝ) : FirstStepEquations d M h ↔ h = meanCoalescenceTime d M := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  constructor
  · rintro ⟨hc, ht⟩
    have h0 := ht same (by decide)
    have h1 := ht different (by decide)
    simp only [PairState.sum_eq, rate, hc] at h0 h1
    have e1 : M * (h different - h same) = d - 1 := by
      field_simp at h1
      linarith
    have e0 : h same = d := by linarith
    funext s
    cases s
    · simpa [meanCoalescenceTime, withinTime] using e0
    · simp only [meanCoalescenceTime, betweenTime]
      have e2 : ((d : ℝ) - 1) / M = h different - h same := by
        rw [div_eq_iff hM.ne']
        linarith
      rw [e2, e0]
      ring
    · exact hc
  · rintro rfl
    refine ⟨rfl, fun s hs => ?_⟩
    cases s
    · simp only [PairState.sum_eq, rate, meanCoalescenceTime, withinTime, betweenTime]
      field_simp
      ring
    · simp only [PairState.sum_eq, rate, meanCoalescenceTime, withinTime, betweenTime]
      field_simp
      ring
    · exact absurd rfl hs

/-- **First-step analysis in jump-chain form.** At each transient state `s` the exit rate is
positive and the mean coalescence time is the mean holding time `1 / qₛ` plus the mean time from
the next state, `h s = 1 / qₛ + ∑ₜ (q(s, t) / qₛ) h t`. -/
theorem meanCoalescenceTime_eq_firstStep {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M)
    {s : PairState} (hs : s ≠ coalesced) :
    0 < exitRate d M s ∧ meanCoalescenceTime d M s =
      1 / exitRate d M s + ∑ t, rate d M s t / exitRate d M s * meanCoalescenceTime d M t := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hq : 0 < exitRate d M s := by
    cases s <;> simp only [exitRate, PairState.sum_eq, rate] <;> first | positivity | simp at hs
  refine ⟨hq, ?_⟩
  have h := ((firstStepEquations_iff hd hM _).2 rfl).2 s hs
  have hsum : ∑ t, rate d M s t * (meanCoalescenceTime d M t - meanCoalescenceTime d M s) =
      ∑ t, rate d M s t * meanCoalescenceTime d M t -
        exitRate d M s * meanCoalescenceTime d M s := by
    simp only [exitRate, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hsum] at h
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp
  linear_combination -h

/-- Slatkin's mean coalescence time `T̄ = T₀ / d + (d - 1) T₁ / d` of two genes drawn from two
demes chosen independently and uniformly at random. -/
noncomputable def totalTime (d : ℕ) (M : ℝ) : ℝ :=
  withinTime d / d + (d - 1) / d * betweenTime d M

/-- Slatkin's (1991) `F_ST = (T̄ - T₀) / T̄` for the finite island model. -/
noncomputable def slatkinFST (d : ℕ) (M : ℝ) : ℝ :=
  (totalTime d M - withinTime d) / totalTime d M

/-- `T̄ = d + (d - 1)² / (d M)` for `d ≥ 1`. -/
theorem totalTime_eq {d : ℕ} (hd : 1 ≤ d) (M : ℝ) :
    totalTime d M = d + (d - 1) ^ 2 / (d * M) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rcases eq_or_ne M 0 with rfl | hM
  · simp only [totalTime, withinTime, betweenTime, div_zero, add_zero, mul_zero]
    field_simp
    ring
  · simp only [totalTime, withinTime, betweenTime]
    field_simp
    ring

/-- The denominator of Slatkin's `F_ST` is positive: `0 < T̄` for `d ≥ 1` and `M > 0`. -/
theorem totalTime_pos {d : ℕ} (hd : 1 ≤ d) {M : ℝ} (hM : 0 < M) : 0 < totalTime d M := by
  rw [totalTime_eq hd]
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- **Slatkin's `F_ST` for the finite island model (Slatkin 1991).** For `d ≥ 2` demes and
`M = 4Nm > 0`, `F_ST = 1 / (1 + M d² / (d - 1)²)`. -/
theorem slatkinFST_eq {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M) :
    slatkinFST d M = 1 / (1 + M * d ^ 2 / (d - 1) ^ 2) := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd0 : (0 : ℝ) < d := by linarith
  rw [slatkinFST, totalTime_eq (by omega), withinTime]
  field_simp
  ring

/-- Slatkin's `F_ST` lies in `(0, 1)` for `d ≥ 2` and `M > 0`. -/
theorem slatkinFST_mem_Ioo {d : ℕ} (hd : 2 ≤ d) {M : ℝ} (hM : 0 < M) :
    slatkinFST d M ∈ Set.Ioo (0 : ℝ) 1 := by
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hx : 0 < M * d ^ 2 / (d - 1) ^ 2 := by positivity
  rw [slatkinFST_eq hd hM]
  exact ⟨by positivity, (div_lt_one (by linarith)).2 (by linarith)⟩

/-- **Many demes (Slatkin 1991).** As the number of demes grows, Slatkin's `F_ST` tends to
Wright's `1 / (1 + M) = 1 / (1 + 4Nm)` for every `M > 0`. -/
theorem tendsto_slatkinFST {M : ℝ} (hM : 0 < M) :
    Tendsto (fun d : ℕ => slatkinFST d M) atTop (𝓝 (1 / (1 + M))) := by
  -- `d² / (d - 1)² = 1 / (1 - 1 / d)²`
  have hinv : Tendsto (fun d : ℕ => 1 / (d : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hden : Tendsto (fun d : ℕ => 1 + M / (1 - 1 / (d : ℝ)) ^ 2) atTop
      (𝓝 (1 + M / (1 - 0) ^ 2)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div
      ((tendsto_const_nhds.sub hinv).pow 2) (by norm_num))
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).div hden (by norm_num; linarith)
  norm_num at hlim
  rw [one_div]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with d hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have h1 : 1 - (d : ℝ)⁻¹ = (d - 1) / d := by field_simp
  change (1 : ℝ) / (1 + M / (1 - (d : ℝ)⁻¹) ^ 2) = slatkinFST d M
  rw [slatkinFST_eq hd hM, h1]
  field_simp

end MathlibExt.Biology.PopulationGenetics.StructuredCoalescent

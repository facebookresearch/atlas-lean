/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics

/-!
# Shift, stem and rerooting invariance of f-statistics in the drift model

In the drift model every f-statistic is a sum over edges of products of weight
differences times edge lengths. Hence f-statistics are unchanged when every weight
vector is shifted by a common vector (more generally, by a common signed shift with
signs `±1`), when the length of an edge traversed equally by all populations changes,
and when binary lineages change by a fixed symmetric difference (as they do when a tree
is rerooted). So on a tree the root position and root-stem length are not identifiable
from `f2`, which is then the unrooted path metric.

## Main results

* `DriftModel.f4_eq_of_weight_eq_mul_add`: invariance under a common signed shift.
* `DriftModel.f4_eq_of_weight_eq_add`, `DriftModel.f2_eq_of_weight_eq_add`,
  `DriftModel.f3_eq_of_weight_eq_add`: common-shift invariance.
* `DriftModel.f4_eq_of_len_eq_of_weight_const`: stem invariance.
* `DriftModel.f4_eq_of_lineage_eq_symmDiff`, `DriftModel.f2_eq_of_lineage_eq_symmDiff`:
  rerooting invariance.

## References

* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192 (2012),
  1065–1093 (additivity of f2 branch lengths on a tree).
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped symmDiff

namespace MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

variable {Ω Ω' P E : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {μ' : Measure Ω'} [Fintype E]

/-- f-statistics see the weight vectors only up to a common signed shift: if two drift models
(possibly on different probability spaces) have the same edge lengths and
`w' X e = s e * w X e + c e` with `s e = ± 1` for every population `X`, then every `f4`
agrees. -/
theorem f4_eq_of_weight_eq_mul_add (M : DriftModel μ E P) (M' : DriftModel μ' E P)
    (hlen : M'.len = M.len) (s c : E → ℝ) (hs : ∀ e, s e = 1 ∨ s e = -1)
    (hw : ∀ X e, M'.weight X e = s e * M.weight X e + c e) (A B C D : P) :
    f4 μ' M'.freq A B C D = f4 μ M.freq A B C D := by
  rw [M'.f4_freq, M.f4_freq, hlen]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hs2 : s e * s e = 1 := by rcases hs e with h | h <;> rw [h] <;> norm_num
  simp only [hw]
  linear_combination ((M.weight A e - M.weight B e) * (M.weight C e - M.weight D e) * M.len e) *
    hs2

/-- Common-shift invariance: replacing every weight vector `w X` by `w X + c` for one vector `c`
leaves every `f4` unchanged. -/
theorem f4_eq_of_weight_eq_add (M : DriftModel μ E P) (M' : DriftModel μ' E P)
    (hlen : M'.len = M.len) (c : E → ℝ) (hw : ∀ X, M'.weight X = M.weight X + c)
    (A B C D : P) : f4 μ' M'.freq A B C D = f4 μ M.freq A B C D :=
  f4_eq_of_weight_eq_mul_add M M' hlen (fun _ => 1) c (fun _ => Or.inl rfl)
    (fun X e => by simp [hw X]) A B C D

/-- Common-shift invariance of `f2`. -/
theorem f2_eq_of_weight_eq_add (M : DriftModel μ E P) (M' : DriftModel μ' E P)
    (hlen : M'.len = M.len) (c : E → ℝ) (hw : ∀ X, M'.weight X = M.weight X + c) (X Y : P) :
    f2 μ' M'.freq X Y = f2 μ M.freq X Y := by
  rw [f2_eq_f4, f2_eq_f4, f4_eq_of_weight_eq_add M M' hlen c hw]

/-- Common-shift invariance of `f3`. -/
theorem f3_eq_of_weight_eq_add (M : DriftModel μ E P) (M' : DriftModel μ' E P)
    (hlen : M'.len = M.len) (c : E → ℝ) (hw : ∀ X, M'.weight X = M.weight X + c) (C A B : P) :
    f3 μ' M'.freq C A B = f3 μ M.freq C A B := by
  rw [f3_eq_f4, f3_eq_f4, f4_eq_of_weight_eq_add M M' hlen c hw]

/-- Stem invariance: changing the length of edges whose weight is the same for every population
(on a rooted tree, the root stem above the most recent common ancestor) leaves every `f4`
unchanged, so such lengths are not identifiable from f-statistics. -/
theorem f4_eq_of_len_eq_of_weight_const (M : DriftModel μ E P) (M' : DriftModel μ' E P)
    (hw : M'.weight = M.weight)
    (hlen : ∀ e, M'.len e ≠ M.len e → ∀ X Y, M.weight X e = M.weight Y e) (A B C D : P) :
    f4 μ' M'.freq A B C D = f4 μ M.freq A B C D := by
  rw [M'.f4_freq, M.f4_freq, hw]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : M'.len e = M.len e
  · rw [he]
  · rw [hlen e he A B]
    ring

/-- Rerooting invariance: if two binary-loading models with the same edge lengths have lineage
sets differing by a fixed edge set `R` (`lineage' X = lineage X ∆ R`; rerooting a tree at a
vertex `v` reverses exactly the edges `R` on the old-root–`v` path), then every `f4` agrees. -/
theorem f4_eq_of_lineage_eq_symmDiff [DecidableEq E] (M : DriftModel μ E P)
    (M' : DriftModel μ' E P) (hM : M.HasBinaryLoadings) (hM' : M'.HasBinaryLoadings)
    (hlen : M'.len = M.len) (R : Finset E) (hL : ∀ X, M'.lineage X = M.lineage X ∆ R)
    (A B C D : P) : f4 μ' M'.freq A B C D = f4 μ M.freq A B C D := by
  refine f4_eq_of_weight_eq_mul_add M M' hlen (fun e => if e ∈ R then -1 else 1)
    (fun e => if e ∈ R then 1 else 0) (fun e => by by_cases h : e ∈ R <;> simp [h]) ?_ A B C D
  intro X e
  have hmem := congrArg (e ∈ ·) (hL X)
  simp only [lineage, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    eq_iff_iff] at hmem
  rcases hM X e with h | h <;> rcases hM' X e with h' | h' <;> by_cases hR : e ∈ R <;>
    simp_all

/-- Rerooting invariance of `f2`: invariance under the symmetric-difference change of
lineages above. When the lineages come from rerooting a tree this says `f2` does not see
the root position; for general binary loadings no path-metric conclusion is claimed. -/
theorem f2_eq_of_lineage_eq_symmDiff [DecidableEq E] (M : DriftModel μ E P)
    (M' : DriftModel μ' E P) (hM : M.HasBinaryLoadings) (hM' : M'.HasBinaryLoadings)
    (hlen : M'.len = M.len) (R : Finset E) (hL : ∀ X, M'.lineage X = M.lineage X ∆ R)
    (X Y : P) : f2 μ' M'.freq X Y = f2 μ M.freq X Y := by
  rw [f2_eq_f4, f2_eq_f4, f4_eq_of_lineage_eq_symmDiff M M' hM hM' hlen R hL]

end MathlibExt.Biology.PopulationGenetics.FStatistics.DriftModel

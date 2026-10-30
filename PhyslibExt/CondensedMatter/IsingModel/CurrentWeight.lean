/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.RandomCurrent
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.TwoReplica
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRep
public import PhyslibExt.CondensedMatter.IsingModel.AizenmanInclusionExclusion
public import PhyslibExt.CondensedMatter.IsingModel.AizenmanTrueBackbone
public import PhyslibExt.CondensedMatter.IsingModel.AizenmanHdom

/-!
# Factorization of current weights across a cut

Current weights and source sets split along a vertex set closed under the edges.

## i. Overview

For a set `S` of sites such that every edge lies inside `S` or inside its complement, a current
splits into its restrictions to the two sides, its weight factorizes, and its source set is the
disjoint union of the two source sets. The file also expresses ratios of current sums through
correlations.

## ii. Key results

- `StatMech.Ising.acwRestrict` : restriction of a current to an edge predicate
- `StatMech.Ising.acw_weight_factor_cut` : factorization of the weight
- `StatMech.Ising.acw_sources_partition` : sources split across a closed cut
- `StatMech.Ising.acw_currentSum_ratio` : ratios of current sums

## iii. Table of contents

- A. Restriction to a cut
- B. Weights
- C. Sources
- D. Current sums

## iv. References

- M. Aizenman, *Geometric analysis of φ⁴ fields and Ising models. Parts I and II*, Comm. Math. Phys.
  86 (1982) 1–48
-/

@[expose] public section

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Restriction to a cut -/

/-- The restriction of the current `n` to the edges satisfying `p` (zero elsewhere). -/
noncomputable def acwRestrict (p : Sym2 V → Prop) [DecidablePred p] (n : Current V) : Current V :=
  fun e => if p e then n e else 0

/-- Both endpoints of `e` lie in `S`. -/
def acwInternal (S : Finset V) (e : Sym2 V) : Prop := ∀ z ∈ e, z ∈ S

/-- Being an internal edge of `S` is decidable. -/
instance (S : Finset V) : DecidablePred (acwInternal S) := fun e => by
  unfold acwInternal; infer_instance

/-- Every edge of `G` lies inside `S` or inside its complement. -/
def acwClosedCut (S : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, acwInternal S e ∨ acwInternal Sᶜ e

/-! ## B. Weights -/

omit [DecidableEq V] in
lemma acw_weight_restrict (β : ℝ) (J : Sym2 V → ℝ) (p : Sym2 V → Prop) [DecidablePred p]
    (n : Current V) :
    weight G β J (acwRestrict p n)
      = ∏ e ∈ G.edgeFinset.filter p, (β * J e) ^ (n e) / (Nat.factorial (n e)) := by
  unfold weight acwRestrict
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset p]
  rw [show (∏ e ∈ G.edgeFinset.filter (fun e => ¬ p e),
        (β * J e) ^ (if p e then n e else 0) / (Nat.factorial (if p e then n e else 0))) = 1 from
      Finset.prod_eq_one (fun e he => by rw [Finset.mem_filter] at he; simp [he.2])]
  rw [mul_one]
  refine Finset.prod_congr rfl (fun e he => by rw [Finset.mem_filter] at he; simp [he.2])

omit [DecidableEq V] in
lemma acw_weight_factor (β : ℝ) (J : Sym2 V → ℝ) (p : Sym2 V → Prop) [DecidablePred p]
    (n : Current V) :
    weight G β J n = weight G β J (acwRestrict p n) * weight G β J (acwRestrict (fun e => ¬ p e) n)
        := by
  rw [acw_weight_restrict, acw_weight_restrict]
  rw [show weight G β J n = ∏ e ∈ G.edgeFinset, (β * J e) ^ (n e) / (Nat.factorial (n e)) from rfl]
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset p
        (fun e => (β * J e) ^ (n e) / (Nat.factorial (n e)))]

lemma acw_weight_factor_cut (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (n : Current V) :
    weight G β J n
      = weight G β J (acwRestrict (acwInternal S) n)
        * weight G β J (acwRestrict (fun e => ¬ acwInternal S e) n) :=
  acw_weight_factor G β J (acwInternal S) n

/-! ## C. Sources -/

lemma acw_incidentFlux_internal_mem (S : Finset V) (hcut : acwClosedCut G S) (n : Current V)
    {x : V} (hx : x ∈ S) :
    Sharpness.incidentFlux G (acwRestrict (acwInternal S) n) x = Sharpness.incidentFlux G n x := by
  unfold Sharpness.incidentFlux acwRestrict
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter] at he
  obtain ⟨heG, hxe⟩ := he
  by_cases hint : acwInternal S e
  · simp [hint]
  · exfalso
    rcases hcut e heG with h | h
    · exact hint h
    · exact (Finset.mem_compl.1 (h x hxe)) hx

lemma acw_incidentFlux_internal_not_mem (S : Finset V) (n : Current V)
    {x : V} (hx : x ∉ S) :
    Sharpness.incidentFlux G (acwRestrict (acwInternal S) n) x = 0 := by
  unfold Sharpness.incidentFlux acwRestrict
  refine Finset.sum_eq_zero (fun e he => ?_)
  rw [Finset.mem_filter] at he
  obtain ⟨heG, hxe⟩ := he
  by_cases hint : acwInternal S e
  · exact absurd (hint x hxe) hx
  · simp [hint]

lemma acw_sources_internal_eq (S : Finset V) (hcut : acwClosedCut G S) (n : Current V) :
    Sharpness.sources G (acwRestrict (acwInternal S) n) = (Sharpness.sources G n) ∩ S := by
  ext x
  rw [Sharpness.mem_sources, Finset.mem_inter, Sharpness.mem_sources]
  by_cases hx : x ∈ S
  · rw [acw_incidentFlux_internal_mem G S hcut n hx]; simp [hx]
  · rw [acw_incidentFlux_internal_not_mem G S n hx]; simp [hx]

lemma acw_sources_external_eq (S : Finset V) (hcut : acwClosedCut G S) (n : Current V) :
    Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = (Sharpness.sources G n) ∩ Sᶜ := by
  have hcut' : acwClosedCut G Sᶜ := by
    intro e he
    rcases hcut e he with h | h
    · right; rwa [compl_compl]
    · left; exact h
  exact acw_sources_internal_eq G Sᶜ hcut' n

lemma acw_sources_partition (S : Finset V) (hcut : acwClosedCut G S) (n : Current V) :
    Sharpness.sources G n
      = Sharpness.sources G (acwRestrict (acwInternal S) n) ∪ Sharpness.sources G (acwRestrict
          (acwInternal Sᶜ) n)
    ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n))
        (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) := by
  rw [acw_sources_internal_eq G S hcut n, acw_sources_external_eq G S hcut n]
  refine ⟨?_, ?_⟩
  · rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  · exact Finset.disjoint_left.2 (fun a ha hb =>
      (Finset.mem_compl.1 (Finset.mem_inter.1 hb).2) (Finset.mem_inter.1 ha).2)

/-! ## D. Current sums -/

/-- `Z_A = ⟨σ_A⟩ Z_∅`. -/
lemma acw_currentSum_eq_expectation (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
    Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ :=
        by
  rw [Sharpness.current_representation, div_mul_cancel₀ _ h0]

lemma acw_currentSum_ratio (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) (hA : Sharpness.expectationJ G β J A ≠ 0) :
    Sharpness.currentSum G β J B
      = (Sharpness.expectationJ G β J B / Sharpness.expectationJ G β J A)
        * Sharpness.currentSum G β J A := by
  rw [acw_currentSum_eq_expectation G β J B h0, acw_currentSum_eq_expectation G β J A h0]
  field_simp

open StatMech.Sharpness.RandomCurrent

end Ising

end StatMech

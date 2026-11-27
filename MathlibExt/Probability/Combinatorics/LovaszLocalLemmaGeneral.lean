/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith

/-!
# The general (asymmetric) Lovász local lemma

For a finite family of bad events with a dependency graph, `lovasz_local_lemma_general_finite`
gives a lower bound on the probability of avoiding every event, namely `∏ i, (1 - x i)`.
Inclusion–exclusion gives independence from the complements of non-neighbours. Induction then
bounds the loss in avoidance probability from adding each event.
-/

@[expose] public section

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemmaGeneralWanted

section

variable {I Ω : Type*}

private lemma mem_finset_inf [DecidableEq Ω] [Fintype Ω] (B : I → Finset Ω) (S : Finset I)
    (ω : Ω) : ω ∈ S.inf B ↔ ∀ j ∈ S, ω ∈ B j := by
  simpa only [← Finset.singleton_subset_iff] using
    (Finset.le_inf_iff (a := {ω}) (s := S) (f := B))

-- Inclusion–exclusion extends a factorization on intersections to one on complements.
private lemma factor_avoidance [DecidableEq Ω] [Fintype Ω] (B : I → Finset Ω) (N : Finset I)
    (w pmf : Ω → ℝ) (p : ℝ)
    (h : ∀ T ⊆ N, ∑ ω ∈ T.inf B, w ω = p * ∑ ω ∈ T.inf B, pmf ω) :
    ∑ ω ∈ N.inf (fun j ↦ (B j)ᶜ), w ω = p * ∑ ω ∈ N.inf (fun j ↦ (B j)ᶜ), pmf ω := by
  rw [inclusion_exclusion_sum_inf_compl, inclusion_exclusion_sum_inf_compl, mul_sum]
  refine sum_congr rfl fun T hT ↦ ?_
  rw [h T (mem_powerset.mp hT), mul_smul_comm]

-- Multiply the one-event estimates while adjoining the elements of D one at a time.
private lemma prod_mul_le_union [DecidableEq I] (q : Finset I → ℝ) (x : I → ℝ)
    (hx1 : ∀ i, x i < 1) (D N : Finset I) (hd : Disjoint D N)
    (step : ∀ T ⊂ D ∪ N, ∀ j ∉ T, (1 - x j) * q T ≤ q (insert j T)) :
    (∏ j ∈ D, (1 - x j)) * q N ≤ q (D ∪ N) := by
  refine Finset.induction_on' (motive := fun R ↦ (∏ j ∈ R, (1 - x j)) * q N ≤ q (R ∪ N))
    D (by simp) ?_
  intro j R hj hR hjR ih
  have hjRN : j ∉ R ∪ N := by
    simp [hjR, Finset.disjoint_left.mp hd hj]
  have hlt := (ssubset_iff_of_subset (union_subset_union_left (t := N) hR)).2
    ⟨j, mem_union_left _ hj, hjRN⟩
  rw [prod_insert hjR, mul_assoc, insert_union]
  exact (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hx1 j).le)).trans (step _ hlt j hjRN)

-- The loss from adjoining i is controlled by the mass avoiding its non-neighbours.
private lemma avoidance_bound [Fintype I] [DecidableEq I] (G : SimpleGraph I)
    [DecidableRel G.Adj] (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (q : Finset I → ℝ) (hq : ∀ S, 0 ≤ q S) (h_empty : q ∅ = 1)
    (loss : ∀ S : Finset I, ∀ i ∉ S, q S - q (insert i S) ≤
      (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) * q (S \ G.neighborFinset i)) :
    ∏ i, (1 - x i) ≤ q univ := by
  have step (S : Finset I) : ∀ i ∉ S, (1 - x i) * q S ≤ q (insert i S) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro i hi
      let D := S ∩ G.neighborFinset i
      let N := S \ G.neighborFinset i
      have hDN : D ∪ N = S := (union_comm D N).trans (sdiff_union_inter ..)
      have hd : Disjoint D N := Finset.disjoint_sdiff.mono_left inter_subset_right
      have hchain := prod_mul_le_union q x hx1 D N hd (by rwa [hDN])
      rw [hDN] at hchain
      have hprod : (∏ j ∈ G.neighborFinset i, (1 - x j)) ≤ ∏ j ∈ D, (1 - x j) :=
        prod_le_prod_of_subset_of_le_one₀ inter_subset_right
          (fun j _ ↦ sub_nonneg.mpr (hx1 j).le) (fun j _ _ ↦ sub_le_self _ (hx0 j))
      have hbound : q S - q (insert i S) ≤ x i * q S := calc
        _ ≤ _ := loss S i hi
        _ = x i * ((∏ j ∈ G.neighborFinset i, (1 - x j)) * q N) := mul_assoc ..
        _ ≤ x i * q S := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right hprod (hq N)).trans hchain) (hx0 i)
      linarith only [hbound]
  simpa [h_empty] using prod_mul_le_union q x hx1 univ ∅ (by simp) (fun T _ ↦ step T)

end

/-- **Lovász local lemma, general form.** Let `pmf` be a probability mass function on a finite
set `Ω`, let `(Aᵢ)_{i ∈ I}` be finitely many events and `G` a graph on `I` such that, for every
`i` and every set `S` of indices that are neither `i` nor neighbours of `i`,
`P(Aᵢ ∩ ⋂_{j ∈ S} Aⱼ) = P(Aᵢ) P(⋂_{j ∈ S} Aⱼ)`. If `x : I → [0, 1)` satisfies
`P(Aᵢ) ≤ xᵢ ∏_{j ~ i} (1 - xⱼ)` for all `i`, then the probability that no `Aᵢ` occurs is at least
`∏ᵢ (1 - xᵢ)` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019,
Theorem 6.10, with mutual independence as in Definition 6.2; the hypothesis on intersections
of the `Aⱼ` with all `S` is the form used in `lovasz_local_lemma_symmetric_finite`). -/
theorem lovasz_local_lemma_general_finite {Ω I : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] (pmf : Ω → ℝ) (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
    (hpmf_sum : ∑ ω : Ω, pmf ω = 1) (A : I → Set Ω) (G : SimpleGraph I) [DecidableRel G.Adj]
    (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) →
      ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
        (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
          (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hA : ∀ i, ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤
      x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ ∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0) := by
  classical
  let B (i : I) := (A i).toFinset
  let avoid (S : Finset I) := S.inf fun j ↦ (B j)ᶜ
  let q (S : Finset I) := ∑ ω ∈ avoid S, pmf ω
  have hq (S : Finset I) : 0 ≤ q S := sum_nonneg fun ω _ ↦ hpmf_nonneg ω
  have h_empty : q ∅ = 1 := by simpa [q, avoid] using hpmf_sum
  have h := avoidance_bound G x hx0 hx1 q hq h_empty (by
    intro S i hi
    let N := S \ G.neighborFinset i
    let w (ω : Ω) := if ω ∈ B i then pmf ω else 0
    have havoid : avoid (insert i S) = avoid S \ B i := by
      simp [avoid, Finset.sdiff_eq_inter_compl, inf_comm]
    have hloss : q S - q (insert i S) = ∑ ω ∈ avoid S, w ω := by
      simp only [q, havoid, w, sum_ite_mem]
      linarith [sum_inter_add_sum_sdiff (avoid S) (B i) pmf]
    rw [hloss]
    calc
      _ ≤ ∑ ω ∈ avoid N, w ω :=
        sum_le_sum_of_subset_of_nonneg (Finset.inf_mono sdiff_subset)
          (fun ω _ _ ↦ by
            dsimp [w]
            split <;> simp [hpmf_nonneg])
      _ = (∑ ω, w ω) * q N := by
        apply factor_avoidance B N w pmf
        intro T hT
        have hdis (j : I) (hj : j ∈ T) : j ∉ insert i (G.neighborSet i) := by
          obtain ⟨hjS, hjN⟩ := mem_sdiff.mp (hT hj)
          have hne : j ≠ i := fun e ↦ hi (e ▸ hjS)
          exact fun h ↦ (Set.mem_insert_iff.mp h).elim hne
            (fun hadj ↦ hjN ((G.mem_neighborFinset i j).2 hadj))
        rw [← sum_ite_mem_eq (T.inf B) w, ← sum_ite_mem_eq (T.inf B) pmf]
        simpa only [mem_finset_inf, w, B, Set.mem_toFinset, ← ite_and, and_comm] using
          hDep i T hdis
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa [w, B] using hA i) (hq N))
  change _ ≤ ∑ ω ∈ avoid univ, pmf ω at h
  rw [← sum_ite_mem_eq (avoid univ) pmf] at h
  simpa only [avoid, mem_finset_inf, Finset.mem_compl,
    B, Set.mem_toFinset, Finset.mem_univ, true_imp_iff] using h

end MathlibExt.Probability.Combinatorics.LovaszLocalLemmaGeneralWanted

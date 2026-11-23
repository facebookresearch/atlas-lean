/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.CurrentRep

/-!
# Random-current representation at zero field

Zero-field Ising correlations as ratios of random-current partition sums, written with explicit
`β`-weights.

## i. Overview

The random-current representation expresses `⟨σ_A⟩_{β,0}` as `Z(∂ = A)/Z(∂ = ∅)`, where `Z(∂ = A)`
sums the weights `∏_e β^{n_e}/n_e!` over currents `n` whose odd-degree vertices form `A`. This file
unfolds that sum over edge-indexed currents and records positivity of the denominator.

## ii. Key results

- `gc_ergrep_betaWeight` : zero-field correlations as a ratio of explicit `β`-weighted current sums
- `gc_ergrep_denom_pos` : positivity of the sourceless current sum

## iii. Table of contents

- A. Explicit current sums

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48

-/

@[expose] public section

open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Explicit current sums -/

lemma gc_ergrep_currentSum_eq_betaWeight (β : ℝ) (A : Finset V) :
    currentSum G β (fun _ => 1) A
      = ∑' m : ↥G.edgeFinset → ℕ,
          if sources G (ofEdgeFun G m) = A then
            (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0 := by
  unfold currentSum
  refine tsum_congr (fun m => ?_)
  by_cases h : sources G (ofEdgeFun G m) = A
  · rw [ite_eq_left h, ite_eq_left h, weight_ofEdgeFun]
    exact Finset.prod_congr rfl (fun e _ => by rw [mul_one])
  · rw [ite_eq_right h, ite_eq_right h]

lemma gc_ergrep_betaWeight (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
      = (∑' m : ↥G.edgeFinset → ℕ,
            if sources G (ofEdgeFun G m) = A then
              (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0)
        / (∑' m : ↥G.edgeFinset → ℕ,
            if sources G (ofEdgeFun G m) = ∅ then
              (∏ e : ↥G.edgeFinset, β ^ (m e) / (Nat.factorial (m e))) else 0) := by
  rw [isingExpectation_eq_currentSum_ratio, gc_ergrep_currentSum_eq_betaWeight,
      gc_ergrep_currentSum_eq_betaWeight]

lemma gc_ergrep_denom_pos (β : ℝ) : 0 < currentSum G β (fun _ => 1) ∅ := by
  have hP : partitionJ G β (fun _ => 1)
      = (2 : ℝ) ^ (Fintype.card V) * currentSum G β (fun _ => 1) ∅ :=
    partitionJ_eq_currentSum G β (fun _ => 1)
  have hPpos : 0 < partitionJ G β (fun _ => 1) := partitionJ_pos G β (fun _ => 1)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card V) := by positivity
  rw [hP] at hPpos
  exact (pos_iff_pos_of_mul_pos hPpos).mp h2

end StatMech.Walls

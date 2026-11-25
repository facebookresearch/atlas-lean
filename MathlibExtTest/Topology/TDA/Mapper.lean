/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.Mapper

@[expose] public section

open MathlibExt.Topology.TDA

/-- Every point of a preimage lies in some cluster, so the Mapper vertices cover the data. -/
example (d : ℝ → ℝ → ℝ) (U : Bool → Set ℝ) (x : ℝ) (b : Bool) (hx : x ∈ U b) :
    ∃ C ∈ slClusters d 1 (id ⁻¹' U b), x ∈ C :=
  exists_mem_slClusters hx

/-- With a cover by two sets, the Mapper complex has dimension at most one. -/
example (d : ℝ → ℝ → ℝ) (U : Bool → Set ℝ) {σ} (hσ : σ ∈ mapper d 1 id U) : σ.card ≤ 2 :=
  mapper_card_le (n := 1) (fun s _ => (Finset.card_le_univ s).trans (by simp)) hσ

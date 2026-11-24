/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.DecompositionSubgroup

@[expose] public section

example (p : ℕ) [Fact p.Prime] :
    ((padicPlace p).decompositionSubgroup ℚ
        : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      ≤ (MonoidHom.range (localGaloisToGlobal p)).topologicalClosure :=
  ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
    p

example (τ : PadicAlgCl 2 ≃ₐ[ℚ_[2]] PadicAlgCl 2) :
    localGaloisToGlobal 2 τ ∈ (padicPlace 2).decompositionSubgroup ℚ :=
  localGaloisToGlobal_mem_decompositionSubgroup 2 τ

example : (1 : AlgebraicClosure ℚ) ∈ padicPlace 2 := by
  rw [mem_padicPlace_iff]
  simp

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortCoordinateCertificates

/-! Sparse multiplication by the actual integer Leech basis omits only its zero entries.
The universal equality preserves every integer coordinate certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Multiply by the genuine Leech basis, summing its nonzero integer entries on each row. -/
def generatedNinthShortSparseBasisMul (c : Fin 24 → ℤ) (i : Fin 24) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin 24 => leechBasisMatrix i j ≠ 0),
    leechBasisMatrix i j * c j

/-- Sparse multiplication equals the actual full basis multiplication on every integer vector. -/
theorem generatedNinth_short_sparse_basis_mul (c : Fin 24 → ℤ) :
    generatedNinthShortSparseBasisMul c = leechBasisMatrix *ᵥ c := by
  funext i
  simp only [generatedNinthShortSparseBasisMul, Finset.sum_filter, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : leechBasisMatrix i j = 0 <;> simp [h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

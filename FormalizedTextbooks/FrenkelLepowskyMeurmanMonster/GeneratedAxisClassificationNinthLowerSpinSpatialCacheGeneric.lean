/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric

/-! Complete integer matrix and coordinate replay for sparse spatial factor caches. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- A sparse row retains every source column, including repeated indices and zero coefficients. -/
def generatedNinthLowerSpinSpatialFourMatrix
    (p : Fin 24 → Fin 4 → Fin 24) (c : Fin 24 → Fin 4 → ℤ) :
    Matrix (Fin 24) (Fin 24) ℤ :=
  fun j k => ∑ z : Fin 4, if k = p j z then c j z else 0

/-- The complete sparse matrix acts by precisely its four original source terms. -/
theorem generatedNinth_lower_spin_spatial_four_matrix_action
    (p : Fin 24 → Fin 4 → Fin 24) (c : Fin 24 → Fin 4 → ℤ)
    (v : Fin 24 → ℤ) (j : Fin 24) :
    ((generatedNinthLowerSpinSpatialFourMatrix p c) *ᵥ v) j =
      ∑ z : Fin 4, c j z * v (p j z) := by
  change (∑ k : Fin 24, (∑ z : Fin 4, if k = p j z then c j z else 0) * v k) = _
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp

/-- All original packed coordinates follow from all original signed-digit equations. -/
theorem generatedNinth_lower_spin_spatial_coordinates_of_digits
    (w : Fin 4 → Fin 16 → Fin 16 → ℕ) (t : Fin 16 → Fin 16 → ℕ)
    (c : Fin 4 → ℤ)
    (h : ∀ b a i : Fin 16,
      (∑ z : Fin 4, c z * generatedRootEightPackedSignedDigit (w z b a) i) =
        generatedRootEightPackedSignedDigit (t b a) i) (n : Fin 4096) :
    (∑ z : Fin 4, c z * generatedNinthLowerSpinTensorPackedCoordinate (w z) n) =
      generatedNinthLowerSpinTensorPackedCoordinate t n := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hn : n = generatedNinthLowerSpinPackedPrefixIndex a i := by
    apply Fin.ext
    dsimp [generatedNinthLowerSpinPackedPrefixIndex, a, i]
    omega
  rw [hn]
  simp_rw [generatedNinth_lower_spin_packed_prefix_coordinate]
  exact h _ _ i

/-- Exact full matrix prefixes and full integer coordinate steps identify every cached vector. -/
theorem generatedNinth_lower_spin_spatial_integer_cache_replay
    (k : ℕ) (C F : ℕ → Matrix (Fin 24) (Fin 24) ℤ)
    (V : ℕ → Fin 4096 → Fin 24 → ℤ) (input : Fin 4096 → Fin 24 → ℤ)
    (hc0 : C 0 = 1) (hv0 : ∀ n, V 0 n = input n)
    (hc : ∀ s, s < k → C (s + 1) = F s * C s)
    (hv : ∀ s, s < k → ∀ n, V (s + 1) n = F s *ᵥ V s n) :
    ∀ s, s ≤ k → ∀ n, V s n = C s *ᵥ input n := by
  intro s
  induction s with
  | zero =>
    intro _ n
    rw [hv0, hc0, Matrix.one_mulVec]
  | succ s ih =>
    intro hs n
    have hsk : s < k := by omega
    rw [hv s hsk n, ih (by omega) n, hc s hsk]
    rw [Matrix.mulVec_mulVec]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InterleavedSequencesTensor

/-! # Tests for interleaved sequences and tensor products of ultrafilters -/

open Filter

namespace MetaMathlibExt.exists_interleaved_sequences_iff_mem_tensor

-- A set in the tensor square `U ⊗ U` of a non-principal ultrafilter contains interleaved
-- sequences: take `V₁ = V₂ = U`.
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (X : Set (ℕ × ℕ))
    (hX : {n | {m | (n, m) ∈ X} ∈ U} ∈ U) :
    ∃ a b : ℕ → ℕ, StrictMono a ∧ StrictMono b ∧ Disjoint (Set.range a) (Set.range b) ∧
      (∀ i j, i ≤ j → (a i, b j) ∈ X) ∧ (∀ i j, j < i → (b j, a i) ∈ X) :=
  (exists_interleaved_sequences_iff_mem_tensor X).2 ⟨U, U, hU, hU, hX, hX⟩

-- The pairs of numbers of different parities: the even numbers `2 i` and the odd numbers `2 j + 1`
-- interleave, so this set lies in `V₁ ⊗ V₂` and in `V₂ ⊗ V₁` for some non-principal `V₁`, `V₂`.
example : ∃ V₁ V₂ : Ultrafilter ℕ, (V₁ : Filter ℕ) ≤ cofinite ∧ (V₂ : Filter ℕ) ≤ cofinite ∧
    {n | {m | n % 2 ≠ m % 2} ∈ V₂} ∈ V₁ ∧ {n | {m | n % 2 ≠ m % 2} ∈ V₁} ∈ V₂ :=
  (exists_interleaved_sequences_iff_mem_tensor {p | p.1 % 2 ≠ p.2 % 2}).1
    ⟨fun i => 2 * i, fun j => 2 * j + 1, fun _ _ h => by dsimp only; omega,
      fun _ _ h => by dsimp only; omega,
      Set.disjoint_left.2 fun _ ⟨i, hi⟩ ⟨j, hj⟩ => by dsimp only at hi hj; omega,
      fun i j _ => show 2 * i % 2 ≠ (2 * j + 1) % 2 by omega,
      fun i j _ => show (2 * j + 1) % 2 ≠ 2 * i % 2 by omega⟩

-- No tensor square `U ⊗ U` contains that set, so the two ultrafilters above must differ.
example (U : Ultrafilter ℕ) : {n | {m | n % 2 ≠ m % 2} ∈ U} ∉ U := by
  intro h
  rcases U.mem_or_compl_mem {m | m % 2 = 0} with hE | hE
  · obtain ⟨n, hn, hnE⟩ := U.nonempty_of_mem (inter_mem h hE)
    obtain ⟨m, hm, hmE⟩ := U.nonempty_of_mem (inter_mem hn hE)
    simp only [Set.mem_ofPred_eq] at hnE hm hmE
    omega
  · obtain ⟨n, hn, hnE⟩ := U.nonempty_of_mem (inter_mem h hE)
    obtain ⟨m, hm, hmE⟩ := U.nonempty_of_mem (inter_mem hn hE)
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hnE hm hmE
    omega

-- The strict lower triangle has finite sections `{m | m < n}`, so it lies in no `V₁ ⊗ V₂` with
-- `V₂` non-principal; hence it contains no interleaved sequences.
example : ¬∃ a b : ℕ → ℕ, StrictMono a ∧ StrictMono b ∧ Disjoint (Set.range a) (Set.range b) ∧
    (∀ i j, i ≤ j → (a i, b j) ∈ {p : ℕ × ℕ | p.2 < p.1}) ∧
    (∀ i j, j < i → (b j, a i) ∈ {p : ℕ × ℕ | p.2 < p.1}) := by
  rw [exists_interleaved_sequences_iff_mem_tensor]
  rintro ⟨V₁, V₂, -, hV₂, h₁₂, -⟩
  obtain ⟨n, hn⟩ := V₁.nonempty_of_mem h₁₂
  exact Ultrafilter.compl_mem_iff_notMem.1 (hV₂ (Set.finite_lt_nat n).compl_mem_cofinite) hn

end MetaMathlibExt.exists_interleaved_sequences_iff_mem_tensor

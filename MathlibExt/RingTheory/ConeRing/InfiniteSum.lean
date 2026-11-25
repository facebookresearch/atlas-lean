/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.ConeRing
public import Mathlib.Algebra.Ring.Pi

/-!
# The literal Wagoner infinite-sum endomorphism

The endomorphism repeats the original matrix along a countable block diagonal
and reindexes it using the original countable pairing. The block-sum operation
uses the independently constructed first and successor block injections.
Their actual entries prove `A ⊕ A∞ = A∞`, with the same original matrix,
inclusions, projections and copy indices.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

namespace ConeRing

open Matrix.LocallyFinite

variable {R : Type uR} {S : Type uS}

/-- The actual countable repeated block diagonal endomorphism of the original cone ring. -/
def infinityHom (R : Type uR) [Semiring R] : ConeRing R →+* ConeRing R :=
  (reindexRingEquiv (R := R) Nat.pairEquiv).toRingHom.comp
    (blockDiagonalRingHom.comp (Pi.constRingHom ℕ (ConeRing R)))

/-- Every repeated block entry retains the actual original matrix coefficient. -/
theorem infinityHom_apply_pair [Semiring R] (A : ConeRing R) (k i l j : ℕ) :
    infinityHom R A (Nat.pair k i) (Nat.pair l j) = if k = l then A i j else 0 := by
  change blockDiagonal (fun _ : ℕ => A)
    (Nat.unpair (Nat.pair k i)) (Nat.unpair (Nat.pair l j)) = _
  rw [Nat.unpair_pair, Nat.unpair_pair]
  by_cases h : k = l <;> simp [blockDiagonal_apply, h]

/-- The arbitrary original coefficient reader uses the actual unpaired copy and row indices. -/
theorem infinityHom_apply [Semiring R] (A : ConeRing R) (i j : ℕ) :
    infinityHom R A i j =
      if i.unpair.1 = j.unpair.1 then A i.unpair.2 j.unpair.2 else 0 := by
  simpa only [Nat.pair_unpair] using
    infinityHom_apply_pair A i.unpair.1 i.unpair.2 j.unpair.1 j.unpair.2

private theorem blockSum_first_tail [Semiring R] (A B : ConeRing R) (i j : ℕ) :
    blockSumHom R (A, B) (firstEmbedding i) (tailEmbedding j) = 0 := by
  have hi : firstEmbedding i ∉ Set.range tailEmbedding :=
    fun h => Set.disjoint_left.mp ranges_disjoint (Set.mem_range_self i) h
  have hj : tailEmbedding j ∉ Set.range firstEmbedding :=
    fun h => Set.disjoint_left.mp ranges_disjoint.symm (Set.mem_range_self j) h
  change extend firstEmbedding firstEmbedding A (firstEmbedding i) (tailEmbedding j) +
    extend tailEmbedding tailEmbedding B (firstEmbedding i) (tailEmbedding j) = 0
  rw [extend_apply_of_notMem_column_range _ _ A _ _ hj,
    extend_apply_of_notMem_row_range _ _ B _ _ hi, zero_add]

private theorem blockSum_tail_first [Semiring R] (A B : ConeRing R) (i j : ℕ) :
    blockSumHom R (A, B) (tailEmbedding i) (firstEmbedding j) = 0 := by
  have hi : tailEmbedding i ∉ Set.range firstEmbedding :=
    fun h => Set.disjoint_left.mp ranges_disjoint.symm (Set.mem_range_self i) h
  have hj : firstEmbedding j ∉ Set.range tailEmbedding :=
    fun h => Set.disjoint_left.mp ranges_disjoint (Set.mem_range_self j) h
  change extend firstEmbedding firstEmbedding A (tailEmbedding i) (firstEmbedding j) +
    extend tailEmbedding tailEmbedding B (tailEmbedding i) (firstEmbedding j) = 0
  rw [extend_apply_of_notMem_row_range _ _ A _ _ hi,
    extend_apply_of_notMem_column_range _ _ B _ _ hj, zero_add]

/-- The block-sum operation absorbs the independently constructed repeated original matrix. -/
theorem blockSum_infinity [Semiring R] (A : ConeRing R) :
    blockSumHom R (A, infinityHom R A) = infinityHom R A := by
  ext i j
  obtain ⟨⟨k, r⟩, rfl⟩ := Nat.pairEquiv.surjective i
  obtain ⟨⟨l, s⟩, rfl⟩ := Nat.pairEquiv.surjective j
  change blockSumHom R (A, infinityHom R A) (Nat.pair k r) (Nat.pair l s) =
    infinityHom R A (Nat.pair k r) (Nat.pair l s)
  cases k with
  | zero =>
      cases l with
      | zero =>
          calc
            blockSumHom R (A, infinityHom R A) (Nat.pair 0 r) (Nat.pair 0 s) = A r s :=
              blockSumRingHom_apply_left firstEmbedding tailEmbedding
                ranges_disjoint ranges_cover _ r s
            _ = infinityHom R A (Nat.pair 0 r) (Nat.pair 0 s) := by
              simp [infinityHom_apply_pair]
      | succ l =>
          calc
            blockSumHom R (A, infinityHom R A) (Nat.pair 0 r) (Nat.pair (l + 1) s) = 0 := by
              rw [← tailEmbedding_apply_pair l s]
              exact blockSum_first_tail A (infinityHom R A) r (Nat.pair l s)
            _ = infinityHom R A (Nat.pair 0 r) (Nat.pair (l + 1) s) := by
              simp [infinityHom_apply_pair]
  | succ k =>
      cases l with
      | zero =>
          calc
            blockSumHom R (A, infinityHom R A) (Nat.pair (k + 1) r) (Nat.pair 0 s) = 0 := by
              rw [← tailEmbedding_apply_pair k r]
              exact blockSum_tail_first A (infinityHom R A) (Nat.pair k r) s
            _ = infinityHom R A (Nat.pair (k + 1) r) (Nat.pair 0 s) := by
              simp [infinityHom_apply_pair]
      | succ l =>
          calc
            blockSumHom R (A, infinityHom R A)
                (Nat.pair (k + 1) r) (Nat.pair (l + 1) s) =
              infinityHom R A (Nat.pair k r) (Nat.pair l s) := by
              rw [← tailEmbedding_apply_pair k r, ← tailEmbedding_apply_pair l s]
              exact blockSumRingHom_apply_right firstEmbedding tailEmbedding
                ranges_disjoint ranges_cover _ (Nat.pair k r) (Nat.pair l s)
            _ = infinityHom R A (Nat.pair (k + 1) r) (Nat.pair (l + 1) s) := by
              by_cases h : k = l
              · subst l
                simp [infinityHom_apply_pair]
              · simp [infinityHom_apply_pair, h]

/-- The original block sum is exactly the conjugated direct-sum regular-module action. -/
theorem blockSumHom_eq [Semiring R] (A B : ConeRing R) :
    blockSumHom R (A, B) =
      firstInclusion R * A * firstProjection R + tailInclusion R * B * tailProjection R := by
  change extend firstEmbedding firstEmbedding A + extend tailEmbedding tailEmbedding B =
    ((inclusion firstEmbedding).comp A).comp (projection firstEmbedding) +
      ((inclusion tailEmbedding).comp B).comp (projection tailEmbedding)
  rw [inclusion_comp_comp_projection, inclusion_comp_comp_projection]

/-- The repeated original matrix has the literal first-plus-tail decomposition. -/
theorem infinityHom_decomposition [Semiring R] (A : ConeRing R) :
    infinityHom R A = firstInclusion R * A * firstProjection R +
      tailInclusion R * infinityHom R A * tailProjection R :=
  (blockSum_infinity A).symm.trans (blockSumHom_eq A (infinityHom R A))

/-- The actual infinity action intertwines the original first inclusion with the original action. -/
theorem infinity_mul_firstInclusion [Semiring R] (A : ConeRing R) :
    infinityHom R A * firstInclusion R = firstInclusion R * A := by
  rw [infinityHom_decomposition A, add_mul]
  simp only [mul_assoc, firstProjection_mul_firstInclusion, tailProjection_mul_firstInclusion,
    mul_one, mul_zero, add_zero]

/-- The actual infinity action intertwines the original successor inclusion with itself. -/
theorem infinity_mul_tailInclusion [Semiring R] (A : ConeRing R) :
    infinityHom R A * tailInclusion R = tailInclusion R * infinityHom R A := by
  conv_lhs => rw [infinityHom_decomposition A]
  rw [add_mul]
  simp only [mul_assoc, firstProjection_mul_tailInclusion, tailProjection_mul_tailInclusion,
    mul_zero, mul_one, zero_add]

/-- The original first projection intertwines the actual infinity action and original action. -/
theorem firstProjection_mul_infinity [Semiring R] (A : ConeRing R) :
    firstProjection R * infinityHom R A = A * firstProjection R := by
  rw [infinityHom_decomposition A, mul_add]
  simp only [← mul_assoc, firstProjection_mul_firstInclusion, firstProjection_mul_tailInclusion,
    one_mul, zero_mul, add_zero]

/-- The original tail projection intertwines the actual infinity action with itself. -/
theorem tailProjection_mul_infinity [Semiring R] (A : ConeRing R) :
    tailProjection R * infinityHom R A = infinityHom R A * tailProjection R := by
  conv_lhs => rw [infinityHom_decomposition A]
  rw [mul_add]
  simp only [← mul_assoc, tailProjection_mul_firstInclusion, tailProjection_mul_tailInclusion,
    zero_mul, one_mul, zero_add]

/-- The actual repeated cone endomorphism is natural for arbitrary coefficient ring maps. -/
theorem map_infinityHom [Semiring R] [Semiring S] (f : R →+* S) (A : ConeRing R) :
    map f (infinityHom R A) = infinityHom S (map f A) := by
  ext i j
  obtain ⟨⟨k, r⟩, rfl⟩ := Nat.pairEquiv.surjective i
  obtain ⟨⟨l, s⟩, rfl⟩ := Nat.pairEquiv.surjective j
  change f (infinityHom R A (Nat.pair k r) (Nat.pair l s)) =
    infinityHom S (map f A) (Nat.pair k r) (Nat.pair l s)
  by_cases h : k = l <;> simp [infinityHom_apply_pair, map, h]

/-- The repeated matrix endomorphism is injective on its original coefficient carrier. -/
theorem infinityHom_injective (R : Type uR) [Semiring R] : Function.Injective (infinityHom R) := by
  intro A B h
  ext i j
  have h0 := congrArg (fun C : ConeRing R => C (Nat.pair 0 i) (Nat.pair 0 j)) h
  simpa [infinityHom_apply_pair] using h0

/-- A repeated original matrix has finite total support exactly when the original matrix is zero. -/
theorem infinityHom_hasFiniteSupport_iff [Semiring R] (A : ConeRing R) :
    HasFiniteSupport (infinityHom R A) ↔ A = 0 := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := exists_bound_of_hasFiniteSupport h
    ext i j
    have hn := hN (Nat.pair N i) (Nat.pair N j) (Or.inl (Nat.left_le_pair N i))
    simpa [infinityHom_apply_pair] using hn
  · rintro rfl
    exact (infinityHom R).map_zero.symm ▸ hasFiniteSupport_zero

/-- The actual repeated endomorphism fixes the original scalar diagonal inclusion. -/
theorem infinityHom_scalarHom [Semiring R] (r : R) :
    infinityHom R (scalarHom R r) = scalarHom R r := by
  ext i j
  obtain ⟨⟨k, a⟩, rfl⟩ := Nat.pairEquiv.surjective i
  obtain ⟨⟨l, b⟩, rfl⟩ := Nat.pairEquiv.surjective j
  change infinityHom R (scalarHom R r) (Nat.pair k a) (Nat.pair l b) =
    scalarHom R r (Nat.pair k a) (Nat.pair l b)
  by_cases hk : k = l <;> by_cases hab : a = b <;>
    simp [infinityHom_apply_pair, scalarHom, diagonal_apply, Nat.pair_eq_pair, hk, hab]

end ConeRing

end

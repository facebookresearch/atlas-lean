/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.MatrixSpace.Blowup
public import MathlibExt.LinearAlgebra.MatrixSpace.Wong
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Rat.Cast.Order

/-!
# Uniform rank bounds from shrunk subspaces

An actual shrunk subspace of a native matrix space amplifies to a shrunk subspace
of every square Kronecker blow-up. Restricted and global rank-nullity then bound
the rank of every matrix in that blow-up. For a positive block degree, rational
division gives the corresponding normalized upper bound.

The stable Wong preimage supplies such a subspace when the actual stable value
stays inside the starting matrix's range. Its kernel deficiency therefore bounds
all square-blow-up ranks by the starting rank times the block degree.

These statements concern concrete matrices and subspaces. The integral bounds include
empty block indices; the normalized bounds use a nonempty block-index type.

## References

Gábor Ivanyos, Youming Qiao and K. V. Subrahmanyam, *Constructive noncommutative rank
computation in deterministic polynomial time over fields of arbitrary characteristics*,
§1, the shrunk-space upper bound preceding Theorem 1; and *Non-commutative Edmonds'
problem and matrix semi-invariants*, §2.2, Fact 2.1 and §5.1.
-/

@[expose] public section

universe u v w z

namespace Matrix

variable {K : Type u} [Field K] {i : Type v} {j : Type w} {d : Type z}

private theorem map₂_toLin'_eq [Fintype j] [DecidableEq j]
    (B : Submodule K (Matrix i j K)) (U : Submodule K (j → K)) :
    Submodule.map₂ LinearMap.id (B.map Matrix.toLin'.toLinearMap) U =
      Submodule.map₂ (Matrix.mulVecBilin K K) B U := by
  rw [Submodule.map₂_map_left, LinearMap.id_comp]
  rfl

section Uniform

variable [Finite i] [Fintype j] [Fintype d]

/-- The actual amplified subspace transports a shrink inequality to every square blow-up. -/
theorem kroneckerBlowup_shrunkSpace (B : Submodule K (Matrix i j K))
    (U : Submodule K (j → K)) {s : ℕ}
    (hU : Module.finrank K (Submodule.map₂ (Matrix.mulVecBilin K K) B U) + s ≤
      Module.finrank K U) :
    Module.finrank K
        (Submodule.map₂ (Matrix.mulVecBilin K K) (kroneckerBlowup B d) (U.columnAmplification d)) +
      s * Fintype.card d ≤ Module.finrank K (U.columnAmplification d) := by
  let := Fintype.ofFinite i
  rw [kroneckerBlowup_image_columnAmplification, Submodule.finrank_columnAmplification,
    Submodule.finrank_columnAmplification]
  simpa only [add_mul] using Nat.mul_le_mul_right (Fintype.card d) hU

/-- A base shrunk subspace bounds the rank of every actual square-blow-up member. -/
theorem rank_add_mul_card_le_of_mem_kroneckerBlowup (B : Submodule K (Matrix i j K))
    (U : Submodule K (j → K)) {s : ℕ}
    (hU : Module.finrank K (Submodule.map₂ (Matrix.mulVecBilin K K) B U) + s ≤
      Module.finrank K U) {C : Matrix (i × d) (j × d) K} (hC : C ∈ kroneckerBlowup B d) :
    C.rank + s * Fintype.card d ≤ Fintype.card j * Fintype.card d := by
  let := Fintype.ofFinite i
  have hAmp := kroneckerBlowup_shrunkSpace (d := d) B U hU
  let H : Submodule K ((j × d → K) →ₗ[K] (i × d → K)) :=
    (kroneckerBlowup B d).map (Matrix.mulVecBilin K K)
  have hAmp' : Module.finrank K
      (Submodule.map₂ LinearMap.id H (U.columnAmplification d)) + s * Fintype.card d ≤
      Module.finrank K (U.columnAmplification d) := by
    dsimp only [H]
    rw [Submodule.map₂_map_left, LinearMap.id_comp]
    exact hAmp
  have hC' : Matrix.mulVecBilin K K C ∈ H := Submodule.mem_map_of_mem hC
  have h := LinearMap.finrank_range_add_le_of_shrunkSpace
    H (C := Matrix.mulVecBilin K K C) hAmp' hC'
  change C.rank + s * Fintype.card d ≤ Module.finrank K (j × d → K) at h
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using h

/-- For a positive block degree, a real shrunk subspace gives a rational normalized rank bound. -/
theorem rank_div_card_le_of_mem_kroneckerBlowup [Nonempty d]
    (B : Submodule K (Matrix i j K)) (U : Submodule K (j → K)) {s : ℕ}
    (hU : Module.finrank K (Submodule.map₂ (Matrix.mulVecBilin K K) B U) + s ≤
      Module.finrank K U) {C : Matrix (i × d) (j × d) K} (hC : C ∈ kroneckerBlowup B d) :
    (C.rank : ℚ) / (Fintype.card d : ℚ) ≤ (Fintype.card j : ℚ) - (s : ℚ) := by
  have h := rank_add_mul_card_le_of_mem_kroneckerBlowup B U hU hC
  have hq : ((C.rank + s * Fintype.card d : ℕ) : ℚ) ≤
      ((Fintype.card j * Fintype.card d : ℕ) : ℚ) := Nat.cast_le.mpr h
  simp only [Nat.cast_add, Nat.cast_mul] at hq
  have hd : (0 : ℚ) < (Fintype.card d : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hd).mpr
  rw [sub_mul]
  exact le_sub_iff_add_le.mpr hq

end Uniform

section Wong

variable {n : Type v} [Fintype n] [DecidableEq n] [Fintype d]

/-- Containment of the actual stable Wong space bounds every square-blow-up member's rank
by the starting matrix's rank times the block degree. -/
theorem rank_le_mul_card_of_secondWongLimit_le_range (A : Matrix n n K)
    (B : Submodule K (Matrix n n K))
    (hW : LinearMap.secondWongLimit (Matrix.toLin' A) (B.map Matrix.toLin'.toLinearMap) ≤
      (Matrix.toLin' A).range) {C : Matrix (n × d) (n × d) K}
    (hC : C ∈ kroneckerBlowup B d) : C.rank ≤ A.rank * Fintype.card d := by
  let f := Matrix.toLin' A
  let H := B.map Matrix.toLin'.toLinearMap
  let U := (LinearMap.secondWongLimit f H).comap f
  have hU : Module.finrank K (Submodule.map₂ (Matrix.mulVecBilin K K) B U) +
      Module.finrank K f.ker ≤ Module.finrank K U := by
    rw [← map₂_toLin'_eq]
    exact (LinearMap.secondWongLimit_deficiency f H hW).le
  have hbound := rank_add_mul_card_le_of_mem_kroneckerBlowup B U hU hC
  have hnull := f.finrank_range_add_finrank_ker
  change A.rank + Module.finrank K f.ker = Module.finrank K (n → K) at hnull
  rw [Module.finrank_fintype_fun_eq_card] at hnull
  have hscale := congrArg (fun r : ℕ => r * Fintype.card d) hnull
  rw [add_mul] at hscale
  omega

/-- The actual stable-preimage certificate bounds normalized ranks at every positive block degree. -/
theorem rank_div_card_le_of_secondWongLimit_le_range [Nonempty d] (A : Matrix n n K)
    (B : Submodule K (Matrix n n K))
    (hW : LinearMap.secondWongLimit (Matrix.toLin' A) (B.map Matrix.toLin'.toLinearMap) ≤
      (Matrix.toLin' A).range) {C : Matrix (n × d) (n × d) K}
    (hC : C ∈ kroneckerBlowup B d) :
    (C.rank : ℚ) / (Fintype.card d : ℚ) ≤ (A.rank : ℚ) := by
  have h := rank_le_mul_card_of_secondWongLimit_le_range A B hW hC
  have hq : (C.rank : ℚ) ≤ ((A.rank * Fintype.card d : ℕ) : ℚ) := Nat.cast_le.mpr h
  simp only [Nat.cast_mul] at hq
  have hd : (0 : ℚ) < (Fintype.card d : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  exact (div_le_iff₀ hd).mpr hq

end Wong

end Matrix

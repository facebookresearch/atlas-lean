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
# Rank bounds for square Kronecker blow-ups

Let K be a field, I,J,D finite index types, B ⊆ Mat(I,J;K) a subspace and U ⊆ K^J. Write B(U)
= span{Ax : A ∈ B, x ∈ U} and B^[D] = span{A ⊗ T : A ∈ B, T ∈ Mat(D,D;K)}. If dim B(U) + s ≤
dim U, every C ∈ B^[D] satisfies rank C + s|D| ≤ |J||D|. For nonempty D this gives rank C/|D|
≤ |J| − s in ℚ. For square matrices, containment of the stable second Wong subspace in im A
gives rank C ≤ rank A · |D| for every C in the blow-up.

## References

Gábor Ivanyos, Youming Qiao and K. V. Subrahmanyam, *Constructive noncommutative rank
computation in deterministic polynomial time over fields of arbitrary characteristics*, §1,
the shrunk-space upper bound preceding Theorem 1; and *Non-commutative Edmonds' problem and
matrix semi-invariants*, §2.2, Fact 2.1 and §5.1.
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

/-- **Amplification of a shrunk subspace.**

Let K be a field, I,J,D finite index types, B ⊆ Mat(I,J;K) a subspace and U ⊆ K^J. Write B(U)
= span{Ax : A ∈ B, x ∈ U} and B^[D] = span{A ⊗ T : A ∈ B, T ∈ Mat(D,D;K)}. Assume dim B(U) + s
≤ dim U for s ∈ ℕ. If U^D consists of vectors on J × D with all columns in U, then dim
B^[D](U^D) + s|D| ≤ dim U^D.
-/
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

/-- **A rank bound for every blow-up member.**

Let K be a field, I,J,D finite index types, B ⊆ Mat(I,J;K) a subspace and U ⊆ K^J. Write B(U)
= span{Ax : A ∈ B, x ∈ U} and B^[D] = span{A ⊗ T : A ∈ B, T ∈ Mat(D,D;K)}. Assume dim B(U) + s
≤ dim U for s ∈ ℕ. Every C ∈ B^[D] satisfies rank C + s|D| ≤ |J||D|, including empty D.
-/
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

/-- **A normalized blow-up rank bound.**

Let K be a field, I,J,D finite index types, B ⊆ Mat(I,J;K) a subspace and U ⊆ K^J. Write B(U)
= span{Ax : A ∈ B, x ∈ U} and B^[D] = span{A ⊗ T : A ∈ B, T ∈ Mat(D,D;K)}. Assume D is
nonempty and dim B(U) + s ≤ dim U. For every C ∈ B^[D], one has (rank C)/|D| ≤ |J| − s as an
inequality in ℚ.
-/
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

/-- **A blow-up rank bound from the Wong limit.**

Let K be a field, N,D finite index types, A ∈ Mat(N,N;K) and B ⊆ Mat(N,N;K) a subspace. Let W∞
be the stable value of W₀ = 0, Wⱼ₊₁ = B(A⁻¹Wⱼ). Suppose W∞ ⊆ im A. For B^[D] = span{X ⊗ T : X
∈ B, T ∈ Mat(D,D;K)} and C ∈ B^[D], one has rank C ≤ rank A · |D|.
-/
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

/-- **A normalized rank bound from the Wong limit.**

Let K be a field, N,D finite index types, A ∈ Mat(N,N;K) and B ⊆ Mat(N,N;K) a subspace. Let W∞
be the stable value of W₀ = 0, Wⱼ₊₁ = B(A⁻¹Wⱼ). Assume D is nonempty and W∞ ⊆ im A. For every
C ∈ B^[D] = span{X ⊗ T : X ∈ B, T ∈ Mat(D,D;K)}, one has (rank C)/|D| ≤ rank A in ℚ.
-/
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

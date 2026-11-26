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

public import MathlibExt.LinearAlgebra.MatrixSpace.FirstExit
public import MathlibExt.LinearAlgebra.MatrixSpace.PencilRank
public import MathlibExt.LinearAlgebra.Matrix.KroneckerRank

/-!
# A rank increment from a Wong shift

Let K be a field, N,D finite with D nonempty, B ⊆ Mat(N,N;K), and A ∈ B^[D] of rank r|D|. If
the stable second Wong subspace for A and B^[D] escapes im A, q > r and a scalar set S has
more than |N||D|q elements, there exists M ∈ B^[D × Fin q] with rank M > r|D|q. The matrix M
is a reindexed shift sum D_C or a reindexed pencil A ⊗ I_q + tD_C for t ∈ S.

## References

Ivanyos, Qiao and Subrahmanyam, *Non-commutative Edmonds' problem and matrix semi-invariants*,
Fact 2.2 and Algorithm 2, lines 19–25.
-/

@[expose] public section

universe u v w

namespace Matrix

open scoped Kronecker

private theorem mem_kroneckerBlowup_assoc_iff
    {R : Type u} [CommSemiring R] {n : Type v} {d : Type w} [Finite d]
    (B : Submodule R (Matrix n n R)) (q : ℕ)
    (X : Matrix ((n × d) × Fin q) ((n × d) × Fin q) R) :
    X ∈ kroneckerBlowup (kroneckerBlowup B d) (Fin q) ↔
      Matrix.reindex (Equiv.prodAssoc n d (Fin q))
        (Equiv.prodAssoc n d (Fin q)) X ∈ kroneckerBlowup B (d × Fin q) := by
  simp only [mem_kroneckerBlowup_iff, Matrix.reindex_apply, Matrix.submatrix_submatrix]
  constructor
  · intro h ⟨a, u⟩ ⟨b, v⟩
    exact h u v a b
  · intro h u v a b
    exact h (a, u) (b, v)

variable {K : Type u} [Field K] {n : Type v} {d : Type w}
variable [Fintype n] [Fintype d]

/-- **The shift or pencil gives a larger-rank blow-up.**

Let K be a field, N,D finite with D nonempty and B ⊆ Mat(N,N;K). Put E = B^[D] = span{X ⊗ T :
X ∈ B, T ∈ Mat(D,D;K)}. Suppose A ∈ E, rank A = r|D|, and the stable sequence W₀ = 0, Wⱼ₊₁ =
E(A⁻¹Wⱼ) is not contained in im A. Let q > r and S ⊆ K finite with |S| > |N||D|q. Then some k
≤ r and C₀,…,Cₖ ∈ E give D_C = ∑ᵢ Cᵢ ⊗ E_{i+1 mod q,i} and M ∈ B^[D × Fin q] with rank M >
r|D|q. If rank D_C > r|D|q, M is D_C reindexed by ((n,d),i) ↦ (n,(d,i)); otherwise M is the
same reindexing of A ⊗ I_q + tD_C for some t ∈ S.
-/
theorem exists_wongShift_rank_increment [Nonempty d]
    (A : Matrix (n × d) (n × d) K)
    (B : Submodule K (Matrix n n K)) (r q : ℕ)
    (hA : A ∈ kroneckerBlowup B d)
    (hRank : A.rank = r * Fintype.card d)
    (hExit : ¬LinearMap.secondWongLimit A.mulVecLin
      ((kroneckerBlowup B d).map (Matrix.mulVecBilin K K)) ≤ A.mulVecLin.range)
    (hq : r < q) (S : Finset K)
    (hS : Fintype.card n * Fintype.card d * q < S.card) :
    ∃ k, k ≤ r ∧
      ∃ (C : Fin (k + 1) → kroneckerBlowup B d) (h : k + 1 ≤ q),
        let D := wongShiftSum
          (fun i => (C i : Matrix (n × d) (n × d) K)) h
        let e := Equiv.prodAssoc n d (Fin q)
        ∃ M : Matrix (n × (d × Fin q)) (n × (d × Fin q)) K,
          M ∈ kroneckerBlowup B (d × Fin q) ∧
          r * Fintype.card d * q < M.rank ∧
          ((r * Fintype.card d * q < D.rank ∧ M = Matrix.reindex e e D) ∨
            (D.rank ≤ r * Fintype.card d * q ∧
              ∃ t ∈ S, M = Matrix.reindex e e
                ((A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) + t • D))) := by
  classical
  obtain ⟨k, hk, C, h, hA', hD, w, h0, hstep, hout⟩ :=
    exists_wongShift_blowup_escape A B r q hA hRank hExit hq
  let D := wongShiftSum (fun i => (C i : Matrix (n × d) (n × d) K)) h
  let e := Equiv.prodAssoc n d (Fin q)
  have hOld : (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)).rank =
      r * Fintype.card d * q := by
    simpa only [Fintype.card_fin, hRank] using rank_kronecker_one (d := Fin q) A
  by_cases hLarge : r * Fintype.card d * q < D.rank
  · refine ⟨k, hk, C, h, Matrix.reindex e e D, ?_, ?_, Or.inl ⟨hLarge, rfl⟩⟩
    · exact (mem_kroneckerBlowup_assoc_iff B q D).mp hD
    · rwa [Matrix.rank_reindex]
  · have hSmall : D.rank ≤ r * Fintype.card d * q := Nat.le_of_not_gt hLarge
    have hS' : Fintype.card ((n × d) × Fin q) < S.card := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using hS
    obtain ⟨t, ht, hIncrease⟩ := exists_rank_lt_add_smul_of_uniform_chain
      (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) D k w h0 hstep hout S hS'
    let X := (A ⊗ₖ (1 : Matrix (Fin q) (Fin q) K)) + t • D
    have hX : X ∈ kroneckerBlowup (kroneckerBlowup B d) (Fin q) :=
      Submodule.add_mem _ hA' (Submodule.smul_mem _ t hD)
    refine ⟨k, hk, C, h, Matrix.reindex e e X, ?_, ?_, Or.inr ⟨hSmall, t, ht, rfl⟩⟩
    · exact (mem_kroneckerBlowup_assoc_iff B q X).mp hX
    · rw [Matrix.rank_reindex]
      rwa [hOld] at hIncrease

end Matrix

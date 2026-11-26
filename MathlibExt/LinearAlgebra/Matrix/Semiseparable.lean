/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lower-triangular semiseparable matrices
-/

namespace MetaMathlibExt.Matrix

/-- **Semiseparable matrix.** A lower-triangular $T \times T$ matrix $M$ over a field is
$N$-semiseparable if every submatrix contained in its lower triangle, including the diagonal,
has rank at most $N$. Equivalently, for each index $s$, the block with rows at least $s$ and
columns at most $s$ has rank at most $N$.

Source: Tri Dao and Albert Gu, *Transformers are SSMs: Generalized Models and Efficient
Algorithms Through Structured State Space Duality*, arXiv:2405.21060 (v1), Definition 3.1. -/
@[expose] public def IsSemiseparable {K : Type*} [Field K] {T : ℕ}
    (M : Matrix (Fin T) (Fin T) K) (N : ℕ) : Prop :=
  M.IsLowerTriangular ∧
    ∀ s : Fin T,
      (M.submatrix (Subtype.val : Set.Ici s → Fin T) (Subtype.val : Set.Iic s → Fin T)).rank ≤ N

/-- **Sequentially semiseparable matrices are semiseparable.** If the entries of `M` on and below
the diagonal are $M_{ji} = C_j^{\mathsf T} A_j \cdots A_{i+1} B_i$, and the entries above it are
zero, then `M` is `N`-semiseparable. The transition product takes the factors with indices in
$(i,j]$ in descending order. On the diagonal the list is empty and its product is the identity.

Source: Tri Dao and Albert Gu, *Transformers are SSMs: Generalized Models and Efficient
Algorithms Through Structured State Space Duality*, arXiv:2405.21060 (v1), Lemma 3.3. -/
public theorem isSemiseparable_of_sss {K : Type*} [Field K] {T N : ℕ}
    {M : Matrix (Fin T) (Fin T) K} (A : Fin T → Matrix (Fin N) (Fin N) K)
    (B C : Fin T → Fin N → K)
    (hM : ∀ j i, M j i =
      if i ≤ j then
        let P := (((List.ofFn A).drop (i.val + 1)).take (j.val - i.val)).reverse.prod
        dotProduct (C j) (P.mulVec (B i))
      else 0) : IsSemiseparable M N := by
  let P (j i : Fin T) := (((List.ofFn A).drop (i.val + 1)).take (j.val - i.val)).reverse.prod
  change (∀ j i, M j i = if i ≤ j then dotProduct (C j) ((P j i).mulVec (B i)) else 0) at hM
  have hP (j s i : Fin T) (his : i ≤ s) (hsj : s ≤ j) : P j i = P j s * P s i := by
    change i.val ≤ s.val at his
    change s.val ≤ j.val at hsj
    have hlen : j.val - i.val = (s.val - i.val) + (j.val - s.val) := by omega
    have hstart : i.val + 1 + (s.val - i.val) = s.val + 1 := by omega
    dsimp only [P]
    rw [hlen, List.take_add, List.drop_drop, hstart, List.reverse_append, List.prod_append]
  refine ⟨fun j i hij => (hM j i).trans (ite_eq_right hij.not_ge), ?_⟩
  intro s
  -- Factor the cut block through the N-dimensional state at s.
  let L : Matrix (Set.Ici s) (Fin N) K := Matrix.of fun j => Matrix.vecMul (C j.val) (P j.val s)
  let R : Matrix (Fin N) (Set.Iic s) K := Matrix.of fun k i => (P s i.val).mulVec (B i.val) k
  have hblock :
      M.submatrix (Subtype.val : Set.Ici s → Fin T) (Subtype.val : Set.Iic s → Fin T) = L * R := by
    ext j i
    have his : i.val ≤ s := Set.mem_Iic.mp i.property
    have hsj : s ≤ j.val := Set.mem_Ici.mp j.property
    calc
      _ = dotProduct (C j.val) ((P j.val i.val).mulVec (B i.val)) := by
        rw [Matrix.submatrix_apply, hM, ite_eq_left (his.trans hsj)]
      _ = dotProduct (Matrix.vecMul (C j.val) (P j.val s)) ((P s i.val).mulVec (B i.val)) := by
        rw [hP _ _ _ his hsj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      _ = _ := by rw [Matrix.mul_apply]; rfl
  rw [hblock]
  exact (Matrix.rank_mul_le_left L R).trans (by simpa using L.rank_le_card_width)

end MetaMathlibExt.Matrix

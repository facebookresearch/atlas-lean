/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.LinearCode
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Low-density parity-check codes: regular matrices and Gallager's ensemble

Gallager's low-density parity-check codes are the linear codes `ofParityCheck H` of sparse
parity-check matrices `H`. An `(n, j, k)` matrix has `n` columns, exactly `j` nonzero entries in
each column and exactly `k` in each row (`IsRegular`); over `GF(2) = ZMod 2` the nonzero entries
are the ones, which is Gallager's definition.

* `card_rows_mul_eq`: double counting the nonzero entries gives `(#rows) k = n j`, so an
  `(n, j, k)` matrix has `n j / k` rows.
* `one_sub_div_le_rate`: the code of an `(n, j, k)` matrix has rate `dim C / n ≥ 1 - j / k`.
  This is Gallager's remark after the definition; the rate can be larger because the rows need
  not be independent.
* `gallagerMatrix m j k σ`: the matrices of Gallager's ensemble of `(n, j, k)` matrices for
  `n = m k`. The matrix is a stack of `j` blocks of `m` rows; block `0` has row `r` equal to one
  exactly on the columns `r k, …, r k + k - 1`, and block `t ≥ 1` is that block with its columns
  permuted by `σ t`. Gallager's ensemble is the law of `gallagerMatrix m j k σ` when the `σ t`,
  `t ≥ 1`, are independent and uniform; `σ 0` is ignored.
* `isRegular_gallagerMatrix`, `one_sub_div_le_rate_gallagerMatrix`: every matrix of the
  ensemble is `(m k, j, k)`-regular, so every code of the ensemble has rate at least `1 - j / k`.

## References

* R. G. Gallager, *Low-Density Parity-Check Codes*, MIT Press, 1963, Section 1.2 and
  Section 2.2 with Figure 2.1 (the author's PDF at web.mit.edu/gallager, p. 13).
* R. G. Gallager, Low-density parity-check codes, IRE Trans. Inform. Theory IT-8 (1962), 21–28.
-/

namespace Cslib.CodingTheory.LDPC

open Matrix Module LinearCode

variable {F : Type*} [Field F] [DecidableEq F] {ρ ι : Type*} [Fintype ρ] [Fintype ι]

/-- **Column weight of a matrix.** The number of nonzero entries in column `c` of `H`. -/
def colWeight (H : Matrix ρ ι F) (c : ι) : ℕ := (Finset.univ.filter fun r => H r c ≠ 0).card

/-- **Row weight of a matrix.** The number of nonzero entries in row `r` of `H`. -/
def rowWeight (H : Matrix ρ ι F) (r : ρ) : ℕ := (Finset.univ.filter fun c => H r c ≠ 0).card

/-- **Regular low-density parity-check matrix.** `H` is `(j, k)`-regular if every column has
exactly `j` nonzero entries and every row exactly `k`. With `n` columns over `ZMod 2` this is
Gallager's `(n, j, k)` parity-check matrix (Gallager, *Low-Density Parity-Check Codes*, 1963,
Section 2.2): `j` ones in each column, `k` ones in each row, and zeros elsewhere. -/
def IsRegular (H : Matrix ρ ι F) (j k : ℕ) : Prop :=
  (∀ c, colWeight H c = j) ∧ ∀ r, rowWeight H r = k

/-- **Row and column weights have the same total.** Both count the nonzero entries of `H`. -/
theorem sum_rowWeight_eq_sum_colWeight (H : Matrix ρ ι F) :
    ∑ r, rowWeight H r = ∑ c, colWeight H c := by
  simp only [rowWeight, colWeight, Finset.card_filter]
  exact Finset.sum_comm

/-- **Number of rows of a regular parity-check matrix.** If `H` is `(j, k)`-regular then
`(#rows) · k = (#columns) · j`, by counting the nonzero entries by rows and by columns: an
`(n, j, k)` matrix has `n j / k` rows (Gallager, *Low-Density Parity-Check Codes*, 1963,
Section 2.2). -/
theorem card_rows_mul_eq {H : Matrix ρ ι F} {j k : ℕ} (h : IsRegular H j k) :
    Fintype.card ρ * k = Fintype.card ι * j := by
  have := sum_rowWeight_eq_sum_colWeight H
  simp only [h.1, h.2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  exact this

omit [DecidableEq F] in
/-- **Dimension of a code given by parity checks.** The code of an `m × n` parity-check matrix
has dimension at least `n - m`, since its rank is at most the number of rows. -/
theorem card_sub_card_le_finrank (H : Matrix ρ ι F) :
    Fintype.card ι - Fintype.card ρ ≤ finrank F (ofParityCheck H) := by
  rw [finrank_ofParityCheck]
  have := H.rank_le_card_height
  omega

/-- **Rate of a regular low-density parity-check code.** If the parity-check matrix `H` with
`n > 0` columns is `(j, k)`-regular with `k > 0`, its code has rate at least `1 - j / k`:
`1 - j / k ≤ dim C / n` (Gallager, *Low-Density Parity-Check Codes*, 1963, Section 2.2: "an
`(n, j, k)` parity-check matrix has `nj/k` rows and thus a rate `R ≥ 1 - j/k`"). The inequality
can be strict, since the rows need not be linearly independent. -/
theorem one_sub_div_le_rate {H : Matrix ρ ι F} {j k : ℕ} (h : IsRegular H j k) (hk : 0 < k)
    (hn : 0 < Fintype.card ι) :
    1 - (j : ℝ) / k ≤ finrank F (ofParityCheck H) / Fintype.card ι := by
  have hrows := card_rows_mul_eq h
  have hdim := card_sub_card_le_finrank H
  have hle : (Fintype.card ι : ℝ) - Fintype.card ρ ≤ finrank F (ofParityCheck H) := by
    have : Fintype.card ι ≤ finrank F (ofParityCheck H) + Fintype.card ρ := by omega
    have : (Fintype.card ι : ℝ) ≤ finrank F (ofParityCheck H) + Fintype.card ρ := by
      exact_mod_cast this
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hrowsR : (Fintype.card ρ : ℝ) * k = Fintype.card ι * j := by exact_mod_cast hrows
  rw [le_div_iff₀ hnR]
  have : (1 - (j : ℝ) / k) * Fintype.card ι = Fintype.card ι - Fintype.card ρ := by
    field_simp
    linarith
  linarith

/-! ### Gallager's ensemble -/

/-- **Column permutations of Gallager's ensemble.** Block `0` keeps the columns in order and
block `t ≥ 1` permutes them by `σ t`. -/
def blockPerm {j n : ℕ} (σ : Fin j → Equiv.Perm (Fin n)) (t : Fin j) : Equiv.Perm (Fin n) :=
  if (t : ℕ) = 0 then 1 else σ t

/-- **Gallager's `(n, j, k)` matrix with `n = m k`.** The rows are indexed by a block `t < j`
and a row `r < m`; entry `((t, r), c)` is `1` exactly when `⌊π_t(c) / k⌋ = r`, where `π_t` is
`blockPerm σ t`. So block `0` has its ones "in descending order", row `r` being one on columns
`r k, …, r k + k - 1`, and block `t ≥ 1` is block `0` with its columns permuted
(Gallager, *Low-Density Parity-Check Codes*, 1963, Section 2.2 and Figure 2.1, where
`n = 20`, `j = 3`, `k = 4`). Gallager's ensemble of `(n, j, k)` codes is the law of this matrix
when `σ 1, …, σ (j - 1)` are independent and uniform over all permutations ("random permutations
of the columns of each of the bottom `j - 1` submatrices"). -/
def gallagerMatrix (m j k : ℕ) (σ : Fin j → Equiv.Perm (Fin (m * k))) :
    Matrix (Fin j × Fin m) (Fin (m * k)) (ZMod 2) :=
  fun r c => if ((blockPerm σ r.1 c : Fin (m * k)) : ℕ) / k = r.2 then 1 else 0

theorem gallagerMatrix_ne_zero_iff {m j k : ℕ} (σ : Fin j → Equiv.Perm (Fin (m * k)))
    (r : Fin j × Fin m) (c : Fin (m * k)) :
    gallagerMatrix m j k σ r c ≠ 0 ↔ ((blockPerm σ r.1 c : Fin (m * k)) : ℕ) / k = r.2 := by
  unfold gallagerMatrix
  split_ifs with h <;> simp [h]

/-- **Indices with a given quotient.** In `Fin (m k)`, exactly `k` indices have quotient `r`
by `k`, for every `r < m`. -/
theorem card_filter_div_eq {m k : ℕ} (r : Fin m) :
    (Finset.univ.filter fun c : Fin (m * k) => (c : ℕ) / k = r).card = k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [← Fintype.card_subtype]
  have e : {c : Fin (m * k) // (c : ℕ) / k = r} ≃ Fin k :=
    { toFun := fun c => ⟨(c : ℕ) % k, Nat.mod_lt _ hk⟩
      invFun := fun i => ⟨⟨r * k + i, by
          have := r.2; have := i.2
          calc (r : ℕ) * k + i < r * k + k := by omega
            _ = (r + 1) * k := by ring
            _ ≤ m * k := Nat.mul_le_mul_right _ (by omega)⟩, by
          simp only
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt i.2, zero_add]⟩
      left_inv := fun c => by
        obtain ⟨c, hc⟩ := c
        ext
        simp only
        have := Nat.div_add_mod (c : ℕ) k
        rw [hc] at this
        linarith [Nat.mul_comm k r]
      right_inv := fun i => by
        ext
        simp [Nat.add_mod, Nat.mod_eq_of_lt i.2] }
  exact (Fintype.card_congr e).trans (Fintype.card_fin k)

/-- **Gallager's matrices are regular.** Every `gallagerMatrix m j k σ` has exactly `j` ones in
each column (one per block) and exactly `k` ones in each row: it is an `(m k, j, k)` parity-check
matrix (Gallager, *Low-Density Parity-Check Codes*, 1963, Section 2.2). -/
theorem isRegular_gallagerMatrix (m j k : ℕ) (σ : Fin j → Equiv.Perm (Fin (m * k))) :
    IsRegular (gallagerMatrix m j k σ) j k := by
  classical
  refine ⟨fun c => ?_, fun r => ?_⟩
  · simp only [colWeight, gallagerMatrix_ne_zero_iff]
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    have : ∀ t : Fin j, (∑ r : Fin m,
        if ((blockPerm σ t c : Fin (m * k)) : ℕ) / k = r then 1 else 0) = 1 := by
      intro t
      set x : Fin (m * k) := blockPerm σ t c
      have hx : (x : ℕ) / k < m := by
        have := x.2
        rcases Nat.eq_zero_or_pos k with hk | hk
        · simp [hk] at this
        · exact (Nat.div_lt_iff_lt_mul hk).2 this
      rw [Finset.sum_eq_single ⟨(x : ℕ) / k, hx⟩]
      · simp
      · intro b _ hb
        split_ifs with h
        · exact absurd (Fin.ext h.symm) hb
        · rfl
      · simp
    simp [this]
  · simp only [rowWeight, gallagerMatrix_ne_zero_iff]
    have : (Finset.univ.filter fun c : Fin (m * k) =>
        ((blockPerm σ r.1 c : Fin (m * k)) : ℕ) / k = r.2) =
        (Finset.univ.filter fun c : Fin (m * k) => (c : ℕ) / k = r.2).map
          (blockPerm σ r.1).symm.toEmbedding := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
        Equiv.symm_symm]
    rw [this, Finset.card_map, card_filter_div_eq]

/-- **Rate of Gallager's low-density codes.** Every code of Gallager's `(m k, j, k)` ensemble,
`m, k > 0`, has rate at least `1 - j / k`: for every choice `σ` of column permutations, the code
of `gallagerMatrix m j k σ` has `1 - j / k ≤ dim C / (m k)` (Gallager, *Low-Density Parity-Check
Codes*, 1963, Section 2.2). -/
theorem one_sub_div_le_rate_gallagerMatrix {m j k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (σ : Fin j → Equiv.Perm (Fin (m * k))) :
    1 - (j : ℝ) / k ≤ finrank (ZMod 2) (ofParityCheck (gallagerMatrix m j k σ)) / (m * k : ℕ) := by
  have := one_sub_div_le_rate (isRegular_gallagerMatrix m j k σ) hk
    (by simpa using Nat.mul_pos hm hk)
  simpa using this

end Cslib.CodingTheory.LDPC

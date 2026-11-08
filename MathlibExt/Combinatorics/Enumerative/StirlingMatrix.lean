/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.LinearAlgebra.Matrix.Block
import MathlibExt.Combinatorics.Enumerative.StirlingMatrices

/-!
# Stirling-like matrices and their decompositions

Results from M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid
Salehy, "Some Identities Involving Stirling Numbers Arising from Matrix
Decompositions", *Journal of Integer Sequences* 27 (2024), Article 24.5.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Moghaddamfar/mogh14.tex>).

For a sequence `α : ℕ → ℚ`, the paper's Stirling-like matrix `S_α` is given
entrywise (in the paper's 1-based indexing) by `stirlingLikeEntry`, defined by
the recurrence `S_{i,j} = S_{i-1,j-1} + j S_{i-1,j}` with first row `α_{j-1}`
and first column `α₀`; `uEntry` is the analogous recurrence for `U_α`, and
`rEntry`/`rTildeEntry` are the closed forms for `R_α` and its inverse
candidate `R̃_α`, built from `psi` (`Ψ_α(k) = ∑_{l<k} α_l/(k-1-l)!`) and
`omega` (`Ω(α,j) = ∑_{l<j} (j-1)↓_l α_l`). The paper's `Λ(α,k₁,k₂)` is
`lambda`; `s(i,j)` is MathlibExt's `signedStirlingFirst` and `S(i,j)` is
`Nat.stirlingSecond`. Finite matrices are `Matrix (Fin n) (Fin n) ℚ` with entry
`(a,b)` the paper's `(a+1, b+1)`-entry. Entry values at index `0` are junk;
all statements quantify over indices `≥ 1` as in the paper.

## Proof outline

Two closed forms for the rows of `S_α` carry the paper.

* `stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry`: for every `N > i`,
  `S_{i,j} = ∑_{k<N} S(i,k) U_{k,j}`. It is proved by induction on `i`, from
  `Nat.stirlingSecond_succ_succ` and the recurrence for `U_α`.
* `stirlingLikeEntry_succ`:
  `S_{i+1,j} = ∑_{k=1}^j k^i (-1)^{j-k}/(j-k)! Ψ_α(k)`.
  It is proved by induction on `i`, starting from Lemma 2 (`sum_rEntry_col`).

Theorem 3 reads these off entrywise. Theorem 4 then follows from
`Matrix.det_mul` and the triangularity of `S(n)` and `U_α(n)`, whose diagonals
are `1` and `Ω(α, i)` (`uEntry_self`). Lemma 7 and Proposition 8 rest on
`sum_rEntry_mul_descFactorial`, `∑_{m=1}^j R_{k,m} (j-1)↓_{m-1} = δ_{k,j}
Ω(α,j)`. That identity needs no nonvanishing hypothesis, so the hypothesis `h`
of Proposition 8 is not used; nor is the hypothesis `1 ≤ j` of Propositions 5
and 9. These hypotheses are kept so that the statements match the source.
Proposition 9 combines the first closed form with
the orthogonality `MetaMathlibExt.sum_signedStirlingFirst_mul_stirlingSecond`.
Corollary 10 is Proposition 9 for `α = (1, 0, 0, …)`. The alternating sums of
factorial quotients come from `add_pow_div_factorial`.

Corollary 6 of the paper (the classical formula
`S(i,j) = (1/j!) ∑_{k=1}^j C(j,k) (-1)^{j-k} k^i`) is already proved in
MathlibExt as `MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum` and is
therefore not restated here.

## Main results

* `uEntry_eq_lambda`, `uEntry_eq_zero_of_lt` (Lemma 1).
* `sum_rEntry_col` (Lemma 2).
* `stirlingLikeMatrix_decomp` (Theorem 3): `S_α(n) = S(n) U_α(n) = V(n) R_α(n)`.
* `stirlingLikeMatrix_det` (Theorem 4).
* `sum_stirlingSecond_lambda` (Proposition 5).
* `rTildeMatrix_eq_inv` (Lemma 7).
* `sum_stirlingSecond_descFactorial_lambda` (Proposition 8).
* `sum_signed_psi_eq` (Proposition 9), `sum_signed_eq_delta` (Corollary 10).

## References

* M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima Salehy, and Navid Salehy,
  "Some Identities Involving Stirling Numbers Arising from Matrix
  Decompositions", *Journal of Integer Sequences* 27 (2024), Article 24.5.3.
-/

@[expose] public section

open Finset
open scoped Nat

namespace MetaMathlibExt

/-! ### Binomial sums and reindexing -/

/-- The binomial theorem divided by `m !`. -/
theorem add_pow_div_factorial {K : Type*} [Field K] [CharZero K] (x y : K)
    (m : ℕ) :
    (x + y) ^ m / m ! =
      ∑ t ∈ range (m + 1), x ^ t / t ! * (y ^ (m - t) / (m - t)!) := by
  rw [add_pow, sum_div]
  refine sum_congr rfl fun t ht => ?_
  rw [Nat.cast_choose K (Nat.lt_succ_iff.mp (mem_range.mp ht))]
  have : (m ! : K) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  field_simp

/-- `∑_{t ≤ m} (-1) ^ t / (t ! (m - t)!)` is `1` if `m = 0` and `0`
otherwise. -/
theorem sum_range_neg_one_pow_div_factorial_mul {K : Type*} [Field K]
    [CharZero K] (m : ℕ) :
    ∑ t ∈ range (m + 1), (-1 : K) ^ t / (t ! * (m - t)!) =
      if m = 0 then 1 else 0 := by
  have h := add_pow_div_factorial (-1 : K) 1 m
  simp only [neg_add_cancel, one_pow, div_mul_div_comm, mul_one] at h
  rw [← h]
  rcases m with _ | m <;> simp

/-- `∑_{t ≤ m} (-1) ^ (m - t) / (t ! (m - t)!)` is `1` if `m = 0` and `0`
otherwise. -/
theorem sum_range_neg_one_pow_sub_div_factorial_mul {K : Type*} [Field K]
    [CharZero K] (m : ℕ) :
    ∑ t ∈ range (m + 1), (-1 : K) ^ (m - t) / (t ! * (m - t)!) =
      if m = 0 then 1 else 0 := by
  have h := add_pow_div_factorial (1 : K) (-1) m
  simp only [add_neg_cancel, one_pow, div_mul_div_comm, one_mul] at h
  rw [← h]
  rcases m with _ | m
  · simp
  · simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, zero_div, ite_false]

/-- A sum over `Icc 1 n` as a sum over `range n`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (n : ℕ) : ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [add_comm 1]

/-- Pascal's rule summed against a sequence `f`. -/
theorem sum_range_choose_succ_mul {R : Type*} [Semiring R] (f : ℕ → R)
    (i : ℕ) :
    ∑ l ∈ range (i + 2), ((i + 1).choose l : R) * f l =
      ∑ l ∈ range (i + 1), (i.choose l : R) * f l +
        ∑ l ∈ range (i + 1), (i.choose l : R) * f (l + 1) := by
  rw [sum_range_succ', sum_range_succ' (fun l => (i.choose l : R) * f l)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
    Nat.choose_zero_right]
  rw [sum_range_succ (fun l => (i.choose (l + 1) : R) * f (l + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  abel

/-- A sum over `Fin n` of a function of the `1`-based index as a sum over
`Icc 1 n`. -/
theorem sum_fin_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ c : Fin n, f (c.val + 1) = ∑ k ∈ Icc 1 n, f k := by
  rw [sum_Icc_one_eq_sum_range, Fin.sum_univ_eq_sum_range (fun c => f (c + 1))]

end MetaMathlibExt

namespace MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-- Entries of the Stirling-like matrix `S_α` in 1-based
indexing, by the paper's recurrence (value `0` at index
`0`). -/
def stirlingLikeEntry (α : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, j => if j = 0 then 0 else α (j - 1)
  | i + 2, j =>
      if j = 1 then α 0
      else if j = 0 then 0
      else stirlingLikeEntry α (i + 1) (j - 1) +
        (j : ℚ) * stirlingLikeEntry α (i + 1) j

/-- Entries of the matrix `U_α` in 1-based indexing, by
the paper's recurrence (value `0` at index `0` and in the
first column below the top entry). -/
def uEntry (α : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, _ => 0
  | 1, j => if j = 0 then 0 else α (j - 1)
  | i + 2, j =>
      if j ≤ 1 then 0
      else uEntry α (i + 1) (j - 1) +
        ((j : ℚ) - (i + 2) + 1) * uEntry α (i + 1) j

/-- The paper's `Ψ_α(k) = ∑_{l=0}^{k-1} α_l/(k-1-l)!`. -/
def psi (α : ℕ → ℚ) (k : ℕ) : ℚ :=
  ∑ l ∈ Finset.range k, α l / (k - 1 - l).factorial

/-- The paper's `Ω(α, j) = ∑_{l=0}^{j-1} (j-1)↓_l α_l`. -/
def omega (α : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range j,
    (Nat.descFactorial (j - 1) l : ℚ) * α l

/-- The paper's `Λ(α, k₁, k₂) = ∑_{l=0}^{k₁-1} C(k₁-1, l)
(l+k₂-k₁)!/(k₂-k₁)! α_{l+k₂-k₁}`. -/
def lambda (α : ℕ → ℚ) (k₁ k₂ : ℕ) : ℚ :=
  ∑ l ∈ Finset.range k₁, (Nat.choose (k₁ - 1) l : ℚ) *
    ((l + k₂ - k₁).factorial : ℚ) / (k₂ - k₁).factorial *
    α (l + k₂ - k₁)

/-- Entries of the matrix `R_α` in 1-based indexing, by
the paper's closed form. -/
def rEntry (α : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then (-1 : ℚ) ^ (j - i) / (j - i).factorial * psi α i
  else 0

/-- Entries of the matrix `R̃_α` in 1-based indexing, by
the paper's closed form. -/
def rTildeEntry (α : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then
    (Nat.descFactorial (j - 1) (i - 1) : ℚ) / omega α j
  else 0

/-- The finite Stirling-like matrix `S_α(n)`. -/
def stirlingLikeMatrix (α : ℕ → ℚ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => stirlingLikeEntry α (a.val + 1) (b.val + 1)

/-- The finite matrix `U_α(n)`. -/
def uMatrix (α : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => uEntry α (a.val + 1) (b.val + 1)

/-- The finite matrix `R_α(n)`. -/
def rMatrix (α : ℕ → ℚ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => rEntry α (a.val + 1) (b.val + 1)

/-- The finite matrix `R̃_α(n)`. -/
def rTildeMatrix (α : ℕ → ℚ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => rTildeEntry α (a.val + 1) (b.val + 1)

/-- The Stirling matrix of the second kind `S(n)`. -/
def stirlingMatrix2 (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b =>
    (Nat.stirlingSecond (a.val + 1) (b.val + 1) : ℚ)

/-- The Vandermonde matrix `V(n)` with `V_{i,j} = j^{i-1}`
(1-based). -/
def vandermondeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun a b => ((b.val + 1 : ℕ) : ℚ) ^ a.val

open MetaMathlibExt

/-! ### `Ψ_α`, `Ω` and the column sums of `R_α` -/

/-- `Ω(α, j + 1) = j! Ψ_α(j + 1)`. -/
theorem omega_succ (α : ℕ → ℚ) (j : ℕ) :
    omega α (j + 1) = j ! * psi α (j + 1) := by
  simp only [omega, psi, Nat.add_sub_cancel, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl : l ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rw [← Nat.factorial_mul_descFactorial hl]
  have : ((j - l)! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (j - l).factorial_ne_zero
  push_cast
  field_simp

/-- **Lemma 2**: the `j`-th column sum of `R_α` is
`∑_{i=1}^j R_{i,j} = α_{j-1}`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 2.

Proves `Wanted` entry `sum_rEntry_col`. -/
theorem sum_rEntry_col (α : ℕ → ℚ) (j : ℕ)
    (hj : 1 ≤ j) :
    ∑ i ∈ Finset.Icc 1 j, rEntry α i j = α (j - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, sum_Icc_one_eq_sum_range]
  calc ∑ t ∈ range (n + 1), rEntry α (t + 1) (n + 1)
      = ∑ t ∈ range (n + 1), ∑ l ∈ range (t + 1),
          (-1 : ℚ) ^ (n - t) / (n - t)! * (α l / (t - l)!) := by
        refine sum_congr rfl fun t ht => ?_
        have ht : t ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ht)
        simp only [rEntry, psi, mul_sum, Nat.add_sub_add_right,
          Nat.add_sub_cancel, ite_eq_left (Nat.succ_le_succ ht)]
    _ = ∑ l ∈ range (n + 1), ∑ t ∈ Icc l n,
          (-1 : ℚ) ^ (n - t) / (n - t)! * (α l / (t - l)!) := by
        refine sum_comm' fun t l => ?_
        simp only [mem_range, mem_Icc]
        omega
    _ = ∑ l ∈ range (n + 1), α l * if n - l = 0 then 1 else 0 := by
        refine sum_congr rfl fun l hl => ?_
        have hl : l ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hl)
        rw [← sum_range_neg_one_pow_sub_div_factorial_mul, mul_sum,
          ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
          show n + 1 - l = n - l + 1 by omega]
        refine sum_congr rfl fun s hs => ?_
        rw [show n - (l + s) = n - l - s by omega, Nat.add_sub_cancel_left]
        ring
    _ = α n := by
        rw [sum_eq_single n (fun l hl hln => by
          rw [ite_eq_right (by simp only [mem_range] at hl; omega), mul_zero])
          (fun h => absurd (self_mem_range_succ n) h)]
        simp

/-! ### The decomposition `S_α = V R_α` -/

/-- Closed form of the rows of `S_α` from which `S_α = V R_α` is read off:
`S_{i+1,j} = ∑_{k=1}^j k^i (-1)^{j-k}/(j-k)! Ψ_α(k)`. -/
theorem stirlingLikeEntry_succ (α : ℕ → ℚ) (i j : ℕ) :
    stirlingLikeEntry α (i + 1) j =
      ∑ k ∈ Icc 1 j, (k : ℚ) ^ i *
        ((-1 : ℚ) ^ (j - k) / (j - k).factorial) * psi α k := by
  induction i generalizing j with
  | zero =>
    rcases j with _ | j
    · simp [stirlingLikeEntry]
    · have h := sum_rEntry_col α (j + 1) (by omega)
      rw [Nat.add_sub_cancel] at h
      simp only [stirlingLikeEntry, Nat.add_one_ne_zero, ite_false,
        Nat.add_sub_cancel, ← h]
      refine sum_congr rfl fun k hk => ?_
      rw [rEntry, ite_eq_left (mem_Icc.mp hk).2, pow_zero, one_mul]
  | succ i ih =>
    rcases j with _ | _ | m
    · simp [stirlingLikeEntry]
    · simp [stirlingLikeEntry, psi]
    · have key : ∀ k ∈ Icc 1 (m + 1),
          (k : ℚ) ^ i * ((-1 : ℚ) ^ (m + 1 - k) / (m + 1 - k)!) * psi α k +
            ((m + 1 + 1 : ℕ) : ℚ) * ((k : ℚ) ^ i *
              ((-1 : ℚ) ^ (m + 1 + 1 - k) / (m + 1 + 1 - k)!) * psi α k) =
          (k : ℚ) ^ (i + 1) *
            ((-1 : ℚ) ^ (m + 1 + 1 - k) / (m + 1 + 1 - k)!) * psi α k := by
        intro k hk
        have hk : k ≤ m + 1 := (mem_Icc.mp hk).2
        obtain ⟨t, ht⟩ : ∃ t, m + 1 = k + t := ⟨m + 1 - k, by omega⟩
        rw [show m + 1 + 1 - k = t + 1 by omega, show m + 1 - k = t by omega,
          show m + 1 + 1 = k + t + 1 by omega, pow_succ, pow_succ,
          Nat.factorial_succ]
        have : (t ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr t.factorial_ne_zero
        push_cast
        field_simp
        ring
      simp only [stirlingLikeEntry, show m + 1 + 1 ≠ 1 by omega,
        show m + 1 + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
      rw [ih, ih, sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1),
        sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1), mul_add, mul_sum,
        ← add_assoc, ← sum_add_distrib, sum_congr rfl key, pow_succ]
      ring

/-! ### The matrix `U_α` -/

/-- The first column of `U_α` vanishes (junk index `0`). -/
@[simp]
theorem uEntry_zero_right (α : ℕ → ℚ) (i : ℕ) : uEntry α i 0 = 0 := by
  rcases i with _ | _ | i <;> simp [uEntry]

/-- The row of `U_α` at the junk index `0` vanishes. -/
@[simp]
theorem uEntry_zero_left (α : ℕ → ℚ) (j : ℕ) : uEntry α 0 j = 0 := by
  simp [uEntry]

/-- The recurrence for `U_α` from the second row on, for columns `≥ 2`. -/
theorem uEntry_succ_succ (α : ℕ → ℚ) (i j : ℕ) :
    uEntry α (i + 2) (j + 2) =
      uEntry α (i + 1) (j + 1) +
        ((j : ℚ) - i + 1) * uEntry α (i + 1) (j + 2) := by
  simp only [uEntry, show ¬ j + 2 ≤ 1 by omega, ite_false]
  push_cast
  ring_nf

/-- **Lemma 1**, triangularity: `U_α` is upper
triangular: `U_{i,j} = 0` for `j < i`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 1.

Proves `Wanted` entry `uEntry_eq_zero_of_lt`. -/
theorem uEntry_eq_zero_of_lt (α : ℕ → ℚ) (i j : ℕ)
    (h : j < i) :
    uEntry α i j = 0 := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    rcases i with _ | i
    · obtain rfl : j = 0 := by omega
      simp
    rcases j with _ | _ | j
    · simp
    · simp [uEntry]
    · rw [uEntry_succ_succ, ih _ (by omega), zero_add]
      rcases Nat.lt_or_ge (j + 2) (i + 1) with hj | hj
      · rw [ih _ hj, mul_zero]
      · rw [show (j : ℚ) = i - 1 by
          rw [eq_sub_iff_add_eq]; exact_mod_cast (by omega : j + 1 = i)]
        ring

/-- Shifted form of Lemma 1: `U_{i+1, i+1+d} = Λ(α, i + 1, i + 1 + d)`. -/
theorem uEntry_add (α : ℕ → ℚ) (i d : ℕ) :
    uEntry α (i + 1) (i + 1 + d) =
      ∑ l ∈ range (i + 1), (i.choose l : ℚ) * ((l + d)! : ℚ) / d ! *
        α (l + d) := by
  have hd : ∀ d, (d ! : ℚ) ≠ 0 := fun d =>
    Nat.cast_ne_zero.mpr d.factorial_ne_zero
  induction i generalizing d with
  | zero => simp [uEntry, show 1 + d - 1 = d by omega, hd]
  | succ i ih =>
    have h := sum_range_choose_succ_mul
      (fun l => ((l + d)! : ℚ) / d ! * α (l + d)) i
    rw [show i + 1 + 1 + d = i + d + 2 by omega, uEntry_succ_succ,
      show i + d + 1 = i + 1 + d by omega,
      show i + d + 2 = i + 1 + (d + 1) by omega, ih, ih]
    simp only [mul_div_assoc, mul_assoc] at h ⊢
    rw [h, mul_sum]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    rw [show l + (d + 1) = l + 1 + d by omega, Nat.factorial_succ d]
    push_cast
    field_simp
    ring

/-- **Lemma 1**, explicit formula: for `j ≥ i ≥ 1`,
`U_{i,j} = Λ(α, i, j)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 1.

Proves `Wanted` entry `uEntry_eq_lambda`. -/
theorem uEntry_eq_lambda (α : ℕ → ℚ) (i j : ℕ)
    (hi : 1 ≤ i) (hij : i ≤ j) :
    uEntry α i j = lambda α i j := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
  rw [uEntry_add, lambda, Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  refine sum_congr rfl fun l _ => ?_
  rw [show l + (i + 1 + d) - (i + 1) = l + d by omega]

/-! ### The decomposition `S_α = S U_α` -/

/-- Entrywise form of `S_α = S U_α`: for every `N > i`,
`S_{i,j} = ∑_{k<N} S(i,k) U_{k,j}`. -/
theorem stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry (α : ℕ → ℚ)
    {N i : ℕ} (hi : i < N) (j : ℕ) :
    stirlingLikeEntry α i j =
      ∑ k ∈ range N, (Nat.stirlingSecond i k : ℚ) * uEntry α k j := by
  induction i using Nat.strong_induction_on generalizing N j with
  | _ i ih =>
  rcases i with _ | _ | i
  · refine (sum_eq_zero fun k _ => ?_).symm
    rcases k with _ | k
    · simp
    · simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.succ_pos k)]
  · rw [sum_eq_single 1 (fun k _ hk => ?_) (fun h => absurd (mem_range.2 hi) h)]
    · rcases j with _ | j <;>
        simp [stirlingLikeEntry, uEntry, Nat.stirlingSecond_self]
    · rcases k with _ | _ | k
      · simp
      · exact absurd rfl hk
      · simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : 1 < k + 2)]
  rcases j with _ | _ | m
  · simp [stirlingLikeEntry]
  · rw [sum_eq_single 1 (fun k _ hk => ?_)
      (fun h => absurd (mem_range.2 (by omega)) h)]
    · simp [stirlingLikeEntry, uEntry, Nat.stirlingSecond_one_right]
    · rcases k with _ | _ | k
      · simp
      · exact absurd rfl hk
      · simp [uEntry_eq_zero_of_lt α (k + 2) 1 (by omega)]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  -- Split off `k = 0` and apply the recurrence for `S(i + 2, k + 1)`.
  have hR : ∑ k ∈ range (M + 1), (Nat.stirlingSecond (i + 1 + 1) k : ℚ) *
        uEntry α k (m + 1 + 1) =
      ∑ k ∈ range M, ((k + 1 : ℕ) : ℚ) * Nat.stirlingSecond (i + 1) (k + 1) *
          uEntry α (k + 1) (m + 1 + 1) +
        ∑ k ∈ range M, (Nat.stirlingSecond (i + 1) k : ℚ) *
          uEntry α (k + 1) (m + 1 + 1) := by
    rw [sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul,
      add_zero, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    ring
  -- Shift the index back in the first sum: its terms at `0` and `M` vanish.
  have hshift : ∑ k ∈ range M, ((k + 1 : ℕ) : ℚ) *
        Nat.stirlingSecond (i + 1) (k + 1) * uEntry α (k + 1) (m + 1 + 1) =
      ∑ k ∈ range M, (k : ℚ) * Nat.stirlingSecond (i + 1) k *
        uEntry α k (m + 1 + 1) := by
    have h := sum_range_succ' (fun k => (k : ℚ) * Nat.stirlingSecond (i + 1) k *
      uEntry α k (m + 1 + 1)) M
    rw [sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (by omega : i + 1 < M)]
      at h
    simpa using h.symm
  -- The recurrence for `U_α` (the term `k = 0` vanishes as `S(i + 1, 0) = 0`).
  have hrec : ∀ k, (Nat.stirlingSecond (i + 1) k : ℚ) *
        uEntry α (k + 1) (m + 1 + 1) =
      (Nat.stirlingSecond (i + 1) k : ℚ) * (uEntry α k (m + 1) +
        ((m : ℚ) + 2 - k) * uEntry α k (m + 1 + 1)) := by
    intro k
    rcases k with _ | k
    · simp
    · rw [uEntry_succ_succ]
      push_cast
      ring_nf
  rw [hR, hshift, sum_congr rfl fun k _ => hrec k]
  simp only [stirlingLikeEntry, show m + 1 + 1 ≠ 1 by omega,
    show m + 1 + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
  rw [ih (i + 1) (by omega) (by omega : i + 1 < M),
    ih (i + 1) (by omega) (by omega : i + 1 < M), mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-! ### Theorems 3 and 4 and Proposition 5 -/

/-- **Theorem 3**: the two decompositions
`S_α(n) = S(n) U_α(n)` and `S_α(n) = V(n) R_α(n)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Theorem 3.

Proves `Wanted` entry `stirlingLikeMatrix_decomp`. -/
theorem stirlingLikeMatrix_decomp (α : ℕ → ℚ)
    (n : ℕ) :
    stirlingLikeMatrix α n = stirlingMatrix2 n * uMatrix α n ∧
      stirlingLikeMatrix α n = vandermondeMatrix n * rMatrix α n := by
  constructor <;> ext a b <;>
    simp only [stirlingLikeMatrix, stirlingMatrix2, uMatrix, vandermondeMatrix,
      rMatrix, Matrix.mul_apply, Matrix.of_apply]
  · rw [stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry α
        (by omega : a.val + 1 < n + 1), sum_range_succ', uEntry_zero_left,
      mul_zero, add_zero]
    exact (Fin.sum_univ_eq_sum_range (fun k => (Nat.stirlingSecond (a + 1)
      (k + 1) : ℚ) * uEntry α (k + 1) (b + 1)) n).symm
  · rw [stirlingLikeEntry_succ, sum_Icc_one_eq_sum_range,
      Fin.sum_univ_eq_sum_range (fun k => ((k + 1 : ℕ) : ℚ) ^ a.val *
        rEntry α (k + 1) (b + 1)) n]
    rw [← sum_subset (range_subset_range.2 (by omega : b.val + 1 ≤ n))
      fun k _ hk => by
        rw [rEntry, ite_eq_right (by simp only [mem_range] at hk; omega),
          mul_zero]]
    refine sum_congr rfl fun k hk => ?_
    rw [rEntry, ite_eq_left (by simp only [mem_range] at hk; omega), mul_assoc]

/-- The diagonal entries of `U_α` are `U_{i+1,i+1} = Ω(α, i + 1)`. -/
theorem uEntry_self (α : ℕ → ℚ) (i : ℕ) :
    uEntry α (i + 1) (i + 1) = omega α (i + 1) := by
  have h := uEntry_add α i 0
  rw [add_zero] at h
  rw [h, omega, Nat.add_sub_cancel]
  refine sum_congr rfl fun l _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  simp only [add_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  ring

/-- **Theorem 4**: `det S_α(n) = ∏_{i=0}^{n-1} Ω(α, i+1)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Theorem 4.

Proves `Wanted` entry `stirlingLikeMatrix_det`. -/
theorem stirlingLikeMatrix_det (α : ℕ → ℚ) (n : ℕ) :
    (stirlingLikeMatrix α n).det =
      ∏ i ∈ Finset.range n, omega α (i + 1) := by
  rw [(stirlingLikeMatrix_decomp α n).1, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ fun a b h => by
      simp only [stirlingMatrix2, Matrix.of_apply]
      rw [Nat.stirlingSecond_eq_zero_of_lt (by simpa using h), Nat.cast_zero],
    Matrix.det_of_isUpperTriangular fun a b h => by
      simp only [uMatrix, Matrix.of_apply]
      exact uEntry_eq_zero_of_lt α _ _ (by simpa using h),
    ← Fin.prod_univ_eq_prod_range (fun i => omega α (i + 1))]
  simp [stirlingMatrix2, uMatrix, Nat.stirlingSecond_self, uEntry_self]

-- `hj` is part of the source statement but is not needed: for `j = 0` both
-- sides are empty sums.
set_option linter.unusedVariables false in
/-- **Proposition 5**: for `i, j ≥ 1`,
`∑_{k=1}^{min(i,j)} S(i,k) Λ(α,k,j) =
∑_{k=1}^j k^{i-1} (-1)^{j-k}/(j-k)! Ψ_α(k)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 5.

Proves `Wanted` entry `sum_stirlingSecond_lambda`. -/
theorem sum_stirlingSecond_lambda (α : ℕ → ℚ)
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.Icc 1 (min i j),
        (Nat.stirlingSecond i k : ℚ) * lambda α k j =
      ∑ k ∈ Finset.Icc 1 j, (k : ℚ) ^ (i - 1) *
        ((-1 : ℚ) ^ (j - k) / (j - k).factorial) * psi α k := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← stirlingLikeEntry_succ,
    stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry α (lt_add_one (i + 1))]
  refine (sum_congr rfl fun k hk => ?_).trans
    (sum_subset (fun k hk => ?_) fun k hk hk' => ?_)
  · simp only [mem_Icc] at hk
    rw [uEntry_eq_lambda α k j hk.1 (by omega)]
  · simp only [mem_Icc, mem_range] at hk ⊢
    omega
  · simp only [mem_Icc, mem_range] at hk hk'
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [uEntry_zero_left, mul_zero]
    · rw [uEntry_eq_zero_of_lt α k j (by omega), mul_zero]

/-! ### The inverse of `R_α` -/

/-- Row `k` of `R_α` against the column `((j-1)↓_{m-1})_m`:
`∑_{m=1}^j R_{k,m} (j-1)↓_{m-1} = δ_{k,j} Ω(α, j)`. -/
theorem sum_rEntry_mul_descFactorial (α : ℕ → ℚ) (k j : ℕ) :
    ∑ m ∈ Icc 1 j, rEntry α k m * ((j - 1).descFactorial (m - 1) : ℚ) =
      if k = j then omega α j else 0 := by
  rcases k with _ | k
  · rw [sum_eq_zero fun m _ => by simp [rEntry, psi]]
    split_ifs with h
    · simp [← h, omega]
    · rfl
  rcases Nat.lt_or_ge j (k + 1) with hj | hj
  · rw [sum_eq_zero fun m hm => by
      rw [rEntry, ite_eq_right (by simp only [mem_Icc] at hm; omega), zero_mul],
      ite_eq_right (by omega)]
  obtain ⟨d, rfl⟩ : ∃ d, j = k + 1 + d := ⟨j - (k + 1), by omega⟩
  rw [← sum_subset (Icc_subset_Icc_left (by omega : 1 ≤ k + 1))
      fun m hm hm' => by
        simp only [mem_Icc, not_and_or, not_le] at hm hm'
        rw [rEntry, ite_eq_right (by omega), zero_mul],
    ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
    show k + 1 + d + 1 - (k + 1) = d + 1 by omega]
  calc ∑ t ∈ range (d + 1), rEntry α (k + 1) (k + 1 + t) *
        ((k + 1 + d - 1).descFactorial (k + 1 + t - 1) : ℚ)
      = ∑ t ∈ range (d + 1), (k + d)! * psi α (k + 1) *
          ((-1 : ℚ) ^ t / (t ! * (d - t)!)) := by
        refine sum_congr rfl fun t ht => ?_
        have ht : t ≤ d := Nat.lt_succ_iff.mp (mem_range.mp ht)
        have h := Nat.factorial_mul_descFactorial (by omega : k + t ≤ k + d)
        rw [show k + d - (k + t) = d - t by omega] at h
        have hD : ((k + d).descFactorial (k + t) : ℚ) =
            (k + d)! / (d - t)! := by
          rw [eq_div_iff (by positivity), mul_comm]
          exact_mod_cast h
        rw [rEntry, ite_eq_left (by omega), Nat.add_sub_cancel_left,
          show k + 1 + d - 1 = k + d by omega,
          show k + 1 + t - 1 = k + t by omega, hD]
        field_simp
    _ = if k + 1 = k + 1 + d then omega α (k + 1 + d) else 0 := by
        rw [← mul_sum, sum_range_neg_one_pow_div_factorial_mul]
        rcases d with _ | d
        · rw [add_zero, omega_succ]
          simp
        · simp only [Nat.add_one_ne_zero, ite_false, mul_zero]
          rw [ite_eq_right (by omega)]

/-- **Lemma 7**: `R̃_α(n) = R_α(n)⁻¹` provided
`∏_{j=1}^n Ω(α, j) ≠ 0`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Lemma 7.

Proves `Wanted` entry `rTildeMatrix_eq_inv`. -/
theorem rTildeMatrix_eq_inv (α : ℕ → ℚ) (n : ℕ)
    (h : ∏ j ∈ Finset.Icc 1 n, omega α j ≠ 0) :
    rTildeMatrix α n = (rMatrix α n)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  ext a b
  have hb : omega α (b + 1) ≠ 0 :=
    prod_ne_zero_iff.mp h _ (mem_Icc.2 ⟨by omega, b.isLt⟩)
  have hsum := sum_rEntry_mul_descFactorial α (a + 1) (b + 1)
  rw [Nat.add_sub_cancel] at hsum
  simp only [rMatrix, rTildeMatrix, Matrix.mul_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [sum_fin_eq_sum_Icc
      (fun m => rEntry α (a + 1) m * rTildeEntry α m (b + 1)),
    ← sum_subset (Icc_subset_Icc_right (by omega : b.val + 1 ≤ n))
      fun m hm hm' => by
        simp only [mem_Icc, not_and_or, not_le] at hm hm'
        rw [rTildeEntry, ite_eq_right (by omega), mul_zero]]
  rw [sum_congr rfl fun m hm => by
      rw [rTildeEntry, ite_eq_left (mem_Icc.mp hm).2, ← mul_div_assoc],
    ← sum_div, Nat.add_sub_cancel, hsum]
  simp only [Nat.add_right_cancel_iff, Fin.val_inj]
  split_ifs
  · exact div_self hb
  · exact zero_div _

/-! ### Propositions 8 and 9 and Corollary 10 -/

-- The nonvanishing hypothesis `h` is part of the source statement but is not
-- needed (see `sum_rEntry_mul_descFactorial`).
/-- **Proposition 8**: under the nonvanishing condition,
`∑_{k₁=1}^i ∑_{k₂=k₁}^j S(i,k₁) (j-1)↓_{k₂-1}
Λ(α,k₁,k₂) = j^{i-1} Ω(α,j)`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 8.

Proves `Wanted` entry `sum_stirlingSecond_descFactorial_lambda`. -/
theorem sum_stirlingSecond_descFactorial_lambda
    (α : ℕ → ℚ) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : ∏ k ∈ Finset.Icc 1 (max i j), omega α k ≠ 0) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc k₁ j,
        (Nat.stirlingSecond i k₁ : ℚ) *
          (Nat.descFactorial (j - 1) (k₂ - 1) : ℚ) *
          lambda α k₁ k₂ =
      (j : ℚ) ^ (i - 1) * omega α j := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  calc _ = ∑ k₁ ∈ range (i + 1 + 1), ∑ k₂ ∈ Icc 1 j,
          ((j - 1).descFactorial (k₂ - 1) : ℚ) *
            ((Nat.stirlingSecond (i + 1) k₁ : ℚ) * uEntry α k₁ k₂) := by
        refine (sum_congr rfl fun k₁ hk₁ => ?_).trans
          (sum_subset (fun k hk => ?_) fun k hk hk' => ?_)
        · simp only [mem_Icc] at hk₁
          refine (sum_congr rfl fun k₂ hk₂ => ?_).trans
            (sum_subset (Icc_subset_Icc_left hk₁.1) fun k₂ hk₂ hk₂' => ?_)
          · rw [uEntry_eq_lambda α k₁ k₂ hk₁.1 (mem_Icc.mp hk₂).1]
            ring
          · simp only [mem_Icc, not_and_or, not_le] at hk₂ hk₂'
            rw [uEntry_eq_zero_of_lt α k₁ k₂ (by omega)]
            ring
        · simp only [mem_Icc, mem_range] at hk ⊢
          omega
        · obtain rfl : k = 0 := by
            simp only [mem_Icc, mem_range] at hk hk'
            omega
          simp
    _ = ∑ k₂ ∈ Icc 1 j, ((j - 1).descFactorial (k₂ - 1) : ℚ) *
          stirlingLikeEntry α (i + 1) k₂ := by
        rw [sum_comm]
        refine sum_congr rfl fun k₂ _ => ?_
        rw [← mul_sum, stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry α
          (lt_add_one (i + 1))]
    _ = ∑ k₂ ∈ Icc 1 j, ∑ k ∈ Icc 1 j, (k : ℚ) ^ i *
          (rEntry α k k₂ * ((j - 1).descFactorial (k₂ - 1) : ℚ)) := by
        refine sum_congr rfl fun k₂ hk₂ => ?_
        rw [stirlingLikeEntry_succ, mul_sum]
        refine (sum_congr rfl fun k hk => ?_).trans
          (sum_subset (Icc_subset_Icc_right (mem_Icc.mp hk₂).2)
            fun k hk hk' => ?_)
        · rw [rEntry, ite_eq_left (mem_Icc.mp hk).2]
          ring
        · simp only [mem_Icc, not_and_or, not_le] at hk hk'
          rw [rEntry, ite_eq_right (by omega)]
          ring
    _ = ∑ k ∈ Icc 1 j, (k : ℚ) ^ i * if k = j then omega α j else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_sum, sum_rEntry_mul_descFactorial]
    _ = (j : ℚ) ^ i * omega α j := by
        simp only [mul_ite, mul_zero]
        rw [sum_ite_eq_of_mem' _ _ _ (mem_Icc.2 ⟨hj, le_rfl⟩)]

-- `hj` is part of the source statement but is not needed: for `j = 0` both
-- sides are `0`.
set_option linter.unusedVariables false in
/-- **Proposition 9**: for `i, j ≥ 1`,
`∑_{k₁=1}^i ∑_{k₂=1}^j s(i,k₁) k₂^{k₁-1}
(-1)^{j-k₂}/(j-k₂)! Ψ_α(k₂)` equals `Λ(α,i,j)` if
`i ≤ j` and `0` if `i > j`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Proposition 9.

Proves `Wanted` entry `sum_signed_psi_eq`. -/
theorem sum_signed_psi_eq (α : ℕ → ℚ) (i j : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc 1 j,
        (MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) * (k₂ : ℚ) ^ (k₁ - 1) *
          ((-1 : ℚ) ^ (j - k₂) / (j - k₂).factorial) * psi α k₂ =
      if i ≤ j then lambda α i j else 0 := by
  calc _ = ∑ k₁ ∈ range (i + 1), ∑ k ∈ range (i + 1), uEntry α k j *
          ((MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) *
            Nat.stirlingSecond k₁ k) := by
        refine (sum_congr rfl fun k₁ hk₁ => ?_).trans
          (sum_subset (fun k hk => ?_) fun k hk hk' => ?_)
        · simp only [mem_Icc] at hk₁
          obtain ⟨k, rfl⟩ : ∃ k, k₁ = k + 1 := ⟨k₁ - 1, by omega⟩
          have h := stirlingLikeEntry_succ α k j
          rw [stirlingLikeEntry_eq_sum_stirlingSecond_mul_uEntry α
            (by omega : k + 1 < i + 1)] at h
          rw [Nat.add_sub_cancel]
          calc _ = (MetaMathlibExt.signedStirlingFirst i (k + 1) : ℚ) *
                ∑ k₂ ∈ Icc 1 j, (k₂ : ℚ) ^ k *
                  ((-1 : ℚ) ^ (j - k₂) / (j - k₂).factorial) * psi α k₂ := by
                rw [mul_sum]
                exact sum_congr rfl fun _ _ => by ring
            _ = _ := by
                rw [← h, mul_sum]
                exact sum_congr rfl fun _ _ => by ring
        · simp only [mem_Icc, mem_range] at hk ⊢
          omega
        · obtain rfl : k = 0 := by
            simp only [mem_Icc, mem_range] at hk hk'
            omega
          refine sum_eq_zero fun k _ => ?_
          rcases k with _ | k
          · simp
          · simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.succ_pos k)]
    _ = ∑ k ∈ range (i + 1), uEntry α k j * if i = k then 1 else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_sum]
        congr 1
        exact_mod_cast
          MetaMathlibExt.sum_signedStirlingFirst_mul_stirlingSecond i k
    _ = uEntry α i j := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [sum_ite_eq_of_mem _ _ _ (self_mem_range_succ i)]
    _ = _ := by
        split_ifs with hij
        · exact uEntry_eq_lambda α i j hi hij
        · exact uEntry_eq_zero_of_lt α i j (by omega)

/-- **Corollary 10**: `∑_{k₁=1}^i ∑_{k₂=1}^j
(-1)^{j-k₂} s(i,k₁) k₂^{k₁-1} / ((j-k₂)! (k₂-1)!) =
δ_{i,j}`.

Source: M. Bahrami-Taghanaki, A. R. Moghaddamfar, Nima
Salehy, and Navid Salehy, "Some Identities Involving
Stirling Numbers Arising from Matrix Decompositions",
Corollary 10.

Proves `Wanted` entry `sum_signed_eq_delta`. -/
theorem sum_signed_eq_delta (i j : ℕ) (hi : 1 ≤ i)
    (hj : 1 ≤ j) :
    ∑ k₁ ∈ Finset.Icc 1 i, ∑ k₂ ∈ Finset.Icc 1 j,
        (-1 : ℚ) ^ (j - k₂) * (MetaMathlibExt.signedStirlingFirst i k₁ : ℚ) *
          (k₂ : ℚ) ^ (k₁ - 1) /
          ((j - k₂).factorial * (k₂ - 1).factorial) =
      if i = j then 1 else 0 := by
  -- Specialize Proposition 9 to `α = (1, 0, 0, …)`.
  have hpsi : ∀ k, 1 ≤ k →
      psi (fun l => if l = 0 then 1 else 0) k = 1 / (k - 1)! := by
    intro k hk
    rw [psi, sum_eq_single 0 (fun l _ hl => by simp [hl])
      (fun h => absurd (mem_range.2 (by omega)) h)]
    simp
  have hlam : (if i ≤ j then lambda (fun l => if l = 0 then 1 else 0) i j
      else 0) = if i = j then 1 else 0 := by
    rcases eq_or_ne i j with rfl | hij
    · rw [ite_eq_left le_rfl, ite_eq_left rfl, lambda,
        sum_eq_single 0 (fun l _ hl => by simp [hl])
          (fun h => absurd (mem_range.2 (by omega)) h)]
      simp
    · rw [ite_eq_right hij]
      split_ifs with hij'
      · exact sum_eq_zero fun l _ => by
          simp only [show l + j - i ≠ 0 by omega, ite_false, mul_zero]
      · rfl
  rw [← hlam, ← sum_signed_psi_eq _ i j hi hj]
  refine sum_congr rfl fun k₁ _ => sum_congr rfl fun k₂ hk₂ => ?_
  rw [hpsi k₂ (mem_Icc.mp hk₂).1]
  ring

end MathlibExt.Combinatorics.Enumerative.StirlingMatrixWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSCovariance
import Mathlib.Data.Nat.Choose.Cast

/-!
# Fu's closed form for the covariances of the site frequency spectrum

**Source.** Y.-X. Fu (1995), *Statistical properties of segregating sites*, Theor. Popul. Biol.
48, 172–197, the closed form of `σ_{ij}`: under Kingman's
coalescent with infinite-sites mutation at scaled rate `θ`, the unfolded site frequency
spectrum satisfies `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²` for `1 ≤ i, j ≤ n - 1`, with
`a_n = ∑_{k=1}^{n-1} 1/k` (`tajimaA1`),
`β_n(i) = 2n / ((n - i + 1)(n - i)) · (a_{n+1} - a_i) - 2 / (n - i)` (`fuBeta`) and

* `σ_{ii} = β_n(i + 1)` if `2i < n`; `2 (a_n - a_i) / (n - i) - 1/i²` if `2i = n`;
  `β_n(i) - 1/i²` if `2i > n`;
* for `i > j`: `σ_{ij} = (β_n(i + 1) - β_n(i)) / 2` if `i + j < n`;
  `(a_n - a_i) / (n - i) + (a_n - a_j) / (n - j) - (β_n(i) + β_n(j + 1)) / 2 - 1/(ij)` if
  `i + j = n`; `(β_n(j) - β_n(j + 1)) / 2 - 1/(ij)` if `i + j > n`

(`fuSigma`, symmetric in `i, j`). In the conventions of `Coalescent/SFSCovariance.lean`
(mutations at rate `θ / 2` per unit branch length), `σ_{ij} = Cov(L_i, L_j) / 4`, where `L_i` is
the total length of the branches subtending `i` sample copies.

## What is proved

The covariance formula of the SFS comes from `SFSCovariance.covariance_count_kingman`
(not repeated here): `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + (θ / 2)² Cov(L_i, L_j)`. Fu's closed form
of the branch-length covariances enters as the hypothesis `Cov(L_i, L_j) = 4 σ_{ij}`; deriving
it from the random-joining law needs the joint second moments of the block counts and is not
done here. From it:

* `covariance_count_kingman_of_fuSigma`: Fu's `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²`;
* `variance_sum_sfsLength_of_fuSigma`: `Var(∑_i c_i L_i) = 4 ∑_{i,j} c_i c_j σ_{ij}`, and
  `variance_sum_kingman_of_fuSigma`:
  `Var(∑_i a_i ξ_i) = θ ∑_i a_i² / i + θ² ∑_{i,j} a_i a_j σ_{ij}`.

The Tajima (1989) numbers from Fu's matrix:

* `sum_fuSigma_row`: the row sums are `∑_j σ_{ij} = (a_n - a_i) / (n - i)`; the `β_n` terms
  cancel in each row;
* `sum_sum_fuSigma`: `∑_{i,j} σ_{ij} = a₂`, hence `Var(∑_i L_i) = 4 a₂`
  (`variance_sum_sfsLength_one_of_fuSigma`) and Watterson's `Var(S / a₁) = θ / a₁ + θ² a₂ / a₁²`
  (`variance_watterson_kingman_of_fuSigma`);
* `sum_sum_piWeight_mul_fuSigma`: `∑_{i,j} π_i σ_{ij} = (n + 2) / (2n)` for the weights
  `π_i = i (n - i) / C(n, 2)` of `θ_π`, the `θ²` coefficient of `Cov(θ_π, S)`;
* `sum_sum_piWeight_mul_piWeight_mul_fuSigma`: `∑_{i,j} π_i π_j σ_{ij} = b₂ =
  2 (n² + n + 3) / (9 n (n - 1))`, hence `Var(θ_π[L]) = 4 b₂`
  (`variance_thetaPi_sfsLength_of_fuSigma`) and `Var θ_π = b₁ θ + b₂ θ²`
  (`variance_thetaPi_kingman_of_fuSigma`, Tajima 1983). The `β_n` terms cancel against any
  weights symmetric under `i ↦ n - i`: in each row the columns below `min(i, n - i)` cancel those
  above `max(i, n - i)` under `j ↦ n - j`, and the band left in row `n - i` is minus the band of
  row `i`;
* `sum_sum_tajimaNumWeight_mul_fuSigma`: for the weights `w_i = π_i - 1 / a₁` of Tajima's `D`
  numerator, `∑_{i,j} w_i w_j σ_{ij} = c₂ = b₂ - (n + 2) / (a₁ n) + a₂ / a₁²`; hence
  `Var(∑_i w_i L_i) = 4 c₂` (`variance_tajimaNumWeight_sfsLength_of_fuSigma`) and
  `Var(θ_π - S / a₁) = c₁ θ + c₂ θ²` (`variance_tajimaNumerator_kingman_of_fuSigma`), the
  identity that `KingmanTimes.variance_tajimaNumerator` proves from pairwise coalescence times.

## References

* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995),
  172–197.
* F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105
  (1983), 437–460.
* F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA
  polymorphism*, Genetics 123 (1989), 585–595.
* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm

open SiteFrequencySpectrum VariableSFS SFSCovariance

/-- Fu's `β_n(i) = 2n / ((n - i + 1)(n - i)) · (a_{n+1} - a_i) - 2 / (n - i)` (Fu 1995), with
`a_m = tajimaA1 m = ∑_{k=1}^{m-1} 1/k`. Meaningful for `1 ≤ i ≤ n - 1`. -/
noncomputable def fuBeta (n i : ℕ) : ℝ :=
  2 * n / (((n : ℝ) - i + 1) * ((n : ℝ) - i)) * (tajimaA1 (n + 1) - tajimaA1 i) -
    2 / ((n : ℝ) - i)

/-- **Fu's `σ_{ij}`** (Fu 1995): the coefficient of `θ²` in `Cov(ξ_i, ξ_j)` under Kingman's
coalescent, equal to `Cov(L_i, L_j) / 4`. The diagonal has three cases (`2i < n`, `2i = n`,
`2i > n`), the off-diagonal entries three cases (`i + j < n`, `= n`, `> n`), written with
`max i j` and `min i j` so that the definition is symmetric. Meaningful for `1 ≤ i, j ≤ n - 1`. -/
noncomputable def fuSigma (n i j : ℕ) : ℝ :=
  if i = j then
    if 2 * i < n then fuBeta n (i + 1)
    else if 2 * i = n then 2 * (tajimaA1 n - tajimaA1 i) / ((n : ℝ) - i) - 1 / (i : ℝ) ^ 2
    else fuBeta n i - 1 / (i : ℝ) ^ 2
  else if i + j < n then (fuBeta n (max i j + 1) - fuBeta n (max i j)) / 2
  else if i + j = n then
    (tajimaA1 n - tajimaA1 (max i j)) / ((n : ℝ) - max i j) +
      (tajimaA1 n - tajimaA1 (min i j)) / ((n : ℝ) - min i j) -
      (fuBeta n (max i j) + fuBeta n (min i j + 1)) / 2 - 1 / ((i : ℝ) * j)
  else (fuBeta n (min i j) - fuBeta n (min i j + 1)) / 2 - 1 / ((i : ℝ) * j)

/-- Fu's matrix is symmetric. -/
theorem fuSigma_comm (n i j : ℕ) : fuSigma n i j = fuSigma n j i := by
  unfold fuSigma
  by_cases h : i = j
  · subst h; rfl
  · simp only [h, Ne.symm h, ↓reduceIte, add_comm i j, max_comm i j, min_comm i j,
      mul_comm (i : ℝ) j]

section Row

variable {n i j : ℕ}

private lemma fuSigma_diag_lt (h : 2 * i < n) : fuSigma n i i = fuBeta n (i + 1) := by
  simp [fuSigma, h]

private lemma fuSigma_diag_eq (h : 2 * i = n) :
    fuSigma n i i = 2 * (tajimaA1 n - tajimaA1 i) / ((n : ℝ) - i) - 1 / (i : ℝ) ^ 2 := by
  simp [fuSigma, h]

private lemma fuSigma_diag_gt (h : n < 2 * i) : fuSigma n i i = fuBeta n i - 1 / (i : ℝ) ^ 2 := by
  simp [fuSigma, show ¬ 2 * i < n by omega, show 2 * i ≠ n by omega]

private lemma fuSigma_off_lt (hji : j < i) (h : i + j < n) :
    fuSigma n i j = (fuBeta n (i + 1) - fuBeta n i) / 2 := by
  simp [fuSigma, hji.ne', h, max_eq_left hji.le]

private lemma fuSigma_off_eq (hji : j < i) (h : i + j = n) :
    fuSigma n i j = (tajimaA1 n - tajimaA1 i) / ((n : ℝ) - i) +
      (tajimaA1 n - tajimaA1 j) / ((n : ℝ) - j) -
      (fuBeta n i + fuBeta n (j + 1)) / 2 - 1 / ((i : ℝ) * j) := by
  simp [fuSigma, hji.ne', h, max_eq_left hji.le, min_eq_right hji.le]

private lemma fuSigma_off_gt (hji : j < i) (h : n < i + j) :
    fuSigma n i j = (fuBeta n j - fuBeta n (j + 1)) / 2 - 1 / ((i : ℝ) * j) := by
  simp [fuSigma, hji.ne', show ¬ i + j < n by omega, show i + j ≠ n by omega,
    min_eq_right hji.le]


private lemma sum_Ico_inv {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Ico a b, (j : ℝ)⁻¹ = tajimaA1 b - tajimaA1 a := by
  unfold tajimaA1
  rw [← sum_Ico_consecutive _ ha hab]
  ring

private lemma tajimaA1_succ {k : ℕ} (hk : 1 ≤ k) : tajimaA1 (k + 1) = tajimaA1 k + (k : ℝ)⁻¹ := by
  unfold tajimaA1
  rw [sum_Ico_succ_top hk]

/-- Row `i`, columns `j < q` with `i + j < n`. -/
private lemma row_left {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ i) (hiq : i + q ≤ n) :
    ∑ j ∈ Ico 1 q, fuSigma n i j = ((q : ℝ) - 1) * ((fuBeta n (i + 1) - fuBeta n i) / 2) := by
  rw [sum_congr rfl fun j hj => fuSigma_off_lt (by have := mem_Ico.1 hj; omega)
      (by have := mem_Ico.1 hj; omega), sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub hq1]
  simp

/-- Row `i`, columns `p ≤ j < n` with `i < j` and `n < i + j`. -/
private lemma row_right {p : ℕ} (hip : i < p) (hp : n < i + p) (hpn : p ≤ n) :
    ∑ j ∈ Ico p n, fuSigma n i j =
      ((n : ℝ) - p) * ((fuBeta n i - fuBeta n (i + 1)) / 2) -
        (tajimaA1 n - tajimaA1 p) / i := by
  have hi0 : (i : ℝ) ≠ 0 := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · omega
    · positivity
  rw [sum_congr rfl fun j hj => (fuSigma_comm n i j).trans (fuSigma_off_gt
      (by have := mem_Ico.1 hj; omega) (by have := mem_Ico.1 hj; omega)),
    sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hpn,
    ← sum_Ico_inv (by omega) hpn, div_eq_mul_inv _ (i : ℝ), sum_mul]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := mem_Ico.1 hj; omega)
  field_simp

private lemma sum_inv_mul {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (i : ℕ) :
    ∑ j ∈ Ico p q, 1 / ((i : ℝ) * j) = (tajimaA1 q - tajimaA1 p) / i := by
  rw [← sum_Ico_inv hp hpq, div_eq_mul_inv _ (i : ℝ), sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [one_div, mul_inv, mul_comm]

/-- **Row sums of Fu's covariance matrix**: `∑_{j=1}^{n-1} σ_{ij} = (a_n - a_i) / (n - i)`.
The `β_n` terms cancel in every row. -/
theorem sum_fuSigma_row {n i : ℕ} (hi : i ∈ Ico 1 n) :
    ∑ j ∈ Ico 1 n, fuSigma n i j = (tajimaA1 n - tajimaA1 i) / ((n : ℝ) - i) := by
  obtain ⟨hi1, hin⟩ := mem_Ico.1 hi
  have hni : (n : ℝ) - i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hin.ne')
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hcast : ((n - i : ℕ) : ℝ) = n - i := Nat.cast_sub hin.le
  have hnni : (n : ℝ) - ((n : ℝ) - i) = i := by ring
  rw [← sum_Ico_consecutive _ hi1 hin.le, sum_eq_sum_Ico_succ_bot hin]
  rcases lt_trichotomy (2 * i) n with h | h | h
  · rw [row_left hi1 le_rfl (by omega), fuSigma_diag_lt h,
      ← sum_Ico_consecutive _ (show i + 1 ≤ n - i by omega) (show n - i ≤ n by omega),
      sum_eq_sum_Ico_succ_bot (show n - i < n by omega),
      row_right (p := n - i + 1) (by omega) (by omega) (by omega),
      sum_congr rfl fun j hj => (fuSigma_comm n i j).trans (fuSigma_off_lt
        (mem_Ico.1 hj).1 (by have := mem_Ico.1 hj; omega)),
      ← sum_div, sum_Ico_sub (f := fuBeta n) (by omega),
      fuSigma_comm n i (n - i), fuSigma_off_eq (by omega) (by omega),
      tajimaA1_succ (show 1 ≤ n - i by omega)]
    simp only [Nat.cast_add, Nat.cast_one, hcast, hnni]
    field_simp
    ring
  · have hn2 : (n : ℝ) = 2 * i := by exact_mod_cast h.symm
    rw [row_left hi1 le_rfl (by omega), fuSigma_diag_eq h,
      row_right (p := i + 1) (by omega) (by omega) (by omega), tajimaA1_succ hi1]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hn2] at hni ⊢
    field_simp
    ring
  · have hmid : ∑ j ∈ Ico (n - i + 1) i, fuSigma n i j =
        (fuBeta n (n - i + 1) - fuBeta n i) / 2 - (tajimaA1 i - tajimaA1 (n - i + 1)) / i := by
      rw [sum_congr rfl fun j hj => fuSigma_off_gt (by have := mem_Ico.1 hj; omega)
          (by have := mem_Ico.1 hj; omega), sum_sub_distrib, ← sum_div,
        sum_inv_mul (by omega) (by omega)]
      have tel := sum_Ico_sub (f := fuBeta n) (m := n - i + 1) (n := i) (by omega)
      have : ∑ j ∈ Ico (n - i + 1) i, (fuBeta n j - fuBeta n (j + 1)) =
          -∑ j ∈ Ico (n - i + 1) i, (fuBeta n (j + 1) - fuBeta n j) := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun _ _ => by ring
      rw [this, tel]
      ring
    rw [← sum_Ico_consecutive _ (show 1 ≤ n - i by omega) (show n - i ≤ i by omega),
      sum_eq_sum_Ico_succ_bot (show n - i < i by omega),
      row_left (q := n - i) (by omega) (by omega) (by omega),
      fuSigma_off_eq (j := n - i) (by omega) (by omega), hmid, fuSigma_diag_gt h,
      row_right (p := i + 1) (by omega) (by omega) (by omega), tajimaA1_succ hi1,
      tajimaA1_succ (show 1 ≤ n - i by omega)]
    simp only [Nat.cast_add, Nat.cast_one, hcast, hnni]
    field_simp
    ring

end Row

/-! ### The `θ²` coefficients of Watterson's estimator and of `Cov(θ_π, S)` -/

private lemma sum_inv_reflect (n : ℕ) :
    ∑ m ∈ Ico 1 n, (((n - m : ℕ) : ℝ))⁻¹ = tajimaA1 n := by
  unfold tajimaA1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [sum_Ico_reflect (fun j => ((j : ℕ) : ℝ)⁻¹) 1 (show n ≤ n + 1 by omega)]
  congr 1
  ext j
  simp only [mem_Ico]
  omega

/-- `∑_{m=1}^{n-1} 1 / (m (n - m)) = 2 a_n / n`. -/
private lemma sum_inv_mul_sub (n : ℕ) :
    ∑ m ∈ Ico 1 n, 1 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) = 2 * tajimaA1 n / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tajimaA1]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ m ∈ Ico 1 n, 1 / ((m : ℝ) * ((n - m : ℕ) : ℝ)) =
      ((m : ℝ)⁻¹ + (((n - m : ℕ) : ℝ))⁻¹) / n := fun m hm => by
    obtain ⟨hm1, hmn⟩ := mem_Ico.1 hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hnm : ((n - m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [Nat.cast_sub hmn.le] at hnm ⊢
    field_simp
    ring
  rw [sum_congr rfl h, ← sum_div, sum_add_distrib, sum_inv_reflect]
  unfold tajimaA1
  ring

/-- `∑_{m=1}^{n-1} (a_n - a_{n-m}) / m = a₂`. -/
private lemma sum_tail_div (n : ℕ) :
    ∑ m ∈ Ico 1 n, (tajimaA1 n - tajimaA1 (n - m)) / m = tajimaA2 n := by
  induction n with
  | zero => simp [tajimaA2]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [tajimaA2]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hstep : ∀ m ∈ Ico 1 n, (tajimaA1 (n + 1) - tajimaA1 (n + 1 - m)) / m =
        (tajimaA1 n - tajimaA1 (n - m)) / m + ((n : ℝ)⁻¹ / m -
          1 / ((m : ℝ) * ((n - m : ℕ) : ℝ))) := fun m hm => by
      obtain ⟨hm1, hmn⟩ := mem_Ico.1 hm
      rw [show n + 1 - m = n - m + 1 by omega, tajimaA1_succ (by omega : 1 ≤ n - m),
        tajimaA1_succ hn]
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hnm : ((n - m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      field_simp
      ring
    have hinv : ∑ x ∈ Ico 1 n, (n : ℝ)⁻¹ / x = (n : ℝ)⁻¹ * tajimaA1 n := by
      rw [tajimaA1, mul_sum]
      exact sum_congr rfl fun _ _ => div_eq_mul_inv _ _
    have ha1 : tajimaA1 1 = 0 := by simp [tajimaA1]
    rw [sum_Ico_succ_top (by omega : 1 ≤ n), sum_congr rfl hstep, sum_add_distrib, ih,
      sum_sub_distrib, sum_inv_mul_sub, hinv, show n + 1 - n = 1 by omega, ha1,
      tajimaA1_succ hn]
    unfold tajimaA2
    rw [sum_Ico_succ_top (by omega : 1 ≤ n)]
    field_simp
    ring

/-- **Watterson's `θ²` coefficient from Fu's closed form**: `∑_{i,j=1}^{n-1} σ_{ij} = a₂`, so
`Var(∑_i L_i) = 4 a₂` and `Var S = θ a₁ + θ² a₂` (Watterson 1975). -/
theorem sum_sum_fuSigma (n : ℕ) :
    ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, fuSigma n i j = tajimaA2 n := by
  rw [sum_congr rfl fun i hi => sum_fuSigma_row hi, ← sum_tail_div n]
  refine sum_nbij' (fun i => n - i) (fun m => n - m) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Ico] at hi ⊢
    omega
  · intro m hm
    simp only [mem_Ico] at hm ⊢
    omega
  · intro i hi
    simp only [mem_Ico] at hi
    omega
  · intro m hm
    simp only [mem_Ico] at hm
    omega
  · intro i hi
    obtain ⟨hi1, hin⟩ := mem_Ico.1 hi
    rw [Nat.sub_sub_self hin.le, Nat.cast_sub hin.le]

private lemma sum_Ico_cast (n : ℕ) : ∑ i ∈ Ico 1 n, (i : ℝ) = n * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [sum_Ico_succ_top (by omega : 1 ≤ n), ih]
    push_cast
    ring

/-- `∑_{i=1}^{n-1} i (a_n - a_i) = (n - 1)(n + 2) / 4` for `n ≥ 1`. -/
private lemma sum_mul_tail {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Ico 1 n, (i : ℝ) * (tajimaA1 n - tajimaA1 i) = ((n : ℝ) - 1) * (n + 2) / 4 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [sum_Ico_succ_top hn, tajimaA1_succ hn]
    have : ∀ i ∈ Ico 1 n, (i : ℝ) * (tajimaA1 n + (n : ℝ)⁻¹ - tajimaA1 i) =
        (i : ℝ) * (tajimaA1 n - tajimaA1 i) + (i : ℝ) * (n : ℝ)⁻¹ := fun i _ => by ring
    rw [sum_congr rfl this, sum_add_distrib, ih, ← sum_mul, sum_Ico_cast]
    push_cast
    rw [add_sub_cancel_left]
    field_simp
    ring

/-- **The `θ²` coefficient of `Cov(θ_π, S)` from Fu's closed form**:
`∑_{i,j=1}^{n-1} π_i σ_{ij} = (n + 2) / (2 n)` with `π_i = i (n - i) / C(n, 2)`, the weights of
`θ_π` (Tajima 1983, 1989). -/
theorem sum_sum_piWeight_mul_fuSigma {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, ((n : ℝ) - i) / (n.choose 2 : ℝ) * i * fuSigma n i j =
      ((n : ℝ) + 2) / (2 * n) := by
  have hC : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, ((n : ℝ) - i) / (n.choose 2 : ℝ) * i * fuSigma n i j =
      (i : ℝ) * (tajimaA1 n - tajimaA1 i) / (n.choose 2 : ℝ) := fun i hi => by
    rw [← mul_sum, sum_fuSigma_row hi]
    have : (n : ℝ) - i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (mem_Ico.1 hi).2.ne')
    field_simp
  rw [sum_congr rfl h, ← sum_div, sum_mul_tail (by omega), hC]
  field_simp
  ring

/-! ### The `θ_π` coefficient `b₂`

Split `σ_{ij}` into its `β_n`-free part `fuSigmaR` and the rest `fuSigmaB`. Against weights that
are symmetric under `i ↦ n - i` (such as `π_i`) the `β_n` part sums to zero: in each row the
columns below `min(i, n - i)` cancel the columns above `max(i, n - i)` under `j ↦ n - j`, and the
remaining band of row `n - i` is minus that of row `i`. -/

/-- The `β_n`-free part of `σ_{ij}`. -/
private noncomputable def fuSigmaR (n i j : ℕ) : ℝ :=
  (if i + j = n then (tajimaA1 n - tajimaA1 i) / j + (tajimaA1 n - tajimaA1 j) / i -
    1 / ((i : ℝ) * j) else 0) - if n < i + j then 1 / ((i : ℝ) * j) else 0

/-- The `β_n` part of `σ_{ij}`. -/
private noncomputable def fuSigmaB (n i j : ℕ) : ℝ := fuSigma n i j - fuSigmaR n i j

private lemma fuSigmaB_comm (n i j : ℕ) : fuSigmaB n i j = fuSigmaB n j i := by
  unfold fuSigmaB fuSigmaR
  rw [fuSigma_comm, add_comm i j, mul_comm (i : ℝ) j]
  ring_nf

section B

variable {n i j : ℕ}

private lemma fuSigmaB_diag_lt (h : 2 * i < n) : fuSigmaB n i i = fuBeta n (i + 1) := by
  simp [fuSigmaB, fuSigmaR, fuSigma_diag_lt h, show i + i ≠ n by omega,
    show ¬ n < i + i by omega]

private lemma fuSigmaB_diag_eq (hi : 1 ≤ i) (h : 2 * i = n) : fuSigmaB n i i = 0 := by
  have hn : (n : ℝ) - i = i := by
    rw [← h]; push_cast; ring
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  simp only [fuSigmaB, fuSigmaR, fuSigma_diag_eq h, show i + i = n by omega, ↓reduceIte,
    lt_irrefl, hn]
  field_simp
  ring

private lemma fuSigmaB_diag_gt (h : n < 2 * i) : fuSigmaB n i i = fuBeta n i := by
  simp only [fuSigmaB, fuSigmaR, fuSigma_diag_gt h, show i + i ≠ n by omega,
    show n < i + i by omega, ↓reduceIte]
  ring

private lemma fuSigmaB_off_lt (hji : j < i) (h : i + j < n) :
    fuSigmaB n i j = (fuBeta n (i + 1) - fuBeta n i) / 2 := by
  simp [fuSigmaB, fuSigmaR, fuSigma_off_lt hji h, show i + j ≠ n by omega,
    show ¬ n < i + j by omega]

private lemma fuSigmaB_off_eq (hji : j < i) (h : i + j = n) :
    fuSigmaB n i j = -(fuBeta n i + fuBeta n (j + 1)) / 2 := by
  have h1 : (n : ℝ) - i = j := by rw [← h]; push_cast; ring
  have h2 : (n : ℝ) - j = i := by rw [← h]; push_cast; ring
  simp only [fuSigmaB, fuSigmaR, fuSigma_off_eq hji h, h, ↓reduceIte, lt_irrefl, h1, h2]
  ring

private lemma fuSigmaB_off_gt (hji : j < i) (h : n < i + j) :
    fuSigmaB n i j = (fuBeta n j - fuBeta n (j + 1)) / 2 := by
  simp only [fuSigmaB, fuSigmaR, fuSigma_off_gt hji h, show i + j ≠ n by omega, h,
    ↓reduceIte]
  ring

end B

/-- `∑_{j=n-m+1}^{n-1} f j = ∑_{j=1}^{m-1} f (n - j)`. -/
private lemma sum_Ico_top_reflect (f : ℕ → ℝ) {n m : ℕ} (hm : m ≤ n) :
    ∑ j ∈ Ico (n - m + 1) n, f j = ∑ j ∈ Ico 1 m, f (n - j) := by
  refine sum_nbij' (fun j => n - j) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_Ico] at hj ⊢; omega
  · intro j hj; simp only [mem_Ico] at hj ⊢; omega
  · intro j hj; simp only [mem_Ico] at hj; omega
  · intro j hj; simp only [mem_Ico] at hj; omega
  · intro j hj
    simp only [mem_Ico] at hj
    rw [Nat.sub_sub_self (by omega)]

/-- `∑_{i=1}^{n-1} f (n - i) = ∑_{i=1}^{n-1} f i`. -/
private lemma sum_Ico_one_reflect (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Ico 1 n, f (n - i) = ∑ i ∈ Ico 1 n, f i := by
  refine sum_nbij' (fun j => n - j) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_Ico] at hj ⊢; omega
  · intro j hj; simp only [mem_Ico] at hj ⊢; omega
  · intro j hj; simp only [mem_Ico] at hj; omega
  · intro j hj; simp only [mem_Ico] at hj; omega
  · intro j _; rfl

/-- The band of row `i` of `fuSigmaB` left after the outer columns cancel. -/
private noncomputable def fuBand (n : ℕ) (d : ℕ → ℝ) (i : ℕ) : ℝ :=
  if 2 * i < n then (fuBeta n (i + 1) - fuBeta n (n - i)) * d i / 2 +
    ∑ j ∈ Ico (i + 1) (n - i), (fuBeta n (j + 1) - fuBeta n j) * d j / 2
  else if 2 * i = n then 0
  else (fuBeta n i - fuBeta n (n - i + 1)) * d i / 2 -
    ∑ j ∈ Ico (n - i + 1) i, (fuBeta n (j + 1) - fuBeta n j) * d j / 2

private lemma fuBand_reflect {n : ℕ} {d : ℕ → ℝ} (hd : ∀ j ∈ Ico 1 n, d (n - j) = d j)
    {i : ℕ} (hi : i ∈ Ico 1 n) : fuBand n d (n - i) = -fuBand n d i := by
  obtain ⟨hi1, hin⟩ := mem_Ico.1 hi
  have hdi := hd i hi
  have hnn : n - (n - i) = i := Nat.sub_sub_self hin.le
  unfold fuBand
  rcases lt_trichotomy (2 * i) n with h | h | h
  · simp only [show ¬ 2 * (n - i) < n by omega, show 2 * (n - i) ≠ n by omega, h, hnn, hdi,
      ↓reduceIte]
    ring
  · simp only [show 2 * (n - i) = n by omega, h, lt_irrefl,
      ↓reduceIte, neg_zero]
  · simp only [show 2 * (n - i) < n by omega, show ¬ 2 * i < n by omega,
      show 2 * i ≠ n by omega, hnn, hdi, ↓reduceIte]
    ring

/-- Row `i` of `fuSigmaB` against symmetric weights is the band `fuBand`. -/
private lemma sum_fuSigmaB_row {n : ℕ} {d : ℕ → ℝ} (hd : ∀ j ∈ Ico 1 n, d (n - j) = d j)
    {i : ℕ} (hi : i ∈ Ico 1 n) : ∑ j ∈ Ico 1 n, d j * fuSigmaB n i j = fuBand n d i := by
  obtain ⟨hi1, hin⟩ := mem_Ico.1 hi
  have hdi := hd i hi
  -- left columns `j < q` with `i + j < n`
  have hL : ∀ q, q ≤ i → i + q ≤ n → ∑ j ∈ Ico 1 q, d j * fuSigmaB n i j =
      (∑ j ∈ Ico 1 q, d j) * ((fuBeta n (i + 1) - fuBeta n i) / 2) := fun q hq hiq => by
    rw [sum_mul]
    exact sum_congr rfl fun j hj => by
      rw [fuSigmaB_off_lt (by have := mem_Ico.1 hj; omega) (by have := mem_Ico.1 hj; omega)]
  -- right columns `j ≥ n - q + 1 > i` with `n < i + j`, reflected onto `j < q`
  have hR : ∀ q, q ≤ n → i < n - q + 1 → n < i + (n - q + 1) →
      ∑ j ∈ Ico (n - q + 1) n, d j * fuSigmaB n i j =
        (∑ j ∈ Ico 1 q, d j) * ((fuBeta n i - fuBeta n (i + 1)) / 2) := fun q hq h1 h2 => by
    rw [sum_congr rfl fun j hj => by
        rw [fuSigmaB_comm, fuSigmaB_off_gt (by have := mem_Ico.1 hj; omega)
          (by have := mem_Ico.1 hj; omega)],
      ← sum_mul, sum_Ico_top_reflect (fun j => d j) hq]
    congr 1
    exact sum_congr rfl fun j hj => hd j (by have := mem_Ico.1 hj; simp only [mem_Ico]; omega)
  rw [← sum_Ico_consecutive _ hi1 hin.le, sum_eq_sum_Ico_succ_bot hin]
  unfold fuBand
  rcases lt_trichotomy (2 * i) n with h | h | h
  · have hmid : ∑ j ∈ Ico (i + 1) (n - i), d j * fuSigmaB n i j =
        ∑ j ∈ Ico (i + 1) (n - i), (fuBeta n (j + 1) - fuBeta n j) * d j / 2 :=
      sum_congr rfl fun j hj => by
        rw [fuSigmaB_comm, fuSigmaB_off_lt (n := n) (mem_Ico.1 hj).1
          (by have := mem_Ico.1 hj; omega)]
        ring
    simp only [h, ↓reduceIte]
    rw [hL i le_rfl (by omega), fuSigmaB_diag_lt h,
      ← sum_Ico_consecutive _ (show i + 1 ≤ n - i by omega) (show n - i ≤ n by omega),
      sum_eq_sum_Ico_succ_bot (show n - i < n by omega), hR i hin.le (by omega) (by omega),
      hmid, fuSigmaB_comm n i (n - i), fuSigmaB_off_eq (by omega) (by omega), hdi]
    ring
  · simp only [h, lt_irrefl, ↓reduceIte]
    rw [hL i le_rfl (by omega), fuSigmaB_diag_eq hi1 h,
      show Ico (i + 1) n = Ico (n - i + 1) n by congr 1; omega,
      hR i hin.le (by omega) (by omega)]
    ring
  · have hmid : ∑ j ∈ Ico (n - i + 1) i, d j * fuSigmaB n i j =
        -∑ j ∈ Ico (n - i + 1) i, (fuBeta n (j + 1) - fuBeta n j) * d j / 2 := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun j hj => by
        rw [fuSigmaB_off_gt (by have := mem_Ico.1 hj; omega) (by have := mem_Ico.1 hj; omega)]
        ring
    simp only [show ¬ 2 * i < n by omega, show 2 * i ≠ n by omega, ↓reduceIte]
    rw [← sum_Ico_consecutive _ (show 1 ≤ n - i by omega) (show n - i ≤ i by omega),
      sum_eq_sum_Ico_succ_bot (show n - i < i by omega), hL (n - i) (by omega) (by omega),
      fuSigmaB_off_eq (j := n - i) (by omega) (by omega), hmid,
      fuSigmaB_diag_gt h, show Ico (i + 1) n = Ico (n - (n - i) + 1) n by congr 1; omega,
      hR (n - i) (by omega) (by omega) (by omega), hdi]
    ring

/-- Against weights symmetric under `i ↦ n - i`, the `β_n` part of Fu's matrix sums to zero. -/
private lemma sum_sum_fuSigmaB {n : ℕ} {c d : ℕ → ℝ} (hc : ∀ i ∈ Ico 1 n, c (n - i) = c i)
    (hd : ∀ j ∈ Ico 1 n, d (n - j) = d j) :
    ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, c i * d j * fuSigmaB n i j = 0 := by
  have : ∀ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, c i * d j * fuSigmaB n i j = c i * fuBand n d i :=
    fun i hi => by
      rw [← sum_fuSigmaB_row hd hi, mul_sum]
      exact sum_congr rfl fun _ _ => by ring
  rw [sum_congr rfl this]
  refine sum_involution (fun i _ => n - i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [hc i hi, fuBand_reflect hd hi]
    ring
  · intro i hi hne heq
    apply hne
    have h2 : 2 * i = n := by have := (mem_Ico.1 hi).2; omega
    simp [fuBand, h2]
  · intro i hi; simp only [mem_Ico] at hi ⊢; omega
  · intro i hi; simp only [mem_Ico] at hi; omega

private lemma sum_Ico_cast_pow (n : ℕ) :
    ∑ i ∈ Ico 1 n, (i : ℝ) ^ 2 = n * ((n : ℝ) - 1) * (2 * n - 1) / 6 ∧
    ∑ i ∈ Ico 1 n, (i : ℝ) ^ 3 = (n * ((n : ℝ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [sum_Ico_succ_top (by omega : 1 ≤ n), sum_Ico_succ_top (by omega : 1 ≤ n), ih.1, ih.2]
    push_cast
    constructor <;> ring

/-- `∑_{i=1}^{n-1} i² (a_n - a_i)` and `∑_{i=1}^{n-1} i³ (a_n - a_i)` in closed form. -/
private lemma sum_pow_mul_tail {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Ico 1 n, (i : ℝ) ^ 2 * (tajimaA1 n - tajimaA1 i) =
      ((n : ℝ) - 1) * (4 * n ^ 2 + 7 * n + 6) / 36 ∧
    ∑ i ∈ Ico 1 n, (i : ℝ) ^ 3 * (tajimaA1 n - tajimaA1 i) =
      n * ((n : ℝ) - 1) * (n + 1) * (3 * n + 2) / 48 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hstep : ∀ p : ℕ, ∑ i ∈ Ico 1 (n + 1), (i : ℝ) ^ p * (tajimaA1 (n + 1) - tajimaA1 i) =
        ∑ i ∈ Ico 1 n, (i : ℝ) ^ p * (tajimaA1 n - tajimaA1 i) +
          (∑ i ∈ Ico 1 n, (i : ℝ) ^ p) * (n : ℝ)⁻¹ + (n : ℝ) ^ p * (n : ℝ)⁻¹ := fun p => by
      rw [sum_Ico_succ_top hn, tajimaA1_succ hn, sum_mul, ← sum_add_distrib]
      congr 1
      · exact sum_congr rfl fun _ _ => by ring
      · ring
    rw [hstep, hstep, ih.1, ih.2, (sum_Ico_cast_pow n).1, (sum_Ico_cast_pow n).2]
    push_cast
    constructor
    · field_simp
      ring
    · field_simp
      ring

/-- Row `i` of the `β_n`-free part against the unnormalized `θ_π` weights `e_j = (n - j) j`. -/
private lemma sum_fuSigmaR_row {n i : ℕ} (hi : i ∈ Ico 1 n) :
    ∑ j ∈ Ico 1 n, ((n : ℝ) - j) * j * fuSigmaR n i j =
      i * (tajimaA1 n - tajimaA1 i) + ((n : ℝ) - i) * (tajimaA1 n - tajimaA1 (n - i)) - 1 -
        ((i : ℝ) - 1) / 2 := by
  obtain ⟨hi1, hin⟩ := mem_Ico.1 hi
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hni : (n : ℝ) - i ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hin.ne')
  have hcast : ((n - i : ℕ) : ℝ) = n - i := Nat.cast_sub hin.le
  simp only [fuSigmaR, mul_sub, sum_sub_distrib]
  have h1 : ∑ j ∈ Ico 1 n, ((n : ℝ) - j) * j * (if i + j = n then
      (tajimaA1 n - tajimaA1 i) / j + (tajimaA1 n - tajimaA1 j) / i - 1 / ((i : ℝ) * j)
      else 0) = i * (tajimaA1 n - tajimaA1 i) + ((n : ℝ) - i) * (tajimaA1 n - tajimaA1 (n - i)) -
        1 := by
    rw [sum_eq_single_of_mem (n - i) (by simp only [mem_Ico]; omega) fun j _ hj => by
      simp [show i + j ≠ n by omega]]
    simp only [show i + (n - i) = n by omega, ↓reduceIte, hcast]
    field_simp
    ring
  have h2 : ∑ j ∈ Ico 1 n, ((n : ℝ) - j) * j * (if n < i + j then 1 / ((i : ℝ) * j) else 0) =
      ((i : ℝ) - 1) / 2 := by
    have hfil : ∑ j ∈ Ico 1 n, ((n : ℝ) - j) * j * (if n < i + j then 1 / ((i : ℝ) * j) else 0) =
        ∑ j ∈ Ico (n - i + 1) n, ((n : ℝ) - j) * j * (1 / ((i : ℝ) * j)) := by
      rw [← sum_Ico_consecutive _ (show 1 ≤ n - i + 1 by omega) (show n - i + 1 ≤ n by omega)]
      rw [sum_eq_zero fun j hj => by simp [show ¬ n < i + j by have := mem_Ico.1 hj; omega],
        zero_add]
      exact sum_congr rfl fun j hj => by simp [show n < i + j by have := mem_Ico.1 hj; omega]
    rw [hfil, sum_Ico_top_reflect (fun j => ((n : ℝ) - j) * j * (1 / ((i : ℝ) * j))) hin.le]
    have : ∀ j ∈ Ico 1 i, ((n : ℝ) - ((n - j : ℕ) : ℝ)) * ((n - j : ℕ) : ℝ) *
        (1 / ((i : ℝ) * ((n - j : ℕ) : ℝ))) = (j : ℝ) / i := fun j hj => by
      have hjn : j < n := by have := mem_Ico.1 hj; omega
      have : ((n - j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [Nat.cast_sub hjn.le] at this ⊢
      field_simp
      ring
    rw [sum_congr rfl this, ← sum_div, sum_Ico_cast]
    field_simp
  rw [h1, h2]
  ring

/-- The `β_n`-free part of Fu's matrix against the unnormalized `θ_π` weights:
`∑_{i,j} e_i e_j R_{ij} = n (n - 1)(n² + n + 3) / 18 = C(n, 2)² b₂`. -/
private lemma sum_sum_fuSigmaR {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, ((n : ℝ) - i) * i * (((n : ℝ) - j) * j) * fuSigmaR n i j =
      n * ((n : ℝ) - 1) * (n ^ 2 + n + 3) / 18 := by
  have hrow : ∀ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n,
      ((n : ℝ) - i) * i * (((n : ℝ) - j) * j) * fuSigmaR n i j =
      ((n : ℝ) - i) * i * i * (tajimaA1 n - tajimaA1 i) +
        (((n : ℝ) - i) * (n - i) * i * (tajimaA1 n - tajimaA1 (n - i))) -
        ((n : ℝ) - i) * i * ((i : ℝ) + 1) / 2 := fun i hi => by
    rw [show ∑ j ∈ Ico 1 n, ((n : ℝ) - i) * i * (((n : ℝ) - j) * j) * fuSigmaR n i j =
        ((n : ℝ) - i) * i * ∑ j ∈ Ico 1 n, ((n : ℝ) - j) * j * fuSigmaR n i j by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring, sum_fuSigmaR_row hi]
    ring
  rw [sum_congr rfl hrow, sum_sub_distrib, sum_add_distrib]
  have hrefl : ∑ i ∈ Ico 1 n, ((n : ℝ) - i) * (n - i) * i * (tajimaA1 n - tajimaA1 (n - i)) =
      ∑ i ∈ Ico 1 n, ((n : ℝ) - i) * i * i * (tajimaA1 n - tajimaA1 i) := by
    rw [← sum_Ico_one_reflect (fun k => ((n : ℝ) - k) * k * k * (tajimaA1 n - tajimaA1 k)) n]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨-, hin⟩ := mem_Ico.1 hi
    simp only [Nat.cast_sub hin.le]
    ring
  have hP : ∑ i ∈ Ico 1 n, ((n : ℝ) - i) * i * i * (tajimaA1 n - tajimaA1 i) =
      n * ∑ i ∈ Ico 1 n, (i : ℝ) ^ 2 * (tajimaA1 n - tajimaA1 i) -
        ∑ i ∈ Ico 1 n, (i : ℝ) ^ 3 * (tajimaA1 n - tajimaA1 i) := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hQ : ∑ i ∈ Ico 1 n, ((n : ℝ) - i) * i * ((i : ℝ) + 1) / 2 =
      (n * ∑ i ∈ Ico 1 n, (i : ℝ) + (n - 1) * ∑ i ∈ Ico 1 n, (i : ℝ) ^ 2 -
        ∑ i ∈ Ico 1 n, (i : ℝ) ^ 3) / 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib, sum_div]
    exact sum_congr rfl fun _ _ => by ring
  rw [hrefl, hP, hQ, (sum_pow_mul_tail hn).1, (sum_pow_mul_tail hn).2, sum_Ico_cast,
    (sum_Ico_cast_pow n).1, (sum_Ico_cast_pow n).2]
  ring

/-- **Tajima's `b₂` from Fu's closed form**: `∑_{i,j=1}^{n-1} π_i π_j σ_{ij} = b₂ =
2 (n² + n + 3) / (9 n (n - 1))` with `π_i = i (n - i) / C(n, 2)` (Tajima 1983), so
`Var(θ_π[L]) = 4 b₂` and `Var θ_π = b₁ θ + b₂ θ²`. The `β_n` part cancels because the weights
are symmetric under `i ↦ n - i`. -/
theorem sum_sum_piWeight_mul_piWeight_mul_fuSigma {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, ((n : ℝ) - i) / (n.choose 2 : ℝ) * i *
      (((n : ℝ) - j) / (n.choose 2 : ℝ) * j) * fuSigma n i j = tajimaB2 n := by
  set p : ℕ → ℝ := fun i => ((n : ℝ) - i) / (n.choose 2 : ℝ) * i with hp
  have hC : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsym : ∀ i ∈ Ico 1 n, p (n - i) = p i := fun i hi => by
    obtain ⟨-, hin⟩ := mem_Ico.1 hi
    simp only [hp, Nat.cast_sub hin.le]
    ring
  have hsplit : ∀ i j, p i * p j * fuSigma n i j =
      p i * p j * fuSigmaB n i j +
        ((n : ℝ) - i) * i * (((n : ℝ) - j) * j) * fuSigmaR n i j / (n.choose 2 : ℝ) ^ 2 :=
    fun i j => by
      simp only [fuSigmaB, hp]
      field_simp
      ring
  change ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, p i * p j * fuSigma n i j = tajimaB2 n
  simp only [hsplit, sum_add_distrib, ← sum_div]
  rw [sum_sum_fuSigmaB hsym hsym, sum_sum_fuSigmaR (by omega), hC, tajimaB2]
  field_simp
  ring

/-- **Tajima's `c₂` from Fu's closed form**: for the weights `w_i = π_i - 1 / a₁` of Tajima's `D`
numerator (`tajimaNumWeight`), `∑_{i,j} w_i w_j σ_{ij} = c₂ = b₂ - (n + 2) / (a₁ n) + a₂ / a₁²`
(Tajima 1989), from `∑ π_i π_j σ_{ij} = b₂`, `∑ π_i σ_{ij} = (n + 2) / (2 n)` and
`∑ σ_{ij} = a₂`. -/
theorem sum_sum_tajimaNumWeight_mul_fuSigma {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, tajimaNumWeight n i * tajimaNumWeight n j * fuSigma n i j =
      tajimaC2 n := by
  set p : ℕ → ℝ := fun i => ((n : ℝ) - i) / (n.choose 2 : ℝ) * i with hp
  have ha : tajimaA1 n ≠ 0 := by
    rw [tajimaA1_eq_harmonic]
    exact_mod_cast (harmonic_pos (by omega)).ne'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hX : ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, p i * fuSigma n i j = ((n : ℝ) + 2) / (2 * n) :=
    sum_sum_piWeight_mul_fuSigma hn
  have hb' : ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, p i * p j * fuSigma n i j = tajimaB2 n :=
    sum_sum_piWeight_mul_piWeight_mul_fuSigma hn
  have hX' : ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, p j * fuSigma n i j =
      ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, p i * fuSigma n i j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [fuSigma_comm]
  have hexp : ∀ i j, tajimaNumWeight n i * tajimaNumWeight n j * fuSigma n i j =
      p i * p j * fuSigma n i j - (tajimaA1 n)⁻¹ * (p i * fuSigma n i j) -
        (tajimaA1 n)⁻¹ * (p j * fuSigma n i j) + ((tajimaA1 n)⁻¹ ^ 2) * fuSigma n i j :=
    fun i j => by simp only [tajimaNumWeight, hp]; ring
  have e : ∀ (c : ℝ) (f : ℕ → ℕ → ℝ), ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, c * f i j =
      c * ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, f i j := fun c f => by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
  simp only [hexp, sum_add_distrib, sum_sub_distrib, e]
  rw [hX', hb', hX, sum_sum_fuSigma, tajimaC2]
  field_simp
  ring

/-! ### Variances of linear SFS statistics under Kingman's coalescent -/

section Kingman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : KingmanTimes μ n} {τ : Ω → List (List ℕ)} {θ : ℝ} {ξ : ℕ → Ω → ℝ}

/-- **Variance of a linear combination of branch lengths from Fu's closed form**: if
`Cov(L_i, L_j) = 4 σ_{ij}` (Fu 1995) for `1 ≤ i, j ≤ n - 1`, then
`Var(∑_i c_i L_i) = 4 ∑_{i,j} c_i c_j σ_{ij}`. -/
theorem variance_sum_sfsLength_of_fuSigma (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j)
    (c : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ Ico 1 n, c i * sfsLength n i (τ ω) (fun k => K.T k ω); μ] =
      4 * ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, c i * c j * fuSigma n i j := by
  rw [variance_sum_eq_sum_covariance (L := fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω))
    (memLp_sfsLength hτ hτ_law) _ c, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [hσ i hi j hj]
  ring

/-- **Fu's covariance of the SFS** (Fu 1995): under Kingman's coalescent, if the branch-length
covariances are `Cov(L_i, L_j) = 4 σ_{ij}`, then `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²`
for `1 ≤ i, j ≤ n - 1`. -/
theorem covariance_count_kingman_of_fuSigma (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j)
    {i j : ℕ} (hi : i ∈ Ico 1 n) (hj : j ∈ Ico 1 n) :
    cov[ξ i, ξ j; μ] = (if i = j then θ / i else 0) + θ ^ 2 * fuSigma n i j := by
  rw [covariance_count_kingman hT hτ hτ_law h_indep h hi j, hσ i hi j hj]
  ring

/-- **Variance of a linear SFS statistic from Fu's closed form**:
`Var(∑_i a_i ξ_i) = θ ∑_i a_i² / i + θ² ∑_{i,j} a_i a_j σ_{ij}`. -/
theorem variance_sum_kingman_of_fuSigma (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j)
    (a : ℕ → ℝ) :
    Var[fun ω => ∑ i ∈ Ico 1 n, a i * ξ i ω; μ] =
      θ * ∑ i ∈ Ico 1 n, a i ^ 2 / i +
        θ ^ 2 * ∑ i ∈ Ico 1 n, ∑ j ∈ Ico 1 n, a i * a j * fuSigma n i j := by
  rw [variance_sum_kingman hT hτ hτ_law h_indep h,
    variance_sum_sfsLength_of_fuSigma hτ hτ_law hσ]
  ring

/-- **Variance of the total length of the segregating branches from Fu's closed form**:
`Var(∑_{i=1}^{n-1} L_i) = 4 a₂` (the variance of the total branch length, Watterson 1975). -/
theorem variance_sum_sfsLength_one_of_fuSigma (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j) :
    Var[fun ω => ∑ i ∈ Ico 1 n, sfsLength n i (τ ω) (fun k => K.T k ω); μ] =
      4 * tajimaA2 n := by
  simpa [sum_sum_fuSigma] using variance_sum_sfsLength_of_fuSigma hτ hτ_law hσ (fun _ => 1)

/-- **Variance of Watterson's estimator from Fu's closed form** (`n ≥ 2`):
`Var(S / a₁) = θ / a₁ + θ² a₂ / a₁²`, i.e. `Var S = θ a₁ + θ² a₂` (Watterson 1975), as in
`KingmanTimes.variance_segSites`. -/
theorem variance_watterson_kingman_of_fuSigma (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j) :
    Var[fun ω => (∑ i ∈ Ico 1 n, ξ i ω) / tajimaA1 n; μ] =
      θ / tajimaA1 n + θ ^ 2 * tajimaA2 n / tajimaA1 n ^ 2 := by
  have ha : tajimaA1 n ≠ 0 := by
    rw [tajimaA1_eq_harmonic]
    exact_mod_cast (harmonic_pos (by omega)).ne'
  rw [variance_watterson_kingman hn hT hτ hτ_law h_indep h,
    variance_sum_sfsLength_one_of_fuSigma hτ hτ_law hσ]
  field_simp
  ring

/-- **Variance of the branch-length form of `θ_π` from Fu's closed form** (`n ≥ 2`):
`Var(∑_i π_i L_i) = 4 b₂` (Tajima 1983). -/
theorem variance_thetaPi_sfsLength_of_fuSigma (hn : 2 ≤ n)
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j) :
    Var[thetaPi n (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)); μ] = 4 * tajimaB2 n := by
  unfold thetaPi thetaWeighted
  rw [variance_sum_sfsLength_of_fuSigma hτ hτ_law hσ,
    sum_sum_piWeight_mul_piWeight_mul_fuSigma hn]

/-- **Variance of `θ_π` from the SFS and Fu's closed form** (`n ≥ 2`):
`Var θ_π = b₁ θ + b₂ θ²` (Tajima 1983), as `variance_meanPairDiff` proves from pairwise
coalescence times. -/
theorem variance_thetaPi_kingman_of_fuSigma (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j) :
    Var[thetaPi n ξ; μ] = tajimaB1 n * θ + tajimaB2 n * θ ^ 2 := by
  rw [variance_thetaPi_kingman hn hT hτ hτ_law h_indep h,
    variance_thetaPi_sfsLength_of_fuSigma hn hτ hτ_law hσ]
  ring

/-- **Variance of the branch-length form of Tajima's `D` numerator from Fu's closed form**
(`n ≥ 2`): `Var(∑_i w_i L_i) = 4 c₂` with `w_i = tajimaNumWeight n i` (Tajima 1989). -/
theorem variance_tajimaNumWeight_sfsLength_of_fuSigma (hn : 2 ≤ n)
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j) :
    Var[fun ω => ∑ i ∈ Ico 1 n, tajimaNumWeight n i *
      sfsLength n i (τ ω) (fun k => K.T k ω); μ] = 4 * tajimaC2 n := by
  rw [variance_sum_sfsLength_of_fuSigma hτ hτ_law hσ,
    sum_sum_tajimaNumWeight_mul_fuSigma hn]

/-- **Variance of Tajima's `D` numerator from the SFS and Fu's closed form** (`n ≥ 2`):
`Var(θ_π - S / a₁) = c₁ θ + c₂ θ²` (Tajima 1989). The same identity from pairwise coalescence
times is `KingmanTimes.variance_tajimaNumerator`. -/
theorem variance_tajimaNumerator_kingman_of_fuSigma (hn : 2 ≤ n) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (h : SFSCondMoments μ (MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) θ ξ
      (fun i ω => sfsLength n i (τ ω) (fun k => K.T k ω)))
    (hσ : ∀ i ∈ Ico 1 n, ∀ j ∈ Ico 1 n,
      cov[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω),
        fun ω => sfsLength n j (τ ω) (fun k => K.T k ω); μ] = 4 * fuSigma n i j) :
    Var[fun ω => thetaPi n ξ ω - (∑ i ∈ Ico 1 n, ξ i ω) / tajimaA1 n; μ] =
      tajimaC1 n * θ + tajimaC2 n * θ ^ 2 := by
  rw [variance_tajimaNumerator_kingman hn hT hτ hτ_law h_indep h,
    variance_tajimaNumWeight_sfsLength_of_fuSigma hn hτ hτ_law hσ]
  ring

end Kingman

end MathlibExt.Biology.PopulationGenetics.Coalescent.SFSFuClosedForm

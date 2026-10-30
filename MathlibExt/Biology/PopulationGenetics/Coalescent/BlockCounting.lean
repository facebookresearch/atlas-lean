/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.ExponentialLimit
public import MathlibExt.Biology.PopulationGenetics.Coalescent.Kingman
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Kingman's theorem for the ancestral lineage count, and Tavaré's formula

Trace `k` gene copies back one generation in a neutral Wright–Fisher population of `M` gene
copies (`M = 2N` for `N` diploid individuals): each copy picks its parent uniformly and
independently among the `M` copies of the previous generation, and the number of ancestral
lineages one generation back is the number `j` of distinct parents. Exactly
`Nat.stirlingSecond k j * M.descFactorial j` of the `M ^ k` parent assignments have `j` distinct
parents, so the one-generation transition probability is
`stirlingSecond k j * M^{(j)} / M ^ k` (`wfLineageProb`), and the lineage count is a Markov chain
on `{0, …, n}` with transition matrix `wfLineageMatrix n M`. The model needs `M ≥ 1`; at
`M = 0` the definition is Lean's totalized `0 / 0 = 0` (e.g. `wfLineageProb 0 1 1 = 0`), which
does not affect the limit `M → ∞`.

Kingman's theorem, restricted to the block-counting (lineage-count) process, says that with
time measured in units of `M` generations this chain converges to the pure-death process in
which `k` lineages become `k - 1` at rate `k.choose 2` (`blockCountingGenerator n`): after
`⌊t M⌋` generations the transition matrix converges entrywise to `exp (t • G)`. The proof
writes `wfLineageMatrix n M = 1 + M⁻¹ • Y M` with `Y M → G` entrywise and applies the
compound-interest limit in the Banach algebra of matrices
(`NormedSpace.tendsto_one_add_inv_smul_pow`).

Tavaré (1984) computed the transition probabilities of the pure-death process: for
`1 ≤ j ≤ i`, `P(i → j in time t)` is `∑_{k=j}^{i} e^{-k(k-1)t/2} (2k-1) (-1)^{k-j}
j^{(k-1)} i_{(k)} / (j! (k-j)! i^{(k)})`, where `a^{(m)}` is the rising factorial
`Nat.ascFactorial a m` and `a_{(m)}` the falling factorial `Nat.descFactorial a m`
(`tavareProb`). The proof diagonalizes the generator: the columns of
`blockCountingRightEigen n` (entries `i_{(k)} / i^{(k)}`) are right eigenvectors, the rows of
`blockCountingLeftEigen n` are left eigenvectors, both for the eigenvalue `-(k.choose 2)`, and
the two matrices are mutually inverse. The formula holds for every real `t`.

## Main results

* `tendsto_smul_wfLineageMatrix_sub_one`: `M • (wfLineageMatrix n M - 1) → G` entrywise.
* `tendsto_wfLineageMatrix_pow_floor`: **Kingman's theorem** for the lineage count.
* `blockCountingGenerator_mul_rightEigen`, `blockCountingLeftEigen_mul_generator`: right and
  left eigenvectors of `G`.
* `blockCountingLeftEigen_mul_rightEigen`: the eigenvector matrices are mutually inverse (proved
  from the eigen-relations and triangularity, without a summation identity).
* `exp_smul_blockCountingGenerator`: the spectral decomposition of `exp (t • G)`.
* `exp_blockCountingGenerator_apply`: **Tavaré's formula**.

## References

* J. F. C. Kingman, "The coalescent", Stochastic Process. Appl. 13 (1982) 235–248.
* J. F. C. Kingman, "On the genealogy of large populations", J. Appl. Probab. 19A (1982)
  27–43.
* S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population
  genetics models", Theor. Popul. Biol. 26 (1984) 119–164.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008), ch. 1.
-/

@[expose] public section

open Filter Topology Matrix

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-- One-generation transition probability of the ancestral lineage count in a neutral
Wright–Fisher population of `M` gene copies: `k` lineages pick their parents uniformly and
independently among `M` copies, and `j` distinct parents occur with probability
`stirlingSecond k j * M.descFactorial j / M ^ k`. -/
noncomputable def wfLineageProb (M k j : ℕ) : ℝ :=
  (Nat.stirlingSecond k j : ℝ) * (M.descFactorial j : ℝ) / (M : ℝ) ^ k

/-- The one-generation transition matrix of the ancestral lineage count of a sample of at most
`n` gene copies in a Wright–Fisher population of `M` copies; row `k`, column `j` is
`wfLineageProb M k j`. -/
noncomputable def wfLineageMatrix (n M : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j => wfLineageProb M k j

/-- The rate matrix of Kingman's block-counting (pure-death) process on `{0, …, n}`: `k`
lineages become `k - 1` at rate `k.choose 2`, time in units of `M = 2N` generations. -/
noncomputable def blockCountingGenerator (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j =>
    if (j : ℕ) + 1 = k then ((k : ℕ).choose 2 : ℝ)
    else if j = k then -((k : ℕ).choose 2 : ℝ) else 0

/-- Tavaré's closed form for the probability that `i` lineages of Kingman's coalescent have
`j` ancestors `t` time units (`2N` generations each) earlier, for `1 ≤ j ≤ i`. -/
noncomputable def tavareProb (i j : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc j i,
    Real.exp (-((k : ℝ) * (k - 1) * t / 2)) * (2 * k - 1) * (-1) ^ (k - j) *
      (j.ascFactorial (k - 1) : ℝ) * (i.descFactorial k : ℝ) /
      ((j.factorial : ℝ) * ((k - j).factorial : ℝ) * (i.ascFactorial k : ℝ))

/-! ### Kingman's limit -/

/-- Entrywise form of `tendsto_smul_wfLineageMatrix_sub_one`, on natural-number indices. -/
private theorem tendsto_entry (a b : ℕ) :
    Tendsto (fun M : ℕ => (M : ℝ) * (wfLineageProb M a b - if b = a then 1 else 0)) atTop
      (𝓝 (if b + 1 = a then (a.choose 2 : ℝ) else if b = a then -(a.choose 2 : ℝ) else 0)) := by
  have hpos : ∀ᶠ M : ℕ in atTop, 0 < M := eventually_gt_atTop 0
  rcases lt_trichotomy b a with hba | rfl | hab
  · have hne : b ≠ a := hba.ne
    simp only [hne, ite_false, sub_zero]
    rcases Nat.lt_or_ge (b + 1) a with h1 | h1
    · -- at least two coalescences in one generation: probability `O(1/M²)`
      have hne' : b + 1 ≠ a := h1.ne
      simp only [hne', ite_false]
      obtain ⟨d, rfl⟩ : ∃ d, a = b + 1 + (d + 1) := ⟨a - (b + 2), by omega⟩
      have hlim : Tendsto (fun M : ℕ => (Nat.stirlingSecond (b + 1 + (d + 1)) b : ℝ) *
          noCoalProb M b * ((M : ℝ)⁻¹) ^ (d + 1)) atTop (𝓝 (_ * 1 * 0 ^ (d + 1))) :=
        ((tendsto_noCoalProb_one b).const_mul _).mul
          ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).pow _)
      rw [zero_pow (Nat.succ_ne_zero d), mul_zero] at hlim
      refine hlim.congr' ?_
      filter_upwards [hpos] with M hM
      have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      rw [noCoalProb_eq_descFactorial_div hM, wfLineageProb, inv_pow]
      field_simp
      ring
    · -- exactly one coalescence: rate `a.choose 2`
      have heq : b + 1 = a := by omega
      subst heq
      simp only [ite_true]
      have hlim := (tendsto_noCoalProb_one b).const_mul ((b + 1).choose 2 : ℝ)
      rw [mul_one] at hlim
      refine hlim.congr' ?_
      filter_upwards [hpos] with M hM
      have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      rw [noCoalProb_eq_descFactorial_div hM, wfLineageProb, Nat.stirlingSecond_succ_self_left]
      field_simp
      ring
  · -- no coalescence
    simp only [ite_true, show b + 1 ≠ b by omega, ite_false]
    have hlim := (tendsto_coalescence_rate b).neg
    refine hlim.congr' ?_
    filter_upwards [hpos] with M hM
    rw [wfLineageProb, Nat.stirlingSecond_self, Nat.cast_one, one_mul,
      ← noCoalProb_eq_descFactorial_div hM]
    ring
  · -- more ancestors than descendants: probability `0`
    simp only [show b ≠ a by omega, show b + 1 ≠ a by omega, ite_false, sub_zero,
      wfLineageProb, Nat.stirlingSecond_eq_zero_of_lt hab, Nat.cast_zero, zero_mul, zero_div,
      mul_zero]
    exact tendsto_const_nhds

/-- The scaled one-generation increment `M • (wfLineageMatrix n M - 1)` converges entrywise to
the block-counting generator: `k` lineages coalesce to `k - 1` with probability
`(k.choose 2) / M + o(1/M)`, and to fewer with probability `O(1/M²)`. -/
theorem tendsto_smul_wfLineageMatrix_sub_one (n : ℕ) :
    Tendsto (fun M : ℕ => (M : ℝ) • (wfLineageMatrix n M - 1)) atTop
      (𝓝 (blockCountingGenerator n)) := by
  refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
  change Tendsto (fun M : ℕ => ((M : ℝ) • (wfLineageMatrix n M - 1)) k j) atTop
    (𝓝 (blockCountingGenerator n k j))
  have h := tendsto_entry k j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, wfLineageMatrix,
    blockCountingGenerator, Matrix.of_apply, smul_eq_mul]
  simpa [Fin.ext_iff, eq_comm] using h

/-- **Kingman's theorem for the lineage count.** For `t ≥ 0`, the `⌊t M⌋`-generation transition
matrix of the Wright–Fisher ancestral lineage count converges, as the population size `M`
tends to infinity, to the transition matrix `exp (t • G)` of the pure-death process with rates
`k.choose 2`.

Source: Kingman (1982); Durrett (2008), ch. 1. Proves the deferred entry
`tendsto_wfLineageMatrix_pow_floor`. -/
theorem tendsto_wfLineageMatrix_pow_floor (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => wfLineageMatrix n M ^ ⌊t * M⌋₊) atTop
      (𝓝 (NormedSpace.exp (t • blockCountingGenerator n))) := by
  have hm : Tendsto (fun M : ℕ => (⌊t * M⌋₊ : ℝ) / M) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht).comp tendsto_natCast_atTop_atTop
  open scoped Matrix.Norms.Operator in
  refine (NormedSpace.tendsto_one_add_inv_smul_pow
    (tendsto_smul_wfLineageMatrix_sub_one n) hm).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with M hM
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hM), one_smul, add_sub_cancel]

/-! ### Tavaré's formula -/

/-- Right eigenvectors of the block-counting generator, as columns: column `k` has entries
`i_{(k)} / i^{(k)}` (falling over rising factorial) and eigenvalue `-(k.choose 2)`. -/
noncomputable def blockCountingRightEigen (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i k => ((i : ℕ).descFactorial k : ℝ) / ((i : ℕ).ascFactorial k : ℝ)

/-- Left eigenvectors of the block-counting generator, as rows: row `0` is the indicator of
state `0`, and for `1 ≤ k` row `k` has entries `(2k-1) (-1)^{k-j} j^{(k-1)} / (j! (k-j)!)` for
`j ≤ k` and `0` for `j > k`; the eigenvalue is `-(k.choose 2)`. -/
noncomputable def blockCountingLeftEigen (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j =>
    if (k : ℕ) = 0 then (if (j : ℕ) = 0 then 1 else 0)
    else if (j : ℕ) ≤ k then
      (2 * (k : ℕ) - 1) * (-1) ^ ((k : ℕ) - j) * ((j : ℕ).ascFactorial ((k : ℕ) - 1) : ℝ) /
        (((j : ℕ).factorial : ℝ) * (((k : ℕ) - j).factorial : ℝ))
    else 0

/-- The eigenvalues of the block-counting generator, `-(k.choose 2)`. -/
noncomputable def blockCountingEigenvalue (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  -((k : ℕ).choose 2 : ℝ)

/-! #### Scalar identities behind the eigenvector relations -/

/-- The entries of `blockCountingRightEigen`, on natural-number indices. -/
private noncomputable def vR (i k : ℕ) : ℝ := (i.descFactorial k : ℝ) / (i.ascFactorial k : ℝ)

/-- The entries of `blockCountingLeftEigen`, on natural-number indices. -/
private noncomputable def wL (k j : ℕ) : ℝ :=
  if k = 0 then (if j = 0 then 1 else 0)
  else if j ≤ k then
    (2 * k - 1) * (-1) ^ (k - j) * (j.ascFactorial (k - 1) : ℝ) /
      ((j.factorial : ℝ) * ((k - j).factorial : ℝ))
  else 0

private theorem rightEigen_apply (n : ℕ) (i k : Fin (n + 1)) :
    blockCountingRightEigen n i k = vR i k := rfl

private theorem leftEigen_apply (n : ℕ) (k j : Fin (n + 1)) :
    blockCountingLeftEigen n k j = wL k j := rfl

private theorem vR_eq_zero {i k : ℕ} (h : i < k) : vR i k = 0 := by
  simp [vR, Nat.descFactorial_eq_zero_iff_lt.2 h]

private theorem wL_eq_zero {k j : ℕ} (h : k < j) : wL k j = 0 := by
  unfold wL
  split_ifs <;> first | rfl | omega

/-- Cast of `(i + 1) - k` times a falling factorial, valid for all `k` (both sides vanish
when `k > i + 1`). -/
private theorem descFactorial_rel (i k : ℕ) :
    ((i : ℝ) + 1 - k) * ((i + 1).descFactorial k : ℝ) = (i + 1) * (i.descFactorial k : ℝ) := by
  have h := Nat.succ_descFactorial_succ i k
  rw [Nat.descFactorial_succ] at h
  by_cases hk : k ≤ i + 1
  · have h' : (((i + 1 - k : ℕ) : ℝ)) * ((i + 1).descFactorial k : ℝ) =
        (i + 1) * (i.descFactorial k : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hk] at h'
    push_cast at h'
    linarith
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega), Nat.descFactorial_eq_zero_iff_lt.2
      (by omega)]
    simp

private theorem ascFactorial_rel (i k : ℕ) :
    (i : ℝ) * ((i + 1).ascFactorial k : ℝ) = (i + k) * (i.ascFactorial k : ℝ) := by
  exact_mod_cast Nat.succ_ascFactorial i k

/-- The right-eigenvector recursion `(C(i+1,2) - C(k,2)) v(i+1) = C(i+1,2) v(i)`. -/
private theorem vR_rec (i k : ℕ) :
    (((i + 1).choose 2 : ℝ) - (k.choose 2 : ℝ)) * vR (i + 1) k =
      ((i + 1).choose 2 : ℝ) * vR i k := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.lt_or_ge 1 k with hk | hk
    · rw [vR_eq_zero (by omega : 0 + 1 < k)]
      simp
    · interval_cases k <;> simp [vR]
  · have hA1 : ((i + 1).ascFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ascFactorial_pos i k).ne'
    have hA0 : (i.ascFactorial k : ℝ) ≠ 0 := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact_mod_cast (Nat.ascFactorial_pos i' k).ne'
    have hd := descFactorial_rel i k
    have ha := ascFactorial_rel i k
    simp only [vR, Nat.cast_choose_two]
    rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hA1 hA0]
    push_cast
    linear_combination ((i : ℝ) + k) * (i.ascFactorial k : ℝ) / 2 * hd -
      ((i : ℝ) + 1) * (i.descFactorial k : ℝ) / 2 * ha

/-- The left-eigenvector recursion `C(j+1,2) w(j+1) = (C(j,2) - C(k,2)) w(j)`. -/
private theorem wL_rec (k j : ℕ) :
    ((j + 1).choose 2 : ℝ) * wL k (j + 1) =
      ((j.choose 2 : ℝ) - (k.choose 2 : ℝ)) * wL k j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [wL]
    · simp [wL, hj.ne']
  rcases Nat.lt_or_ge j k with hjk | hjk
  · -- `j + 1 ≤ k`: write `k = j + 1 + d`
    obtain ⟨d, rfl⟩ : ∃ d, k = j + 1 + d := ⟨k - (j + 1), by omega⟩
    have h1 : j + 1 + d - (j + 1) = d := by omega
    have h2 : j + 1 + d - j = d + 1 := by omega
    have h3 : j + 1 + d - 1 = j + d := by omega
    simp only [wL, show j + 1 + d ≠ 0 by omega, ite_false, show j + 1 ≤ j + 1 + d by omega,
      show j ≤ j + 1 + d by omega, ite_true, h1, h2, h3]
    have ha : (j : ℝ) * ((j + 1).ascFactorial (j + d) : ℝ) =
        (j + (j + d : ℕ)) * (j.ascFactorial (j + d) : ℝ) := ascFactorial_rel j (j + d)
    have hf1 : ((j + 1).factorial : ℝ) = (j + 1) * (j.factorial : ℝ) := by
      push_cast [Nat.factorial_succ]; ring
    have hf2 : ((d + 1).factorial : ℝ) = (d + 1) * (d.factorial : ℝ) := by
      push_cast [Nat.factorial_succ]; ring
    have hj0 : (j.factorial : ℝ) ≠ 0 := by positivity
    have hd0 : (d.factorial : ℝ) ≠ 0 := by positivity
    rw [hf1, hf2, pow_succ, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast at ha ⊢
    linear_combination (norm := skip) (2 * ((j : ℝ) + 1 + d) - 1) * (-1) ^ d /
      (2 * (j.factorial : ℝ) * (d.factorial : ℝ)) * ha
    field_simp
    ring
  · -- `j ≥ k`: the left side vanishes; the right side vanishes too
    rw [wL_eq_zero (by omega : k < j + 1), mul_zero]
    rcases hjk.lt_or_eq with hlt | rfl
    · rw [wL_eq_zero hlt, mul_zero]
    · ring

/-- The diagonal entries of `W V` are `1`. -/
private theorem wL_vR_self (a : ℕ) : wL a a * vR a a = 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [wL, vR]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hA : ((b + 1).ascFactorial b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ascFactorial_pos b b).ne'
  have hF : ((b + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (2 * ((b : ℝ) + 1) - 1) ≠ 0 := ne_of_gt (by linarith [b.cast_nonneg (α := ℝ)])
  simp only [wL, vR, show b + 1 ≠ 0 by omega, ite_false, le_refl, ite_true, Nat.sub_self,
    pow_zero, Nat.factorial_zero, Nat.add_sub_cancel, Nat.descFactorial_self,
    Nat.ascFactorial_succ]
  push_cast
  field_simp
  ring

/-- The entry `(1, 0)` of `W V` vanishes (the double eigenvalue `0`). -/
private theorem wL_vR_one_zero : wL 1 0 * vR 0 0 + wL 1 1 * vR 1 0 = 0 := by
  norm_num [wL, vR]

/-- The last column of the left-eigenvector relation. -/
private theorem wL_last {n k : ℕ} (hk : k ≤ n) :
    ((n.choose 2 : ℝ) - (k.choose 2 : ℝ)) * wL k n = 0 := by
  rcases hk.lt_or_eq with hlt | rfl
  · rw [wL_eq_zero hlt, mul_zero]
  · ring

/-- Row `i ≥ 1` of `G * A`: only the subdiagonal and diagonal entries of `G` contribute. -/
private theorem generator_mul_apply_succ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {i p : Fin (n + 1)} (hp : (p : ℕ) + 1 = i) (k : Fin (n + 1)) :
    (blockCountingGenerator n * A) i k =
      ((i : ℕ).choose 2 : ℝ) * (A p k - A i k) := by
  have hne : i ≠ p := fun h => by rw [h] at hp; omega
  rw [Matrix.mul_apply, Fintype.sum_eq_add i p hne]
  · simp only [blockCountingGenerator, Matrix.of_apply, hp, show (i : ℕ) + 1 ≠ i by omega,
      ite_true, ite_false]
    ring
  · intro l ⟨hli, hlp⟩
    have h1 : (l : ℕ) + 1 ≠ i := fun h => hlp (Fin.ext (by omega))
    simp [blockCountingGenerator, h1, hli]

/-- Row `0` of `G` vanishes. -/
private theorem generator_mul_apply_zero (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {i : Fin (n + 1)} (hi : (i : ℕ) = 0) (k : Fin (n + 1)) :
    (blockCountingGenerator n * A) i k = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp [blockCountingGenerator, hi]

/-- Column `j < n` of `A * G`. -/
private theorem mul_generator_apply_castSucc (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) {j q : Fin (n + 1)} (hq : (j : ℕ) + 1 = q) :
    (A * blockCountingGenerator n) k j =
      -((j : ℕ).choose 2 : ℝ) * A k j + ((q : ℕ).choose 2 : ℝ) * A k q := by
  have hne : j ≠ q := fun h => by rw [h] at hq; omega
  rw [Matrix.mul_apply, Fintype.sum_eq_add j q hne]
  · simp only [blockCountingGenerator, Matrix.of_apply, hq, show (q : ℕ) ≠ j by omega,
      ite_true, ite_false]
    ring
  · intro l ⟨hlj, hlq⟩
    have h1 : (j : ℕ) + 1 ≠ l := fun h => hlq (Fin.ext (by omega))
    simp [blockCountingGenerator, h1, Ne.symm hlj]

/-- The last column of `A * G`. -/
private theorem mul_generator_apply_last (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (k : Fin (n + 1)) {j : Fin (n + 1)} (hj : (j : ℕ) = n) :
    (A * blockCountingGenerator n) k j = -((j : ℕ).choose 2 : ℝ) * A k j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single j]
  · simp [blockCountingGenerator, mul_comm]
  · intro l hl
    have h1 : (j : ℕ) + 1 ≠ l := by have := l.isLt; omega
    simp [blockCountingGenerator, h1, Ne.symm hl]

/-- The columns of `blockCountingRightEigen n` are right eigenvectors: `G V = V D`. -/
theorem blockCountingGenerator_mul_rightEigen (n : ℕ) :
    blockCountingGenerator n * blockCountingRightEigen n =
      blockCountingRightEigen n * diagonal (blockCountingEigenvalue n) := by
  ext i k
  rw [Matrix.mul_diagonal, rightEigen_apply, blockCountingEigenvalue]
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · rw [generator_mul_apply_zero n _ hi, hi]
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
    · simp [hk]
    · rw [vR_eq_zero hk, zero_mul]
  · set p : Fin (n + 1) := ⟨i - 1, by omega⟩
    have hp : (p : ℕ) + 1 = i := by simp only [p]; omega
    rw [generator_mul_apply_succ n _ hp, rightEigen_apply, rightEigen_apply]
    have h := vR_rec p k
    rw [hp] at h
    linear_combination -h

/-- The rows of `blockCountingLeftEigen n` are left eigenvectors: `W G = D W`. -/
theorem blockCountingLeftEigen_mul_generator (n : ℕ) :
    blockCountingLeftEigen n * blockCountingGenerator n =
      diagonal (blockCountingEigenvalue n) * blockCountingLeftEigen n := by
  ext k j
  rw [Matrix.diagonal_mul, leftEigen_apply, blockCountingEigenvalue]
  rcases Nat.lt_or_ge (j : ℕ) n with hj | hj
  · set q : Fin (n + 1) := ⟨j + 1, by omega⟩
    have hq : (j : ℕ) + 1 = q := rfl
    rw [mul_generator_apply_castSucc n _ k hq, leftEigen_apply, leftEigen_apply]
    have h := wL_rec k j
    rw [hq] at h
    linear_combination h
  · have hjn : (j : ℕ) = n := by have := j.isLt; omega
    rw [mul_generator_apply_last n _ k hjn, leftEigen_apply]
    have h := wL_last (n := n) (k := k) (by have := k.isLt; omega)
    rw [hjn]
    linear_combination -h

/-- The left and right eigenvector matrices are mutually inverse: `W V = 1`. -/
theorem blockCountingLeftEigen_mul_rightEigen (n : ℕ) :
    blockCountingLeftEigen n * blockCountingRightEigen n = 1 := by
  -- `W V` commutes with the diagonal matrix of eigenvalues.
  have hcomm : blockCountingLeftEigen n * blockCountingRightEigen n *
      diagonal (blockCountingEigenvalue n) =
      diagonal (blockCountingEigenvalue n) *
        (blockCountingLeftEigen n * blockCountingRightEigen n) := by
    rw [Matrix.mul_assoc, ← blockCountingGenerator_mul_rightEigen, ← Matrix.mul_assoc,
      blockCountingLeftEigen_mul_generator, Matrix.mul_assoc]
  have hdiag : ∀ a : Fin (n + 1),
      (blockCountingLeftEigen n * blockCountingRightEigen n) a a = 1 := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · exact wL_vR_self a
    · intro l _ hla
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hla) with h | h
      · rw [rightEigen_apply, vR_eq_zero h, mul_zero]
      · rw [leftEigen_apply, wL_eq_zero h, zero_mul]
    · simp
  ext a b
  rcases lt_trichotomy (a : ℕ) b with hab | hab | hab
  · -- above the diagonal: both factors are lower triangular
    rw [Matrix.one_apply_ne (Fin.ne_of_val_ne hab.ne), Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases Nat.lt_or_ge (a : ℕ) l with h | h
    · rw [leftEigen_apply, wL_eq_zero h, zero_mul]
    · rw [rightEigen_apply, vR_eq_zero (by omega), mul_zero]
  · rw [Fin.ext hab, Matrix.one_apply_eq, hdiag]
  · rw [Matrix.one_apply_ne (Fin.ne_of_val_ne hab.ne')]
    by_cases h10 : (a : ℕ) = 1 ∧ (b : ℕ) = 0
    · -- the double eigenvalue `0` (states `0` and `1`)
      rw [Matrix.mul_apply, Fintype.sum_eq_add b a (Fin.ne_of_val_ne hab.ne)]
      · simp only [leftEigen_apply, rightEigen_apply, h10.1, h10.2]
        exact wL_vR_one_zero
      · intro l ⟨hlb, hla⟩
        have hl : (a : ℕ) < l := by
          have h1 := Fin.val_ne_of_ne hlb
          have h2 := Fin.val_ne_of_ne hla
          omega
        rw [leftEigen_apply, wL_eq_zero hl, zero_mul]
    · -- distinct eigenvalues force the entry to vanish
      have hd : blockCountingEigenvalue n a ≠ blockCountingEigenvalue n b := by
        intro hd
        simp only [blockCountingEigenvalue, neg_inj, Nat.cast_choose_two] at hd
        have : ((a : ℝ) - b) * ((a : ℝ) + b - 1) = 0 := by linear_combination 2 * hd
        rcases mul_eq_zero.1 this with h | h
        · have : (a : ℝ) = b := by linarith
          exact absurd (by exact_mod_cast this : (a : ℕ) = b) hab.ne'
        · have : ((a + b : ℕ) : ℝ) = 1 := by push_cast; linarith
          have : (a : ℕ) + b = 1 := by exact_mod_cast this
          omega
      have h := congrFun (congrFun hcomm a) b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      have : (blockCountingLeftEigen n * blockCountingRightEigen n) a b *
          (blockCountingEigenvalue n b - blockCountingEigenvalue n a) = 0 := by
        linear_combination h
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hd.symm)

/-- The spectral decomposition of the transition matrix of the block-counting process:
`exp (t • G) = V diag(exp (-(k.choose 2) t)) W`. -/
theorem exp_smul_blockCountingGenerator (n : ℕ) (t : ℝ) :
    NormedSpace.exp (t • blockCountingGenerator n) =
      blockCountingRightEigen n *
        diagonal (fun k => Real.exp (t * blockCountingEigenvalue n k)) *
        blockCountingLeftEigen n := by
  have hWV := blockCountingLeftEigen_mul_rightEigen n
  have hVW := mul_eq_one_comm.1 hWV
  let U : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ˣ := ⟨_, _, hVW, hWV⟩
  have hG : t • blockCountingGenerator n =
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
        diagonal (fun k => t * blockCountingEigenvalue n k) *
        (↑U⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    have hd : diagonal (fun k => t * blockCountingEigenvalue n k) =
        t • diagonal (blockCountingEigenvalue n) := by
      ext a b
      by_cases hab : a = b <;> simp [hab]
    change _ = blockCountingRightEigen n * _ * blockCountingLeftEigen n
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← blockCountingGenerator_mul_rightEigen,
      Matrix.mul_assoc, hVW, Matrix.mul_one]
  rw [hG, Matrix.exp_units_conj, Matrix.exp_diagonal, Pi.exp_def]
  simp only [← Real.exp_eq_exp_ℝ]
  rfl

/-- **Tavaré's formula.** The transition probabilities of Kingman's block-counting process
from `i` to `j` lineages in time `t`, for `1 ≤ j ≤ i ≤ n`, are given by `tavareProb`.

Source: Tavaré (1984). Proves the deferred entry `exp_blockCountingGenerator_apply`. -/
theorem exp_blockCountingGenerator_apply (n : ℕ) (t : ℝ) (i j : Fin (n + 1))
    (hj : 1 ≤ (j : ℕ)) (hji : j ≤ i) :
    NormedSpace.exp (t • blockCountingGenerator n) i j = tavareProb i j t := by
  rw [exp_smul_blockCountingGenerator, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, rightEigen_apply, leftEigen_apply, blockCountingEigenvalue]
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.isLt
  have hji' : (j : ℕ) ≤ i := hji
  calc _ = ∑ k ∈ Finset.range (n + 1),
        vR i k * Real.exp (t * -((k.choose 2 : ℕ) : ℝ)) * wL k j :=
        Fin.sum_univ_eq_sum_range
          (fun k => vR i k * Real.exp (t * -((k.choose 2 : ℕ) : ℝ)) * wL k j) (n + 1)
    _ = ∑ k ∈ Finset.Icc (j : ℕ) i,
        vR i k * Real.exp (t * -((k.choose 2 : ℕ) : ℝ)) * wL k j := by
      refine (Finset.sum_subset (fun k hk => ?_) fun k _ hk => ?_).symm
      · simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_range]
        omega
      · simp only [Finset.mem_Icc, not_and_or, not_le] at hk
        rcases hk with hk | hk
        · rw [wL_eq_zero hk, mul_zero]
        · rw [vR_eq_zero hk, zero_mul, zero_mul]
    _ = tavareProb i j t := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hexp : Real.exp (t * -((k.choose 2 : ℕ) : ℝ)) =
          Real.exp (-((k : ℝ) * (k - 1) * t / 2)) := by
        rw [Nat.cast_choose_two]; ring_nf
      simp only [wL, show k ≠ 0 by omega, ite_false, hk.1, ite_true, vR, hexp]
      ring

end MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

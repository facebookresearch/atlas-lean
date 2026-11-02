/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Selection
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Diploid Baum–Eagon mean-fitness inequality for multi-allele viability selection

One locus with a finite set `ι` of alleles, random mating (Hardy–Weinberg proportions at birth)
and viability selection with genotype fitnesses `w i j ≥ 0`. One generation maps the allele
frequencies `p` to `p' = diploidSelect p w` (`Selection.lean`):
`p'_i = p_i m_i / w̄` with marginal fitness `m_i = ∑ j, (w i j + w j i) / 2 * p_j` and mean
fitness `w̄ = ∑ i, ∑ j, p_i p_j w i j`.

The map `p ↦ p'` is the Baum–Eagon growth transformation `p_i ↦ p_i ∂_i w̄ / ∑ p_j ∂_j w̄` of the
quadratic form `w̄`, so mean fitness never decreases. We prove the sharp form
`log w̄(p') - log w̄(p) ≥ 2 ∑ i, p'_i log (p'_i / p_i)`: by Jensen's inequality for `log` under
the genotype weights `p_i p_j (w i j + w j i) / (2 w̄)`, whose allele marginal is `p'`. On the
simplex the right side is twice the relative entropy of `p'` from `p`, which is positive unless
`p' = p`. Ordered fitnesses enter
only through their symmetrization `(w i j + w j i) / 2`, so no symmetry hypothesis is needed.

## Main results

* `two_mul_relEntropy_le_log_diploidMeanFitness_diploidSelect`: the sharp inequality above.
* `diploidMeanFitness_le_diploidMeanFitness_diploidSelect`: **mean fitness never decreases**
  under diploid multi-allele viability selection (Mulholland–Smith 1959; Scheuer–Mandel 1959;
  Kingman 1961).
* `diploidMeanFitness_diploidSelect_eq_iff`: mean fitness stays constant exactly at the
  equilibria `p' = p`; `diploidMeanFitness_lt_diploidMeanFitness_diploidSelect` is the strict
  form.
* `hasDerivAt_diploidMeanFitness_two`, `diploidSelect_two_sub`: for two alleles with frequencies
  `(x, 1 - x)`, **Wright's formula** `Δx = x (1 - x) (dw̄/dx) / (2 w̄)`.

The general Baum–Eagon inequality for homogeneous polynomials of any degree with nonnegative
coefficients is not covered; this file proves its degree-two case.

## References

* H. P. Mulholland, C. A. B. Smith, *An inequality arising in genetical theory*,
  Amer. Math. Monthly 66 (1959), 673–683.
* P. A. G. Scheuer, S. P. H. Mandel, *An inequality in population genetics*, Heredity 13 (1959),
  519–524.
* J. F. C. Kingman, *On an inequality in partial averages*, Quart. J. Math. Oxford (2) 12 (1961),
  78–80.
* L. E. Baum, J. A. Eagon, *An inequality with applications to statistical estimation for
  probabilistic functions of Markov processes and to a model for ecology*,
  Bull. Amer. Math. Soc. 73 (1967), 360–363.
* S. Wright, *The distribution of gene frequencies in populations*, Proc. Natl. Acad. Sci. USA 23
  (1937), 307–320.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.Selection

variable {ι : Type*} [Fintype ι]

/-- Each summand of a relative entropy dominates the difference of the masses:
`q log (q / r) ≥ q - r` for `q, r ≥ 0` with `r = 0 → q = 0`. -/
private lemma sub_le_mul_log_div {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hrq : r = 0 → q = 0) :
    q - r ≤ q * Real.log (q / r) := by
  rcases hq.eq_or_lt with rfl | hq'
  · simpa using hr
  have hr' : 0 < r := hr.lt_of_ne fun h => hq'.ne' (hrq h.symm)
  have h := Real.log_le_sub_one_of_pos (div_pos hr' hq')
  have e : Real.log (r / q) = -Real.log (q / r) := by rw [← Real.log_inv, inv_div]
  have : q * (r / q - 1) = r - q := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hq'.le]

/-- Equality case of `sub_le_mul_log_div`: `q log (q / r) = q - r` forces `q = r`. -/
private lemma eq_of_mul_log_div_eq {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hrq : r = 0 → q = 0) (h : q * Real.log (q / r) = q - r) : q = r := by
  rcases hq.eq_or_lt with rfl | hq'
  · simp at h; linarith
  have hr' : 0 < r := hr.lt_of_ne fun h => hq'.ne' (hrq h.symm)
  by_contra hne
  have hx : r / q ≠ 1 := fun h1 => hne (by field_simp at h1; linarith)
  have hlt := Real.log_lt_sub_one_of_pos (div_pos hr' hq') hx
  have e : Real.log (r / q) = -Real.log (q / r) := by rw [← Real.log_inv, inv_div]
  have : q * (r / q - 1) = r - q := by field_simp
  nlinarith [mul_lt_mul_of_pos_left hlt hq']

/-- **Gibbs' inequality** for finite distributions: `∑ q log (q / r) ≥ 0` when `q` and `r` are
nonnegative with equal total mass and `r_i = 0 → q_i = 0`. -/
private lemma relEntropy_nonneg {q r : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hrq : ∀ i, r i = 0 → q i = 0) (hsum : ∑ i, q i = ∑ i, r i) :
    0 ≤ ∑ i, q i * Real.log (q i / r i) := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    sub_le_mul_log_div (hq i) (hr i) (hrq i)
  rwa [Finset.sum_sub_distrib, hsum, sub_self] at this

/-- Equality case of Gibbs' inequality: zero relative entropy forces `q = r`. -/
private lemma eq_of_relEntropy_eq_zero {q r : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i)
    (hrq : ∀ i, r i = 0 → q i = 0) (hsum : ∑ i, q i = ∑ i, r i)
    (h0 : ∑ i, q i * Real.log (q i / r i) = 0) : q = r := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ q i * Real.log (q i / r i) - (q i - r i) := fun i _ =>
    sub_nonneg.2 (sub_le_mul_log_div (hq i) (hr i) (hrq i))
  have hz : ∑ i, (q i * Real.log (q i / r i) - (q i - r i)) = 0 := by
    rw [Finset.sum_sub_distrib, h0, Finset.sum_sub_distrib, hsum, sub_self, sub_self]
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz i (Finset.mem_univ i)
  exact eq_of_mul_log_div_eq (hq i) (hr i) (hrq i) (by linarith)

/-- Mean fitness is the frequency-weighted mean of the marginal fitnesses. -/
private lemma sum_mul_marginalFitness (p : ι → ℝ) (w : ι → ι → ℝ) :
    ∑ i, p i * marginalFitness p w i = diploidMeanFitness p w := by
  have hs : ∑ i, ∑ j, p i * p j * w j i = diploidMeanFitness p w := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have he : ∑ i, p i * marginalFitness p w i =
      (diploidMeanFitness p w + ∑ i, ∑ j, p i * p j * w j i) / 2 := by
    simp only [marginalFitness, diploidMeanFitness, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [he, hs]
  ring

/-- Alleles absent before selection stay absent, and selected frequencies are nonnegative. -/
private lemma diploidSelect_facts {p : ι → ℝ} {w : ι → ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hw0 : ∀ i j, 0 ≤ w i j) (hpos : 0 < diploidMeanFitness p w) :
    (∀ i, 0 ≤ diploidSelect p w i) ∧ (∀ i, p i = 0 → diploidSelect p w i = 0) ∧
      ∑ i, diploidSelect p w i = 1 := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hp0 i) (Finset.sum_nonneg fun j _ =>
    mul_nonneg (div_nonneg (add_nonneg (hw0 i j) (hw0 j i)) zero_le_two) (hp0 j))) hpos.le,
    fun i hi => by simp [diploidSelect, hi], sum_diploidSelect hpos.ne'⟩

/-- Mean fitness stays positive after one generation of diploid viability selection (for
nonnegative frequencies and fitnesses; normalization is not needed). -/
theorem diploidMeanFitness_diploidSelect_pos {p : ι → ℝ} {w : ι → ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : 0 < diploidMeanFitness p w) :
    0 < diploidMeanFitness (diploidSelect p w) w := by
  obtain ⟨hs0, -, -⟩ := diploidSelect_facts hp0 hw0 hpos
  have hm0 : ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) → ∀ i, 0 ≤ marginalFitness q w i := fun q hq i =>
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (div_nonneg (add_nonneg (hw0 i j) (hw0 j i)) zero_le_two) (hq j)
  rw [← sum_mul_marginalFitness]
  have hpos' := hpos
  rw [← sum_mul_marginalFitness] at hpos'
  have pos_of {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a * b) : 0 < a ∧ 0 < b :=
    ⟨ha.lt_of_ne fun h' => by rw [← h', zero_mul] at h; exact lt_irrefl _ h,
      hb.lt_of_ne fun h' => by rw [← h', mul_zero] at h; exact lt_irrefl _ h⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (s := Finset.univ) (g := fun i => p i * marginalFitness p w i)
    (by rw [Finset.sum_const_zero]; exact hpos')
  obtain ⟨hpi, hmi⟩ := pos_of (hp0 i) (hm0 p hp0 i) hi
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (s := Finset.univ) (g := fun j => (w i j + w j i) / 2 * p j)
    (by rw [Finset.sum_const_zero]; exact hmi)
  obtain ⟨hwij, hpj⟩ := pos_of (div_nonneg (add_nonneg (hw0 i j) (hw0 j i)) zero_le_two)
    (hp0 j) hj
  have hmj : 0 < marginalFitness p w j := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun k => (w j k + w k j) / 2 * p k) (fun k _ =>
        mul_nonneg (div_nonneg (add_nonneg (hw0 j k) (hw0 k j)) zero_le_two) (hp0 k))
      (Finset.mem_univ i))
    rw [add_comm (w j i)]
    exact mul_pos hwij hpi
  have hsi : 0 < diploidSelect p w i := div_pos (mul_pos hpi hmi) hpos
  have hsj : 0 < diploidSelect p w j := div_pos (mul_pos hpj hmj) hpos
  have hm'i : 0 < marginalFitness (diploidSelect p w) w i :=
    lt_of_lt_of_le (mul_pos hwij hsj) (Finset.single_le_sum
      (f := fun k => (w i k + w k i) / 2 * diploidSelect p w k) (fun k _ =>
        mul_nonneg (div_nonneg (add_nonneg (hw0 i k) (hw0 k i)) zero_le_two) (hs0 k))
      (Finset.mem_univ j))
  exact lt_of_lt_of_le (mul_pos hsi hm'i) (Finset.single_le_sum
    (f := fun k => diploidSelect p w k * marginalFitness (diploidSelect p w) w k)
    (fun k _ => mul_nonneg (hs0 k) (hm0 _ hs0 k)) (Finset.mem_univ i))

/-- **Diploid Baum–Eagon mean-fitness inequality, sharp form.** With
nonnegative allele frequencies and genotype fitnesses and positive mean fitness, one generation
of selection raises the log mean fitness by at least twice the relative entropy
`∑ i, p'_i log (p'_i / p_i)` of the new allele frequencies `p'` from the old ones `p`
(Baum–Eagon's argument for the quadratic form `w̄`). Alleles absent before selection stay absent
(`p_i = 0 → p'_i = 0`), so the summands with `p_i = 0` vanish. The inequality does not need
`∑ p = 1`; on the simplex its right side is nonnegative (Gibbs' inequality). This is a
mean-fitness monotonicity inequality, not Fisher's fundamental theorem: Fisher's theorem
concerns the change attributable to selection expressed through additive genetic variance,
which is not proved here. -/
theorem two_mul_relEntropy_le_log_diploidMeanFitness_diploidSelect {p : ι → ℝ}
    {w : ι → ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : 0 < diploidMeanFitness p w) :
    2 * ∑ i, diploidSelect p w i * Real.log (diploidSelect p w i / p i) ≤
      Real.log (diploidMeanFitness (diploidSelect p w) w) -
        Real.log (diploidMeanFitness p w) := by
  classical
  set q := diploidSelect p w with hq
  set W := diploidMeanFitness p w with hW
  have hposq := diploidMeanFitness_diploidSelect_pos hp0 hw0 hpos
  obtain ⟨hq0, hsupp, -⟩ := diploidSelect_facts hp0 hw0 hpos
  set ws : ι → ι → ℝ := fun i j => (w i j + w j i) / 2 with hws
  have hws0 : ∀ i j, 0 ≤ ws i j := fun i j =>
    div_nonneg (add_nonneg (hw0 i j) (hw0 j i)) zero_le_two
  have hwsymm : ∀ i j, ws i j = ws j i := fun i j => by simp only [hws]; ring
  -- mean fitness through the symmetrized fitnesses, as a sum over genotypes
  have hmean : ∀ r : ι → ℝ,
      diploidMeanFitness r w = ∑ x : ι × ι, r x.1 * r x.2 * ws x.1 x.2 := by
    intro r
    rw [Fintype.sum_prod_type]
    have hs : ∑ i, ∑ j, r i * r j * w j i = diploidMeanFitness r w := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have : ∑ i, ∑ j, r i * r j * ws i j =
        (diploidMeanFitness r w + ∑ i, ∑ j, r i * r j * w j i) / 2 := by
      simp only [hws, diploidMeanFitness, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, hs]; ring
  have hmarg : ∀ i, marginalFitness p w i = ∑ j, ws i j * p j := fun i => rfl
  -- genotype weights
  set π : ι × ι → ℝ := fun x => p x.1 * p x.2 * ws x.1 x.2 / W with hπ
  have hπ0 : ∀ x, 0 ≤ π x := fun x =>
    div_nonneg (mul_nonneg (mul_nonneg (hp0 _) (hp0 _)) (hws0 _ _)) hpos.le
  have hrow : ∀ i, ∑ j, π (i, j) = q i := by
    intro i
    simp only [hπ, hq, diploidSelect, hmarg, ← Finset.sum_div, Finset.mul_sum]
    exact congrArg (· / W) (Finset.sum_congr rfl fun j _ => by ring)
  have hcol : ∀ j, ∑ i, π (i, j) = q j := by
    intro j
    rw [← hrow j]
    exact Finset.sum_congr rfl fun i _ => by simp only [hπ, hwsymm i j]; ring
  set S := (Finset.univ : Finset (ι × ι)).filter fun x => 0 < π x with hS
  have hoff : ∀ x, x ∉ S → π x = 0 := fun x hx =>
    le_antisymm (not_lt.1 fun h => hx (by simp [hS, h])) (hπ0 x)
  -- positivity on the support
  have hpos_of : ∀ x ∈ S, 0 < p x.1 ∧ 0 < p x.2 ∧ 0 < q x.1 ∧ 0 < q x.2 := by
    intro x hx
    have hx' : 0 < π x := (Finset.mem_filter.1 hx).2
    have h3 : 0 < p x.1 * p x.2 * ws x.1 x.2 := by
      have := mul_pos hx' hpos
      rwa [hπ, div_mul_cancel₀ _ hpos.ne'] at this
    have h1 : 0 < p x.1 := (hp0 _).lt_of_ne fun h => by rw [← h] at h3; simp at h3
    have h2 : 0 < p x.2 := (hp0 _).lt_of_ne fun h => by rw [← h] at h3; simp at h3
    have h4 : 0 < ws x.1 x.2 := (hws0 _ _).lt_of_ne fun h => by rw [← h] at h3; simp at h3
    have hm1 : 0 < marginalFitness p w x.1 := by
      rw [hmarg]
      exact lt_of_lt_of_le (mul_pos h4 h2) (Finset.single_le_sum
        (f := fun k => ws x.1 k * p k) (fun k _ => mul_nonneg (hws0 _ _) (hp0 k))
        (Finset.mem_univ _))
    have hm2 : 0 < marginalFitness p w x.2 := by
      rw [hmarg]
      refine lt_of_lt_of_le (mul_pos (h4.trans_eq (hwsymm _ _)) h1) (Finset.single_le_sum
        (f := fun k => ws x.2 k * p k) (fun k _ => mul_nonneg (hws0 _ _) (hp0 k))
        (Finset.mem_univ _))
    exact ⟨h1, h2, div_pos (mul_pos h1 hm1) hpos, div_pos (mul_pos h2 hm2) hpos⟩
  -- the ratio of mean fitnesses as a π-average
  set ρ : ι × ι → ℝ := fun x => q x.1 * q x.2 / (p x.1 * p x.2) with hρ
  have hsum1 : ∑ x ∈ S, π x = 1 := by
    rw [Finset.sum_filter_of_ne fun x _ hx => (hπ0 x).lt_of_ne hx.symm]
    simp only [hπ, ← Finset.sum_div, ← hmean]
    exact div_self hpos.ne'
  have hzero : ∀ x, x ∉ S → q x.1 * q x.2 * ws x.1 x.2 = 0 := by
    intro x hx
    have h0 := hoff x hx
    have : p x.1 * p x.2 * ws x.1 x.2 = 0 := by
      rw [hπ, div_eq_zero_iff] at h0
      exact h0.resolve_right hpos.ne'
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · simp [hq, hsupp _ h]
      · simp [hq, hsupp _ h]
    · simp [h]
  have hratio : ∑ x ∈ S, π x * ρ x = diploidMeanFitness q w / W := by
    have hterm : ∀ x ∈ S, π x * ρ x = q x.1 * q x.2 * ws x.1 x.2 / W := by
      intro x hx
      obtain ⟨h1, h2, -, -⟩ := hpos_of x hx
      simp only [hπ, hρ]
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_subset (Finset.subset_univ S)
      fun x _ hx => by rw [hzero x hx, zero_div], ← Finset.sum_div, ← hmean]
  have hjensen : ∑ x ∈ S, π x * Real.log (ρ x) ≤ Real.log (∑ x ∈ S, π x * ρ x) := by
    have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := S) (w := π) (p := ρ)
      (fun x _ => hπ0 x) hsum1 fun x hx => by
        obtain ⟨h1, h2, h3, h4⟩ := hpos_of x hx
        exact Set.mem_Ioi.2 (div_pos (mul_pos h3 h4) (mul_pos h1 h2))
    simpa only [smul_eq_mul] using this
  have hsplit : ∑ x ∈ S, π x * Real.log (ρ x) = 2 * ∑ i, q i * Real.log (q i / p i) := by
    have h1 : ∀ x ∈ S, π x * Real.log (ρ x) =
        π x * Real.log (q x.1 / p x.1) + π x * Real.log (q x.2 / p x.2) := by
      intro x hx
      obtain ⟨h1, h2, h3, h4⟩ := hpos_of x hx
      rw [← mul_add, ← Real.log_mul (div_pos h3 h1).ne' (div_pos h4 h2).ne', hρ]
      dsimp only
      rw [mul_div_mul_comm]
    rw [Finset.sum_congr rfl h1, Finset.sum_subset (Finset.subset_univ S) fun x _ hx => by
      rw [hoff x hx, zero_mul, zero_mul, add_zero], Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => π (i, j) * Real.log (q j / p j))]
    simp only [← Finset.sum_mul, hrow, hcol]
    ring
  rw [← hsplit, ← Real.log_div hposq.ne' hpos.ne', ← hratio]
  exact hjensen

/-- **Mean fitness never decreases** under diploid multi-allele viability selection with random
mating (Mulholland–Smith 1959; Scheuer–Mandel 1959; Kingman 1961). -/
theorem diploidMeanFitness_le_diploidMeanFitness_diploidSelect {p : ι → ℝ} {w : ι → ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : 0 < diploidMeanFitness p w) :
    diploidMeanFitness p w ≤ diploidMeanFitness (diploidSelect p w) w := by
  obtain ⟨hs0, hsupp, hs1⟩ := diploidSelect_facts hp0 hw0 hpos
  have hkl := relEntropy_nonneg hs0 hp0 hsupp (by rw [hs1, hp])
  have h := two_mul_relEntropy_le_log_diploidMeanFitness_diploidSelect hp0 hw0 hpos
  have hpos' := diploidMeanFitness_diploidSelect_pos hp0 hw0 hpos
  exact (Real.log_le_log_iff hpos hpos').1 (by linarith)

/-- Mean fitness is unchanged by one generation of selection exactly when the allele
frequencies are at an equilibrium of the selection map. -/
theorem diploidMeanFitness_diploidSelect_eq_iff {p : ι → ℝ} {w : ι → ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : 0 < diploidMeanFitness p w) :
    diploidMeanFitness (diploidSelect p w) w = diploidMeanFitness p w ↔
      diploidSelect p w = p := by
  obtain ⟨hs0, hsupp, hs1⟩ := diploidSelect_facts hp0 hw0 hpos
  refine ⟨fun heq => ?_, fun h => by rw [h]⟩
  have hkl := relEntropy_nonneg hs0 hp0 hsupp (by rw [hs1, hp])
  have h := two_mul_relEntropy_le_log_diploidMeanFitness_diploidSelect hp0 hw0 hpos
  rw [heq, sub_self] at h
  exact eq_of_relEntropy_eq_zero hs0 hp0 hsupp (by rw [hs1, hp]) (by linarith)

/-- Away from equilibria, mean fitness strictly increases under diploid viability selection. -/
theorem diploidMeanFitness_lt_diploidMeanFitness_diploidSelect {p : ι → ℝ} {w : ι → ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) (hw0 : ∀ i j, 0 ≤ w i j)
    (hpos : 0 < diploidMeanFitness p w) (hne : diploidSelect p w ≠ p) :
    diploidMeanFitness p w < diploidMeanFitness (diploidSelect p w) w := by
  refine (diploidMeanFitness_le_diploidMeanFitness_diploidSelect hp0 hp hw0 hpos).lt_of_ne ?_
  intro h
  exact hne ((diploidMeanFitness_diploidSelect_eq_iff hp0 hp hw0 hpos).1 h.symm)

/-! ### Two alleles: Wright's formula -/

/-- For two alleles with frequencies `(x, 1 - x)`, the mean fitness
`w̄(x) = x² w₀₀ + x (1 - x) (w₀₁ + w₁₀) + (1 - x)² w₁₁` has derivative `2 (m₀ - m₁)`, twice the
difference of the marginal fitnesses. This holds for every real `x`. -/
theorem hasDerivAt_diploidMeanFitness_two (w : Fin 2 → Fin 2 → ℝ) (x : ℝ) :
    HasDerivAt (fun y => diploidMeanFitness ![y, 1 - y] w)
      (2 * (marginalFitness ![x, 1 - x] w 0 - marginalFitness ![x, 1 - x] w 1)) x := by
  have h : (fun y => diploidMeanFitness ![y, 1 - y] w) = fun y =>
      y * y * w 0 0 + y * (1 - y) * w 0 1 +
        ((1 - y) * y * w 1 0 + (1 - y) * (1 - y) * w 1 1) := by
    funext y
    simp [diploidMeanFitness, Fin.sum_univ_two]
  rw [h]
  have hx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x :=
    HasDerivAt.sub (hasDerivAt_const x (1 : ℝ)) hx
  have hm (f g : ℝ → ℝ) (f' g' c : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
      HasDerivAt (fun y => f y * g y * c) ((f' * g x + f x * g') * c) x :=
    HasDerivAt.mul_const (HasDerivAt.mul hf hg) c
  refine HasDerivAt.congr_deriv (HasDerivAt.add (HasDerivAt.add (hm _ _ _ _ (w 0 0) hx hx)
    (hm _ _ _ _ (w 0 1) hx h1)) (HasDerivAt.add (hm _ _ _ _ (w 1 0) h1 hx)
    (hm _ _ _ _ (w 1 1) h1 h1))) ?_
  simp only [marginalFitness, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Wright's formula** (Wright 1937): for two alleles with frequencies `(x, 1 - x)`, one
generation of viability selection changes the frequency of allele `0` by
`Δx = x (1 - x) (dw̄/dx) / (2 w̄)`. The identity is algebraic and holds for every real `x` with
`w̄(x) ≠ 0`; the model domain is `x ∈ [0, 1]` with nonnegative fitnesses. -/
theorem diploidSelect_two_sub (w : Fin 2 → Fin 2 → ℝ) (x : ℝ)
    (hw : diploidMeanFitness ![x, 1 - x] w ≠ 0) :
    diploidSelect ![x, 1 - x] w 0 - x =
      x * (1 - x) * deriv (fun y => diploidMeanFitness ![y, 1 - y] w) x /
        (2 * diploidMeanFitness ![x, 1 - x] w) := by
  rw [(hasDerivAt_diploidMeanFitness_two w x).deriv]
  have hsum : diploidMeanFitness ![x, 1 - x] w =
      x * marginalFitness ![x, 1 - x] w 0 + (1 - x) * marginalFitness ![x, 1 - x] w 1 := by
    simp only [diploidMeanFitness, marginalFitness, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  simp only [diploidSelect, Matrix.cons_val_zero]
  rw [div_sub' hw, div_eq_div_iff hw (mul_ne_zero two_ne_zero hw), hsum]
  ring

end MathlibExt.Biology.PopulationGenetics.Selection

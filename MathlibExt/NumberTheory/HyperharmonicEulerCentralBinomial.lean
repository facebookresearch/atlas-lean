/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperharmonicEulerSums
import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic
import MathlibExt.NumberTheory.CatalanOddMultipleHarmonicDivTsum

/-!
# Central binomial odd harmonic sums

Duality reduces the central binomial sum with denominator $4^n(n+1)^2$ to a series of
rational functions. Iterating a partial-fraction identity reduces it to a grouped
alternating harmonic series and finitely many half-integer reciprocal power sums.

## References

* Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
  INTEGERS 26 (2026), Article A81, pp. 1–22, (2.12) and Corollaries 1 and 3.
-/

namespace MetaMathlibExt

open Finset Filter
open scoped Topology

-- Only the subset omitting zero can give a nonzero product at depth one.
private lemma generalizedHyperharmonic_succ_one_zero (n : ℕ) :
    generalizedHyperharmonic (n + 1) 1 0 = 1 / ((n : ℂ) + 1) := by
  let e : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  let s := (range n).map e
  have hs : s = (range (n + 1)).erase 0 := by
    ext j
    cases j <;> simp [s, e, Function.Embedding.coeFn_mk]
  have hc : s.card = n := by simp [s]
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simp only [generalizedHyperharmonic, show 1 ≤ n + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
  have hsub : s ⊆ range (n + 1) := by
    rw [hs]
    exact erase_subset _ _
  rw [sum_eq_single_of_mem s (mem_powersetCard.mpr ⟨hsub, hc⟩)]
  · have hprod : (∏ j ∈ s, ((0 : ℂ) + j)) = (n.factorial : ℂ) := by
      simp only [s, prod_map, e, Function.Embedding.coeFn_mk, zero_add]
      rw [← Nat.cast_prod, prod_range_add_one_eq_factorial]
    rw [hprod, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
  · intro t ht hts
    apply prod_eq_zero (i := 0) _ (by simp)
    by_contra hzero
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp ht
    have htsub : t ⊆ s := by
      rw [hs]
      exact subset_erase.mpr ⟨hsub, hzero⟩
    exact hts (eq_of_subset_of_card_le htsub (by rw [hc, hcard]))

private lemma nat_add_one_half_ne_zero (n : ℕ) : ((n : ℂ) + 1 + 1 / 2) ≠ 0 := by
  intro h
  have hz := congrArg Complex.re h
  norm_num at hz
  linarith [Nat.cast_nonneg (α := ℝ) n]

private noncomputable def dualTerm (k n : ℕ) : ℂ :=
  1 / (((n : ℂ) + 1) * ((n : ℂ) + 1 + 1 / 2) ^ (k + 1))

private lemma dual_hasSum (k : ℕ) :
    HasSum (dualTerm k) (hyperharmonicEulerSum k (1 / 2) 2 1) := by
  obtain ⟨_, hs, heq⟩ := hyperharmonicEulerSum_duality k 1 (1 / 2) 0 (by norm_num)
    (by simp only [Complex.zero_re]; positivity)
  have h := hs.hasSum
  change HasSum _ (hyperharmonicEulerSum 1 0 ((k : ℤ) + 1) (1 - 1 / 2)) at h
  rw [← heq] at h
  norm_num at h ⊢
  apply h.congr_fun
  intro n
  rw [dualTerm, generalizedHyperharmonic_succ_one_zero, div_div, ← Int.natCast_succ,
    zpow_natCast]

private lemma hasSum_half_tail (s : ℕ) (hs : 1 < s) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1 + 1 / 2) ^ s)
      ((2 ^ s - 1) * riemannZeta (s : ℂ) - 2 ^ s) := by
  have htail := (hasSum_nat_add_iff' 1).mpr (hasSum_one_div_nat_add_half_pow s hs)
  simpa only [sum_range_one, Nat.cast_zero, zero_add, one_div, ← inv_pow,
    inv_div, inv_inv, div_one, Nat.cast_add, Nat.cast_one] using htail

-- An odd-length alternating partial sum starts with 1 and then contains complete pairs.
private lemma dual_zero_hasSum : HasSum (dualTerm 0) (4 * (1 - (Real.log 2 : ℂ))) := by
  let A (N : ℕ) := ∑ i ∈ range N, (-1 : ℝ) ^ i / ((i : ℝ) + 1)
  have hpair (N : ℕ) : (∑ n ∈ range N, dualTerm 0 n) = 4 * (1 - (A (2 * N + 1) : ℂ)) := by
    induction N with
    | zero => norm_num [A]
    | succ N ih =>
      rw [sum_range_succ, ih, show 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 by omega]
      have he : Even (2 * N + 1 + 1) := ⟨N + 1, by omega⟩
      have ho : Odd (2 * N + 1) := ⟨N, rfl⟩
      simp only [A, sum_range_succ _ (2 * N + 1 + 1), sum_range_succ _ (2 * N + 1),
        he.neg_one_pow, ho.neg_one_pow, Complex.ofReal_add, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      have hp : dualTerm 0 N = 4 / (2 * (N : ℂ) + 1 + 1) - 4 / (2 * (N : ℂ) + 1 + 1 + 1) := by
        let x : ℂ := (N : ℂ) + 1
        let y : ℂ := x + 1 / 2
        have h₂ : (2 * (N : ℂ) + 1 + 1) = 2 * x := by dsimp [x]; ring
        have h₃ : (2 * (N : ℂ) + 1 + 1 + 1) = 2 * y := by dsimp [x, y]; ring
        have hx : x ≠ 0 := by dsimp [x]; exact_mod_cast Nat.succ_ne_zero N
        have hy : y ≠ 0 := nat_add_one_half_ne_zero N
        rw [h₃, h₂]
        change 1 / (x * y ^ (1 : ℕ)) = _
        rw [pow_one]
        field_simp [hx, hy]
        dsimp [y]
        ring
      rw [hp]
      ring
  have hN : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
    apply tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega)
    exact tendsto_id
  have hA : Tendsto (fun N => A (2 * N + 1)) atTop (𝓝 (Real.log 2)) :=
    Real.tendsto_sum_alternating_harmonic.comp hN
  have hA' := Complex.continuous_ofReal.continuousAt.tendsto.comp hA
  have hlim := tendsto_const_nhds (x := (4 : ℂ)) |>.mul
    (tendsto_const_nhds (x := (1 : ℂ)) |>.sub hA')
  have h := (dual_hasSum 0).tendsto_sum_nat
  simp_rw [hpair] at h
  have heq := tendsto_nhds_unique h hlim
  rw [← heq]
  exact dual_hasSum 0

private lemma sum_Icc_one_succ (k : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Icc 1 (k + 1), f j) = f 1 + ∑ j ∈ Icc 1 k, f (j + 1) := by
  let e : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  have h : Icc 1 (k + 1) = insert 1 ((Icc 1 k).map e) := by
    ext j
    simp only [mem_Icc, mem_insert, Finset.mem_map, e, Function.Embedding.coeFn_mk]
    constructor
    · intro hj
      by_cases h : j = 1
      · exact Or.inl h
      · exact Or.inr ⟨j - 1, by omega, by omega⟩
    · rintro (rfl | ⟨i, hi, rfl⟩) <;> omega
  rw [h, sum_insert, sum_map]
  · rfl
  · simp [e, Finset.mem_Icc]

-- One partial-fraction step raises the reciprocal power by one.
private lemma dualTerm_succ (k n : ℕ) :
    dualTerm (k + 1) n = 2 * dualTerm k n - 2 * (1 / ((n : ℂ) + 1 + 1 / 2) ^ (k + 2)) := by
  let x : ℂ := (n : ℂ) + 1
  let y : ℂ := x + 1 / 2
  have hx : x ≠ 0 := by dsimp [x]; exact_mod_cast Nat.succ_ne_zero n
  have hy : y ≠ 0 := nat_add_one_half_ne_zero n
  change 1 / (x * y ^ ((k + 1) + 1)) = 2 * (1 / (x * y ^ (k + 1))) - 2 * (1 / y ^ (k + 2))
  simp only [show k + 2 = (k + 1) + 1 by omega, pow_succ _ (k + 1)]
  field_simp [hx, hy]
  dsimp [y]
  ring

private lemma dual_eval (k : ℕ) : HasSum (dualTerm k)
    (2 ^ (k + 2) * (k + 1 - Real.log 2) -
      ∑ j ∈ Icc 1 k, (2 ^ (k + 2) - 2 ^ j) * riemannZeta ((k + 2 - j : ℕ) : ℂ)) := by
  induction k with
  | zero => simpa [pow_two, show (2 : ℂ) * 2 = 4 by norm_num] using dual_zero_hasSum
  | succ k ih =>
    have hs := ((ih.mul_left (2 : ℂ)).sub ((hasSum_half_tail (k + 2) (by omega)).mul_left 2))
    have ht := hs.congr_fun (fun n => dualTerm_succ k n)
    convert ht using 1
    rw [sum_Icc_one_succ]
    have hsum : (∑ j ∈ Icc 1 k,
        ((2 : ℂ) ^ (k + 1 + 2) - 2 ^ (j + 1)) * riemannZeta ((k + 1 + 2 - (j + 1) : ℕ) : ℂ)) =
        2 * ∑ j ∈ Icc 1 k, (2 ^ (k + 2) - 2 ^ j) * riemannZeta ((k + 2 - j : ℕ) : ℂ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      rw [show k + 1 + 2 - (j + 1) = k + 2 - j by omega,
        show k + 1 + 2 = k + 2 + 1 by omega, pow_succ, pow_succ (2 : ℂ) j]
      ring
    rw [hsum, show k + 1 + 2 - 1 = k + 2 by omega,
      show k + 1 + 2 = k + 2 + 1 by omega, pow_succ, pow_one, Nat.cast_succ]
    ring

@[expose] public section

/-- **Central binomial odd harmonic sum with denominator $4^n (n + 1)^2$.** For every integer
$k \ge 0$, with $O_n(k)$ the depth-$k$ odd harmonic number,
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n (n + 1)^2} =
2^{k+2} (k + 1 - \log 2) - \sum_{j=1}^{k} (2^{k+2} - 2^j) \zeta(k + 2 - j).$$

The terms with $n < k$ vanish, since $O_n(k) = 0$ for $n < k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 3 (`integers-2026-A81-cor-3`). -/
theorem centralBinom_oddMultipleHarmonic_div_succ_sq_tsum (k : ℕ) :
    ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      2 ^ (k + 2) * (k + 1 - Real.log 2) -
        ∑ j ∈ Finset.Icc 1 k, (2 ^ (k + 2) - 2 ^ j) * riemannZeta ((k + 2 - j : ℕ) : ℂ) := by
  rw [← (dual_hasSum k).unique (dual_eval k), hyperharmonicEulerSum_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [generalizedHyperharmonic_half_eq, show (2 : ℤ) = (2 : ℕ) by norm_num, zpow_natCast]
  push_cast
  rw [div_mul_eq_mul_div, div_div]

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CyclotomicTraceMetric
import MathlibExt.NumberTheory.SymmetricPowerSums
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Ring

/-!
# Second moment of the trace distance on the cyclotomic box

The second moment `M₂(p, N)` of the trace metric over the box `B(p, N)` equals
`2 / 3 * (p ^ 3 - 2 * p ^ 2 + 1) * N * (N + 1)`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 4.
-/

namespace MetaMathlibExt

open IsCyclotomicExtension

open Polynomial in
private theorem trace_zeta_pow {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (n : ℕ) :
    Algebra.trace ℚ K (zeta p ℚ K ^ n) = (if p ∣ n then (p : ℚ) else 0) - 1 := by
  have hζ := zeta_spec p ℚ K
  have hirr := cyclotomic.irreducible_rat hp.pos
  by_cases hn : p ∣ n
  · rw [ite_eq_left hn, (hζ.pow_eq_one_iff_dvd n).2 hn, ← map_one (algebraMap ℚ K),
      Algebra.trace_algebraMap, IsCyclotomicExtension.finrank K hirr, Nat.totient_prime hp]
    simp [nsmul_eq_mul, Nat.cast_sub hp.one_le]
  · have hprim := hζ.pow_of_coprime n (hp.coprime_iff_not_dvd.mpr hn).symm
    have hdeg : (cyclotomic p ℚ).natDegree = p - 1 := by
      rw [natDegree_cyclotomic, Nat.totient_prime hp]
    have htwo := hp.two_le
    let : Fact p.Prime := ⟨hp⟩
    rw [ite_eq_right hn, zero_sub, ← hprim.powerBasis_gen ℚ,
      PowerBasis.trace_gen_eq_nextCoeff_minpoly, hprim.powerBasis_gen ℚ,
      ← hprim.minpoly_eq_cyclotomic_of_irreducible hirr,
      nextCoeff_of_natDegree_pos (by omega), hdeg, cyclotomic_prime, finsetSum_coeff]
    simp [coeff_X_pow, show p - 1 - 1 < p by omega]

private theorem lattice_sub_eq {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (a b : Fin (p - 1) → ℤ) :
    cyclotomicLatticePoint K a - cyclotomicLatticePoint K b
      = ∑ i, ((((a i - b i : ℤ)) : ℚ) : K) * zeta p ℚ K ^ (i.val + 1) := by
  unfold cyclotomicLatticePoint
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_mul, ← Int.cast_sub, Rat.cast_intCast]

private theorem trace_lattice_sub {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (a b : Fin (p - 1) → ℤ) :
    Algebra.trace ℚ K (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b)
      = -∑ i, (((a i - b i : ℤ)) : ℚ) := by
  rw [lattice_sub_eq]
  rw [map_sum]
  have hterm : ∀ i : Fin (p - 1),
      Algebra.trace ℚ K (((((a i - b i : ℤ)) : ℚ) : K) * zeta p ℚ K ^ (i.val + 1))
        = -(((a i - b i : ℤ)) : ℚ) := by
    intro i
    have hndvd : ¬p ∣ i.val + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have htrace : Algebra.trace ℚ K (zeta p ℚ K ^ (i.val + 1)) = -1 := by
      rw [trace_zeta_pow hp]
      rw [ite_eq_right hndvd]
      simp
    have hsmul : ((((a i - b i : ℤ)) : ℚ) : K) * zeta p ℚ K ^ (i.val + 1)
        = (((a i - b i : ℤ)) : ℚ) • zeta p ℚ K ^ (i.val + 1) := by
      simp [Rat.smul_def]
    rw [hsmul, (Algebra.trace ℚ K).map_smul, htrace]
    simp
  simp_rw [hterm, Finset.sum_neg_distrib]

private theorem normSq_lattice_sub {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (a b : Fin (p - 1) → ℤ) :
    cyclotomicTraceNormSq p (cyclotomicLatticePoint K a - cyclotomicLatticePoint K b)
      = ((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
        - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2) := by
  have heq := (cyclotomicTraceNormSq_eq_and_ge (K := K) hp
    (fun i => (((a i - b i : ℤ)) : ℚ))).1
  rw [lattice_sub_eq]
  have htr := trace_lattice_sub (K := K) hp a b
  rw [lattice_sub_eq] at htr
  rw [heq, htr]
  ring

private theorem dist_sq_eq {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (α β : K) :
    cyclotomicTraceDist p α β ^ 2 = (cyclotomicTraceNormSq p (α - β) : ℝ) := by
  unfold cyclotomicTraceDist cyclotomicTraceNorm
  rw [Real.sq_sqrt]
  unfold cyclotomicTraceNormSq
  rw [Rat.cast_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Rat.cast_pow]
  apply sq_nonneg

private theorem card_Icc_eq (N : ℕ) : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  have h : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private theorem card_box_eq (p N : ℕ) : (cyclotomicBox p N).card = (2 * N + 1) ^ (p - 1) := by
  unfold cyclotomicBox
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Int.card_Icc]
  have h : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private theorem sum_single_zero (N : ℕ) : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, (x : ℚ) = 0 := by
  have h : (∑ x ∈ Finset.Icc (-(N : ℤ)) N, x : ℤ) = 0 := by
    simpa only [pow_one] using (symmetric_power_sums N).1 1 odd_one
  have h2 : ((∑ x ∈ Finset.Icc (-(N : ℤ)) N, x : ℤ) : ℚ) = 0 := by exact_mod_cast h
  rw [Int.cast_sum] at h2
  simpa using h2

private theorem sum_sub_const (N : ℕ) (c : ℤ) :
    ∑ x ∈ Finset.Icc (-(N : ℤ)) N, (((x - c : ℤ)) : ℚ)
      = -((Finset.Icc (-(N : ℤ)) N).card : ℚ) * (c : ℚ) := by
  simp_rw [Int.cast_sub, Finset.sum_sub_distrib, sum_single_zero]
  simp [Finset.sum_const, nsmul_eq_mul]

private theorem sum_pair_sq (N : ℕ) :
    ∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N, ((x - y : ℤ) : ℚ) ^ 2
      = 2 * N * (N + 1) * (2 * N + 1) ^ 2 / 3 := by
  have h0 : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, (x : ℚ) = 0 := sum_single_zero N
  have h2 := (symmetric_power_sums N).2.1
  have hC := card_Icc_eq N
  have hexpand : ∀ x y : ℤ, ((x - y : ℤ) : ℚ) ^ 2
      = (x : ℚ) ^ 2 - 2 * (x : ℚ) * (y : ℚ) + (y : ℚ) ^ 2 := by
    intro x y
    rw [Int.cast_sub]
    ring
  simp_rw [hexpand]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hxx : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (x : ℚ) ^ 2
      = ((Finset.Icc (-(N : ℤ)) N).card : ℚ) * ∑ x ∈ Finset.Icc (-(N : ℤ)) N, (x : ℚ) ^ 2 := by
    rw [Finset.sum_comm]
    simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hyy : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (y : ℚ) ^ 2
      = ((Finset.Icc (-(N : ℤ)) N).card : ℚ) * ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (y : ℚ) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hxy : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N, 2 * (x : ℚ) * (y : ℚ)
      = 0 := by
    have hmul : ∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (x : ℚ) * (y : ℚ)
        = (∑ x ∈ Finset.Icc (-(N : ℤ)) N, (x : ℚ)) * ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (y : ℚ) := by
      rw [Finset.sum_mul_sum]
    have hfactor : (∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N,
          2 * (x : ℚ) * (y : ℚ))
        = 2 * ∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N,
          (x : ℚ) * (y : ℚ) := by
      simp [mul_assoc, Finset.mul_sum]
    rw [hfactor, hmul, h0, mul_zero, mul_zero]
  rw [hxx, hyy, hxy]
  rw [h2, hC]
  push_cast
  ring

private theorem diag_box_sum (p N : ℕ) (i : Fin (p - 1)) :
    ∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N, (((a i - b i : ℤ) : ℚ) ^ 2)
      = (((Finset.Icc (-(N : ℤ)) N).card ^ (Fintype.card (Fin (p - 1)) - 1) : ℕ) : ℚ) ^ 2 *
        (∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N,
          (((x - y : ℤ) : ℚ) ^ 2)) := by
  have hinner : ∀ a : Fin (p - 1) → ℤ,
      ∑ b ∈ cyclotomicBox p N, (((a i - b i : ℤ) : ℚ) ^ 2)
        = (Finset.Icc (-(N : ℤ)) N).card ^ (Fintype.card (Fin (p - 1)) - 1) •
          ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (((a i - y : ℤ) : ℚ) ^ 2) := by
    intro a
    unfold cyclotomicBox
    exact Fintype.sum_piFinset_apply (fun y : ℤ => (((a i - y : ℤ) : ℚ) ^ 2)) _ i
  have houter : ∀ y : ℤ,
      ∑ a ∈ cyclotomicBox p N, (((a i - y : ℤ) : ℚ) ^ 2)
        = (Finset.Icc (-(N : ℤ)) N).card ^ (Fintype.card (Fin (p - 1)) - 1) •
          ∑ x ∈ Finset.Icc (-(N : ℤ)) N, (((x - y : ℤ) : ℚ) ^ 2) := by
    intro y
    unfold cyclotomicBox
    exact Fintype.sum_piFinset_apply (fun x : ℤ => (((x - y : ℤ) : ℚ) ^ 2)) _ i
  simp_rw [hinner, nsmul_eq_mul, ← Finset.mul_sum]
  have hT : (∑ a ∈ cyclotomicBox p N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N, (((a i - y : ℤ) : ℚ) ^ 2))
      = (((Finset.Icc (-(N : ℤ)) N).card ^ (Fintype.card (Fin (p - 1)) - 1) : ℕ) : ℚ) *
        (∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N,
          (((x - y : ℤ) : ℚ) ^ 2)) := by
    rw [Finset.sum_comm]
    simp_rw [houter, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hT]
  ring

private theorem offdiag_single_box_sum (p N : ℕ) (i j : Fin (p - 1)) (hij : i ≠ j) :
    ∑ b ∈ cyclotomicBox p N, (b i : ℚ) * (b j : ℚ) = 0 := by
  let g : Fin (p - 1) → ℤ → ℚ := fun k x => if k = i then (x : ℚ) else if k = j then (x : ℚ) else 1
  have hprod : ∀ b : Fin (p - 1) → ℤ, ∏ k, g k (b k) = (b i : ℚ) * (b j : ℚ) := by
    intro b
    have h := Fintype.prod_eq_mul (f := fun k => g k (b k)) i j hij (by
      intro k hk
      simp only [g, hk.1, hk.2, ite_false])
    have hi : g i (b i) = (b i : ℚ) := by simp [g]
    have hj : g j (b j) = (b j : ℚ) := by simp [g, hij.symm]
    rw [hi, hj] at h
    exact h
  have hsum : ∑ b ∈ cyclotomicBox p N, (b i : ℚ) * (b j : ℚ)
      = ∑ b ∈ cyclotomicBox p N, ∏ k, g k (b k) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [hprod]
  rw [hsum]
  unfold cyclotomicBox
  rw [Finset.sum_prod_piFinset]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [g] using sum_single_zero N

private theorem offdiag_box_sum (p N : ℕ) (i j : Fin (p - 1)) (hij : i ≠ j) :
    ∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      (((a i - b i : ℤ)) : ℚ) * (((a j - b j : ℤ)) : ℚ) = 0 := by
  let s := Finset.Icc (-(N : ℤ)) N
  let C : ℚ := (s.card : ℚ)
  let g : (Fin (p - 1) → ℤ) → Fin (p - 1) → ℤ → ℚ :=
    fun b k x => if k = i then (((x - b i : ℤ)) : ℚ) else if k = j then (((x - b j : ℤ)) : ℚ) else 1
  have hinner : ∀ b : Fin (p - 1) → ℤ,
      ∑ a ∈ cyclotomicBox p N, (((a i - b i : ℤ)) : ℚ) * (((a j - b j : ℤ)) : ℚ)
        = ∏ k, ∑ x ∈ s, g b k x := by
    intro b
    have hprod : ∀ a : Fin (p - 1) → ℤ, ∏ k, g b k (a k)
        = (((a i - b i : ℤ)) : ℚ) * (((a j - b j : ℤ)) : ℚ) := by
      intro a
      have h := Fintype.prod_eq_mul (f := fun k => g b k (a k)) i j hij (by
        intro k hk
        simp only [g, hk.1, hk.2, ite_false])
      have hi : g b i (a i) = (((a i - b i : ℤ)) : ℚ) := by simp [g]
      have hj : g b j (a j) = (((a j - b j : ℤ)) : ℚ) := by simp [g, hij.symm]
      rw [hi, hj] at h
      exact h
    have hsum : ∑ a ∈ cyclotomicBox p N, (((a i - b i : ℤ)) : ℚ) * (((a j - b j : ℤ)) : ℚ)
        = ∑ a ∈ cyclotomicBox p N, ∏ k, g b k (a k) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hprod]
    rw [hsum]
    unfold cyclotomicBox s
    rw [Finset.sum_prod_piFinset]
  have hsplit : ∀ b : Fin (p - 1) → ℤ,
      (∏ k, ∑ x ∈ s, g b k x)
        = (∑ x ∈ s, g b i x) * (∑ x ∈ s, g b j x) *
          ∏ k ∈ (Finset.univ.erase i).erase j, ∑ x ∈ s, g b k x := by
    intro b
    have h1 : (∏ k, ∑ x ∈ s, g b k x)
        = (∑ x ∈ s, g b i x) * ∏ k ∈ Finset.univ.erase i, ∑ x ∈ s, g b k x :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    have h2 : (∏ k ∈ Finset.univ.erase i, ∑ x ∈ s, g b k x)
        = (∑ x ∈ s, g b j x) * ∏ k ∈ (Finset.univ.erase i).erase j, ∑ x ∈ s, g b k x :=
      (Finset.mul_prod_erase _ _ hjmem).symm
    rw [h1, h2, mul_assoc]
  have hSi : ∀ b : Fin (p - 1) → ℤ, (∑ x ∈ s, g b i x) = -C * (b i : ℚ) := by
    intro b
    have hgi : ∀ x : ℤ, g b i x = (((x - b i : ℤ)) : ℚ) := fun x => by simp [g]
    simp_rw [hgi]
    exact sum_sub_const N (b i)
  have hSj : ∀ b : Fin (p - 1) → ℤ, (∑ x ∈ s, g b j x) = -C * (b j : ℚ) := by
    intro b
    have hgj : ∀ x : ℤ, g b j x = (((x - b j : ℤ)) : ℚ) := fun x => by simp [g, hij.symm]
    simp_rw [hgj]
    exact sum_sub_const N (b j)
  have hR : ∀ b : Fin (p - 1) → ℤ,
      (∏ k ∈ (Finset.univ.erase i).erase j, ∑ x ∈ s, g b k x)
        = ∏ k ∈ (Finset.univ.erase i).erase j, C := by
    intro b
    apply Finset.prod_congr rfl
    intro k hk
    have hki : k ≠ i := by
      have := Finset.mem_of_mem_erase hk
      exact (Finset.mem_erase.mp this).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hg1 : ∀ x : ℤ, g b k x = 1 := fun x => by simp [g, hki, hkj]
    simp_rw [hg1]
    exact (Finset.cast_card s).symm
  rw [Finset.sum_comm]
  simp_rw [hinner, hsplit, hSi, hSj, hR]
  have hfactor : (∑ b ∈ cyclotomicBox p N, (-C * (b i : ℚ)) * (-C * (b j : ℚ)) *
      ∏ k ∈ (Finset.univ.erase i).erase j, C)
      = (∏ k ∈ (Finset.univ.erase i).erase j, C) *
        ∑ b ∈ cyclotomicBox p N, (-C * (b i : ℚ)) * (-C * (b j : ℚ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfactor]
  have hzero : (∑ b ∈ cyclotomicBox p N, (-C * (b i : ℚ)) * (-C * (b j : ℚ))) = 0 := by
    have hrewrite : ∀ b : Fin (p - 1) → ℤ, (-C * (b i : ℚ)) * (-C * (b j : ℚ))
        = C ^ 2 * ((b i : ℚ) * (b j : ℚ)) := fun b => by ring
    simp_rw [hrewrite, ← Finset.mul_sum, offdiag_single_box_sum p N i j hij, mul_zero]
  rw [hzero, mul_zero]

/-- **Second moment of the trace distance on the cyclotomic box.** Let $p$ be a prime, let $N$ be
a natural number, and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of
unity, with fixed primitive $p$-th root of unity $\omega \in K$. Let $M_2(p, N)$ be the second
moment of the trace metric $d$ of $K$ over the box $B(p, N)$: the average of
$d(\alpha_a, \alpha_b)^2$ over all pairs $(a, b)$ of integer vectors in $\mathbb{Z}^{p-1}$ whose
coordinates lie in $[-N, N]$, where $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Then $M_2(p, N) = \frac{2}{3} (p^3 - 2 p^2 + 1) N (N + 1)$.

The asymptotic form $M_2(p, N) = \frac{2}{3} p^3 N^2 + O(p^2 N^2 + p^3 N)$ follows from this
exact formula.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 4 (`integers-2025-A10-lem-4`). -/
public theorem cyclotomicDistMoment_two {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (N : ℕ) :
    cyclotomicDistMoment p K N 2 = 2 / 3 * ((p : ℝ) ^ 3 - 2 * p ^ 2 + 1) * N * (N + 1) := by
  set Dval : ℚ := ((((Finset.Icc (-(N : ℤ)) N).card
    ^ (Fintype.card (Fin (p - 1)) - 1) : ℕ)) : ℚ) ^ 2 *
    (∑ x ∈ Finset.Icc (-(N : ℤ)) N, ∑ y ∈ Finset.Icc (-(N : ℤ)) N,
      (((x - y : ℤ) : ℚ) ^ 2)) with hDval
  have hdiag : ∀ i : Fin (p - 1),
      (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N, (((a i - b i : ℤ) : ℚ) ^ 2))
        = Dval := by
    intro i
    rw [hDval]
    exact diag_box_sum p N i
  have hT1 : (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      ∑ i, (((a i - b i : ℤ) : ℚ) ^ 2)) = ((p - 1 : ℕ) : ℚ) * Dval := by
    simp_rw [Finset.sum_comm (s := cyclotomicBox p N) (t := Finset.univ)]
    simp_rw [hdiag]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hT2 : (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2) = ((p - 1 : ℕ) : ℚ) * Dval := by
    have hexp : ∀ a b : Fin (p - 1) → ℤ, (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2
        = ∑ i, ∑ j, (((a i - b i : ℤ)) : ℚ) * (((a j - b j : ℤ)) : ℚ) := by
      intro a b
      rw [pow_two, Finset.sum_mul_sum]
    simp_rw [hexp, Finset.sum_comm (s := cyclotomicBox p N) (t := Finset.univ)]
    have hinner : ∀ i j : Fin (p - 1),
        (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
          (((a i - b i : ℤ)) : ℚ) * (((a j - b j : ℤ)) : ℚ))
          = (if i = j then Dval else 0) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl]
        simpa only [← pow_two] using hdiag i
      · rw [ite_eq_right hij]
        exact offdiag_box_sum p N i j hij
    simp_rw [hinner]
    have hsingle : ∀ i : Fin (p - 1), (∑ j, (if i = j then Dval else 0)) = Dval := by
      intro i
      rw [Finset.sum_ite_eq]
      simp
    simp_rw [hsingle]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hSsplit : (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      ((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
        - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2))
      = (p : ℚ) ^ 2 * (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
        ∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
        - (p + 1) * (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
          (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2) := by
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hS : (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      ((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
        - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2))
      = ((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ) * Dval := by
    rw [hSsplit, hT1, hT2]
    ring
  have hDval_eq : Dval = ((2 * (N : ℚ) + 1) ^ (p - 1 - 1)) ^ 2 *
      (2 * (N : ℚ) * ((N : ℚ) + 1) * (2 * (N : ℚ) + 1) ^ 2 / 3) := by
    rw [hDval, Fintype.card_fin, card_Icc_eq, sum_pair_sq]
    push_cast
    ring
  have hpow : ((2 * (N : ℚ) + 1) ^ (p - 1 - 1)) ^ 2 * (2 * (N : ℚ) + 1) ^ 2
      = ((2 * (N : ℚ) + 1) ^ (p - 1)) ^ 2 := by
    have h1 : 1 ≤ p - 1 := by have h2 := hp.two_le; omega
    have hpp : p - 1 = (p - 1 - 1) + 1 := (Nat.sub_add_cancel h1).symm
    conv_rhs => rw [hpp, pow_succ]
    ring
  have hSeq : (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      ((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
        - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2))
      = (((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ)
        * (2 * (N : ℚ) * ((N : ℚ) + 1) / 3)) * ((2 * (N : ℚ) + 1) ^ (p - 1)) ^ 2 := by
    rw [hS]
    calc ((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ) * Dval
        = ((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ)
          * (2 * (N : ℚ) * ((N : ℚ) + 1) / 3)
          * (((2 * (N : ℚ) + 1) ^ (p - 1 - 1)) ^ 2 * (2 * (N : ℚ) + 1) ^ 2) := by
          rw [hDval_eq]
          ring
      _ = (((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ)
          * (2 * (N : ℚ) * ((N : ℚ) + 1) / 3)) * ((2 * (N : ℚ) + 1) ^ (p - 1)) ^ 2 := by
          rw [hpow]
  have hterm : ∀ a b : Fin (p - 1) → ℤ,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ 2
        = ((((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
          - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2 : ℚ)) : ℝ) := by
    intro a b
    rw [dist_sq_eq, normSq_lattice_sub hp]
  have hnum : (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ 2)
      = (((∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
        ((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
          - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2) : ℚ)) : ℝ) := by
    simp_rw [hterm]
    simp_rw [← Rat.cast_sum]
  unfold cyclotomicDistMoment
  rw [hnum]
  have hcard : ((cyclotomicBox p N).card : ℝ) = (2 * (N : ℝ) + 1) ^ (p - 1) := by
    rw [card_box_eq]
    push_cast
    ring
  have hSℝ : (((∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      ((p : ℚ) ^ 2 * (∑ i, (((a i - b i : ℤ)) : ℚ) ^ 2)
        - (p + 1) * (∑ i, (((a i - b i : ℤ)) : ℚ)) ^ 2) : ℚ)) : ℝ)
      = ((((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ)
        * (2 * (N : ℚ) * ((N : ℚ) + 1) / 3) : ℚ) : ℝ)
        * (((((2 * (N : ℚ) + 1) ^ (p - 1)) ^ 2 : ℚ)) : ℝ) := by
    exact_mod_cast hSeq
  have hW : (((((2 * (N : ℚ) + 1) ^ (p - 1)) ^ 2 : ℚ)) : ℝ)
      = (((cyclotomicBox p N).card : ℕ) : ℝ) ^ 2 := by
    rw [hcard]
    push_cast
    ring
  have hpos : (0 : ℝ) < (((cyclotomicBox p N).card : ℕ)) := by
    rw [hcard]
    have hbase : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
    exact pow_pos hbase (p - 1)
  have hcard_ne : ((((cyclotomicBox p N).card : ℕ)) : ℝ) ^ 2 ≠ 0 :=
    ne_of_gt (pow_pos hpos 2)
  rw [hSℝ, hW, mul_div_cancel_right₀ _ hcard_ne]
  have hK : ((((p : ℚ) ^ 2 - (p + 1)) * ((p - 1 : ℕ) : ℚ)
      * (2 * (N : ℚ) * ((N : ℚ) + 1) / 3) : ℚ) : ℝ)
      = 2 / 3 * ((p : ℝ) ^ 3 - 2 * p ^ 2 + 1) * N * (N + 1) := by
    push_cast
    rw [Nat.cast_sub hp.one_le]
    ring
  exact hK

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.KFull
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The Dirichlet series of squareful integers weighted by the number of prime factors

We factor the series with squareful coefficients `2 ^ ω(n)` as a zeta quotient times a
Dirichlet series converging absolutely on `1 / 5 < re s`.
-/

open Complex

namespace MetaMathlibExt
namespace squareful_two_pow_omega_LSeries_eq_zeta_quotient_five

/-- Multiplicative extension of the local coefficients at prime powers. -/
private def coeff (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod fun _ k => c k

private lemma coeff_mul (c : ℕ → ℂ) {a b : ℕ} (hab : a.Coprime b) :
    coeff c (a * b) = coeff c a * coeff c b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [coeff]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [coeff]
  simp only [coeff, ite_eq_right ha, ite_eq_right hb, ite_eq_right (mul_ne_zero ha hb),
    Nat.factorization_mul_of_coprime hab]
  exact Finsupp.prod_add_index_of_disjoint hab.disjoint_primeFactors _

private lemma coeff_pow {c : ℕ → ℂ} (hc : c 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    coeff c (p ^ k) = c k := by
  simp only [coeff, ite_eq_right (pow_ne_zero k hp.ne_zero), hp.factorization_pow]
  exact Finsupp.prod_single_index hc

private lemma term_eq (c : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (coeff c) s n = coeff c n * riemannZetaSummandHom hs n :=
  LSeries.term_def₀ (by simp [coeff]) s n

private lemma term_mul (c : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) {a b : ℕ} (hab : a.Coprime b) :
    LSeries.term (coeff c) s (a * b) = LSeries.term (coeff c) s a * LSeries.term (coeff c) s b := by
  simp only [term_eq c hs, coeff_mul c hab, map_mul]
  ring

private lemma term_one (c : ℕ → ℂ) (s : ℂ) : LSeries.term (coeff c) s 1 = 1 := by
  simp [coeff]

private lemma term_pow {c : ℕ → ℂ} (hc : c 0 = 1) {s : ℂ} (hs : s ≠ 0)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.term (coeff c) s (p ^ k) = c k * ((p : ℂ) ^ (-s)) ^ k := by
  rw [term_eq c hs, coeff_pow hc hp, map_pow]
  rfl

/- A prime power with exponent at least d contributes at most
`4 * p ^ (-d * σ) * (2 ^ (-σ)) ^ (k - d)`. Summing products over all finite sets
of pairs (base, exponent) bounds the sum over the graphs of prime factorizations. -/
private lemma summable_coeff {c : ℕ → ℂ} (hc : c 0 = 1) (hbound : ∀ k, ‖c k‖ ≤ 4)
    {d : ℕ} (hgap : ∀ k, 0 < k → k < d → c k = 0) {s : ℂ}
    (hpos : 0 < s.re) (hs : 1 < s.re * d) : LSeriesSummable (coeff c) s := by
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hpos
  let r : ℝ := 2 ^ (-s.re)
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hpos)
  let A (p : ℕ) : ℝ := 4 * (p : ℝ) ^ (-s.re * d)
  let B (k : ℕ) : ℝ := r ^ (k - d)
  have hA : Summable A := (Real.summable_nat_rpow.mpr (by linarith : -s.re * d < -1)).mul_left 4
  have hB : Summable B := (summable_nat_add_iff d).mp (by
    simpa [B] using summable_geometric_of_lt_one hr hr₁)
  have hAB := hA.mul_of_nonneg hB (fun p => by dsimp [A]; positivity)
    (fun k => pow_nonneg hr (k - d))
  have hprod := summable_finsetProd_of_summable_nonneg (fun i => by
    dsimp [A, B]
    positivity) hAB
  let graph (m : ℕ) := (m + 1).factorization.graph
  have inj : Function.Injective graph := by
    intro m n h
    have he := Nat.factorization_inj (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
      (Finsupp.graph_inj.mp h)
    exact Nat.succ.inj he
  apply (summable_nat_add_iff 1).mp
  apply (hprod.comp_injective inj).of_norm_bounded
  intro m
  rw [Nat.multiplicative_factorization _ (fun _ _ => term_mul c hs₀) (term_one c s)
    (Nat.succ_ne_zero m)]
  simp only [Finsupp.prod, Complex.norm_prod, Function.comp_apply, graph, Finsupp.graph,
    Finset.prod_map]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro p hp
  let k := (m + 1).factorization p
  have hk : k ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [term_pow hc hs₀ hprime, norm_mul, norm_pow, norm_natCast_cpow_of_pos hprime.pos, neg_re]
  change ‖c k‖ * ((p : ℝ) ^ (-s.re)) ^ k ≤ A p * B k
  by_cases hd : d ≤ k
  · have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hpr : (p : ℝ) ^ (-s.re) ≤ r :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp₂ (by linarith)
    have he : ((p : ℝ) ^ (-s.re)) ^ k =
        (p : ℝ) ^ (-s.re * d) * ((p : ℝ) ^ (-s.re)) ^ (k - d) := by
      rw [Real.rpow_mul_natCast (by positivity), ← pow_add, Nat.add_sub_of_le hd]
    rw [he, ← mul_assoc]
    dsimp [A, B]
    gcongr
    exact hbound k
  · rw [hgap k (Nat.pos_of_ne_zero hk) (by omega), norm_zero, zero_mul]
    dsimp [A, B]
    positivity

private lemma euler {c : ℕ → ℂ} (hc : c 0 = 1) {s : ℂ} (hs : s ≠ 0)
    (hsum : LSeriesSummable (coeff c) s) :
    HasProd (fun p : Nat.Primes => ∑' k, c k * ((p : ℂ) ^ (-s)) ^ k)
      (LSeries (coeff c) s) :=
  (EulerProduct.eulerProduct_hasProd (term_one c s) (term_mul c hs) hsum.norm
    (LSeries.term_zero _ _)).congr_fun fun p => tsum_congr fun k => (term_pow hc hs p.2 k).symm

private def squarefulLocal (k : ℕ) : ℂ :=
  if k = 0 then 1 else if 2 ≤ k then 2 else 0

open Classical in
private lemma squareful_coeff (n : ℕ) :
    coeff squarefulLocal n = if Nat.IsKFull 2 n then
      (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff, Nat.not_isKFull_zero]
  rw [coeff, ite_eq_right hn, Nat.prod_factorization_eq_prod_primeFactors,
    ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  have hfull : Nat.IsKFull 2 n ↔ ∀ p ∈ n.primeFactors, 2 ≤ n.factorization p := by
    simp [Nat.isKFull_iff_factorization hn, Nat.mem_primeFactors, hn]
  have hne {p} (hp : p ∈ n.primeFactors) : n.factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp (show p ∈ n.factorization.support from hp)
  split_ifs with h
  · calc
      _ = ∏ _p ∈ n.primeFactors, (2 : ℂ) := Finset.prod_congr rfl fun p hp => by
        simp [squarefulLocal, (hfull.mp h) p hp, hne hp]
      _ = _ := by simp
  · rw [hfull] at h
    push Not at h
    obtain ⟨p, hp, hk⟩ := h
    exact Finset.prod_eq_zero hp (by simp [squarefulLocal, hne hp, hk.not_ge])

private lemma squareful_bound (k : ℕ) : ‖squarefulLocal k‖ ≤ 4 := by
  unfold squarefulLocal
  split_ifs <;> norm_num

/-- The tail starting at degree eight is `4 / (1 + x²)`. -/
private def tail : ℕ → ℂ
  | 0 => 4
  | 1 => 0
  | k + 2 => -tail k

private lemma tail_bound (k : ℕ) : ‖tail k‖ ≤ 4 := by
  induction k using tail.induct with
  | case1 => norm_num [tail]
  | case2 => norm_num [tail]
  | case3 k ih => simpa [tail] using ih

private def remainderLocal : ℕ → ℂ
  | 0 => 1
  | 1 | 2 | 3 | 4 => 0
  | 5 => -2
  | 6 => -3
  | 7 => 2
  | k + 8 => tail k

private lemma remainder_bound (k : ℕ) : ‖remainderLocal k‖ ≤ 4 := by
  rcases le_or_gt 8 k with hk | hk
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact tail_bound k
  · interval_cases k <;> norm_num [remainderLocal]

private lemma local_summable {c : ℕ → ℂ} (hb : ∀ k, ‖c k‖ ≤ 4) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun k : ℕ => c k * x ^ k) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left 4).of_norm_bounded
  intro k
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb k) (by positivity)

private lemma squareful_series {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' k, squarefulLocal k * x ^ k = 1 + 2 * x ^ 2 * (1 - x)⁻¹ := by
  rw [← (local_summable squareful_bound hx).sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ, squarefulLocal, pow_add, mul_comm (x ^ _ : ℂ) (x ^ 2),
    tsum_mul_left, tsum_geometric_of_norm_lt_one hx, mul_assoc]

private lemma remainder_series {x : ℂ} (hx : ‖x‖ < 1) :
    (∑' k, remainderLocal k * x ^ k) * (1 + x ^ 2) =
      (1 - 2 * x ^ 5 - 3 * x ^ 6 + 2 * x ^ 7) * (1 + x ^ 2) + 4 * x ^ 8 := by
  let T := ∑' k, tail k * x ^ k
  have hT : 4 - T * x ^ 2 = T := by
    have ht := (local_summable tail_bound hx).sum_add_tsum_nat_add 2
    simpa [Finset.sum_range_succ, tail, pow_add, ← mul_assoc, tsum_mul_right, tsum_neg,
      sub_eq_add_neg, T] using ht
  rw [← (local_summable remainder_bound hx).sum_add_tsum_nat_add 8]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, remainderLocal, pow_add,
    ← mul_assoc, tsum_mul_right]
  dsimp only [T] at hT
  linear_combination -(x ^ 8) * hT

private lemma local_identity {x : ℂ} (hx : ‖x‖ < 1) :
    (∑' k, squarefulLocal k * x ^ k) * (1 - x ^ 4)⁻¹ =
      (1 - x ^ 2)⁻¹ ^ 2 * (1 - x ^ 3)⁻¹ ^ 2 * ∑' k, remainderLocal k * x ^ k := by
  have hpow (k : ℕ) (hk : k ≠ 0) : ‖x ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx hk
  have hsub (k : ℕ) (hk : k ≠ 0) := (IsUnit.one_sub_of_norm_lt_one (hpow k hk)).ne_zero
  have hplus : 1 + x ^ 2 ≠ 0 := by
    have hneg : ‖-(x ^ 2)‖ < 1 := by simpa using hpow 2 (by decide)
    simpa using (IsUnit.one_sub_of_norm_lt_one hneg).ne_zero
  rw [squareful_series hx, (eq_div_iff hplus).mpr (remainder_series hx)]
  field_simp [(IsUnit.one_sub_of_norm_lt_one hx).ne_zero, hsub 2 (by decide), hsub 3 (by decide),
    hsub 4 (by decide), hplus]
  ring

private lemma zeta_product (k : ℕ) {s : ℂ} (hs : 1 < ((k : ℂ) * s).re) :
    HasProd (fun p : Nat.Primes => (1 - ((p : ℂ) ^ (-s)) ^ k)⁻¹) (riemannZeta (k * s)) :=
  (riemannZeta_eulerProduct_hasProd hs).congr_fun fun p => by
    rw [← Complex.cpow_nat_mul, mul_neg]

end squareful_two_pow_omega_LSeries_eq_zeta_quotient_five

open squareful_two_pow_omega_LSeries_eq_zeta_quotient_five

open Classical in
/-- **Coarse zeta factorization of the squareful $2^{\omega(n)}$ Dirichlet series.** Let
$\omega(n)$ be the number of distinct prime factors of $n$, call $n$ squareful when $n \ne 0$ and
$p^2 \mid n$ for every prime $p \mid n$ (that is, $n$ is $2$-full), and let
$F(s) = \sum_{n \text{ squareful}} 2^{\omega(n)} n^{-s}$. There is a sequence
$h : \mathbb{N} \to \mathbb{C}$ whose Dirichlet series $H(s) = \sum_{n \ge 1} h(n) n^{-s}$
converges absolutely for $\operatorname{Re} s > 1/5$, such that for every complex $s$ with
$\operatorname{Re} s > 1/2$,
$$F(s) = \frac{\zeta(2s)^2 \zeta(3s)^2}{\zeta(4s)} H(s).$$

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 2 (`integers-2024-A110-lem-2`). -/
public theorem squareful_two_pow_omega_LSeries_eq_zeta_quotient_five :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 1 / 5 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        LSeries (fun n => if Nat.IsKFull 2 n then
            (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) s =
          riemannZeta (2 * s) ^ 2 * riemannZeta (3 * s) ^ 2 / riemannZeta (4 * s) *
            LSeries h s := by
  have hrem {s : ℂ} (hs : 1 / 5 < s.re) : LSeriesSummable (coeff remainderLocal) s := by
    apply summable_coeff (d := 5) rfl remainder_bound
    · intro k hk hk'
      interval_cases k <;> rfl
    · linarith
    · norm_num
      linarith
  refine ⟨coeff remainderLocal, fun _ => hrem, ?_⟩
  intro s hs
  have hpos : 0 < s.re := by linarith
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hpos
  have hf : LSeriesSummable (coeff squarefulLocal) s := by
    apply summable_coeff (d := 2) rfl squareful_bound _ hpos
    · norm_num
      linarith
    · intro k hk hk'
      have : k = 1 := by omega
      subst k
      rfl
  have hz (k : ℕ) (hk : 2 ≤ k) : 1 < ((k : ℂ) * s).re := by
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have z₂ := (zeta_product 2 (hz 2 (by decide))).pow 2
  have z₃ := (zeta_product 3 (hz 3 (by decide))).pow 2
  have z₄ := zeta_product 4 (hz 4 (by decide))
  have left := (euler (c := squarefulLocal) rfl hs₀ hf).mul z₄
  have right := (z₂.mul z₃).mul (euler (c := remainderLocal) rfl hs₀ (hrem (by linarith)))
  have heq := left.unique (right.congr_fun (fun p => local_identity (x := (p : ℂ) ^ (-s)) (by
    rw [norm_natCast_cpow_of_pos p.2.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith))))
  simp only [Nat.cast_ofNat] at heq
  simp_rw [← squareful_coeff]
  have hn := riemannZeta_ne_zero_of_one_lt_re (hz 4 (by decide))
  simp only [Nat.cast_ofNat] at hn
  rw [div_mul_eq_mul_div, eq_div_iff hn]
  exact heq

end MetaMathlibExt

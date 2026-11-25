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

The coarse and fine zeta factorizations of the series with squareful coefficients `2 ^ ω(n)`
have remainders converging absolutely on `1 / 5 < re s` and `1 / 15 < re s`, respectively.
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

/- Split off the first `d` powers of each prime. The remaining series of absolute local
coefficients converges at `r = 2 ^ (-s.re)`, which bounds the contribution of every prime.
Summing products over finite sets of pairs bounds the sum over prime factorizations. -/
private lemma summable_coeff {c : ℕ → ℂ} (hc : c 0 = 1)
    (hlocal : ∀ {x : ℂ}, ‖x‖ < 1 → Summable fun k => c k * x ^ k)
    {d : ℕ} (hgap : ∀ k, 0 < k → k < d → c k = 0) {s : ℂ}
    (hpos : 0 < s.re) (hs : 1 < s.re * d) : LSeriesSummable (coeff c) s := by
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hpos
  let r : ℝ := 2 ^ (-s.re)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hpos)
  let A (p : ℕ) : ℝ := (p : ℝ) ^ (-s.re * d)
  let B (k : ℕ) : ℝ := ‖c k‖ * r ^ (k - d)
  have hA : Summable A := Real.summable_nat_rpow.mpr (by linarith : -s.re * d < -1)
  have hB : Summable B := by
    have hr' : ‖(r : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr₁
    have h := ((summable_nat_add_iff d).mpr (hlocal hr').norm).div_const (r ^ d)
    apply (summable_nat_add_iff d).mp
    simpa [B, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hr, pow_add, ← mul_assoc,
      hr.ne'] using h
  have hAB := hA.mul_of_nonneg hB (fun p => by dsimp [A]; positivity)
    (fun k => by dsimp [B]; positivity)
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
    rw [he, mul_left_comm, ← mul_assoc]
    dsimp [A, B]
    rw [← mul_assoc]
    gcongr
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

namespace squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen

private lemma squareful_summable {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeriesSummable (coeff squarefulLocal) s := by
  apply summable_coeff (d := 2) rfl (local_summable squareful_bound)
  · intro k hk hk'
    have : k = 1 := by omega
    subst k
    rfl
  · linarith
  · norm_num
    linarith

private lemma scaled_re_gt_one {s : ℂ} (hs : 1 / 2 < s.re) (k : ℕ) (hk : 2 ≤ k) :
    1 < ((k : ℂ) * s).re := by
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

end squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen

open squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen

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
    apply summable_coeff (d := 5) rfl (local_summable remainder_bound)
    · intro k hk hk'
      interval_cases k <;> rfl
    · linarith
    · norm_num
      linarith
  refine ⟨coeff remainderLocal, fun _ => hrem, ?_⟩
  intro s hs
  have hpos : 0 < s.re := by linarith
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hpos
  have hf := squareful_summable hs
  have hz := scaled_re_gt_one hs
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

namespace squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen

/-- Multiplying a local series by `1 - x ^ d` takes a lagged difference. -/
private def difference (d : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a n - if d ≤ n then a (n - d) else 0

/-- Dividing by `1 - x ^ d` sums the coefficients in one residue class modulo `d`. -/
private def accumulate (d : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), if d ∣ j then a (n - j) else 0

private def Generates (a : ℕ → ℤ) (x v : ℂ) : Prop :=
  HasSum (fun n => (a n : ℂ) * x ^ n) v

private lemma difference_generates {a : ℕ → ℤ} {x v : ℂ} (ha : Generates a x v) (d : ℕ) :
    Generates (difference d a) x (v * (1 - x ^ d)) := by
  let shift (n : ℕ) : ℂ := if d ≤ n then (a (n - d) : ℂ) * x ^ n else 0
  have hshift : HasSum shift (v * x ^ d) := by
    have hz : ∑ j ∈ Finset.range d, shift j = 0 := Finset.sum_eq_zero fun j hj => by
      simp [shift, (Finset.mem_range.mp hj).not_ge]
    apply (hasSum_nat_add_iff' d).mp
    simpa [hz, shift, pow_add, ← mul_assoc] using ha.mul_right (x ^ d)
  rw [mul_sub, mul_one]
  apply (ha.sub hshift).congr_fun
  intro n
  by_cases hn : d ≤ n <;> simp [difference, shift, hn, sub_mul]

private lemma accumulate_generates {a : ℕ → ℤ} {x v : ℂ} (ha : Generates a x v)
    (hx : ‖x‖ < 1) {d : ℕ} (hd : 0 < d) :
    Generates (accumulate d a) x (v * (1 - x ^ d)⁻¹) := by
  let g (j : ℕ) : ℂ := if d ∣ j then x ^ j else 0
  have hg : HasSum g (1 - x ^ d)⁻¹ := by
    apply ((mul_right_injective₀ hd.ne').hasSum_iff ?_).mp
    · have hpow : ‖x ^ d‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg x) hx hd.ne'
      simpa [g, pow_mul, Function.comp_def] using hasSum_geometric_of_norm_lt_one hpow
    · intro j hj
      have hnd : ¬ d ∣ j := fun ⟨k, hk⟩ => hj ⟨k, hk.symm⟩
      simp [g, hnd]
  rw [mul_comm v, ← hg.tsum_eq, ← ha.tsum_eq]
  apply (hasSum_sum_range_mul_of_summable_norm hg.summable.norm ha.summable.norm).congr_fun
  intro n
  simp only [accumulate, Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  by_cases hdj : d ∣ j
  · simp [g, hdj, mul_left_comm (x ^ j), ← pow_add, Nat.add_sub_of_le hjn]
  · simp [g, hdj]

private def numerator : List ℕ :=
  List.replicate 2 2 ++ List.replicate 2 3 ++ List.replicate 2 7 ++ List.replicate 4 8 ++
    List.replicate 5 12 ++ List.replicate 14 13 ++ List.replicate 5 14

private def denominator : List ℕ :=
  [4] ++ List.replicate 2 5 ++ List.replicate 3 6 ++ List.replicate 5 10 ++ List.replicate 6 11

/-- Coefficients of the local squareful factor after extracting the zeta quotient. -/
private def localCoeff : ℕ → ℤ :=
  denominator.foldr accumulate (numerator.foldr difference fun n =>
    if n = 0 then 1 else if 2 ≤ n then 2 else 0)

-- Only these first fifteen integer coefficients are needed for the convergence estimate.
set_option maxRecDepth 8192 in
private lemma initial_coefficients (n : Fin 15) :
    localCoeff n = if n.val = 0 then 1 else 0 := by
  decide +revert

private lemma fold_generates (op : ℕ → (ℕ → ℤ) → ℕ → ℤ) (f : ℕ → ℂ) {x : ℂ}
    (L : List ℕ) {a : ℕ → ℤ} {v : ℂ} (ha : Generates a x v)
    (step : ∀ d ∈ L, ∀ {b w}, Generates b x w → Generates (op d b) x (w * f d)) :
    Generates (L.foldr op a) x ((L.map f).prod * v) := by
  induction L with
  | nil => simpa using ha
  | cons d ds ih =>
    have h := step d (by simp) (ih (fun k hk => step k (by simp [hk])))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

private lemma local_generates {x : ℂ} (hx : ‖x‖ < 1) :
    Generates localCoeff x
      ((denominator.map fun d => (1 - x ^ d)⁻¹).prod *
        ((numerator.map fun d => 1 - x ^ d).prod * ∑' k, squarefulLocal k * x ^ k)) := by
  apply fold_generates accumulate
  · apply fold_generates difference
    · apply (local_summable squareful_bound hx).hasSum.congr_fun
      intro n
      by_cases h : n = 0 <;> by_cases h' : 2 ≤ n <;> simp [squarefulLocal, h, h']
    · exact fun d _ {_ _} h => difference_generates h d
  · intro d hd b w h
    have hpos : ∀ k ∈ denominator, 0 < k := by decide
    exact accumulate_generates h hx (hpos d hd)

private lemma factor_product {s : ℂ} (hs : 1 / 2 < s.re) (L : List ℕ)
    (hL : ∀ d ∈ L, 2 ≤ d) :
    HasProd (fun p : Nat.Primes => (L.map fun d => (1 - ((p : ℂ) ^ (-s)) ^ d)⁻¹).prod)
      ((L.map fun d : ℕ => riemannZeta (d * s)).prod) := by
  induction L with
  | nil => simp
  | cons d ds ih =>
    exact (zeta_product d (scaled_re_gt_one hs d (hL d (by simp)))).mul
      (ih fun k hk => hL k (by simp [hk]))

private lemma local_identity_fine {x : ℂ} (hx : ‖x‖ < 1) :
    (∑' k, squarefulLocal k * x ^ k) * (denominator.map fun d => (1 - x ^ d)⁻¹).prod =
      (numerator.map fun d => (1 - x ^ d)⁻¹).prod * ∑' k, (localCoeff k : ℂ) * x ^ k := by
  rw [(local_generates hx).tsum_eq]
  have cancel (L : List ℕ) (hL : ∀ d ∈ L, 0 < d) :
      (L.map fun d => (1 - x ^ d)⁻¹).prod * (L.map fun d => 1 - x ^ d).prod = 1 := by
    induction L with
    | nil => simp
    | cons d ds ih =>
      have hpow : ‖x ^ d‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg x) hx (hL d (by simp)).ne'
      simp only [List.map_cons, List.prod_cons, mul_mul_mul_comm,
        inv_mul_cancel₀ (IsUnit.one_sub_of_norm_lt_one hpow).ne_zero,
        ih (fun k hk => hL k (by simp [hk])), mul_one]
  have h := cancel numerator (by decide)
  linear_combination -(denominator.map fun d => (1 - x ^ d)⁻¹).prod *
    (∑' k, squarefulLocal k * x ^ k) * h

end squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen

open Classical in
/-- **Fine zeta factorization of the squareful $2^{\omega(n)}$ Dirichlet series.** Let
$\omega(n)$ be the number of distinct prime factors of $n$, call $n$ squareful when $n \ne 0$ and
$p^2 \mid n$ for every prime $p \mid n$ (that is, $n$ is $2$-full), and let
$F(s) = \sum_{n \text{ squareful}} 2^{\omega(n)} n^{-s}$. There is a sequence
$h : \mathbb{N} \to \mathbb{C}$ whose Dirichlet series $H(s) = \sum_{n \ge 1} h(n) n^{-s}$
converges absolutely for $\operatorname{Re} s > 1/15$, such that for every complex $s$ with
$\operatorname{Re} s > 1/2$,
$$F(s) = \frac{\zeta(2s)^2 \zeta(3s)^2 \zeta(7s)^2 \zeta(8s)^4 \zeta(12s)^5 \zeta(13s)^{14}
\zeta(14s)^5}{\zeta(4s) \zeta(5s)^2 \zeta(6s)^3 \zeta(10s)^5 \zeta(11s)^6} H(s).$$

Source: Kampamolla Venkatasubbareddy and Ayyadurai Sankaranarayanan, *On the
Distribution of the Restricted Sequence of Integers 2^{ω(n)}*, INTEGERS 24
(2024), Article A110, Lemma 1 (`integers-2024-A110-lem-1`). -/
public theorem squareful_two_pow_omega_LSeries_eq_zeta_quotient_fifteen :
    ∃ h : ℕ → ℂ, (∀ s : ℂ, 1 / 15 < s.re → LSeriesSummable h s) ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        LSeries (fun n => if Nat.IsKFull 2 n then
            (2 : ℂ) ^ ArithmeticFunction.cardDistinctFactors n else 0) s =
          riemannZeta (2 * s) ^ 2 * riemannZeta (3 * s) ^ 2 * riemannZeta (7 * s) ^ 2 *
              riemannZeta (8 * s) ^ 4 * riemannZeta (12 * s) ^ 5 *
              riemannZeta (13 * s) ^ 14 * riemannZeta (14 * s) ^ 5 /
            (riemannZeta (4 * s) * riemannZeta (5 * s) ^ 2 * riemannZeta (6 * s) ^ 3 *
              riemannZeta (10 * s) ^ 5 * riemannZeta (11 * s) ^ 6) * LSeries h s := by
  let c (k : ℕ) : ℂ := localCoeff k
  have hc : c 0 = 1 := by
    simpa [c] using congrArg (fun a : ℤ => (a : ℂ)) (initial_coefficients 0)
  have hrem {s : ℂ} (hs : 1 / 15 < s.re) : LSeriesSummable (coeff c) s := by
    apply summable_coeff (d := 15) hc (fun hx => (local_generates hx).summable)
    · intro k hk hk'
      simp [c, initial_coefficients ⟨k, hk'⟩, hk.ne']
    · linarith
    · norm_num
      linarith
  refine ⟨coeff c, fun _ => hrem, ?_⟩
  intro s hs
  have hpos : 0 < s.re := by linarith
  have hs₀ : s ≠ 0 := fun h => by simp [h] at hpos
  have hnum : ∀ d ∈ numerator, 2 ≤ d := by decide
  have hden : ∀ d ∈ denominator, 2 ≤ d := by decide
  have left := (euler rfl hs₀ (squareful_summable hs)).mul (factor_product hs denominator hden)
  have right := (factor_product hs numerator hnum).mul (euler hc hs₀ (hrem (by linarith)))
  have heq := left.unique (right.congr_fun fun p => local_identity_fine (x := (p : ℂ) ^ (-s)) (by
    rw [norm_natCast_cpow_of_pos p.2.pos, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)))
  have hn : (denominator.map fun d : ℕ => riemannZeta (d * s)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hz
    exact riemannZeta_ne_zero_of_one_lt_re (scaled_re_gt_one hs d (hden d hd)) he
  have hquot := (eq_div_iff hn).mpr heq
  rw [← div_mul_eq_mul_div] at hquot
  simp_rw [← squareful_coeff]
  simpa only [numerator, denominator, List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Nat.cast_ofNat] using hquot

end MetaMathlibExt

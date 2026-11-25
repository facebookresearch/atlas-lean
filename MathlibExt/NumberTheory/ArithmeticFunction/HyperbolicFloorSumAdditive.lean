/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.HyperbolicFloorSum
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Hyperbolic floor sums of additive functions

We prove the asymptotic of Karras and Bouderbala for the divisor-weighted floor sum of a
function additive over prime powers. Write `d = ⌊x / n⌋`. For small `d`, differences of
the divisor summatory function give the coefficients of the main polynomial. For large
`d`, the pointwise growth of the additive function and a harmonic sum over ordered
factorizations bound the contribution by `O(x)`.
-/

open Finset Asymptotics Filter

namespace MetaMathlibExt.hyperbolic_floor_sum_asymptotic_additive

noncomputable section

private def additive (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, g (n.factorization p)

-- Each prime power contributes at most a constant times √n, and n has O(log n) prime factors.
private theorem additive_bound {g : ℕ → ℝ}
    (hg : g =O[atTop] fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) :
    ∃ C > 0, ∀ n : ℕ, |additive g n| ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, h⟩ := bound_of_isBigO_nat_atTop hg
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * C / Real.log 2, by positivity, fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [additive]
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hcard : 2 ^ n.primeFactors.card ≤ n :=
    (n.primeFactors.pow_card_le_prod id 2 fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le).trans
        (Nat.le_of_dvd hn' (Nat.prod_primeFactors_dvd n))
  have hcard' : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hcard)
  calc
    |additive g n| ≤ ∑ p ∈ n.primeFactors, |g (n.factorization p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.primeFactors, C * (n : ℝ) ^ (1 / 2 : ℝ) := by
      apply sum_le_sum
      intro p hp
      have he : 2 ^ n.factorization p ≤ n :=
        (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _).trans
          (Nat.le_of_dvd hn' (Nat.ordProj_dvd n p))
      have ht := h (x := n.factorization p) (by positivity)
      simp only [Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)] at ht
      refine ht.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      rw [div_eq_mul_inv, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      rw [one_div]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast he) (by norm_num)
    _ = (n.primeFactors.card : ℝ) * (C * (n : ℝ) ^ (1 / 2 : ℝ)) := by simp
    _ ≤ (4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log 2) * (C * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      gcongr
      apply (le_div_iff₀ hlog).mpr
      have hl := Real.log_le_rpow_div (Nat.cast_nonneg (α := ℝ) n) (by norm_num : (0 : ℝ) < 1 / 4)
      exact hcard'.trans (by linarith)
    _ = _ := by
      rw [show (3 / 4 : ℝ) = 1 / 4 + 1 / 2 by norm_num,
        Real.rpow_add (by exact_mod_cast hn' : 0 < (n : ℝ))]
      ring

private abbrev tau (r n : ℕ) : ℝ := (Nat.finMulAntidiag r n).card

private abbrev total (r : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, tau r n

private def pairs (r N : ℕ) := (Icc 1 N).sigma (Nat.finMulAntidiag r)

private def box (r N : ℕ) := Fintype.piFinset fun _ : Fin r => Icc 1 N

private theorem pair_coords {r N : ℕ} {a : (_ : ℕ) × (Fin r → ℕ)} (ha : a ∈ pairs r N) :
    a.2 ∈ box r N ∧ ∏ i, a.2 i = a.1 := by
  obtain ⟨hn, ht⟩ := mem_sigma.mp ha
  refine ⟨Fintype.mem_piFinset.mpr fun i => mem_Icc.mpr ⟨?_, ?_⟩,
    (Nat.mem_finMulAntidiag.mp ht).1⟩
  · exact Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag ht i)
  · exact (Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.dvd_of_mem_finMulAntidiag ht i)).trans
      (mem_Icc.mp hn).2

private theorem box_sum (r N : ℕ) :
    ∑ a ∈ box r N, (∏ i, ((a i : ℕ) : ℝ))⁻¹ = (harmonic N : ℝ) ^ r := by
  simp only [box, ← Finset.prod_inv_distrib,
    Finset.sum_prod_piFinset _ (fun (_ : Fin r) (n : ℕ) => (n : ℝ)⁻¹),
    harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, prod_const,
    card_univ, Fintype.card_fin]

-- Dropping the product constraint puts all tuples in a box with reciprocal mass H(N)^r.
private theorem reciprocal_bound (r N : ℕ) :
    ∑ n ∈ Icc 1 N, tau r n * (n : ℝ)⁻¹ ≤ (harmonic N : ℝ) ^ r := by
  rw [← box_sum]
  calc
    _ = ∑ a ∈ pairs r N, (a.1 : ℝ)⁻¹ := by simp [pairs, sum_sigma, tau]
    _ ≤ _ := by
      apply sum_le_sum_of_injOn (fun a => a.2)
      · intro a ha b hb hab
        have h := (pair_coords ha).2
        change a.2 = b.2 at hab
        rw [hab, (pair_coords hb).2] at h
        cases a
        cases b
        simp_all
      · exact image_subset_iff.mpr fun a ha => (pair_coords ha).1
      · intro a ha
        simp only [← Nat.cast_prod, (pair_coords ha).2, le_refl]
      · intros
        positivity

-- Given the last k coordinates with product m, the first coordinate has at most N / m choices.
private theorem count_bound (k N : ℕ) :
    (∑ n ∈ Icc 1 N, tau (k + 1) n) ≤ (N : ℝ) * (harmonic N : ℝ) ^ k := by
  let t := (box k N).sigma fun a => Icc 1 (N / ∏ i, a i)
  have hc : (pairs (k + 1) N).card ≤ t.card := by
    apply card_le_card_of_injOn (fun a => ⟨Fin.tail a.2, a.2 0⟩)
    · intro a ha
      obtain ⟨hb, hp⟩ := pair_coords ha
      have he := Fintype.mem_piFinset.mp hb
      rw [Fin.prod_univ_succ] at hp
      refine mem_sigma.mpr ⟨Fintype.mem_piFinset.mpr (fun i => he i.succ),
        mem_Icc.mpr ⟨(mem_Icc.mp (he 0)).1, ?_⟩⟩
      apply (Nat.le_div_iff_mul_le (Finset.prod_pos fun i _ => (mem_Icc.mp (he i.succ)).1)).mpr
      exact hp.le.trans (mem_Icc.mp (mem_sigma.mp ha).1).2
    · intro a ha b hb hab
      have ht : Fin.tail a.2 = Fin.tail b.2 := congrArg Sigma.fst hab
      have hz : a.2 0 = b.2 0 := congrArg (fun z => z.2) hab
      have he : a.2 = b.2 := by rw [← Fin.cons_self_tail a.2, ht, hz, Fin.cons_self_tail]
      have hn := (pair_coords ha).2
      rw [he, (pair_coords hb).2] at hn
      cases a
      cases b
      simp_all
  calc
    _ = ((pairs (k + 1) N).card : ℝ) := by simp [pairs, tau, card_sigma]
    _ ≤ (t.card : ℝ) := by exact_mod_cast hc
    _ = ∑ a ∈ box k N, ((N / ∏ i, a i : ℕ) : ℝ) := by simp [t, card_sigma]
    _ ≤ ∑ a ∈ box k N, N * (∏ i, ((a i : ℕ) : ℝ))⁻¹ := by
      apply sum_le_sum
      intro a _
      simpa [div_eq_mul_inv] using (Nat.cast_div_le (m := N) (n := ∏ i, a i) (α := ℝ))
    _ = _ := by rw [← mul_sum, box_sum]

private theorem total_div (r : ℕ) {x : ℝ} (hx : 1 ≤ x) {d : ℕ} (hd : 0 < d) :
    total r (x / d) = ∑ n ∈ Icc 1 ⌊x⌋₊, if d ≤ ⌊x / n⌋₊ then tau r n else 0 := by
  unfold total
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext n
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hle : x / d ≤ x := div_le_self (by linarith) (by exact_mod_cast hd)
  by_cases hn : 1 ≤ n
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    simp only [mem_filter, mem_Icc, hn, true_and, Nat.le_floor_iff (by positivity : 0 ≤ x / d),
      Nat.le_floor_iff (by positivity : 0 ≤ x / n), Nat.le_floor_iff (by linarith : 0 ≤ x)]
    rw [le_div_iff₀ hd', le_div_iff₀ hn', mul_comm (d : ℝ)]
    exact ⟨fun h => ⟨((le_div_iff₀ hd').mpr h).trans hle, h⟩, And.right⟩
  · simp [mem_Icc, hn]

private abbrev block (r : ℕ) (x : ℝ) (k : ℕ) :=
  total r (x / (k + 1)) - total r (x / (k + 2))

private theorem small_sum (r K : ℕ) (f : ℕ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ k ∈ range K, f (k + 1) * block r x k =
      ∑ n ∈ Icc 1 ⌊x⌋₊, if ⌊x / n⌋₊ ≤ K then f ⌊x / n⌋₊ * tau r n else 0 := by
  have hb (k : ℕ) : block r x k =
      ∑ n ∈ Icc 1 ⌊x⌋₊, if k + 1 = ⌊x / n⌋₊ then tau r n else 0 := by
    unfold block
    simp only [← Nat.cast_add_one, show (k : ℝ) + 2 = ((k + 2 : ℕ) : ℝ) by push_cast; ring,
      total_div r hx (Nat.succ_pos _), ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    split_ifs <;> first | omega | simp_all
  simp_rw [hb, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp (mem_Icc.mp hn).2
  have hpos : 0 < ⌊x / n⌋₊ := Nat.floor_pos.mpr ((one_le_div hn').mpr hnx)
  split_ifs with h
  · rw [sum_eq_single_of_mem (⌊x / n⌋₊ - 1) (mem_range.mpr (by omega))]
    · simp [Nat.sub_add_cancel hpos]
    · intro k _ hk
      simp [show ¬ k + 1 = ⌊x / n⌋₊ by omega]
  · apply sum_eq_zero
    intro k hk
    simp [show ¬ k + 1 = ⌊x / n⌋₊ by have := mem_range.mp hk; omega]

-- Beyond this cutoff, d^(1 / 8) absorbs every logarithmic power in the main polynomial.
private abbrev cutoff (r : ℕ) (x : ℝ) := ⌊Real.log x ^ (8 * r)⌋₊

private theorem cutoff_le_weight {r n : ℕ} {x : ℝ} (hx : 1 ≤ Real.log x) (hn : cutoff r x < n) :
    Real.log x ^ r ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
  have h : Real.log x ^ (8 * r) ≤ (n : ℝ) := (Nat.lt_of_floor_lt hn).le
  have he : (Real.log x ^ (8 * r)) ^ (1 / 8 : ℝ) = Real.log x ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log x), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  exact he ▸ Real.rpow_le_rpow (pow_nonneg (by linarith) _) h (by norm_num : 0 ≤ (1 / 8 : ℝ))

private theorem large_sum {r : ℕ} {x C : ℝ} {f : ℕ → ℝ} (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (3 / 4 : ℝ)) (hx : 1 ≤ x) (hL : 1 ≤ Real.log x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, f ⌊x / n⌋₊ * tau r n) -
      ∑ k ∈ range (cutoff r x), f (k + 1) * block r x k| ≤ C * 2 ^ r * x := by
  rw [small_sum r _ f hx, ← sum_sub_distrib]
  have hL₀ : 0 < Real.log x := by linarith
  have hh := (Real.log_nonneg hx).trans (log_le_harmonic_floor x (by linarith))
  let A := C * x / Real.log x ^ r
  calc
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, A * (tau r n * (n : ℝ)⁻¹) := by
      apply sum_le_sum
      intro n hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
      split_ifs with h
      · simp only [sub_self, abs_zero]
        dsimp [A, tau]
        positivity
      · let m := ⌊x / n⌋₊
        have hm : 1 ≤ m := by omega
        have hm' : 1 ≤ (m : ℝ) := by exact_mod_cast hm
        have hw := cutoff_le_weight hL (lt_of_not_ge h)
        have hfm : |f m| * Real.log x ^ r ≤ C * (x / n) := calc
          _ ≤ (C * (m : ℝ) ^ (3 / 4 : ℝ)) * ((m : ℝ) ^ (1 / 8 : ℝ)) := by
            gcongr
            exact hf m
          _ = C * (m : ℝ) ^ (7 / 8 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add (by linarith : 0 < (m : ℝ))]
            norm_num
          _ ≤ C * (m : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hC
            simpa using Real.rpow_le_rpow_of_exponent_le hm' (by norm_num : (7 / 8 : ℝ) ≤ 1)
          _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hC
        rw [sub_zero, abs_mul, abs_of_nonneg (by positivity : 0 ≤ tau r n)]
        calc
          _ ≤ (C * (x / n) / Real.log x ^ r) * tau r n := by
            gcongr
            exact (le_div_iff₀ (pow_pos hL₀ _)).mpr hfm
          _ = _ := by dsimp [A]; ring
    _ = A * ∑ n ∈ Icc 1 ⌊x⌋₊, tau r n * (n : ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ A * ((2 * Real.log x) ^ r) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [A]; positivity)
      apply (reciprocal_bound r _).trans
      gcongr
      linarith [harmonic_floor_le_one_add_log x hx]
    _ = _ := by dsimp [A]; rw [mul_pow]; field_simp

private abbrev model (P : Polynomial ℝ) (x : ℝ) := x * P.eval (Real.log x)

private abbrev remainderBound (r : ℕ) (x : ℝ) :=
  x ^ (1 - 1 / (r : ℝ)) * Real.log x ^ (r - 2)

private theorem log_pow_bound (k : ℕ) (B : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, B * Real.log x ^ k ≤ x ^ b := by
  have h := ((isLittleO_log_rpow_rpow_atTop k hb).const_mul_left B).bound zero_lt_one
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx₀
  simp only [Real.rpow_natCast, one_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hx₀ _)] at hx
  exact (le_abs_self _).trans hx

-- The summatory hypothesis and the elementary counting bound force the degree restriction.
private theorem degree_lt {r : ℕ} (hr : 2 ≤ r) {P : Polynomial ℝ}
    (hP : (fun x => total r x - model P x) =O[atTop] remainderBound r) : P.natDegree < r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hs : (total (k + 1)) =O[atTop] fun x : ℝ => x * Real.log x ^ k := by
    apply IsBigO.of_bound (2 ^ k : ℝ)
    filter_upwards [eventually_ge_atTop 1, hL] with x hx hl
    have hh := (Real.log_nonneg hx).trans (log_le_harmonic_floor x (by linarith))
    have hn : 0 ≤ total (k + 1) x := sum_nonneg fun _ _ => Nat.cast_nonneg _
    rw [Real.norm_of_nonneg hn, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (⌊x⌋₊ : ℝ) * (harmonic ⌊x⌋₊ : ℝ) ^ k := count_bound _ _
      _ ≤ x * (2 * Real.log x) ^ k := by
        gcongr
        · exact Nat.floor_le (by linarith)
        · linarith [harmonic_floor_le_one_add_log x hx]
      _ = _ := by rw [mul_pow]; ring
  have herr : remainderBound (k + 1) =O[atTop] fun x : ℝ => x * Real.log x ^ k := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 1, hL] with x hx hl
    dsimp [remainderBound]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    apply mul_le_mul _ (pow_le_pow_right₀ hl (by omega)) (by positivity) (by linarith)
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show 1 - 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 by
      have : 0 ≤ 1 / ((k + 1 : ℕ) : ℝ) := by positivity
      linarith)
  have hm : model P =O[atTop] fun x : ℝ => x * Real.log x ^ k := by
    simpa only [sub_sub_cancel] using hs.sub (hP.trans herr)
  have he : P.eval =O[atTop] fun t : ℝ => t ^ k := by
    have hc := (isBigO_mul_iff_isBigO_div (f := fun x : ℝ => x)
      (eventually_ne_atTop 0)).mp hm
    simpa [Function.comp_def, Real.log_exp, (Real.exp_pos _).ne'] using
      hc.comp_tendsto Real.tendsto_exp_atTop
  by_contra! h
  have hp : P ≠ 0 := by rintro rfl; simp at h
  have hbad := P.isEquivalent_atTop_lead.symm.isBigO.trans he
  rw [isBigO_const_mul_left_iff (Polynomial.leadingCoeff_ne_zero.mpr hp)] at hbad
  exact (isLittleO_pow_pow_atTop_of_lt (by omega : k < P.natDegree)
    (𝕜 := ℝ)).not_isBigO ((eventually_gt_atTop (0 : ℝ)).mono
      (fun x hx => pow_ne_zero _ hx.ne') |>.frequently) hbad

private abbrev modelBlock (P : Polynomial ℝ) (x : ℝ) (k : ℕ) :=
  model P (x / (k + 1)) - model P (x / (k + 2))

-- For d up to the cutoff both block endpoints tend uniformly to infinity. The loss from
-- bounding every individual error is a power of log x, absorbed by the saving x^(1 / r).
private theorem small_error {r : ℕ} (hr : 2 ≤ r) {P : Polynomial ℝ}
    (hP : (fun x => total r x - model P x) =O[atTop] remainderBound r)
    {C : ℝ} (hC : 0 < C) {f : ℕ → ℝ} (hf : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (3 / 4 : ℝ)) :
    (fun x => (∑ k ∈ range (cutoff r x), f (k + 1) * block r x k) -
      ∑ k ∈ range (cutoff r x), f (k + 1) * modelBlock P x k) =O[atTop] fun x : ℝ => x := by
  obtain ⟨B, hB, h⟩ := hP.exists_pos
  obtain ⟨a, ha⟩ := eventually_atTop.mp h.bound
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have he : 0 ≤ 1 - 1 / (r : ℝ) := sub_nonneg.mpr ((div_le_one (by linarith)).mpr hr')
  have hcut := log_pow_bound (8 * r) (2 * max a 1) (by norm_num : (0 : ℝ) < 1)
  apply IsBigO.of_bound'
  filter_upwards [eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hcut, log_pow_bound (8 * r + 8 * r + (r - 2)) (2 * B * C) (by positivity : 0 < 1 / (r : ℝ))]
    with x hx hl hc hlog
  have hx' : 0 < x := by linarith
  rw [Real.rpow_one] at hc
  let D := Real.log x ^ (8 * r)
  have hD : 1 ≤ D := one_le_pow₀ hl
  have hK : (cutoff r x : ℝ) ≤ D := Nat.floor_le (by linarith)
  have hrem (d : ℝ) (hd : 1 ≤ d) (hdu : d ≤ D + 1) :
      |total r (x / d) - model P (x / d)| ≤ B * remainderBound r x := by
    have ham : max a 1 ≤ x / d := by
      apply (le_div_iff₀ (by linarith)).mpr
      calc
        _ ≤ max a 1 * (2 * D) := by gcongr; linarith
        _ ≤ x := by dsimp [D]; linarith
    have ht : 1 ≤ x / d := (le_max_right _ _).trans ham
    have htx : x / d ≤ x := div_le_self hx'.le hd
    have hv := ha (x / d) ((le_max_left _ _).trans ham)
    have ht₀ := Real.log_nonneg ht
    simp only [Real.norm_eq_abs, remainderBound] at hv
    have hnonneg : 0 ≤ remainderBound r (x / d) := by dsimp [remainderBound]; positivity
    rw [abs_of_nonneg hnonneg] at hv
    apply hv.trans
    dsimp [remainderBound]
    gcongr
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hx'.le, ← sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ range (cutoff r x), _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range (cutoff r x), C * D * (2 * B * remainderBound r x) := by
      apply sum_le_sum
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ (cutoff r x : ℝ) := by exact_mod_cast mem_range.mp hk
      have h1 := hrem (k + 1) (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith)
      have h2 := hrem (k + 2) (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith)
      rw [← mul_sub, abs_mul]
      apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
      · apply (hf _).trans
        apply mul_le_mul_of_nonneg_left _ hC.le
        have hp : 1 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
        calc
          _ ≤ ((k + 1 : ℕ) : ℝ) := by
            simpa using Real.rpow_le_rpow_of_exponent_le hp (by norm_num : (3 / 4 : ℝ) ≤ 1)
          _ ≤ _ := by push_cast; linarith
      · unfold block modelBlock
        rw [sub_sub_sub_comm]
        exact (abs_sub _ _).trans (by linarith)
    _ ≤ D * (C * D * (2 * B * remainderBound r x)) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      gcongr
    _ = (2 * B * C * Real.log x ^ (8 * r + 8 * r + (r - 2))) * x ^ (1 - 1 / (r : ℝ)) := by
      dsimp [D, remainderBound]
      simp only [pow_add]
      ring
    _ ≤ x ^ (1 / (r : ℝ)) * x ^ (1 - 1 / (r : ℝ)) := by gcongr
    _ = x := by rw [← Real.rpow_add hx']; simp

private abbrev scalar (P : Polynomial ℝ) (j i : ℕ) : ℝ :=
  (j.choose i : ℝ) * (-1) ^ i * P.coeff j

private abbrev kernel (i : ℕ) (d : ℝ) := Real.log d ^ i / d

private abbrev term (f : ℕ → ℝ) (i k : ℕ) :=
  f (k + 1) * (kernel i (k + 1) - kernel i (k + 2))

private theorem eval_div {r : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree < r)
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    model P (x / d) = ∑ j ∈ range r, ∑ i ∈ range (j + 1),
      x * scalar P j i * kernel i d * Real.log x ^ (j - i) := by
  unfold model
  rw [Polynomial.eval_eq_sum_range' hdeg, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Real.log_div hx.ne' hd.ne', sub_eq_add_neg, add_comm, add_pow, mul_sum, mul_sum]
  apply sum_congr rfl
  intro i _
  dsimp [scalar, kernel]
  rw [neg_eq_neg_one_mul (Real.log d), mul_pow]
  ring

private theorem model_sum {r : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree < r)
    (f : ℕ → ℝ) (K : ℕ) {x : ℝ} (hx : 0 < x) :
    ∑ k ∈ range K, f (k + 1) * modelBlock P x k =
      x * ∑ j ∈ range r, ∑ i ∈ range (j + 1),
        scalar P j i * (∑ k ∈ range K, term f i k) * Real.log x ^ (j - i) := by
  have h (k : ℕ) : f (k + 1) * modelBlock P x k =
      ∑ j ∈ range r, ∑ i ∈ range (j + 1),
        x * (scalar P j i * term f i k * Real.log x ^ (j - i)) := by
    unfold modelBlock
    simp only [eval_div hdeg hx (show 0 < (k : ℝ) + 1 by positivity),
      eval_div hdeg hx (show 0 < (k : ℝ) + 2 by positivity), ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    dsimp only [term]
    ring
  simp_rw [h]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [mul_sum, sum_mul]

private abbrev weight (k : ℕ) := ((k : ℝ) + 1) ^ (1 / 8 : ℝ)

-- Multiplying by one further eighth power still leaves sublinear growth. This supplies
-- a summable majorant for every logarithmic moment, including its scaled tails.
private theorem moment_summable {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (3 / 4 : ℝ)) (i : ℕ) :
    Summable (fun k => |term f i k| * weight k) := by
  have hF : f =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ) := by
    apply IsBigO.of_bound C
    apply Eventually.of_forall
    intro n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hf n
  have hF' : (fun n : ℕ => f n * (n : ℝ) ^ (1 / 8 : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (7 / 8 : ℝ) := by
    apply (hF.mul (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (1 / 8 : ℝ)) atTop)).congr' .rfl
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [← Real.rpow_add (by exact_mod_cast hn : 0 < (n : ℝ))]
    norm_num
  have H := summable_abs_mul_log_pow_div_sub _ (7 / 8) (by norm_num) (by norm_num) hF' i
  apply H.congr
  intro k
  simp only [Nat.cast_add_one, term, weight, kernel, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 1) _)]
  ring

private theorem tail_bound {r j : ℕ} (hj : j ≤ r) {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (3 / 4 : ℝ)) (i : ℕ) :
    (fun x : ℝ => ((∑ k ∈ range (cutoff r x), term f i k) - ∑' k, term f i k) *
      Real.log x ^ j) =O[atTop] fun _ => (1 : ℝ) := by
  have hW := moment_summable hf i
  have hs : Summable (fun k => |term f i k|) := by
    apply hW.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_rpow (by simp) (by norm_num))
  apply IsBigO.of_bound (∑' k, |term f i k| * weight k)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
  let K := cutoff r x
  have htail := (summable_abs_iff.mp hs).sum_add_tsum_nat_add K
  have habs : Summable (fun k => |term f i (k + K)|) := (summable_nat_add_iff K).mpr hs
  have hp : 0 ≤ Real.log x ^ j := pow_nonneg (by linarith) _
  change ‖((∑ k ∈ range K, term f i k) - ∑' k, term f i k) * Real.log x ^ j‖ ≤ _
  rw [← htail, sub_add_eq_sub_sub, sub_self, zero_sub, norm_mul, norm_neg,
    Real.norm_of_nonneg hp, norm_one, mul_one]
  calc
    _ ≤ (∑' k : ℕ, |term f i (k + K)|) * Real.log x ^ j :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (f := fun k => term f i (k + K)) habs) hp
    _ = ∑' k : ℕ, |term f i (k + K)| * Real.log x ^ j := (habs.tsum_mul_right _).symm
    _ ≤ _ := by
      apply Summable.tsum_le_tsum_of_inj (fun k : ℕ => k + K) (add_left_injective K)
        (fun k _ => mul_nonneg (abs_nonneg _) (by dsimp [weight]; positivity))
        _ (habs.mul_right _) hW
      intro k
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (pow_le_pow_right₀ hx hj).trans
      simpa [weight] using cutoff_le_weight hx (show cutoff r x < (k + K + 1) by dsimp [K]; omega)

private abbrev mainTerm (r : ℕ) (P : Polynomial ℝ) (f : ℕ → ℝ) (x : ℝ) :=
  x * ∑ j ∈ range r, ∑ i ∈ range (j + 1),
    scalar P j i * (∑' k, term f i k) * Real.log x ^ (j - i)

private theorem series_error {r : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree < r)
    {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (3 / 4 : ℝ)) :
    (fun x => (∑ k ∈ range (cutoff r x), f (k + 1) * modelBlock P x k) - mainTerm r P f x)
      =O[atTop] fun x : ℝ => x := by
  have H : (fun x => ∑ j ∈ range r, ∑ i ∈ range (j + 1), scalar P j i *
      (((∑ k ∈ range (cutoff r x), term f i k) - ∑' k, term f i k) * Real.log x ^ (j - i)))
      =O[atTop] fun _ => (1 : ℝ) := by
    apply IsBigO.fun_sum
    intro j hj
    apply IsBigO.fun_sum
    intro i _
    exact (tail_bound (show j - i ≤ r by have := mem_range.mp hj; omega) hf i).const_mul_left _
  apply ((isBigO_refl (fun x : ℝ => x) atTop).mul H).congr' _ (by simp)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [model_sum hdeg _ _ hx]
  unfold mainTerm
  rw [← mul_sub]
  congr 1
  simp only [← sum_sub_distrib, sub_mul, mul_sub, mul_assoc]

end

end MetaMathlibExt.hyperbolic_floor_sum_asymptotic_additive

namespace MetaMathlibExt

open hyperbolic_floor_sum_asymptotic_additive

set_option linter.unusedVariables false in
/-- **Hyperbolic floor sums of additive functions of prime exponents.** Let $r \ge 2$ and let
$\tau_r(n)$ be the number of ordered factorizations $n = n_1 \cdots n_r$ of $n$ into $r$ positive
factors. Let $P(t) = \sum_j a_j t^j$ be a real polynomial with
$\sum_{1 \le n \le x} \tau_r(n) - x P(\log x) = O(x^{1 - 1/r} (\log x)^{r-2})$ as $x \to \infty$.
Let $g$ be a real function on the natural numbers with $g(1) \ne 0$ and $g(a) = O(2^{a/2})$ as
$a \to \infty$. For $n \ge 1$ let $f(n) = \sum_{p \mid n} g(v_p(n))$, the sum over the primes $p$
dividing $n$, where $v_p(n)$ is the exponent of $p$ in $n$, and for $i \ge 0$ let
$$C_i = \sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right).$$
Then, as $x \to \infty$,
$$\sum_{1 \le n \le x} f(\lfloor x/n \rfloor) \, \tau_r(n) = x \sum_{j=0}^{r-1} \sum_{i=0}^{j}
\binom{j}{i} (-1)^i a_j C_i (\log x)^{j-i} + O(x (\log x)^{r-2} \log \log x).$$

Since $f(n)$ sums only over the primes dividing $n$, the source's convention $g(0) = 0$ is not
needed.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Proposition 1 (`integers-2026-A37-prop-1`). -/
public theorem hyperbolic_floor_sum_asymptotic_additive
    (r : ℕ) (hr : 2 ≤ r) (P : Polynomial ℝ)
    (hP : (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * P.eval (Real.log x)) =O[atTop]
        fun x : ℝ => x ^ (1 - 1 / (r : ℝ)) * Real.log x ^ (r - 2))
    (g : ℕ → ℝ) (hg1 : g 1 ≠ 0)
    (hg : (fun n : ℕ => g n) =O[atTop] fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2)) :
    (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            (∑ p ∈ (⌊x / n⌋₊).primeFactors, g ((⌊x / n⌋₊).factorization p)) *
              ((Nat.finMulAntidiag r n).card : ℝ)) -
          x * ∑ j ∈ Finset.range r, ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (-1) ^ i * P.coeff j *
              (∑' n : ℕ, (∑ p ∈ (n + 1).primeFactors, g ((n + 1).factorization p)) *
                (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))) *
              Real.log x ^ (j - i)) =O[atTop]
      fun x : ℝ => x * Real.log x ^ (r - 2) * Real.log (Real.log x) := by
  let f := additive g
  obtain ⟨C, hC, hf⟩ := additive_bound hg
  change (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, f ⌊x / n⌋₊ * tau r n) - mainTerm r P f x)
    =O[atTop] (_ : ℝ → ℝ)
  have hlarge : (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, f ⌊x / n⌋₊ * tau r n) -
      ∑ k ∈ range (cutoff r x), f (k + 1) * block r x k) =O[atTop] fun x : ℝ => x := by
    apply IsBigO.of_bound (C * 2 ^ r)
    filter_upwards [eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with x hx hl
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by linarith : 0 ≤ x)]
    exact large_sum hC.le hf hx hl
  have h := (hlarge.add (small_error hr hP hC hf)).add (series_error (degree_lt hr hP) hf)
  refine ((h.congr_left fun x => ?_).trans ?_)
  · ring
  apply IsBigO.of_bound'
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with x hx hl hll
  change 1 ≤ Real.log (Real.log x) at hll
  rw [Real.norm_of_nonneg (by linarith : 0 ≤ x), Real.norm_of_nonneg (by positivity)]
  exact (le_mul_of_one_le_right (by linarith : 0 ≤ x) (one_le_pow₀ hl)).trans
    (le_mul_of_one_le_right (by positivity) hll)

end MetaMathlibExt

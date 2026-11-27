/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Order.Compact

/-!
# Dirichlet series of the square-splitting divisor function

This module proves the Euler product and zeta factorization of the Dirichlet series of
`τ⋆`, the count of square-splitting divisors. The main result is
`MetaMathlibExt.squareSplitDivisorCount_LSeries`: for `Re s > 1` the local series at each
prime sums to `(1 + 2p⁻ˢ)/(1 - p⁻²ˢ)²`, the Dirichlet series equals the product of these
local factors and also `ζ(s)²ζ(2s)²H(s)`; for `Re s > 1/2` the series defining `H`
converges absolutely, `H` is holomorphic, and `H(1) ≠ 0`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting A-Convolution of
Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 9 (`integers-2026-A56-thm-9`).
-/

namespace MetaMathlibExt
namespace squareSplitDivisorCount_LSeries

/-- The square-splitting divisor count `τ⋆(n) = |A(n)|`. -/
private abbrev tauStar : ℕ → ℂ := fun n => ((squareSplitDivisors n).card : ℂ)

/-- Local coefficient `τ⋆(p^k) = (k % 2 + 1) * (k / 2 + 1)`, independent of `p`. -/
private abbrev locCoeff : ℕ → ℂ := fun k => (((k % 2 + 1) * (k / 2 + 1) : ℕ) : ℂ)

/-- The Euler factor remainder `H(s) = ∏_p (1 - 3p⁻²ˢ + 2p⁻³ˢ)`. -/
private noncomputable abbrev hFun : ℂ → ℂ := fun s => ∏' p : Nat.Primes,
  (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))

/-- `τ⋆(1) = 1`. -/
private theorem tauStar_one : tauStar 1 = 1 := by
  simp [tauStar, squareSplitDivisors_one]

/-- `τ⋆` is multiplicative on nonzero coprime arguments. -/
private theorem tauStar_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m.Coprime n) : tauStar (m * n) = tauStar m * tauStar n := by
  have hF : (squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ)
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ)).IsMultiplicative :=
    squareSplitConv_isMultiplicative ArithmeticFunction.isMultiplicative_zeta.natCast
      ArithmeticFunction.isMultiplicative_zeta.natCast
  have hFn : ∀ k : ℕ, k ≠ 0 →
      squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ)
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) k = tauStar k := by
    intro k hk
    rw [squareSplitConv_apply _ _ hk]
    have hmem := (squareSplitDivisors_properties.1 k hk).2.2
    have hterm : ∀ d ∈ squareSplitDivisors k,
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) d *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (k / d) = 1 := by
      intro d hd
      have hdiv := hmem d hd
      have hd0 : d ≠ 0 := fun hd0 => hk (by simpa [hd0] using hdiv)
      have hkd0 : k / d ≠ 0 :=
        fun hkd0 => hk (by rw [← Nat.mul_div_cancel' hdiv, hkd0, mul_zero])
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hd0,
        ArithmeticFunction.zeta_apply_ne hkd0]
    rw [Finset.sum_congr rfl hterm]
    simp [tauStar]
  rw [← hFn (m * n) (mul_ne_zero hm hn), ← hFn m hm, ← hFn n hn]
  exact hF.map_mul_of_coprime h

/-- Values of `τ⋆` at prime powers. -/
private theorem tauStar_prime_pow {p k : ℕ} (hp : p.Prime) :
    tauStar (p ^ k) = locCoeff k := by
  have hU : squareSplitU (p ^ k) = p ^ (k % 2) := by
    change (p ^ k).factorization.prod (fun p e => p ^ (e % 2)) = _
    rw [Nat.Prime.factorization_pow hp]
    exact Finsupp.prod_single_index (by simp)
  have hV : squareSplitV (p ^ k) = p ^ (k / 2) := by
    change (p ^ k).factorization.prod (fun p e => p ^ (e / 2)) = _
    rw [Nat.Prime.factorization_pow hp]
    exact Finsupp.prod_single_index (by simp)
  have hcard : ∀ j : ℕ, (p ^ j).divisors.card = j + 1 := by
    intro j
    rw [Nat.divisors_prime_pow hp]
    simp
  have hmain :=
    (squareSplitDivisors_properties.2.2 (p ^ k) (pow_ne_zero k hp.ne_zero)).1
  rw [hU, hV] at hmain
  simp only [hcard] at hmain
  change ((squareSplitDivisors (p ^ k)).card : ℂ) = _
  rw [hmain]

/-- The local coefficient at `0` is `1`. -/
private theorem locCoeff_zero : locCoeff 0 = 1 := by
  norm_num [locCoeff]

/-- The local coefficient at even indices. -/
private theorem locCoeff_even (m : ℕ) : locCoeff (2 * m) = (m : ℂ) + 1 := by
  have h1 : (2 * m) % 2 = 0 := by omega
  have h2 : (2 * m) / 2 = m := by omega
  have hN : ((2 * m) % 2 + 1) * ((2 * m) / 2 + 1) = m + 1 := by rw [h1, h2]; ring
  change (((((2 * m) % 2 + 1) * ((2 * m) / 2 + 1)) : ℕ) : ℂ) = _
  exact_mod_cast hN

/-- The local coefficient at odd indices. -/
private theorem locCoeff_odd (m : ℕ) : locCoeff (2 * m + 1) = 2 * ((m : ℂ) + 1) := by
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  have hN : ((2 * m + 1) % 2 + 1) * ((2 * m + 1) / 2 + 1) = 2 * (m + 1) := by
    rw [h1, h2]
  change (((((2 * m + 1) % 2 + 1) * ((2 * m + 1) / 2 + 1)) : ℕ) : ℂ) = _
  exact_mod_cast hN

/-- Linear bound on the local coefficient. -/
private theorem locCoeff_bound (k : ℕ) : ‖locCoeff k‖ ≤ 2 * ((k : ℝ) + 1) := by
  have h1 : k % 2 + 1 ≤ 2 := by omega
  have h2 : k / 2 + 1 ≤ k + 1 := by omega
  have hN := mul_le_mul h1 h2 (Nat.zero_le _) (Nat.zero_le _)
  change ‖(((((k % 2 + 1) * (k / 2 + 1)) : ℕ)) : ℂ)‖ ≤ _
  rw [Complex.norm_natCast]
  exact_mod_cast hN

/-- The differentiated geometric series `∑ (m+1) z ^ m = 1 / (1-z)^2`. -/
private theorem hasSum_locSeries {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun m : ℕ => ((m : ℂ) + 1) * z ^ m) (1 / (1 - z) ^ 2) := by
  have hne : (1 : ℂ) - z ≠ 0 := (isUnit_one_sub_of_norm_lt_one hz).ne_zero
  have hne2 : ((1 : ℂ) - z) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hval : (1 - z)⁻¹ + z / (1 - z) ^ 2 = 1 / (1 - z) ^ 2 := by
    field_simp
    ring
  have hadd := (hasSum_geometric_of_norm_lt_one hz).add
    (hasSum_coe_mul_geometric_of_norm_lt_one hz)
  rw [hval] at hadd
  exact hadd.congr_fun (fun m => by ring)

/-- Local power series with `locCoeff` coefficients converge inside the unit disc. -/
private theorem hlocal {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun k : ℕ => locCoeff k * x ^ k) := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
  have hE : Summable (fun m : ℕ => ((m : ℂ) + 1) * (x ^ 2) ^ m) :=
    (hasSum_locSeries hx2).summable
  have hO : Summable (fun m : ℕ => (2 * x) * (((m : ℂ) + 1) * (x ^ 2) ^ m)) :=
    hE.mul_left (2 * x)
  have hE' : Summable (fun m : ℕ => locCoeff (2 * m) * x ^ (2 * m)) := by
    simpa [locCoeff_even, pow_mul] using hE
  have hO' : Summable (fun m : ℕ => locCoeff (2 * m + 1) * x ^ (2 * m + 1)) :=
    (summable_congr (fun m => by rw [locCoeff_odd, pow_succ, pow_mul]; ring)).mpr hO
  refine Summable.even_add_odd (f := fun k : ℕ => locCoeff k * x ^ k) ?_ ?_
  · simpa using hE'
  · simpa using hO'

/-- Nonzero natural base to a complex power is nonzero. -/
private theorem natCast_cpow_ne_zero {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ((n : ℂ) ^ s) ≠ 0 := by
  have hpos : (0 : ℝ) < ‖((n : ℂ) ^ s)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
  exact norm_pos_iff.mp hpos

/-- The `LSeries` term at `1` is `1`. -/
private theorem term_one (s : ℂ) : LSeries.term tauStar s 1 = 1 := by
  rw [LSeries.term_of_ne_zero one_ne_zero, tauStar_one]
  simp

/-- The `LSeries` terms are multiplicative in `n`. -/
private theorem term_mul (s : ℂ) {a b : ℕ} (hab : a.Coprime b) :
    LSeries.term tauStar s (a * b) =
      LSeries.term tauStar s a * LSeries.term tauStar s b := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
    simp [hb, LSeries.term]
  rcases eq_or_ne b 0 with rfl | hb
  · have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    simp [ha1, LSeries.term]
  · have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
    rw [LSeries.term_of_ne_zero hab0, LSeries.term_of_ne_zero ha,
      LSeries.term_of_ne_zero hb, tauStar_mul ha hb hab, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    have ha' : ((a : ℂ) ^ s) ≠ 0 := natCast_cpow_ne_zero ha s
    have hb' : ((b : ℂ) ^ s) ≠ 0 := natCast_cpow_ne_zero hb s
    field_simp

/-- The `LSeries` term at a prime power in factored form. -/
private theorem term_pow {p : ℕ} (hp : p.Prime) (s : ℂ) (k : ℕ) :
    LSeries.term tauStar s (p ^ k) = locCoeff k * (((p : ℂ) ^ (-s)) ^ k) := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  rw [LSeries.term_of_ne_zero hpk, tauStar_prime_pow hp, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  rw [← Complex.cpow_nat_mul]
  congr 1
  ring

/-- The Dirichlet series of `τ⋆` converges absolutely for `Re s > 1`. -/
private theorem tauStar_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable tauStar s := by
  have hpos : 0 < s.re := by linarith
  let r : ℝ := 2 ^ (-s.re)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hpos)
  let A : ℕ → ℝ := fun p => (p : ℝ) ^ (-s.re)
  let B : ℕ → ℝ := fun k => ‖locCoeff k‖ * r ^ (k - 1)
  have hA : Summable A := Real.summable_nat_rpow.mpr (by linarith)
  have hr' : ‖(r : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr₁
  have hloc : Summable (fun k : ℕ => ‖locCoeff k * (r : ℂ) ^ k‖) := (hlocal hr').norm
  have hC : Summable (fun k : ℕ => ‖locCoeff k * (r : ℂ) ^ k‖ * (1 / r)) :=
    hloc.mul_right (1 / r)
  have hB : Summable B := by
    refine hC.of_nonneg_of_le ?_ ?_
    · intro k
      dsimp [B]
      positivity
    · intro k
      have hnorm : ‖locCoeff k * (r : ℂ) ^ k‖ = ‖locCoeff k‖ * r ^ k := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      change ‖locCoeff k‖ * r ^ (k - 1) ≤ ‖locCoeff k * (r : ℂ) ^ k‖ * (1 / r)
      rw [hnorm]
      rcases eq_or_ne k 0 with rfl | hk
      · rw [locCoeff_zero, norm_one]
        have h0 : (0 : ℕ) - 1 = 0 := rfl
        rw [h0]
        simp only [pow_zero, one_mul, mul_one]
        exact one_le_one_div hr hr₁.le
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
        have hpow : r ^ (k - 1) * r = r ^ k := by rw [← pow_succ, Nat.sub_add_cancel hk1]
        have heq : ‖locCoeff k‖ * r ^ k * (1 / r) = ‖locCoeff k‖ * r ^ (k - 1) := by
          rw [← hpow]
          field_simp
        rw [heq]
  have hAB := hA.mul_of_nonneg hB (fun p => by dsimp [A]; positivity)
    (fun k => by dsimp [B]; positivity)
  have hprod := summable_finsetProd_of_summable_nonneg (fun i => by
    dsimp [A, B]
    positivity) hAB
  let graph : ℕ → Finset (ℕ × ℕ) := fun m => (m + 1).factorization.graph
  have inj : Function.Injective graph := by
    intro m n h
    have he := Nat.factorization_inj (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
      (Finsupp.graph_inj.mp h)
    exact Nat.succ.inj he
  apply (summable_nat_add_iff 1).mp
  apply (hprod.comp_injective inj).of_norm_bounded
  intro m
  rw [Nat.multiplicative_factorization _ (fun _ _ => term_mul s) (term_one s)
    (Nat.succ_ne_zero m)]
  simp only [Finsupp.prod, Complex.norm_prod, Function.comp_apply, graph, Finsupp.graph,
    Finset.prod_map]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro p hp
  have hk : (m + 1).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [term_pow hprime s, norm_mul, norm_pow,
    Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  have hpr : (p : ℝ) ^ (-s.re) ≤ r :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp₂ (by linarith)
  have hk1 : 1 ≤ (m + 1).factorization p := Nat.pos_of_ne_zero hk
  have he : ((p : ℝ) ^ (-s.re)) ^ ((m + 1).factorization p) =
      (p : ℝ) ^ (-s.re) * ((p : ℝ) ^ (-s.re)) ^ ((m + 1).factorization p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk1]
  have hle : ((p : ℝ) ^ (-s.re)) ^ ((m + 1).factorization p - 1) ≤
      r ^ ((m + 1).factorization p - 1) :=
    pow_le_pow_left₀ (by positivity) hpr _
  dsimp [A, B]
  rw [he]
  calc ‖locCoeff ((m + 1).factorization p)‖ *
        ((p : ℝ) ^ (-s.re) * ((p : ℝ) ^ (-s.re)) ^ ((m + 1).factorization p - 1))
      = ((p : ℝ) ^ (-s.re) * ‖locCoeff ((m + 1).factorization p)‖) *
        ((p : ℝ) ^ (-s.re)) ^ ((m + 1).factorization p - 1) := by ring
    _ ≤ ((p : ℝ) ^ (-s.re) * ‖locCoeff ((m + 1).factorization p)‖) *
        r ^ ((m + 1).factorization p - 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (p : ℝ) ^ (-s.re) *
        (‖locCoeff ((m + 1).factorization p)‖ * r ^ ((m + 1).factorization p - 1)) := by
        ring

/-- The double-exponent `cpow` as a square. -/
private theorem hX2pow {p : ℕ} (s : ℂ) :
    ((p : ℂ) ^ (-(2 * s))) = (((p : ℂ) ^ (-s)) ^ 2) := by
  rw [← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

/-- The triple-exponent `cpow` as a cube. -/
private theorem hX3pow {p : ℕ} (s : ℂ) :
    ((p : ℂ) ^ (-(3 * s))) = (((p : ℂ) ^ (-s)) ^ 3) := by
  rw [← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

/-- The local Euler factor identity at each prime. -/
private theorem hasSum_local {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => tauStar (p ^ k) * ((p : ℂ) ^ (-(k * s))))
      ((1 + 2 * ((p : ℂ) ^ (-s))) / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2) := by
  have hXle : ‖((p : ℂ) ^ (-s))‖ ≤ 1 / 2 :=
    Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  have hX2 : ((p : ℂ) ^ (-(2 * s))) = (((p : ℂ) ^ (-s)) ^ 2) := hX2pow s
  have hZlt : ‖((p : ℂ) ^ (-(2 * s)))‖ < 1 := by
    rw [hX2, norm_pow]
    calc ‖((p : ℂ) ^ (-s))‖ ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hXle 2
      _ < 1 := by norm_num
  have hS := hasSum_locSeries hZlt
  have he : HasSum
      (fun m : ℕ => tauStar (p ^ (2 * m)) * ((p : ℂ) ^ (-(((2 * m : ℕ)) * s))))
      (1 / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2) := by
    apply hS.congr_fun
    intro m
    rw [tauStar_prime_pow hp, locCoeff_even]
    congr 1
    rw [← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring
  have ho : HasSum
      (fun m : ℕ => tauStar (p ^ (2 * m + 1)) * ((p : ℂ) ^ (-(((2 * m + 1 : ℕ)) * s))))
      (2 * ((p : ℂ) ^ (-s)) / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2) := by
    have hmul := hS.mul_left (2 * ((p : ℂ) ^ (-s)))
    have hval : 2 * ((p : ℂ) ^ (-s)) * (1 / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2) =
        2 * ((p : ℂ) ^ (-s)) / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2 := by
      rw [mul_one_div]
    rw [hval] at hmul
    apply hmul.congr_fun
    intro m
    rw [tauStar_prime_pow hp, locCoeff_odd]
    have hbase : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hexp : ((p : ℂ) ^ (-(((2 * m + 1 : ℕ)) * s))) =
        ((p : ℂ) ^ (-s)) * (((p : ℂ) ^ (-(2 * s))) ^ m) := by
      have e1 : (-(((2 * m + 1 : ℕ)) * s) : ℂ) = (-s) + (m : ℂ) * (-(2 * s)) := by
        push_cast
        ring
      rw [e1, Complex.cpow_add _ _ hbase, ← Complex.cpow_nat_mul]
    rw [hexp]
    ring
  have hval2 : 1 / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2 +
      2 * ((p : ℂ) ^ (-s)) / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2 =
      (1 + 2 * ((p : ℂ) ^ (-s))) / (1 - ((p : ℂ) ^ (-(2 * s)))) ^ 2 := by
    rw [← add_div]
  have h := HasSum.even_add_odd
    (f := fun k : ℕ => tauStar (p ^ k) * ((p : ℂ) ^ (-(k * s)))) he ho
  rwa [hval2] at h

/-- Absolute convergence of the `H` factor series for `Re s > 1/2`. -/
private theorem hSumm_half {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖) := by
  have h2σ : (1 : ℝ) < 2 * s.re := by linarith
  have hsum2 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * s.re))) := by
    have hN : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * s.re))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact hN.comp_injective Nat.Primes.coe_nat_injective
  have hsum3 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(3 * s.re))) := by
    have hN : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 * s.re))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact hN.comp_injective Nat.Primes.coe_nat_injective
  have hf : Summable (fun p : Nat.Primes =>
      3 * ((p : ℕ) : ℝ) ^ (-(2 * s.re)) + 2 * ((p : ℕ) : ℝ) ^ (-(3 * s.re))) :=
    (hsum2.mul_left 3).add (hsum3.mul_left 2)
  refine hf.of_nonneg_of_le (fun p => norm_nonneg _) ?_
  intro p
  have e2 : (-(2 * s) : ℂ).re = -(2 * s.re) := by simp
  have e3 : (-(3 * s) : ℂ).re = -(3 * s.re) := by simp
  have n2 : ‖((p : ℕ) : ℂ) ^ (-(2 * s))‖ = ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero p.2.ne_zero), e2]
  have n3 : ‖((p : ℕ) : ℂ) ^ (-(3 * s))‖ = ((p : ℕ) : ℝ) ^ (-(3 * s.re)) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero p.2.ne_zero), e3]
  calc ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖
      ≤ ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s))‖ + ‖2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖ :=
        norm_add_le _ _
    _ = 3 * ((p : ℕ) : ℝ) ^ (-(2 * s.re)) + 2 * ((p : ℕ) : ℝ) ^ (-(3 * s.re)) := by
        simp [n2, n3]

/-- The `LSeries` term at a prime power in `HasSum` form. -/
private theorem hterm_eq {p : Nat.Primes} (s : ℂ) (k : ℕ) :
    LSeries.term tauStar s ((p : ℕ) ^ k) =
      tauStar ((p : ℕ) ^ k) * (((p : ℕ) : ℂ) ^ (-((k : ℂ) * s))) := by
  have hpk : (p : ℕ) ^ k ≠ 0 := pow_ne_zero k p.2.ne_zero
  rw [LSeries.term_of_ne_zero hpk, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    div_eq_mul_inv, ← Complex.cpow_neg]

/-- The Dirichlet series as an Euler product of local factors. -/
private theorem hLSeries_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    LSeries tauStar s = ∏' p : Nat.Primes,
      (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 := by
  have hsum : LSeriesSummable tauStar s := tauStar_summable hs
  have heuler := EulerProduct.eulerProduct_hasProd (term_one s) (term_mul s) hsum.norm
    (LSeries.term_zero _ _)
  have hloc : ∀ p : Nat.Primes, (∑' e, LSeries.term tauStar s ((p : ℕ) ^ e)) =
      (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 := by
    intro p
    rw [tsum_congr (hterm_eq s)]
    exact (hasSum_local p.2 hs).tsum_eq
  change (∑' n, LSeries.term tauStar s n) = _
  rw [← heuler.tprod_eq]
  exact tprod_congr hloc

/-- The Euler product as `ζ(s)²ζ(2s)²H(s)`. -/
private theorem hZeta_split {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes,
      (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2) =
      riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * hFun s := by
  have h2s : 1 < (2 * s).re := by
    have e : (2 * s).re = 2 * s.re := by simp
    linarith
  have hZ1 := riemannZeta_eulerProduct_hasProd hs
  have hZ2 := riemannZeta_eulerProduct_hasProd h2s
  have m1 : Multipliable
      (fun p : Nat.Primes => (((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s))⁻¹) ^ 2) :=
    hZ1.multipliable.pow 2
  have m2 : Multipliable
      (fun p : Nat.Primes => (((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹) ^ 2) :=
    hZ2.multipliable.pow 2
  have e1 : (∏' p : Nat.Primes, (((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s))⁻¹) ^ 2) =
      riemannZeta s ^ 2 := by
    rw [hZ1.multipliable.tprod_pow 2, hZ1.tprod_eq]
  have e2 : (∏' p : Nat.Primes, (((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹) ^ 2) =
      riemannZeta (2 * s) ^ 2 := by
    rw [hZ2.multipliable.tprod_pow 2, hZ2.tprod_eq]
  have hAsumm : Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖) :=
    hSumm_half (show 1 / 2 < s.re by linarith)
  have mH : Multipliable (fun p : Nat.Primes =>
      (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))) := by
    rw [multipliable_congr (fun p => by ring :
      ∀ p : Nat.Primes, (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) +
        2 * ((p : ℕ) : ℂ) ^ (-(3 * s))) =
        1 + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))))]
    exact multipliable_one_add_of_summable hAsumm
  have e12 : (∏' p : Nat.Primes, (((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s))⁻¹) ^ 2) *
      (∏' p : Nat.Primes, (((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹) ^ 2) =
      ∏' p : Nat.Primes, ((((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s))⁻¹) ^ 2 *
        ((((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹) ^ 2)) :=
    (m1.tprod_mul m2).symm
  have e123 : riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * hFun s =
      ∏' p : Nat.Primes, ((((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s))⁻¹) ^ 2 *
        ((((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹) ^ 2) *
        (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))) := by
    rw [← e1, ← e2, e12, ← (m1.mul m2).tprod_mul mH]
  rw [e123]
  apply tprod_congr
  intro p
  have hXle : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    Complex.norm_prime_cpow_le_one_half p hs
  have h1 : (1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
    intro hcon
    have h10 : (1 : ℂ) = ((p : ℕ) : ℂ) ^ (-s) := sub_eq_zero.mp hcon
    have hXX : ((p : ℕ) : ℂ) ^ (-s) = 1 := h10.symm
    rw [hXX, norm_one] at hXle
    norm_num at hXle
  have hX2e : ((p : ℕ) : ℂ) ^ (-(2 * s)) = ((((p : ℕ) : ℂ) ^ (-s)) ^ 2) := hX2pow s
  have hX3e : ((p : ℕ) : ℂ) ^ (-(3 * s)) = ((((p : ℕ) : ℂ) ^ (-s)) ^ 3) := hX3pow s
  have h2lt : ‖((p : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
    rw [hX2e, norm_pow]
    calc ‖((p : ℕ) : ℂ) ^ (-s)‖ ^ 2 ≤ (1 / 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hXle 2
      _ < 1 := by norm_num
  have h2 : (1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s)) ≠ 0 :=
    (isUnit_one_sub_of_norm_lt_one h2lt).ne_zero
  have hid : (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) +
      2 * ((p : ℕ) : ℂ) ^ (-(3 * s))) =
      (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-s)) ^ 2 := by
    rw [hX2e, hX3e]
    ring
  have h1sq : ((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-s)) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  have h2sq : ((1 : ℂ) - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 ≠ 0 := pow_ne_zero 2 h2
  rw [hid]
  field_simp

/-- Each `H` summand is differentiable in `s`. -/
private theorem hA_diff (p : Nat.Primes) :
    Differentiable ℂ (fun s : ℂ =>
      (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))) := by
  have hbase : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hexp2 : Differentiable ℂ (fun s : ℂ => -(2 * s)) := by fun_prop
  have hexp3 : Differentiable ℂ (fun s : ℂ => -(3 * s)) := by fun_prop
  have h2 : Differentiable ℂ (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-(2 * s))) :=
    Differentiable.const_cpow hexp2 (Or.inl hbase)
  have h3 : Differentiable ℂ (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-(3 * s))) :=
    Differentiable.const_cpow hexp3 (Or.inl hbase)
  exact (h2.const_mul (-3)).add (h3.const_mul 2)

/-- Each `H` factor, in `1 + ·` form, is differentiable in `s`. -/
private theorem hFactor_diff (p : Nat.Primes) :
    Differentiable ℂ (fun s : ℂ =>
      (1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))) :=
  Differentiable.add (differentiable_const 1) (hA_diff p)

/-- `H` is holomorphic on `Re s > 1/2`. -/
private theorem hDiff : DifferentiableOn ℂ hFun {s | 1 / 2 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hHasProd : HasProdLocallyUniformlyOn
      (fun p : Nat.Primes => fun s : ℂ =>
        (1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))))
      (fun s : ℂ => ∏' p : Nat.Primes,
        ((1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))))
      {s | 1 / 2 < s.re} := by
    apply hasProdLocallyUniformlyOn_of_forall_compact hopen
    intro K hKU hK
    rcases K.eq_empty_or_nonempty with hN | hne
    · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
    · obtain ⟨s₀, hs₀K, -, hmin⟩ :=
        hK.exists_sInf_image_eq_and_le hne Complex.continuous_re.continuousOn
      have hσ : 1 / 2 < s₀.re := hKU hs₀K
      have h2σ : (1 : ℝ) < 2 * s₀.re := by linarith
      have hsum2 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * s₀.re))) := by
        have hN : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * s₀.re))) :=
          Real.summable_nat_rpow.mpr (by linarith)
        exact hN.comp_injective Nat.Primes.coe_nat_injective
      have hsum3 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(3 * s₀.re))) := by
        have hN : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 * s₀.re))) :=
          Real.summable_nat_rpow.mpr (by linarith)
        exact hN.comp_injective Nat.Primes.coe_nat_injective
      have hu : Summable (fun p : Nat.Primes =>
          3 * ((p : ℕ) : ℝ) ^ (-(2 * s₀.re)) + 2 * ((p : ℕ) : ℝ) ^ (-(3 * s₀.re))) :=
        (hsum2.mul_left 3).add (hsum3.mul_left 2)
      refine Summable.hasProdUniformlyOn_one_add hK hu ?_ ?_
      · apply Filter.Eventually.of_forall
        intro p s hsK
        have hσs : s₀.re ≤ s.re := hmin s hsK
        have e2 : (-(2 * s) : ℂ).re ≤ -(2 * s₀.re) := by
          have e : (-(2 * s) : ℂ).re = -(2 * s.re) := by simp
          rw [e]
          linarith
        have e3 : (-(3 * s) : ℂ).re ≤ -(3 * s₀.re) := by
          have e : (-(3 * s) : ℂ).re = -(3 * s.re) := by simp
          rw [e]
          linarith
        have n2 : ‖((p : ℕ) : ℂ) ^ (-(2 * s))‖ ≤ ((p : ℕ) : ℝ) ^ (-(2 * s₀.re)) := by
          rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero p.2.ne_zero)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) e2
        have n3 : ‖((p : ℕ) : ℂ) ^ (-(3 * s))‖ ≤ ((p : ℕ) : ℝ) ^ (-(3 * s₀.re)) := by
          rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero p.2.ne_zero)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) e3
        calc ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖
            ≤ ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s))‖ + ‖2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖ :=
              norm_add_le _ _
          _ = 3 * ‖((p : ℕ) : ℂ) ^ (-(2 * s))‖ + 2 * ‖((p : ℕ) : ℂ) ^ (-(3 * s))‖ := by
              simp
          _ ≤ 3 * ((p : ℕ) : ℝ) ^ (-(2 * s₀.re)) +
              2 * ((p : ℕ) : ℝ) ^ (-(3 * s₀.re)) :=
              add_le_add (mul_le_mul_of_nonneg_left n2 (by norm_num))
                (mul_le_mul_of_nonneg_left n3 (by norm_num))
      · intro p
        exact (hA_diff p).continuous.continuousOn
  have hDf : ∀ᶠ n : Finset Nat.Primes in Filter.atTop, DifferentiableOn ℂ
      (fun s : ℂ => ∏ p ∈ n,
        ((1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))))
      {s | 1 / 2 < s.re} := by
    apply Filter.Eventually.of_forall
    intro n
    simpa [Finset.prod_fn] using
      (DifferentiableOn.fun_finsetProd (fun p _ => (hFactor_diff p).differentiableOn))
  have hT := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hHasProd
  have hD := hT.differentiableOn hDf hopen
  have hEq : ∀ s : ℂ, hFun s = ∏' p : Nat.Primes,
      ((1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))) := by
    intro s
    exact tprod_congr (fun p => by ring)
  rw [show hFun = (fun s : ℂ => ∏' p : Nat.Primes,
    ((1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))))) from
    funext hEq]
  exact hD

/-- `H(1) ≠ 0`. -/
private theorem hH1 : hFun 1 ≠ 0 := by
  have hsum : Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * (1 : ℂ))) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * (1 : ℂ)))‖) :=
    hSumm_half (by rw [Complex.one_re]; norm_num)
  have hfac : ∀ p : Nat.Primes, (1 : ℂ) +
      (-3 * ((p : ℕ) : ℂ) ^ (-(2 * (1 : ℂ))) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * (1 : ℂ)))) ≠ 0 := by
    intro p
    have hq2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hq0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hq0' : ((p : ℕ) : ℝ) ≠ 0 := ne_of_gt hq0
    have e1 : (((p : ℕ) : ℂ) ^ (-(1 : ℂ))) = (((((p : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) := by
      rw [Complex.cpow_neg, Complex.cpow_one, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    have eX2 : (((p : ℕ) : ℂ) ^ (-(2 * (1 : ℂ)))) = (((((p : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) ^ 2 := by
      rw [hX2pow (1 : ℂ), e1]
    have eX3 : (((p : ℕ) : ℂ) ^ (-(3 * (1 : ℂ)))) = (((((p : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) ^ 3 := by
      rw [hX3pow (1 : ℂ), e1]
    have hEqR : (1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * (1 : ℂ))) +
        2 * ((p : ℕ) : ℂ) ^ (-(3 * (1 : ℂ)))) =
        ((((1 - 3 * ((((p : ℕ) : ℝ))⁻¹) ^ 2 + 2 * ((((p : ℕ) : ℝ))⁻¹) ^ 3 : ℝ))) : ℂ) := by
      rw [eX2, eX3]
      push_cast
      ring
    rw [hEqR]
    apply Complex.ofReal_ne_zero.mpr
    have hfactor : (1 : ℝ) - 3 * ((((p : ℕ) : ℝ))⁻¹) ^ 2 + 2 * ((((p : ℕ) : ℝ))⁻¹) ^ 3 =
        ((((p : ℕ) : ℝ) - 1) ^ 2 * (((p : ℕ) : ℝ) + 2)) / (((p : ℕ) : ℝ)) ^ 3 := by
      field_simp
      ring
    rw [hfactor]
    apply ne_of_gt
    apply div_pos _ (by positivity)
    apply mul_pos _ (by linarith)
    exact sq_pos_iff.mpr
      (sub_ne_zero.mpr (ne_of_gt (by linarith : (1 : ℝ) < ((p : ℕ) : ℝ))))
  have hne := tprod_one_add_ne_zero_of_summable hfac hsum
  have hEq : hFun 1 = ∏' p : Nat.Primes,
      ((1 : ℂ) + (-3 * ((p : ℕ) : ℂ) ^ (-(2 * (1 : ℂ))) +
        2 * ((p : ℕ) : ℂ) ^ (-(3 * (1 : ℂ))))) := by
    exact tprod_congr (fun p => by ring)
  rw [hEq]
  exact hne

/-- Main statement, assembled from the pieces above. -/
private theorem main :
    (∀ s : ℂ, 1 < s.re →
      (∀ p : Nat.Primes, HasSum (fun k : ℕ => tauStar ((p : ℕ) ^ k) * ((p : ℕ) : ℂ) ^ (-(k * s)))
        ((1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2)) ∧
      LSeries (fun n => tauStar n) s = ∏' p : Nat.Primes,
        (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 ∧
      LSeries (fun n => tauStar n) s = riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * hFun s) ∧
    (∀ s : ℂ, 1 / 2 < s.re → Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖)) ∧
    DifferentiableOn ℂ hFun {s | 1 / 2 < s.re} ∧ hFun 1 ≠ 0 := by
  refine ⟨?_, fun s hs => hSumm_half hs, hDiff, hH1⟩
  intro s hs
  have hloc : ∀ p : Nat.Primes, HasSum
      (fun k : ℕ => tauStar ((p : ℕ) ^ k) * ((p : ℕ) : ℂ) ^ (-(k * s)))
      ((1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2) := by
    intro p
    exact hasSum_local p.2 hs
  have heuler := hLSeries_eq_tprod hs
  have hzeta : LSeries tauStar s = riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * hFun s := by
    rw [heuler]
    exact hZeta_split hs
  exact ⟨hloc, heuler, hzeta⟩

end squareSplitDivisorCount_LSeries

open squareSplitDivisorCount_LSeries

/-- **Dirichlet series of the square-splitting divisor function.** Let $\tau^\star(n) = |A(n)|$ be
the number of elements of the square-splitting divisor set $A(n)$, and let
$H(s) = \prod_p (1 - 3p^{-2s} + 2p^{-3s})$, where $p$ runs over the primes. For every complex
number $s$ with $\operatorname{Re} s > 1$, the series $\sum_{k \ge 0} \tau^\star(p^k) p^{-ks}$
converges to $(1 + 2p^{-s})/(1 - p^{-2s})^2$ for each prime $p$, and the Dirichlet series
$\sum_{n \ge 1} \tau^\star(n) n^{-s}$ equals both $\prod_p (1 + 2p^{-s})/(1 - p^{-2s})^2$ and
$\zeta(s)^2 \zeta(2s)^2 H(s)$. Moreover, for every $s$ with $\operatorname{Re} s > 1/2$ the series
$\sum_p |-3p^{-2s} + 2p^{-3s}|$ converges (so the product defining $H(s)$ converges absolutely),
$H$ is holomorphic on the half-plane $\operatorname{Re} s > 1/2$, and $H(1) \ne 0$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 9
(`integers-2026-A56-thm-9`). -/
public theorem squareSplitDivisorCount_LSeries :
    let τ : ℕ → ℂ := fun n => ((squareSplitDivisors n).card : ℂ)
    let H : ℂ → ℂ := fun s => ∏' p : Nat.Primes,
      (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))
    (∀ s : ℂ, 1 < s.re →
      (∀ p : Nat.Primes, HasSum (fun k : ℕ => τ ((p : ℕ) ^ k) * ((p : ℕ) : ℂ) ^ (-(k * s)))
        ((1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2)) ∧
      LSeries (fun n => τ n) s = ∏' p : Nat.Primes,
        (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 ∧
      LSeries (fun n => τ n) s = riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * H s) ∧
    (∀ s : ℂ, 1 / 2 < s.re → Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖)) ∧
    DifferentiableOn ℂ H {s | 1 / 2 < s.re} ∧ H 1 ≠ 0 := by
  exact main

end MetaMathlibExt

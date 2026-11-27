/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPsiFChi
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Congruences for generalized cubic partitions modulo primes

The congruence for $p \equiv 5, 7 \pmod{8}$ follows by reducing the generating function to
$\psi(q) f_2^3 / f_{2p}$ modulo $p$. In the numerator, the exponents from Ramanujan's $\psi$
and Jacobi's cube give a quadratic form whose only zero modulo $p$ is the trivial one.

The Lean helpers `Represents` and `Represents.mul`, the coefficient cases in `represents_euler`,
and the Euler expansion, uniqueness, and nonvanishing proofs are adapted from
`OddDistinctsPentagonalRecurrence` in this directory.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

local notation "𝔣" => qEulerProduct

@[expose] public section

/-- **Generating function of generalized cubic partitions.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler products. For a natural number $c$, this is
the integer power series $1/(f_1 f_2^{c-1})$ in $q$, the inverse of $f_1 f_2^{c-1}$ (whose
constant term is $1$). For $c \ge 1$ its coefficient of $q^n$ is the number of partitions of
$n$ whose even parts may each come in $c$ colors. For $c = 0$ the exponent $c - 1$ is
truncated to $0$, so the series is then the inverse of $f_1$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionSeries (c : ℕ) : ℤ⟦X⟧ :=
  invOfUnit (𝔣 1 * 𝔣 2 ^ (c - 1)) 1

/-- **Generalized cubic partition numbers.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ be the
Euler products. For natural numbers $c$ and $n$, $a_c(n)$ is the integer coefficient of $q^n$
in the generating function of generalized cubic partitions, the power series
$1/(f_1 f_2^{c-1})$. For $c \ge 1$ it is the number of partitions of $n$ whose even parts may
each come in $c$ colors; $c = 1$ gives the partition numbers and $c = 2$ Chan's cubic
partition numbers. For $c = 0$ the exponent $c - 1$ is truncated to $0$, so $a_0(n)$ is also
the number of partitions of $n$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public noncomputable def generalizedCubicPartitionCount (c n : ℕ) : ℤ :=
  coeff n (generalizedCubicPartitionSeries c)

/-- **Generating function identity for generalized cubic partition numbers.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$ be the Euler products and $a_c(n)$ the generalized cubic
partition numbers. For every natural number $c$,
$f_1 f_2^{c-1} \sum_{n \ge 0} a_c(n) q^n = 1$ as integer power series in $q$, where for
$c = 0$ the exponent $c - 1$ is truncated to $0$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_generatingFunction (c : ℕ) :
    𝔣 1 * 𝔣 2 ^ (c - 1) * PowerSeries.mk (generalizedCubicPartitionCount c) = 1 := by
  have hmk : PowerSeries.mk (generalizedCubicPartitionCount c) =
      generalizedCubicPartitionSeries c := by
    ext n
    simp [generalizedCubicPartitionCount]
  have hc : constantCoeff (𝔣 1 * 𝔣 2 ^ (c - 1)) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2)]
  rw [hmk, generalizedCubicPartitionSeries, mul_invOfUnit _ _ hc]

/-- **Generalized cubic partitions of zero.** For every natural number $c$, the generalized
cubic partition number $a_c(0)$ equals $1$.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Section 1. -/
public theorem generalizedCubicPartitionCount_zero (c : ℕ) :
    generalizedCubicPartitionCount c 0 = 1 := by
  have h := congrArg (coeff 0) (generalizedCubicPartitionCount_generatingFunction c)
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 2),
    one_pow, one_mul, map_one] at h
  simpa using h

end

namespace generalizedCubicPartition

private lemma euler_eq_expand (k : ℕ) (hk : k ≠ 0) :
    𝔣 k = expand k hk (𝔣 1) := by
  have hcont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have h := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) hcont
  rw [qEulerProduct_one]
  simpa [qEulerProduct, Function.comp_def, pow_mul] using h.tprod_eq

private abbrev triangular (u : ℕ) : ℕ := (u + 1).choose 2

local notation "T" => triangular

/-- The index of the triangular number in the `a`th summand of `f(q, q³)`. -/
private def triangleIndex (a : ℤ) : ℕ := (if a ≤ 0 then -(2 * a) else 2 * a - 1).toNat

private lemma cast_triangleIndex (a : ℤ) :
    (triangleIndex a : ℤ) = if a ≤ 0 then -(2 * a) else 2 * a - 1 :=
  Int.toNat_of_nonneg (by split_ifs <;> omega)

private lemma triangleIndex_injective : Function.Injective triangleIndex := by
  intro a b h
  have hc := congrArg (fun u : ℕ => (u : ℤ)) h
  simp only [cast_triangleIndex] at hc
  split_ifs at hc <;> omega

private lemma triangle_strictMono : StrictMono T := by
  apply strictMono_nat_of_lt_succ
  intro u
  change (u + 1).choose 2 < (u + 1 + 1).choose (1 + 1)
  rw [Nat.choose_succ_succ' (u + 1) 1, Nat.choose_one_right]
  change (u + 1).choose 2 < (u + 1) + (u + 1).choose 2
  omega

private lemma twice_rising (a : ℤ) :
    2 * ((a * (a + 1) / 2).toNat : ℤ) = a * (a + 1) := by
  have h : 0 ≤ a * (a + 1) := by
    rcases le_or_gt 0 a with ha | ha
    · exact mul_nonneg ha (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg h (by decide)), mul_comm]
  exact Int.ediv_mul_cancel (Int.even_mul_succ_self a).two_dvd

private lemma thetaTerm_eq (q : ℂ) (a : ℤ) :
    ramanujanThetaTerm q (q ^ 3) a = q ^ (T (triangleIndex a)) := by
  rw [ramanujanThetaTerm, ← pow_mul, ← pow_add]
  congr 1
  apply Nat.cast_injective (R := ℤ)
  push_cast
  have ht := congrArg (fun u : ℕ => (u : ℤ)) (two_mul_choose_two_succ (triangleIndex a))
  push_cast at ht
  rw [cast_triangleIndex] at ht
  have hm := twice_rising (-a)
  rw [show -a * (-a + 1) = a * (a - 1) by ring] at hm
  split_ifs at ht <;> nlinarith [twice_rising a]

/-- The integer power series for Ramanujan's `ψ`, grouped by exponent. -/
private noncomputable def psiSeries : ℤ⟦X⟧ := by
  classical
  exact PowerSeries.mk fun j => if j ∈ Set.range (T ∘ triangleIndex) then 1 else 0

section Transfer

open UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam 1

/-- An integer power series representing a complex function on the punctured disk. -/
private def Represents (F : ℤ⟦X⟧) (f : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ (F.coeff n : ℂ) * 𝕢 τ ^ n) (f (𝕢 τ))

private lemma Represents.mul {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) :
    Represents (F * G) (fun q ↦ f q * g q) := by
  intro τ
  let ι := Int.castRingHom ℂ
  simpa [← map_mul, coeff_map, ι] using
    ModularCurve.hasSum_qParam_mul 1 one_pos (map ι F) (map ι G)
      (fun z ↦ f (𝕢 z)) (fun z ↦ g (𝕢 z))
      (by simpa [coeff_map, ι, Represents] using hf)
      (by simpa [coeff_map, ι, Represents] using hg) τ

private lemma Represents.eq_of_eval {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g)
    (heq : ∀ q : ℂ, ‖q‖ < 1 → f q = g q) : F = G := by
  have hzero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
    simp [cuspFunction, Pi.zero_comp, Periodic.cuspFunction_zero]
  have han : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := hzero ▸ analyticAt_const
  let c (m : ℕ) : ℂ := (F.coeff m : ℂ) - G.coeff m
  have hh := hasFPowerSeriesOnBall_cuspFunction (c := c) one_pos han (fun τ ↦ by
    have he := heq _ (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    simpa [c, smul_eq_mul, sub_mul, he] using (hf τ).sub (hg τ))
  rw [hzero] at hh
  have hz := hh.hasFPowerSeriesAt.eq_zero_of_eventually (Filter.EventuallyEq.refl _ _)
  apply PowerSeries.ext
  intro n
  have hc := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp
    (congrFun hz n)
  simpa [c, sub_eq_zero] using hc

private lemma represents_euler (k : ℕ) (hk : k ≠ 0) :
    Represents (𝔣 k) (fun q ↦ eulerFunction (q ^ k)) := by
  rw [euler_eq_expand k hk, qEulerProduct_one]
  intro τ
  have hq : ‖𝕢 τ ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (Periodic.norm_qParam_lt_one one_pos τ.im_pos) hk
  have hinj : Function.Injective (k * ·) := mul_right_injective₀ hk
  apply (hinj.hasSum_iff ?_).mp
  · refine (hasSum_eulerFunction_pentagonalSeries hq).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, coeff_expand_mul, pow_mul]
    congr 1
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  · intro n hn
    have hd : ¬ k ∣ n := by simpa [dvd_def, eq_comm] using hn
    simp [coeff_expand_of_not_dvd _ _ _ hd]

private lemma represents_psi : Represents psiSeries (fun q ↦ ramanujanThetaRaw q (q ^ 3)) := by
  intro τ
  have hq := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hθ := (ramanujanTheta_summable (𝕢 τ) (𝕢 τ ^ 3) (by
    rw [← pow_succ', norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide))).of_norm.hasSum
  apply ((triangle_strictMono.injective.comp triangleIndex_injective).hasSum_iff ?_).mp
  · refine hθ.congr_fun fun a ↦ ?_
    simp [psiSeries, thetaTerm_eq]
  · intro j hj
    simp [psiSeries, hj]

private lemma diagonal_eq_euler {q : ℂ} (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInfRaw q q = eulerFunction q := by
  rw [eulerFunction_eq_tprod hq]
  simp only [QPochhammer.qPochhammerInfRaw, pow_succ']

private lemma euler_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : eulerFunction q ≠ 0 := by
  rw [eulerFunction_eq_tprod hq]
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n he
    have he' : q ^ (n + 1) = 1 := by linear_combination -he
    have hn := pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
    rwa [← norm_pow, he', norm_one, lt_self_iff_false] at hn
  · simpa [pow_succ, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right ‖q‖

private lemma psi_mul_euler : psiSeries * 𝔣 1 = 𝔣 2 ^ 2 := by
  have h₁ := represents_euler 1 one_ne_zero
  have h₂ := represents_euler 2 two_ne_zero
  rw [pow_two]
  refine (represents_psi.mul h₁).eq_of_eval (h₂.mul h₂) fun q hq ↦ ?_
  have hq₂ : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have h := (ramanujan_psi_f_chi_eq_qPochhammer q hq).1
  rw [diagonal_eq_euler hq, diagonal_eq_euler hq₂, eq_div_iff (euler_ne_zero hq)] at h
  simpa [sq] using h

end Transfer

/-- The numerator after reduction modulo `p`, in a form exposing its two triangular exponents. -/
private noncomputable def numerator : ℤ⟦X⟧ :=
  psiSeries * expand 2 two_ne_zero jacobiCubeSeries

private lemma euler_mul_numerator : 𝔣 1 * numerator = 𝔣 2 ^ 5 := by
  have hJ : expand 2 two_ne_zero jacobiCubeSeries = 𝔣 2 ^ 3 := by
    rw [← pentagonalSeries_pow_three, map_pow, ← qEulerProduct_one, ← euler_eq_expand]
  calc 𝔣 1 * numerator = (psiSeries * 𝔣 1) * 𝔣 2 ^ 3 := by rw [numerator, hJ]; ring
    _ = 𝔣 2 ^ 5 := by rw [psi_mul_euler]; ring

private lemma not_isSquare_neg_two {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) : ¬ IsSquare (-2 : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  have h : legendreSym p (-2) = -1 := by
    rw [legendreSym.at_neg_two hp2, ZMod.χ₈'_nat_eq_if_mod_eight]
    have ho : p % 2 ≠ 0 := by omega
    rcases hp8 with hp8 | hp8 <;> simp [ho, hp8]
  simpa using ((legendreSym.eq_neg_one_iff (p := p)).mp h)

private lemma right_eq_zero_of_sq_add_two_sq {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) {a b : ZMod p} (h : a ^ 2 + 2 * b ^ 2 = 0) : b = 0 := by
  by_contra hb
  apply not_isSquare_neg_two hp8
  refine ⟨a / b, ?_⟩
  field_simp
  linear_combination -h

private lemma twice_odd_sq (u v : ℕ) :
    8 * (T u + 2 * T v) + 3 = (2 * u + 1) ^ 2 + 2 * (2 * v + 1) ^ 2 := by
  nlinarith only [two_mul_choose_two_succ u, two_mul_choose_two_succ v]

private lemma coeff_numerator_cast_eq_zero {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) {j : ℕ} (hj : p ∣ 8 * j + 3) :
    ((coeff j numerator : ℤ) : ZMod p) = 0 := by
  classical
  rw [numerator, coeff_mul, Int.cast_sum]
  refine Finset.sum_eq_zero fun ⟨a, b⟩ hab ↦ ?_
  have hab : a + b = j := Finset.mem_antidiagonal.mp hab
  rw [Int.cast_mul, psiSeries, coeff_mk, coeff_expand]
  split_ifs with ha hb
  · obtain ⟨u, rfl⟩ := ha
    by_cases hv : ∃ v : ℕ, T v = b / 2
    · obtain ⟨v, hv⟩ := hv
      have hb' : b = 2 * T v := by rw [hv, Nat.mul_div_cancel' hb]
      have hj' : j = T (triangleIndex u) + 2 * T v := by
        simpa [hb', Function.comp_def] using hab.symm
      rw [← hv, coeff_jacobiCubeSeries_triangle, Int.cast_mul]
      have h := (ZMod.natCast_eq_zero_iff _ p).2 hj
      rw [hj', twice_odd_sq] at h
      push_cast at h
      have hv₀ := right_eq_zero_of_sq_add_two_sq hp8 h
      simp [hv₀]
    · rw [coeff_jacobiCubeSeries_eq_zero (not_exists.mp hv), Int.cast_zero, mul_zero]
  · simp
  · simp
  · simp

private lemma euler_pow_reduction {p : ℕ} (hp : p.Prime) :
    map (Int.castRingHom (ZMod p)) (𝔣 2 ^ p) = map (Int.castRingHom (ZMod p)) (𝔣 (2 * p)) := by
  ext j
  rw [coeff_map, coeff_map, Int.coe_castRingHom, ZMod.intCast_eq_intCast_iff]
  simpa using qEulerProduct_iterated_primePower_congruence p 1 2 1 1 hp (by decide)
    (by decide) (by decide) (by decide) j

/-- The reciprocal of `f_{2p}`, obtained by the substitution `X ↦ X^{2p}` in the reciprocal of
`f₁`. In particular, it has no coefficients outside multiples of `2p`. -/
private noncomputable def expandedInverse (k : ℕ) (hk : k ≠ 0) : ℤ⟦X⟧ :=
  expand k hk (invOfUnit (𝔣 1) 1)

private lemma euler_mul_expandedInverse (k : ℕ) (hk : k ≠ 0) :
    𝔣 k * expandedInverse k hk = 1 := by
  rw [euler_eq_expand k hk, expandedInverse, ← map_mul, mul_invOfUnit, map_one]
  simpa using constantCoeff_qEulerProduct (k := 1) le_rfl

private lemma series_reduction {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    map (Int.castRingHom (ZMod p)) (generalizedCubicPartitionSeries (p - 4)) =
      map (Int.castRingHom (ZMod p)) (numerator * expandedInverse (2 * p)
        (Nat.mul_ne_zero two_ne_zero hp.ne_zero)) := by
  let ι := Int.castRingHom (ZMod p)
  let A := 𝔣 1 * 𝔣 2 ^ (p - 4 - 1)
  let S := generalizedCubicPartitionSeries (p - 4)
  let I := expandedInverse (2 * p) (Nat.mul_ne_zero two_ne_zero hp.ne_zero)
  have hAS : S * A = 1 := by
    rw [mul_comm, show S = invOfUnit A 1 by rfl, mul_invOfUnit]
    simp [A, constantCoeff_qEulerProduct le_rfl, constantCoeff_qEulerProduct (by decide : 1 ≤ 2)]
  have hAF : A * numerator = 𝔣 2 ^ p := by
    calc A * numerator = (𝔣 1 * numerator) * 𝔣 2 ^ (p - 4 - 1) := by dsimp [A]; ring
      _ = 𝔣 2 ^ p := by rw [euler_mul_numerator, ← pow_add, show 5 + (p - 4 - 1) = p by omega]
  change map ι S = map ι (numerator * I)
  calc map ι S = map ι (S * (𝔣 (2 * p) * I)) := by
        rw [show 𝔣 (2 * p) * I = 1 from euler_mul_expandedInverse _ _, mul_one]
    _ = map ι (S * (A * numerator) * I) := by
        simp only [map_mul, hAF, euler_pow_reduction hp, mul_assoc, ι]
    _ = map ι (numerator * I) := by rw [← mul_assoc S A, hAS, one_mul]

private lemma coeff_mul_expandedInverse_cast_eq_zero {p : ℕ} [Fact p.Prime]
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) {m : ℕ} (hm : p ∣ 8 * m + 3) (hk : 2 * p ≠ 0) :
    ((coeff m (numerator * expandedInverse (2 * p) hk) : ℤ) : ZMod p) = 0 := by
  rw [coeff_mul, Int.cast_sum]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  have hij : i + j = m := Finset.mem_antidiagonal.mp hij
  rw [Int.cast_mul, expandedInverse]
  by_cases hd : 2 * p ∣ j
  · have hpj : p ∣ j := (dvd_mul_left p 2).trans hd
    have hsplit : 8 * m + 3 = (8 * i + 3) + 8 * j := by rw [← hij]; ring
    rw [hsplit] at hm
    have hi : p ∣ 8 * i + 3 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right hpj 8)).mpr hm
    rw [coeff_numerator_cast_eq_zero hp8 hi, zero_mul]
  · rw [coeff_expand_of_not_dvd _ _ _ hd, Int.cast_zero, mul_zero]

end generalizedCubicPartition

open generalizedCubicPartition in
/-- **Generalized cubic partition congruences for primes $p \equiv 5, 7 \pmod 8$.** Let $a_c(n)$
be the generalized cubic partition numbers, let $p$ be a prime with $p \equiv 5$ or
$p \equiv 7 \pmod 8$, and let $l$ be a natural number with $p \mid 8l + 3$. Then
$a_{p-4}(pn + l) \equiv 0 \pmod p$ for every natural number $n$.

The source assumes $0 \le l \le p - 1$; the statement for a larger $l$ follows from the one for
$l \bmod p$, which satisfies the same divisibility.

Source: Russelle Guadalupe, *A Note on Congruences for Generalized Cubic Partitions Modulo
Primes*, INTEGERS 25 (2025), Article A20, Theorem 2, Equation (9). -/
public theorem generalizedCubicPartitionCount_prime_five_seven_mod_eight {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 5 ∨ p % 8 = 7) {l : ℕ} (hdvd : p ∣ 8 * l + 3) (n : ℕ) :
    (p : ℤ) ∣ generalizedCubicPartitionCount (p - 4) (p * n + l) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by omega
  have hm : p ∣ 8 * (p * n + l) + 3 := by
    rw [show 8 * (p * n + l) + 3 = p * (8 * n) + (8 * l + 3) by ring]
    exact dvd_add (dvd_mul_right p _) hdvd
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have h := congrArg (coeff (p * n + l)) (series_reduction hp hp5)
  simp only [coeff_map, Int.coe_castRingHom] at h
  rw [generalizedCubicPartitionCount, h]
  exact coeff_mul_expandedInverse_cast_eq_zero hp8 hm _

end MetaMathlibExt

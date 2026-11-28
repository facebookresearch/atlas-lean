/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TruncatedLogDiscriminant
import MathlibExt.Analysis.Complex.EnestromKakeya
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Discriminants of truncated logarithmic polynomials at prime multiples

For a natural number $m$ and a prime $q>m$ with $mq \equiv 1 \pmod 4$, if $q$ divides neither
numerator of $X(m)$ and $H_m$, then the discriminant of
$F_{mq}(x)=1+x+x^2/2+\cdots+x^{mq}/(mq)$ is not a square in $\mathbb{Q}$. Here $X(m)$ is the
product over the nontrivial $m$-th roots of unity in Section 4, and $H_m$ is the $m$-th harmonic
number. The congruence forces $m\ge 1$, and $q>m$ ensures that the factorial clearing the
denominators is a $q$-adic unit. The exceptional set uses the union of the primes dividing the two
numerators, as in the proof of Theorem 5 and Table 1, rather than the intersection suggested by the
display in Section 4.

For fixed $m\ge 1$, there are only finitely many primes $q$ with $mq\equiv 1 \pmod 4$ for which
$\operatorname{disc}(F_{mq})$ is a square in $\mathbb{Q}$.

## References

* John Cullinan and Rylan Gajek-Leonard, *On the Discriminants of Truncated Logarithmic
  Polynomials*, INTEGERS 25 (2025), Article A39, pp. 1–12, Theorem 3, Section 4 and Theorem 5.
* `MathlibExt.NumberTheory.TruncatedLogDiscriminant`,
  `MetaMathlibExt.not_isSquare_discr_truncatedLog_mul_prime_of_resultant_ne_zero`, for the
  resultant reduction and the nonsquare obstruction.
* `MathlibExt.Analysis.Complex.EnestromKakeya`, `enestrom_kakeya_zero_localization`, for the
  zero bound used in the proof of finiteness.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Auxiliary product for truncated logarithmic discriminants.** For a natural number $m$, let
$f_m(x) = \sum_{k=0}^{m-1} x^k$ and $g_m(x) = c_m + \sum_{j=1}^{m-1} \frac{x^j}{j}$ in
$\mathbb{Q}[x]$, where $c_m = \frac{1}{m}$ for $m \ge 1$ and $c_0 = 0$. The rational number $X(m)$
is the resultant $\operatorname{Res}(f_m, g_m)$. For $m \ge 1$, since $f_m$ is monic with roots
$\omega^k$ for $1 \le k \le m-1$, where $\omega$ is a primitive $m$-th root of unity, this is
$X(m) = \prod_{k=1}^{m-1} g_m(\omega^k)$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public noncomputable def truncatedLogAuxProduct (m : ℕ) : ℚ :=
  resultant (∑ k ∈ Finset.range m, (X : ℚ[X]) ^ k)
    (C ((m : ℚ)⁻¹) + ∑ j ∈ Finset.Icc 1 (m - 1), C ((j : ℚ)⁻¹) * X ^ j)

/-- **Auxiliary product at $m = 1$.** The auxiliary product $X(m)$ takes the value $X(1) = 1$ at
$m = 1$; it is an empty product.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public theorem truncatedLogAuxProduct_one : truncatedLogAuxProduct 1 = 1 := by
  simp [truncatedLogAuxProduct]

/-- **Exceptional primes for truncated logarithmic discriminants.** For a natural number $m$, the
exceptional set $E_m$ is the set of primes $\ell$ with $m\ell \equiv 1 \pmod 4$ such that the
$\ell$-adic valuation of the auxiliary product $X(m)$ is positive or the $\ell$-adic valuation of
the harmonic number $Y(m) = H_m = 1 + \frac{1}{2} + \dots + \frac{1}{m}$ is positive.

The source's display joins the two valuation conditions with "and", but its text ("all prime
divisors of $X(m)$ and $Y(m)$") and its table ($E_3 = \{11\}$ with $11 \nmid X(3) = 13/36$) use
the union.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public def truncatedLogExceptionalPrimes (m : ℕ) : Set ℕ :=
  {ℓ | ℓ.Prime ∧ (0 < padicValRat ℓ (truncatedLogAuxProduct m) ∨
    0 < padicValRat ℓ (_root_.harmonic m)) ∧ m * ℓ % 4 = 1}

namespace finite_primes_isSquare_discr_truncatedLog

local notation "geomPoly(" R ", " n ")" => (∑ i ∈ Finset.range n, (X : R[X]) ^ i)
local notation "logSum(" R ", " m ")" => (∑ i ∈ Finset.Icc 1 m, C ((i : R)⁻¹) * X ^ i)

private lemma pow_pred_mul {R : Type*} [Monoid R] (a : R) {n : ℕ} (hn : 1 ≤ n) :
    a ^ n = a * a ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact pow_succ' a k

private lemma geom_factor {m q : ℕ} (hq : q.Prime) :
    geomPoly(ZMod q, m * q) = (X - 1) ^ (q - 1) * (geomPoly(ZMod q, m)) ^ q := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hchar : ((X : (ZMod q)[X]) ^ m - 1) ^ q = ((X : (ZMod q)[X]) ^ m) ^ q - 1 := by
    rw [sub_pow_char, one_pow]
  have h1 : (X : (ZMod q)[X]) ^ (m * q) - 1 = ((X : (ZMod q)[X]) ^ m - 1) ^ q := by
    rw [hchar, ← pow_mul]
  have hgeom : ((X : (ZMod q)[X]) - 1) * geomPoly(ZMod q, m * q) =
      (X : (ZMod q)[X]) ^ (m * q) - 1 := by
    have h := geom_sum_mul (X : (ZMod q)[X]) (m * q)
    rw [mul_comm] at h
    exact h
  have hgeom_m : ((X : (ZMod q)[X]) - 1) * geomPoly(ZMod q, m) = (X : (ZMod q)[X]) ^ m - 1 := by
    have h := geom_sum_mul (X : (ZMod q)[X]) m
    rw [mul_comm] at h
    exact h
  have hX1 : ((X : (ZMod q)[X]) - 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (1 : ZMod q)
  have hqpow : ((X : (ZMod q)[X]) - 1) ^ q =
      ((X : (ZMod q)[X]) - 1) * ((X : (ZMod q)[X]) - 1) ^ (q - 1) :=
    pow_pred_mul ((X : (ZMod q)[X]) - 1) hq.one_le
  have hfactor : ((X : (ZMod q)[X]) - 1) * geomPoly(ZMod q, m * q) =
      ((X : (ZMod q)[X]) - 1) * ((X - 1) ^ (q - 1) * (geomPoly(ZMod q, m)) ^ q) := by
    rw [hgeom, h1, ← hgeom_m, mul_pow, hqpow, mul_assoc]
  exact mul_left_cancel₀ hX1 hfactor

private lemma resultant_geom_factor {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (g : (ZMod q)[X]) :
    resultant geomPoly(ZMod q, m * q) (g) =
      (g).eval 1 ^ (q - 1) * resultant (geomPoly(ZMod q, m)) (g) ^ q := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hm0 : 0 < m := by omega
  have hXC : ((X : (ZMod q)[X]) - 1) = X - C (1 : ZMod q) := by simp
  have hX1 : ((X : (ZMod q)[X]) - 1) ≠ 0 := by
    simpa using X_sub_C_ne_zero (1 : ZMod q)
  have hmonic_m : geomPoly(ZMod q, m).Monic :=
    monic_geom_sum_X (by omega : m ≠ 0)
  have hdeg1 : (((X : (ZMod q)[X]) - 1) ^ (q - 1)).natDegree = q - 1 := by
    rw [hXC, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hmul := resultant_mul_left ((X - 1 : (ZMod q)[X]) ^ (q - 1)) ((geomPoly(ZMod q, m)) ^ q)
    (g) ((g).natDegree) le_rfl
  rw [hdeg1] at hmul
  have h1 := resultant_X_sub_C_pow_left (1 : ZMod q) (g) (q - 1)
    ((g).natDegree) le_rfl
  rw [← hXC] at h1
  have h2 := resultant_pow_left (f := geomPoly(ZMod q, m)) (g := g)
    (m := q) (n := (g).natDegree)
    (by rw [hmonic_m.leadingCoeff, one_pow]; exact one_ne_zero) le_rfl
  have hdegmul : (((X - 1 : (ZMod q)[X]) ^ (q - 1)) * (geomPoly(ZMod q, m)) ^ q).natDegree =
      (q - 1) + (geomPoly(ZMod q, m) ^ q).natDegree := by
    rw [natDegree_mul (pow_ne_zero _ hX1) (pow_ne_zero _ hmonic_m.ne_zero), hdeg1]
  rw [geom_factor hq, hdegmul, hmul, h1, h2]

private noncomputable def excA (m : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 m, ((Nat.factorial m / i : ℕ) : ℤ)

private noncomputable def excG (m : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.Icc 1 m, C ((Nat.factorial m / i : ℕ) : ℤ) * X ^ i

private noncomputable def excR (m : ℕ) : ℤ :=
  resultant geomPoly(ℤ, m) (excG m)

private lemma excG_coeff (m j : ℕ) :
    (excG m).coeff j =
      if j = 0 then 0 else if j ≤ m then ((Nat.factorial m / j : ℕ) : ℤ) else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [excG, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    simp [excG, coeff_X_pow, mul_ite, Finset.mem_Icc, h0, hj]

private lemma cast_div_factorial {m q : ℕ} (hq : q.Prime) (hlt : m < q)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    (((Nat.factorial m / i : ℕ) : ℤ) : ZMod q) =
      ((Nat.factorial m : ℕ) : ZMod q) * ((i : ZMod q)⁻¹) := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hiz : (i : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.lt_of_le_of_lt him hlt).not_ge (Nat.le_of_dvd (by omega : 0 < i) h)
  have hdiv : i ∣ Nat.factorial m := Nat.dvd_factorial (by omega : 0 < i) him
  rw [Int.cast_natCast, ← div_eq_mul_inv, eq_div_iff hiz, ← Nat.cast_mul]
  congr 1
  exact Nat.div_mul_cancel hdiv

private lemma eval_one_eq (q m : ℕ) :
    logSum(ZMod q, m).eval 1 = ∑ i ∈ Finset.Icc 1 m, ((i : ZMod q)⁻¹) := by
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  simp [eval_mul, eval_pow, eval_C, eval_X]

private lemma dvd_excA_of_eval_eq_zero {m q : ℕ} (hq : q.Prime) (hlt : m < q)
    (h0 : logSum(ZMod q, m).eval 1 = 0) : (q : ℤ) ∣ excA m := by
  have hcast : ((excA m : ℤ) : ZMod q) =
      ((Nat.factorial m : ℕ) : ZMod q) * logSum(ZMod q, m).eval 1 := by
    rw [excA, Int.cast_sum, eval_one_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact cast_div_factorial hq hlt (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  have h0' : ((excA m : ℤ) : ZMod q) = 0 := by rw [hcast, h0, mul_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0'

private lemma excA_pos {m : ℕ} (hm : 1 ≤ m) : 0 < excA m := by
  rw [excA]
  apply Finset.sum_pos
  · intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have him : i ≤ m := (Finset.mem_Icc.mp hi).2
    have hpos : 0 < Nat.factorial m / i := Nat.div_pos
      (Nat.le_of_dvd (Nat.factorial_pos m) (Nat.dvd_factorial (by omega : 0 < i) him))
      (by omega : 0 < i)
    exact_mod_cast hpos
  · exact Finset.nonempty_Icc.mpr hm

private lemma excG_natDegree {m : ℕ} (hm : 1 ≤ m) : (excG m).natDegree = m := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [excG_coeff, ite_eq_right (by omega : j ≠ 0), ite_eq_right (by omega : ¬ j ≤ m)]
  · rw [excG_coeff, ite_eq_right (by omega : m ≠ 0), ite_eq_left le_rfl]
    have hpos : 0 < Nat.factorial m / m := Nat.div_pos
      (Nat.le_of_dvd (Nat.factorial_pos m) (Nat.dvd_factorial (by omega : 0 < m) le_rfl))
      (by omega : 0 < m)
    exact_mod_cast hpos.ne'

private lemma excG_map {m q : ℕ} (hq : q.Prime) (hlt : m < q) :
    (excG m).map (Int.castRingHom (ZMod q)) =
      C (((Nat.factorial m : ℕ)) : ZMod q) * logSum(ZMod q, m) := by
  rw [excG, Polynomial.map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, Int.coe_castRingHom,
    ← mul_assoc, ← C_mul]
  congr 1
  congr 1
  exact cast_div_factorial hq hlt (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2

private lemma logSum_natDegree_le {K : Type*} [Field K] (m : ℕ) :
    logSum(K, m).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans (by simpa using (Finset.mem_Icc.mp hi).2)

private lemma resultant_geom_unpad {R : Type*} [CommRing R] {m n : ℕ}
    (hm : 1 ≤ m) {g : R[X]} (hg : g.natDegree ≤ n) :
    resultant geomPoly(R, m) g geomPoly(R, m).natDegree n = resultant geomPoly(R, m) g := by
  have hf : geomPoly(R, m).Monic := monic_geom_sum_X (by omega : m ≠ 0)
  simpa only [Nat.add_sub_of_le hg, coeff_natDegree, hf.leadingCoeff, one_pow, one_mul] using
    resultant_add_right_deg geomPoly(R, m) g geomPoly(R, m).natDegree g.natDegree
      (n - g.natDegree) le_rfl

private lemma cast_excR {K : Type*} [Field K] {m : ℕ} (hm : 1 ≤ m) :
    (excR m : K) = resultant geomPoly(K, m) ((excG m).map (Int.castRingHom K))
      geomPoly(K, m).natDegree m := by
  have hf : geomPoly(ℤ, m).Monic := monic_geom_sum_X (by omega : m ≠ 0)
  have hmap : geomPoly(ℤ, m).map (Int.castRingHom K) = geomPoly(K, m) := by
    simp [Polynomial.map_sum]
  change Int.castRingHom K (resultant geomPoly(ℤ, m) (excG m)) = _
  rw [excG_natDegree hm, ← resultant_map_map, ← hf.natDegree_map (Int.castRingHom K), hmap]

private lemma dvd_excR_of_resultant_eq_zero {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hlt : m < q) (h0 : resultant geomPoly(ZMod q, m) logSum(ZMod q, m) = 0) :
    (q : ℤ) ∣ excR m := by
  have : Fact q.Prime := ⟨hq⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [cast_excR hm, excG_map hq hlt, resultant_C_mul_right,
    resultant_geom_unpad hm (logSum_natDegree_le m), h0, mul_zero]

private lemma redPolyC_ne_zero_of_pow {m : ℕ} (hm : 2 ≤ m) {θ : ℂ} (hpow : θ ^ m = 1) :
    logSum(ℂ, m).eval θ ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hnorm : ‖θ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (by omega)
  have hθ : θ ≠ 0 := by
    rintro rfl
    simp at hnorm
  -- `logSum(ℂ, n + 1) = X * Q`, where `Q` has the coefficients `1 / (k + 1)` for `k ≤ n`.
  let a : Fin (n + 1) → ℝ := fun k => ((k : ℕ) + 1 : ℝ)⁻¹
  have hpos : ∀ k, 0 < a k := fun k => by positivity
  have heval : logSum(ℂ, n + 1).eval θ =
      θ * (∑ k : Fin (n + 1), C ((a k : ℝ) : ℂ) * X ^ (k : ℕ)).eval θ := by
    rw [eval_finsetSum, eval_finsetSum, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [a, eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    ring
  rw [heval]
  refine mul_ne_zero hθ fun hQ => ?_
  -- Every adjacent ratio `(k + 2) / (k + 1)` exceeds one, so every zero of `Q` has norm
  -- greater than one by the Eneström–Kakeya theorem.
  have hlow := (MathlibExt.Analysis.Complex.EnestromKakeya.enestrom_kakeya_zero_localization
    hn a hpos θ hQ).1
  rw [hnorm] at hlow
  have hgt : ∀ y ∈ Finset.image (fun k : Fin n => a k.castSucc / a k.succ) Finset.univ,
      1 < y := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
    rw [one_lt_div (hpos _)]
    simp only [a, Fin.val_castSucc, Fin.val_succ]
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    push_cast
    linarith
  exact lt_irrefl _ (lt_of_lt_of_le ((Finset.lt_min'_iff _ _).mpr hgt) hlow)

private lemma cast_factorial_div {K : Type*} [Field K] [CharZero K] {m i : ℕ}
    (hi : i ∈ Finset.Icc 1 m) : (((m.factorial / i : ℕ) : ℤ) : K) =
      (m.factorial : K) * (i : K)⁻¹ := by
  obtain ⟨hi₁, him⟩ := Finset.mem_Icc.mp hi
  rw [Int.cast_natCast, Nat.cast_div_charZero (Nat.dvd_factorial hi₁ him), div_eq_mul_inv]

private lemma excG_map_charZero {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    (excG m).map (Int.castRingHom K) = C (m.factorial : K) * logSum(K, m) := by
  rw [excG, Polynomial.map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, Int.coe_castRingHom,
    ← mul_assoc, ← C_mul]
  exact congrArg (fun a : K => C a * X ^ i) (cast_factorial_div hi)

private lemma excR_eq {K : Type*} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) :
    (excR m : K) = (m.factorial : K) ^ geomPoly(K, m).natDegree *
      resultant geomPoly(K, m) logSum(K, m) geomPoly(K, m).natDegree m := by
  rw [cast_excR hm, excG_map_charZero, resultant_C_mul_right]

private lemma excR_ne_zero {m : ℕ} (hm : 1 ≤ m) : excR m ≠ 0 := by
  have hm0 : 0 < m := by omega
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hmonic : geomPoly(ℂ, m).Monic := monic_geom_sum_X hm0.ne'
  have hfactor : ∀ θ ∈ geomPoly(ℂ, m).roots, logSum(ℂ, m).eval θ ≠ 0 := by
    intro θ hθ
    have h0 : geomPoly(ℂ, m).eval θ = 0 := (mem_roots hmonic.ne_zero).mp hθ
    have hpow : θ ^ m = 1 := by
      have hsum := geom_sum_mul θ m
      have heval : geomPoly(ℂ, m).eval θ = ∑ i ∈ Finset.range m, θ ^ i := by
        change (∑ i ∈ Finset.range m, (X : ℂ[X]) ^ i).eval θ = _
        rw [eval_finsetSum]
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_pow, eval_X]
      rw [heval] at h0
      rw [h0, zero_mul] at hsum
      exact sub_eq_zero.mp hsum.symm
    have hne : θ ≠ 1 := by
      intro h1
      have heval1 : geomPoly(ℂ, m).eval 1 = (m : ℂ) := by
        change (∑ i ∈ Finset.range m, (X : ℂ[X]) ^ i).eval 1 = _
        simp [eval_finsetSum]
      rw [h1, heval1] at h0
      exact hmC h0
    by_cases hm2 : 2 ≤ m
    · exact redPolyC_ne_zero_of_pow hm2 hpow
    · have hm1 : m = 1 := by omega
      rw [hm1, pow_one] at hpow
      exact absurd hpow hne
  have hprod := resultant_eq_prod_eval geomPoly(ℂ, m) logSum(ℂ, m) m
    (logSum_natDegree_le m) (IsAlgClosed.splits _)
  rw [hmonic.leadingCoeff, one_pow, one_mul] at hprod
  have hprod_ne : (Multiset.map (fun x => logSum(ℂ, m).eval x)
      geomPoly(ℂ, m).roots).prod ≠ 0 := by
    rw [ne_eq, Multiset.prod_eq_zero_iff]
    intro hmem
    obtain ⟨θ, hθ, heq⟩ := Multiset.mem_map.mp hmem
    exact hfactor θ hθ heq
  have hfact_ne : (m.factorial : ℂ) ^ geomPoly(ℂ, m).natDegree ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Nat.factorial_pos m).ne')
  have hne0 : ((excR m : ℤ) : ℂ) ≠ 0 := by
    rw [excR_eq hm, hprod]
    exact mul_ne_zero hfact_ne hprod_ne
  intro hcon
  rw [hcon] at hne0
  simp at hne0

private lemma key_nonsquare {m q : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hlt : m < q)
    (h4 : m * q % 4 = 1) (hA : ¬ (q : ℤ) ∣ excA m) (hR : ¬ (q : ℤ) ∣ excR m) :
    ¬ IsSquare (truncatedLogPolynomial (m * q)).discr := by
  have : Fact q.Prime := ⟨hq⟩
  refine not_isSquare_discr_truncatedLog_mul_prime_of_resultant_ne_zero hq hm hlt
    (Nat.odd_iff.mpr (by omega)) ?_
  rw [resultant_geom_factor hq hm]
  exact mul_ne_zero (pow_ne_zero _ fun h => hA (dvd_excA_of_eval_eq_zero hq hlt h))
    (pow_ne_zero _ fun h => hR (dvd_excR_of_resultant_eq_zero hq hm hlt h))

private lemma excA_eq (m : ℕ) : (excA m : ℚ) = (m.factorial : ℚ) * harmonic m := by
  rw [excA, Int.cast_sum, harmonic, Finset.mul_sum, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him := Finset.mem_range.mp hi
  have hmem : i + 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  simpa [Nat.add_comm 1 i] using (cast_factorial_div (K := ℚ) hmem)

private lemma excR_eq_auxProduct {m : ℕ} (hm : 1 ≤ m) :
    (excR m : ℚ) = (m.factorial : ℚ) ^ geomPoly(ℚ, m).natDegree * truncatedLogAuxProduct m := by
  let f := geomPoly(ℚ, m)
  let c : ℚ := (m : ℚ)⁻¹
  let g := C c + logSum(ℚ, m - 1)
  have hsplit : logSum(ℚ, m) = logSum(ℚ, m - 1) + C c * X ^ m := by
    have h := Finset.sum_Icc_succ_top (f := fun i => C ((i : ℚ)⁻¹) * X ^ i)
      (a := 1) (b := m - 1) (by omega : 1 ≤ m - 1 + 1)
    rwa [Nat.sub_add_cancel hm] at h
  have hshift : logSum(ℚ, m) = g + f * (C c * (X - 1)) := by
    rw [hsplit, show f * (C c * (X - 1)) = C c * (X ^ m - 1) by
      rw [mul_left_comm, geom_sum_mul]]
    dsimp [g]
    ring
  have hf : f.natDegree ≤ m - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    simpa using (Nat.le_pred_of_lt (Finset.mem_range.mp hi))
  have hg : g.natDegree ≤ m :=
    natDegree_add_le_of_degree_le (natDegree_C c ▸ Nat.zero_le m)
      ((logSum_natDegree_le (m - 1)).trans (Nat.sub_le _ _))
  have hp : (C c * (X - 1)).natDegree + f.natDegree ≤ m := by
    have h := (natDegree_C_mul_le c (X - 1)).trans (natDegree_sub_le (X : ℚ[X]) 1)
    simp at h
    omega
  rw [excR_eq hm, truncatedLogAuxProduct]
  change _ * resultant f logSum(ℚ, m) f.natDegree m = _ * resultant f g
  rw [hshift, resultant_add_mul_right _ _ _ _ _ hp le_rfl, resultant_geom_unpad hm hg]

-- A prime larger than m divides neither m! nor any of its powers.
private lemma valuation_pos_of_dvd_scaled {m q k : ℕ} (hq : q.Prime) (hmq : m < q)
    {z : ℤ} {a : ℚ} (hz : z ≠ 0) (heq : (z : ℚ) = (m.factorial : ℚ) ^ k * a)
    (hdvd : (q : ℤ) ∣ z) : 0 < padicValRat q a := by
  have : Fact q.Prime := ⟨hq⟩
  have hfact : padicValRat q (m.factorial : ℚ) = 0 := by
    have hndvd : ¬ q ∣ m.factorial := mt hq.dvd_factorial.mp hmq.not_ge
    rw [← Int.cast_natCast, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hndvd), Nat.cast_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    exact hz (Int.cast_eq_zero.mp (heq.trans (mul_zero _)))
  have hzval : 0 < padicValInt q z :=
    ((padicValInt_dvd_iff 1 z).mp (by simpa using hdvd)).resolve_left hz
  have hv : padicValRat q (z : ℚ) = padicValRat q a := by
    rw [heq, padicValRat.mul (by positivity) ha, padicValRat.pow, hfact, mul_zero, zero_add]
  rw [← hv, padicValRat.of_int]
  exact_mod_cast hzval

end finite_primes_isSquare_discr_truncatedLog

open finite_primes_isSquare_discr_truncatedLog in
/-- **Nonsquare discriminants of $F_{mq}$ for non-exceptional primes $q > m$.** Let $m$ be a
natural number, let $E_m$ be the set of exceptional primes for truncated logarithmic
discriminants, and let $F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic
polynomial. If $q$ is a prime with $q \notin E_m$, $q > m$ and $mq \equiv 1 \pmod 4$, then the
discriminant of $F_{mq}$ is not a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 5
(`integers-2025-A39-thm-5`). -/
public theorem not_isSquare_discr_truncatedLog_mul_prime {m q : ℕ} (hq : q.Prime)
    (hE : q ∉ truncatedLogExceptionalPrimes m) (hmq : m < q) (h4 : m * q % 4 = 1) :
    ¬ IsSquare (truncatedLogPolynomial (m * q)).discr := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at h4
  refine key_nonsquare hq hm hmq h4 ?_ ?_
  · intro hA
    have hv := valuation_pos_of_dvd_scaled (k := 1) hq hmq (excA_pos hm).ne'
      (by simpa using excA_eq m) hA
    exact hE ⟨hq, Or.inr hv, h4⟩
  · intro hR
    have hv := valuation_pos_of_dvd_scaled hq hmq (excR_ne_zero hm) (excR_eq_auxProduct hm) hR
    exact hE ⟨hq, Or.inl hv, h4⟩

/-- **Finiteness of square discriminants of $F_{mq}$ with $mq \equiv 1 \pmod 4$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial and let
$m \ge 1$ be a natural number. Then there are only finitely many primes $q$ with
$mq \equiv 1 \pmod 4$ such that the discriminant of $F_{mq}$ is a square in $\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 3
(`integers-2025-A39-thm-3`). -/
public theorem finite_primes_isSquare_discr_truncatedLog {m : ℕ} (hm : 1 ≤ m) :
    {q : ℕ | q.Prime ∧ m * q % 4 = 1 ∧ IsSquare (truncatedLogPolynomial (m * q)).discr}.Finite := by
  have hfin : (Set.Iic m ∪ (Set.Iic
      (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs ∪ Set.Iic
      (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs)).Finite :=
    (Set.finite_Iic m).union ((Set.finite_Iic _).union (Set.finite_Iic _))
  apply hfin.subset
  intro q hq
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic] at hq ⊢
  obtain ⟨hqp, h4, hsq⟩ := hq
  by_cases hle : q ≤ m
  · tauto
  · have hlt : m < q := by omega
    by_cases hdvdA : (q : ℤ) ∣ finite_primes_isSquare_discr_truncatedLog.excA m
    · have hApos : 0 < (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs :=
        Int.natAbs_pos.mpr
          (ne_of_gt (finite_primes_isSquare_discr_truncatedLog.excA_pos hm))
      have h1 : q ∣ (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs := by
        have h2 : (Int.natAbs (q : ℤ)) ∣
            (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs :=
          Int.natAbs_dvd_natAbs.mpr hdvdA
        rwa [Int.natAbs_natCast] at h2
      have hleA : q ≤ (finite_primes_isSquare_discr_truncatedLog.excA m).natAbs :=
        Nat.le_of_dvd hApos h1
      tauto
    · by_cases hdvdR : (q : ℤ) ∣ finite_primes_isSquare_discr_truncatedLog.excR m
      · have hRpos : 0 < (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs :=
          Int.natAbs_pos.mpr
            (finite_primes_isSquare_discr_truncatedLog.excR_ne_zero hm)
        have h1 : q ∣ (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs := by
          have h2 : (Int.natAbs (q : ℤ)) ∣
              (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs :=
            Int.natAbs_dvd_natAbs.mpr hdvdR
          rwa [Int.natAbs_natCast] at h2
        have hleR : q ≤ (finite_primes_isSquare_discr_truncatedLog.excR m).natAbs :=
          Nat.le_of_dvd hRpos h1
        tauto
      · exfalso
        exact finite_primes_isSquare_discr_truncatedLog.key_nonsquare hqp hm hlt h4 hdvdA
          hdvdR hsq

end

end MetaMathlibExt

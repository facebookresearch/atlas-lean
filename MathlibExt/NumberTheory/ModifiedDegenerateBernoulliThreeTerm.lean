/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulli
public import Mathlib.RingTheory.Binomial

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Three-term identity for modified degenerate Bernoulli polynomials

We prove the cyclic three-term identity for modified degenerate Bernoulli polynomials by applying
falling factorials to a homogeneous identity of ordinary Bernoulli polynomials.
-/

open Finset

namespace MetaMathlibExt

namespace modifiedDegenerateBernoulli_three_term

section Series

variable {A : Type*} [CommRing A] [Algebra ℚ A]

private noncomputable def bernoulliSeries (a x : A) : PowerSeries A :=
  PowerSeries.rescale a (PowerSeries.mk fun k =>
    Polynomial.aeval x ((1 / k.factorial : ℚ) • Polynomial.bernoulli k))

local notation:max "E" a:max => PowerSeries.rescale a (PowerSeries.exp A)

private theorem series_mul (a x : A) :
    bernoulliSeries a x * (E a - 1) = PowerSeries.C a * PowerSeries.X * E (a * x) := by
  simpa only [bernoulliSeries, map_mul, map_sub, map_one, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale, mul_comm x a] using
    congrArg (PowerSeries.rescale a) (Polynomial.bernoulli_generating_function x)

-- Moving the minus sign from the series parameter to the argument reflects x about 1/2.
private theorem series_neg_mul (a x : A) :
    bernoulliSeries (-a) x * (E a - 1) =
      PowerSeries.C a * PowerSeries.X * E (a * (1 - x)) := by
  have hexp : E a * E (-a) = 1 := by
    rw [PowerSeries.exp_mul_exp_eq_exp_add, add_neg_cancel, PowerSeries.rescale_zero]
    simp
  have hdenom : E a - 1 = -(E a * (E (-a) - 1)) := by
    rw [mul_sub, hexp, mul_one, neg_sub]
  calc
    _ = -(E a * (bernoulliSeries (-a) x * (E (-a) - 1))) := by rw [hdenom]; ring
    _ = _ := by
      rw [series_mul, map_neg, neg_mul, neg_mul, mul_neg, neg_neg]
      calc
        _ = PowerSeries.C a * PowerSeries.X * (E a * E (-a * x)) := by ac_rfl
        _ = _ := by
          rw [PowerSeries.exp_mul_exp_eq_exp_add, show a + -a * x = a * (1 - x) by ring]

private theorem weighted_series (r s t x y : A) :
    (PowerSeries.C r * (bernoulliSeries t x * bernoulliSeries (-s) y)) *
        ((E r - 1) * (E s - 1) * (E t - 1)) =
      (PowerSeries.C (r * s * t) * PowerSeries.X ^ 2) *
        (E (t * x + s * (1 - y)) * (E r - 1)) := by
  calc
    _ = PowerSeries.C r * ((bernoulliSeries t x * (E t - 1)) *
        (bernoulliSeries (-s) y * (E s - 1))) * (E r - 1) := by ac_rfl
    _ = _ := by
      rw [series_mul, series_neg_mul, map_mul, map_mul, pow_two,
        ← PowerSeries.exp_mul_exp_eq_exp_add]
      ac_rfl

-- Clearing the three exponential denominators gives a telescoping sum.
private theorem cyclic_series [IsDomain A] (r s t x y z : A)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hrst : r + s + t = 0) (hxyz : x + y + z = 1) :
    PowerSeries.C r * (bernoulliSeries t x * bernoulliSeries (-s) y) +
      PowerSeries.C s * (bernoulliSeries r y * bernoulliSeries (-t) z) +
      PowerSeries.C t * (bernoulliSeries s z * bernoulliSeries (-r) x) = 0 := by
  have hne (a : A) (ha : a ≠ 0) : E a - 1 ≠ 0 := by
    intro h
    apply ha
    simpa [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one] using
      congrArg (PowerSeries.coeff 1) h
  have h₁ : t * x + s * (1 - y) + r = s * z + r * (1 - x) := by
    linear_combination x * hrst - s * hxyz
  have h₂ : r * y + t * (1 - z) + s = t * x + s * (1 - y) := by
    linear_combination y * hrst - t * hxyz
  have h₃ : s * z + r * (1 - x) + t = r * y + t * (1 - z) := by
    linear_combination z * hrst - r * hxyz
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (hne r hr) (hne s hs)) (hne t ht))
  rw [zero_mul, add_mul, add_mul, weighted_series]
  have hs' := weighted_series s t r y z
  have ht' := weighted_series t r s z x
  rw [show (E s - 1) * (E t - 1) * (E r - 1) = (E r - 1) * (E s - 1) * (E t - 1) by
    ac_rfl, show s * t * r = r * s * t by ac_rfl] at hs'
  rw [show (E t - 1) * (E r - 1) * (E s - 1) = (E r - 1) * (E s - 1) * (E t - 1) by
    ac_rfl, show t * r * s = r * s * t by ac_rfl] at ht'
  rw [hs', ht']
  rw [mul_sub (E (t * x + s * (1 - y))), mul_sub (E (r * y + t * (1 - z))),
    mul_sub (E (s * z + r * (1 - x)))]
  simp only [mul_one, PowerSeries.exp_mul_exp_eq_exp_add, h₁, h₂, h₃]
  ring

end Series

open MvPolynomial

local notation "P" => MvPolynomial (Fin 3) ℂ
local notation:max "V" i:max => (MvPolynomial.X i : P)
local notation "L" => V 0 + V 1 + V 2

private noncomputable def topTerm (n : ℕ) (i j l : Fin 3) (x y : ℂ) : P :=
  ∑ k ∈ range (n + 1), C ((-1) ^ k *
      Polynomial.aeval x ((1 / (n - k).factorial : ℚ) • Polynomial.bernoulli (n - k)) *
      Polynomial.aeval y ((1 / k.factorial : ℚ) • Polynomial.bernoulli k)) *
    (V i * V j ^ k * V l ^ (n - k))

private theorem topTerm_homogeneous (n : ℕ) (i j l : Fin 3) (x y : ℂ) :
    (topTerm n i j l x y).IsHomogeneous (n + 1) := by
  apply IsHomogeneous.sum
  intro k hk
  have h := ((isHomogeneous_X ℂ i).mul ((isHomogeneous_X ℂ j).pow k)).mul
    ((isHomogeneous_X ℂ l).pow (n - k))
  rw [one_mul, one_mul, show 1 + k + (n - k) = n + 1 by
    have := mem_range.mp hk
    omega] at h
  exact h.C_mul _

private theorem aeval_topTerm (n : ℕ) (i j l : Fin 3) (x y : ℂ) (a : Fin 3 → P) :
    aeval a (topTerm n i j l x y) = PowerSeries.coeff n
      (PowerSeries.C (a i) * (bernoulliSeries (a l) (C x) * bernoulliSeries (-(a j)) (C y))) := by
  have hC (u : ℂ) (p : Polynomial ℚ) :
      Polynomial.aeval (C u : P) p = C (Polynomial.aeval u p) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℂ P) u p
  rw [PowerSeries.coeff_C_mul, mul_comm (bernoulliSeries (a l) (C x)), PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  simp only [topTerm, map_mul, aeval_X, map_sum, map_pow, aeval_C, ← C_eq_algebraMap,
    bernoulliSeries, PowerSeries.coeff_rescale, PowerSeries.coeff_mk, hC, neg_pow (a j), map_neg,
    map_one]
  exact sum_congr rfl fun k _ => by ring

-- Substituting X₀ = -X₁ - X₂ is the identity modulo X₀ + X₁ + X₂.
private theorem linear_dvd_of_subst_eq_zero (p : P)
    (hp : aeval ![-V 1 - V 2, V 1, V 2] p = 0) : L ∣ p := by
  let I : Ideal P := Ideal.span {L}
  let q := Ideal.Quotient.mk I
  have hL : q L = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hq : q.comp (aeval ![-V 1 - V 2, V 1, V 2]).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      fin_cases i <;> simp
      have hsum : q (V 0) + q (V 1) + q (V 2) = 0 := by simpa only [map_add] using hL
      linear_combination -hsum
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q p = 0
  rw [← DFunLike.congr_fun hq p]
  exact (congrArg q hp).trans (map_zero q)

private theorem cyclic_top_dvd (n : ℕ) (x y z : ℂ) (hxyz : x + y + z = 1) :
    L ∣ topTerm n 0 1 2 x y + topTerm n 1 2 0 y z + topTerm n 2 0 1 z x := by
  apply linear_dvd_of_subst_eq_zero
  have hne : -V 1 - V 2 ≠ 0 := by
    intro h
    have h' := congrArg (MvPolynomial.eval ![(0 : ℂ), 1, 0]) h
    norm_num at h'
  have h := cyclic_series (-V 1 - V 2) (V 1) (V 2) (C x) (C y) (C z)
    hne (X_ne_zero 1) (X_ne_zero 2) (by abel) (by rw [← map_add, ← map_add, hxyz, map_one])
  simpa only [map_add, aeval_topTerm, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_zero] using
    congrArg (PowerSeries.coeff n) h

private noncomputable def falling (a : Fin 3 → ℂ) : P →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ fun d : Fin 3 →₀ ℕ =>
    ∏ i, (descPochhammer ℂ (d i)).eval (a i)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem falling_monomial (a : Fin 3 → ℂ) (d : Fin 3 →₀ ℕ) (c : ℂ) :
    falling a (monomial d c) = c * ∏ i, (descPochhammer ℂ (d i)).eval (a i) := by
  simp only [falling, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply, ← single_eq_monomial, AddMonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single, smul_eq_mul]

private theorem falling_step (a : Fin 3 → ℂ) (d : Fin 3 →₀ ℕ) (c : ℂ) (i : Fin 3) :
    falling a (V i * monomial d c) = falling a (monomial d c) * (a i - d i) := by
  rw [mul_comm, ← pow_one (V i), ← monomial_add_single, falling_monomial, falling_monomial]
  rw [← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase _ _ (mem_univ i)]
  set e : Fin 3 →₀ ℕ := d + Finsupp.single i 1 with he
  have h : ∏ j ∈ univ.erase i, (descPochhammer ℂ (e j)).eval (a j) =
      ∏ j ∈ univ.erase i, (descPochhammer ℂ (d j)).eval (a j) := by
    apply prod_congr rfl
    intro j hj
    simp [he, Finsupp.single_eq_of_ne (ne_of_mem_erase hj)]
  rw [h, he, Finsupp.add_apply, Finsupp.single_eq_same, descPochhammer_succ_eval]
  ring

-- In degree n+1, multiplication by L is killed by falling factorial evaluation at weights
-- summing to n. For a degree n monomial the three increments sum to a₀ + a₁ + a₂ - n.
private theorem falling_component_mul (n : ℕ) (a : Fin 3 → ℂ)
    (ha : a 0 + a 1 + a 2 = n) (p : P) :
    falling a (homogeneousComponent (n + 1) (L * p)) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have h : (L * monomial d c : P).IsHomogeneous (d.degree + 1) := by
      rw [Nat.add_comm d.degree 1]
      exact (((isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)).add
        (isHomogeneous_X ℂ 2)).mul (isHomogeneous_monomial c rfl)
    rw [homogeneousComponent_of_mem h]
    by_cases hd : d.degree = n
    · rw [ite_eq_left (by rw [hd]), add_mul, add_mul, map_add, map_add,
        falling_step, falling_step, falling_step]
      have hdeg : (d 0 : ℂ) + d 1 + d 2 = n := by
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hd
        exact_mod_cast (show d 0 + d 1 + d 2 = n by omega)
      linear_combination falling a (monomial d c) * (ha - hdeg)
    · rw [ite_eq_right (by omega), map_zero]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, add_zero]

private theorem falling_cyclic_monomial (a : Fin 3 → ℂ) (i : Fin 3) (k m : ℕ) (c : ℂ) :
    falling a (C c * (V i * V (i + 1) ^ k * V (i + 2) ^ m)) =
      c * a i * (descPochhammer ℂ k).eval (a (i + 1)) *
        (descPochhammer ℂ m).eval (a (i + 2)) := by
  rw [← pow_one (V i), X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial]
  simp only [monomial_mul_monomial, mul_one, C_mul_monomial, falling_monomial]
  fin_cases i <;> simp [Fin.prod_univ_three, Finsupp.single_apply, descPochhammer_one] <;>
    ring

private theorem desc_eq_choose (a : ℂ) (k : ℕ) :
    (descPochhammer ℂ k).eval a = (k.factorial : ℂ) * Ring.choose a k := by
  rw [← descPochhammer_map (algebraMap ℤ ℂ), Polynomial.eval_map,
    ← Polynomial.aeval_def, Polynomial.aeval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

private noncomputable def ordinarySum (n : ℕ) (s t x y : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), (-1) ^ k * Ring.choose s k * Ring.choose t (n - k) *
    Polynomial.aeval x (Polynomial.bernoulli (n - k)) * Polynomial.aeval y (Polynomial.bernoulli k)

private theorem falling_topTerm (n : ℕ) (a : Fin 3 → ℂ) (i : Fin 3) (x y : ℂ) :
    falling a (topTerm n i (i + 1) (i + 2) x y) =
      a i * ordinarySum n (a (i + 1)) (a (i + 2)) x y := by
  rw [topTerm, ordinarySum, map_sum, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [falling_cyclic_monomial, desc_eq_choose, desc_eq_choose]
  simp only [map_smul, Rat.smul_def, one_div, Rat.cast_inv, Rat.cast_natCast]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]

private theorem ordinary_three_term (n : ℕ) (r s t x y z : ℂ) (hrst : r + s + t = n)
    (hxyz : x + y + z = 1) :
    r * ordinarySum n s t x y + s * ordinarySum n t r y z + t * ordinarySum n r s z x = 0 := by
  obtain ⟨p, hp⟩ := cyclic_top_dvd n x y z hxyz
  have hhom := ((topTerm_homogeneous n 0 1 2 x y).add (topTerm_homogeneous n 1 2 0 y z)).add
    (topTerm_homogeneous n 2 0 1 z x)
  have h := falling_component_mul n ![r, s, t] hrst p
  rw [← hp, homogeneousComponent_eq_self hhom, map_add, map_add] at h
  have h₀ : falling ![r, s, t] (topTerm n 0 1 2 x y) = r * ordinarySum n s t x y :=
    falling_topTerm n ![r, s, t] 0 x y
  have h₁ : falling ![r, s, t] (topTerm n 1 2 0 y z) = s * ordinarySum n t r y z :=
    falling_topTerm n ![r, s, t] 1 y z
  have h₂ : falling ![r, s, t] (topTerm n 2 0 1 z x) = t * ordinarySum n r s z x :=
    falling_topTerm n ![r, s, t] 2 z x
  rwa [h₀, h₁, h₂] at h

private theorem scaled_sum (n : ℕ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1)
    (s t x y : ℂ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * Ring.choose s k * Ring.choose t (n - k) *
        modifiedDegenerateBernoulli lam (n - k) x * modifiedDegenerateBernoulli lam k y =
      (Complex.log (1 + lam) / lam) ^ ((n : ℤ) - 2) * ordinarySum n s t x y := by
  set c := Complex.log (1 + lam) / lam with hcdef
  have hc : c ≠ 0 := by
    apply div_ne_zero _ hlam
    have h := Complex.exp_log (x := 1 + lam) (by intro h; apply hlam1; linear_combination h)
    intro hz
    rw [hz, Complex.exp_zero] at h
    exact hlam (by linear_combination -h)
  rw [ordinarySum, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hexp : (((n - k : ℕ) : ℤ) - 1) + ((k : ℤ) - 1) = (n : ℤ) - 2 := by
    rw [Nat.cast_sub (mem_range_succ_iff.mp hk)]
    ring
  simp only [modifiedDegenerateBernoulli, ← hcdef]
  rw [← hexp, zpow_add₀ hc]
  ring

end modifiedDegenerateBernoulli_three_term

set_option linter.unusedVariables false in
/-- **Three-term identity for modified degenerate Bernoulli polynomials.** Let $n \ge 1$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, write
$\mathfrak{B}_{k,\lambda}(x)$ for the modified degenerate Bernoulli polynomials, and for complex
numbers $s, t, x, y$ put
$\mathfrak{D}_{s,t,\lambda}(x, y) = \sum_{k=0}^{n} (-1)^k \binom{s}{k} \binom{t}{n-k}
\mathfrak{B}_{n-k,\lambda}(x) \mathfrak{B}_{k,\lambda}(y)$, where
$\binom{w}{k} = w(w-1) \cdots (w-k+1)/k!$ is the binomial coefficient with a complex upper
argument. If $r, s, t, x, y, z$ are complex numbers with $r + s + t = n$ and $x + y + z = 1$, then
$r\, \mathfrak{D}_{s,t,\lambda}(x, y) + s\, \mathfrak{D}_{t,r,\lambda}(y, z) +
t\, \mathfrak{D}_{r,s,\lambda}(z, x) = 0$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(sunpanD) (`jis-2024-24.5.4-cor-2`). -/
public theorem modifiedDegenerateBernoulli_three_term (n : ℕ) (hn : 1 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) (r s t x y z : ℂ) (hrst : r + s + t = n)
    (hxyz : x + y + z = 1) :
    let D : ℂ → ℂ → ℂ → ℂ → ℂ := fun s t x y =>
      ∑ k ∈ range (n + 1), (-1) ^ k * Ring.choose s k * Ring.choose t (n - k) *
        modifiedDegenerateBernoulli lam (n - k) x * modifiedDegenerateBernoulli lam k y
    r * D s t x y + s * D t r y z + t * D r s z x = 0 := by
  dsimp only
  rw [modifiedDegenerateBernoulli_three_term.scaled_sum n lam hlam hlam1 s t x y,
    modifiedDegenerateBernoulli_three_term.scaled_sum n lam hlam hlam1 t r y z,
    modifiedDegenerateBernoulli_three_term.scaled_sum n lam hlam hlam1 r s z x]
  linear_combination (Complex.log (1 + lam) / lam) ^ ((n : ℤ) - 2) *
    modifiedDegenerateBernoulli_three_term.ordinary_three_term n r s t x y z hrst hxyz

end MetaMathlibExt

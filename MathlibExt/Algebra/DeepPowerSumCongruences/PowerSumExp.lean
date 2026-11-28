/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Exponentials of power-sum series

For a finite set of variables over $\mathbb{Q}$ and a set $S \subseteq \mathbb{N}$ of degrees,
the exponential of $\sum_{s \in S,\ s \ge 1} (-1)^{s-1} p_s t^s / s$ is the generating function
of the corresponding weighted partitions. When all positive degrees are included, its coefficient
at $t^k$ is the elementary symmetric polynomial $e_k$.

The latter identity specializes Proposition 20 to finitely many variables by setting the remaining
variables to zero. As in the paper, the generating series includes the constant term $e_0 = 1$.

## References

* Samuele Anni, Alexandru Ghitza and Anna Medvedovsky, *Elementary Symmetric Functions and Deep
  Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, pp. 1–26, §3.3, Propositions 19 and 20
  and Corollary 21. The authors credit Ira Gessel for the restricted formulation of Proposition 19.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford University Press,
  2015, Chapter I, §2, cited in §3.3 for the standard generating functions of symmetric functions.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt
namespace exp_signedPowerSumSeries_eq_sum_partitions

variable {A : Type*} [CommRing A] [Algebra ℚ A]

private theorem subst_exp_add {f g : PowerSeries A}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (exp ℚ).subst (f + g) = (exp ℚ).subst f * (exp ℚ).subst g := by
  -- Prove the identity in two formal variables, then substitute the given series.
  let x : Fin 2 → MvPowerSeries (Fin 2) ℚ := MvPowerSeries.X
  have hxy : (exp ℚ).subst (x 0 + x 1) = (exp ℚ).subst (x 0) * (exp ℚ).subst (x 1) := by
    ext e
    rw [PowerSeries.coeff_subst_X_zero_add_X_one,
      PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
    simp only [coeff_exp, Algebra.algebraMap_self_apply]
    have h : ((e 0 + e 1).choose (e 0) : ℚ) * (e 0).factorial * (e 1).factorial =
        (e 0 + e 1).factorial := by
      exact_mod_cast (show (e 0 + e 1).choose (e 0) * (e 0).factorial * (e 1).factorial =
        (e 0 + e 1).factorial by
        simpa only [Nat.add_sub_cancel_left] using
          Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1)))
    field_simp
    exact h
  let inputs : Fin 2 → PowerSeries A := ![f, g]
  have hinputs : MvPowerSeries.HasSubst inputs :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro i
      fin_cases i
      · exact hf
      · exact hg)
  have hx (i : Fin 2) : HasSubst (x i) := .X i
  have hsum : HasSubst (x 0 + x 1) := .of_constantCoeff_zero (by simp [x])
  have hcomp {z : MvPowerSeries (Fin 2) ℚ} (hz : HasSubst z) :
      MvPowerSeries.subst inputs ((exp ℚ).subst z) =
        (exp ℚ).subst (MvPowerSeries.subst inputs z) :=
    MvPowerSeries.subst_comp_subst_apply hz.const hinputs _
  have h := congrArg (MvPowerSeries.substAlgHom (R := ℚ) hinputs) hxy
  rw [map_mul] at h
  simp only [MvPowerSeries.substAlgHom_apply] at h
  rw [hcomp hsum, hcomp (hx 0), hcomp (hx 1), MvPowerSeries.subst_add hinputs] at h
  simpa [x, inputs, MvPowerSeries.subst_X hinputs] using h

private theorem subst_exp_sum {ι : Type*} (f : ι → PowerSeries A)
    (hf : ∀ i, constantCoeff (f i) = 0) (s : Finset ι) :
    (exp ℚ).subst (∑ i ∈ s, f i) = ∏ i ∈ s, (exp ℚ).subst (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [subst_zero_eq_C_constantCoeff]
  | cons i s hi ih =>
      rw [sum_cons, prod_cons, subst_exp_add (hf i) (by simp [hf]), ih]

private theorem coeff_subst_exp_congr {f g : PowerSeries A} {n : ℕ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : ∀ j ≤ n, coeff j f = coeff j g) :
    coeff n ((exp ℚ).subst f) = coeff n ((exp ℚ).subst g) := by
  rw [coeff_subst' (.of_constantCoeff_zero' hf), coeff_subst' (.of_constantCoeff_zero' hg)]
  refine finsum_congr fun k ↦ congrArg (_ • ·) ?_
  rw [coeff_pow, coeff_pow]
  refine sum_congr rfl fun l hl ↦ prod_congr rfl fun i hi ↦ h (l i) ?_
  rw [← (mem_finsuppAntidiag.mp hl).1]
  exact single_le_sum (fun _ _ ↦ Nat.zero_le _) hi

private theorem coeff_subst_exp_monomial (a : A) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    coeff n ((exp ℚ).subst (monomial d a)) =
      if d ∣ n then (1 / ((n / d).factorial : ℚ)) • a ^ (n / d) else 0 := by
  have h : HasSubst (monomial d a) := .of_constantCoeff_zero' (by
    rw [← coeff_zero_eq_constantCoeff, coeff_monomial, ite_eq_right hd.symm])
  rw [coeff_subst' h]
  simp_rw [coeff_exp, Algebra.algebraMap_self_apply, monomial_pow, coeff_monomial]
  split_ifs with hn
  · rw [finsum_eq_single _ (n / d)]
    · rw [Nat.mul_comm, Nat.mul_div_cancel' hn, ite_eq_left rfl]
    · intro j hj
      rw [ite_eq_right, smul_zero]
      intro he
      apply hj
      rw [he, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd)]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [ite_eq_right, smul_zero]
    rintro rfl
    exact hn (dvd_mul_left _ _)

private theorem subst_exp_monomial_eq [TopologicalSpace A] [T2Space A]
    (a : A) {d : ℕ} (hd : d ≠ 0) :
    (exp ℚ).subst (monomial d a) =
      (1 : PowerSeries A) +
        ∑' j : ℕ, ((1 / ((j + 1).factorial : ℚ)) • a ^ (j + 1)) • X ^ (d * (j + 1)) := by
  ext n
  have hs := Nat.Partition.summable_genFun_term'
    (fun _ k ↦ (1 / (k.factorial : ℚ)) • a ^ k) hd
  rw [coeff_subst_exp_monomial a hd, map_add,
    hs.map_tsum _ (WithPiTopology.continuous_coeff A n)]
  simp only [map_smul, coeff_X_pow, smul_ite, smul_zero]
  by_cases hzero : n = 0
  · subst n
    simp [hd]
  rw [coeff_one, ite_eq_right hzero, zero_add]
  by_cases hdiv : d ∣ n
  · have hpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hdiv) hd.bot_lt
    have hk : n / d - 1 + 1 = n / d := Nat.sub_add_cancel hpos
    rw [ite_eq_left hdiv, tsum_eq_single (n / d - 1)]
    · simp [hk, Nat.mul_div_cancel' hdiv, smul_eq_mul]
    · intro j hj
      refine ite_eq_right (fun he ↦ hj (Nat.eq_sub_of_add_eq ?_))
      rw [he, Nat.mul_div_cancel_left _ hd.bot_lt]
  · have hne (j : ℕ) : n ≠ d * (j + 1) := fun h ↦ hdiv ⟨j + 1, h⟩
    simp [hdiv, hne]

private theorem subst_exp_eq_genFun [TopologicalSpace A] [T2Space A] (c : ℕ → A) :
    (exp ℚ).subst (PowerSeries.mk fun i ↦ if i = 0 then 0 else c i) =
      Nat.Partition.genFun (fun i k ↦ (1 / (k.factorial : ℚ)) • c i ^ k) := by
  have hprod (s : Finset ℕ) :
      (exp ℚ).subst (∑ i ∈ s, monomial (i + 1) (c (i + 1))) =
        ∏ i ∈ s, (exp ℚ).subst (monomial (i + 1) (c (i + 1))) :=
    subst_exp_sum _ (fun i ↦ by simp [← coeff_zero_eq_constantCoeff, coeff_monomial]) s
  -- To compute coefficient n, every partial sum containing degrees 1 through n suffices.
  have h : HasProd (fun i : ℕ ↦ (exp ℚ).subst (monomial (i + 1) (c (i + 1))))
      ((exp ℚ).subst (PowerSeries.mk fun i ↦ if i = 0 then 0 else c i)) := by
    rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    refine tendsto_atTop_of_eventually_const (i₀ := range n) fun s hs ↦ ?_
    rw [← hprod]
    refine coeff_subst_exp_congr ?_ ?_ fun j hj ↦ ?_
    · simp [← coeff_zero_eq_constantCoeff, coeff_monomial]
    · simp
    rcases j with _ | j
    · simp [coeff_monomial]
    rw [coeff_mk, ite_eq_right (Nat.succ_ne_zero j), map_sum]
    have hmem : j ∈ s := hs (mem_range.mpr (by omega))
    simp [coeff_monomial, hmem]
  simp_rw [subst_exp_monomial_eq _ (Nat.succ_ne_zero _)] at h
  exact h.unique (Nat.Partition.hasProd_genFun _)

private theorem prod_weights {n : ℕ} (l : n.Partition) (p : ℕ → A) :
    (∏ a ∈ l.parts.toFinset, (1 / ((l.parts.count a).factorial : ℚ)) •
      (((-1 : ℚ) ^ (a - 1) / a) • p a) ^ l.parts.count a) =
      ((-1 : ℚ) ^ (n - l.parts.card) /
        ((∏ a ∈ l.parts.toFinset, a ^ l.parts.count a * (l.parts.count a).factorial :
          ℕ) : ℚ)) • (l.parts.map p).prod := by
  have hsign : ∑ a ∈ l.parts.toFinset, (a - 1) * l.parts.count a = n - l.parts.card := by
    simp only [Nat.sub_mul, one_mul]
    rw [sum_tsub_distrib, l.parts.toFinset_sum_count_eq]
    · congr 1
      simpa only [Nat.nsmul_eq_mul, Nat.mul_comm] using
        (sum_multiset_count l.parts).symm.trans l.parts_sum
    · intro a ha
      exact Nat.le_mul_of_pos_left _ (l.parts_pos (Multiset.mem_toFinset.mp ha))
  simp_rw [smul_pow, smul_smul, div_pow, ← pow_mul, one_div_mul_eq_div, div_div]
  rw [prod_smul, prod_div_distrib, prod_pow_eq_pow_sum, hsign, prod_multiset_map_count]
  simp only [Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]

end exp_signedPowerSumSeries_eq_sum_partitions

/-- **Exponential of a power-sum series restricted to a set of degrees.** Let $\sigma$ be a finite
set of variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $p_s = \sum_{i \in \sigma} x_i^s$
be the $s$-th power sum. Let $S$ be a set of natural numbers and let
$P_S(t) = \sum_{s \in S,\ s \ge 1} \frac{(-1)^{s-1}}{s} p_s t^s$. For a partition $\lambda$ of
$n$ with parts $\lambda_1, \dots, \lambda_\ell$, write
$p_\lambda = p_{\lambda_1} \cdots p_{\lambda_\ell}$, $\varepsilon_\lambda = (-1)^{n - \ell}$ and
$z_\lambda = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts equal to $a$ and the
product runs over the distinct parts $a$. Then, as formal power series in $t$ with coefficients
in $\mathbb{Q}[x_i : i \in \sigma]$, $\exp P_S(t) = \sum_{n \ge 0} c_n t^n$, where $c_n$ is the
sum of $\varepsilon_\lambda p_\lambda / z_\lambda$ over the partitions $\lambda$ of $n$ all of
whose parts lie in $S$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 19 (`integers-2024-A46-prop-19`). -/
public theorem exp_signedPowerSumSeries_eq_sum_partitions (σ : Type*) [Fintype σ]
    (S : Set ℕ) [DecidablePred (· ∈ S)] :
    (PowerSeries.subst (PowerSeries.mk fun s => if s ∈ S ∧ s ≠ 0 then
        ((-1 : ℚ) ^ (s - 1) / s) • MvPolynomial.psum σ ℚ s else 0) (PowerSeries.exp ℚ) :
        PowerSeries (MvPolynomial σ ℚ)) =
      PowerSeries.mk fun n => ∑ l : n.Partition with ∀ a ∈ l.parts, a ∈ S,
        ((-1 : ℚ) ^ (n - Multiset.card l.parts) /
          ((l.parts.toFinset.prod fun a => a ^ l.parts.count a * (l.parts.count a).factorial :
            ℕ) : ℚ)) • (l.parts.map (MvPolynomial.psum σ ℚ)).prod := by
  let : TopologicalSpace (MvPolynomial σ ℚ) := ⊥
  let : DiscreteTopology (MvPolynomial σ ℚ) := ⟨rfl⟩
  let c (i : ℕ) := if i ∈ S then ((-1 : ℚ) ^ (i - 1) / i) • MvPolynomial.psum σ ℚ i else 0
  have hseries : (PowerSeries.mk fun i => if i ∈ S ∧ i ≠ 0 then
      ((-1 : ℚ) ^ (i - 1) / i) • MvPolynomial.psum σ ℚ i else 0) =
      PowerSeries.mk fun i ↦ if i = 0 then 0 else c i := by
    ext i
    by_cases hi : i = 0 <;> simp [hi, c]
  rw [hseries, exp_signedPowerSumSeries_eq_sum_partitions.subst_exp_eq_genFun]
  apply PowerSeries.ext
  intro n
  rw [Nat.Partition.coeff_genFun, PowerSeries.coeff_mk, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  by_cases hl : ∀ a ∈ l.parts, a ∈ S
  · rw [ite_eq_left hl]
    calc
      _ = ∏ a ∈ l.parts.toFinset, (1 / ((l.parts.count a).factorial : ℚ)) •
          (((-1 : ℚ) ^ (a - 1) / a) • MvPolynomial.psum σ ℚ a) ^ l.parts.count a := by
        refine prod_congr rfl fun a ha ↦ ?_
        simp only [c, ite_eq_left (hl a (Multiset.mem_toFinset.mp ha))]
      _ = _ := exp_signedPowerSumSeries_eq_sum_partitions.prod_weights l _
  · rw [ite_eq_right hl]
    push Not at hl
    obtain ⟨a, ha, haS⟩ := hl
    refine prod_eq_zero (Multiset.mem_toFinset.mpr ha) ?_
    simp [c, haS, Multiset.count_ne_zero.mpr ha]

private theorem subst_exp_rescale_log {A : Type*} [CommRing A] [Algebra ℚ A] (a : A) :
    (exp ℚ).subst (rescale a (log A)) = 1 + C a * X := by
  have hlog : (exp ℚ).subst (log A) = 1 + (X : PowerSeries A) := calc
    _ = PowerSeries.subst (log A) ((exp ℚ).subst (X : PowerSeries A)) := by
      rw [subst_comp_subst_apply HasSubst.X' HasSubst.log, subst_X HasSubst.log]
    _ = _ := by rw [← map_algebraMap_eq_subst_X, map_exp, subst_exp_log]
  calc
    _ = rescale a ((exp ℚ).subst (log A)) := by
      rw [rescale_eq_subst, rescale_eq_subst,
        subst_comp_subst_apply HasSubst.log (HasSubst.smul_X' a)]
    _ = _ := by rw [hlog, map_add, map_one, rescale_X]

private theorem exp_signedPowerSumSeries_eq_prod (σ : Type*) [Fintype σ] :
    (exp ℚ).subst (PowerSeries.mk fun n ↦ if n ≠ 0 then
      ((-1 : ℚ) ^ (n - 1) / n) • MvPolynomial.psum σ ℚ n else 0) =
        ∏ i : σ, (1 + C (MvPolynomial.X i : MvPolynomial σ ℚ) * X) := by
  let L (i : σ) := rescale (MvPolynomial.X i) (log (MvPolynomial σ ℚ))
  have hL (i : σ) : constantCoeff (L i) = 0 := by
    simp [L, ← coeff_zero_eq_constantCoeff]
  -- Coefficientwise, the signed power-sum series is the sum of the individual logarithms.
  have hsum : (PowerSeries.mk fun n ↦ if n ≠ 0 then
      ((-1 : ℚ) ^ (n - 1) / n) • MvPolynomial.psum σ ℚ n else 0) = ∑ i, L i := by
    apply PowerSeries.ext
    intro n
    by_cases hn : n = 0
    · simp [hn, map_sum, L]
    have hsign : (-1 : ℚ) ^ (n + 1) = (-1 : ℚ) ^ (n - 1) := by
      rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
      norm_num
    simp only [coeff_mk, hn, ne_eq, not_false_eq_true, ↓reduceIte, map_sum, L, coeff_rescale,
      coeff_log, hsign, MvPolynomial.psum]
    rw [Finset.smul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  rw [hsum, exp_signedPowerSumSeries_eq_sum_partitions.subst_exp_sum L hL]
  exact prod_congr rfl fun i _ ↦ subst_exp_rescale_log (MvPolynomial.X i)

private theorem coeff_prod_one_add_X (σ : Type*) [Fintype σ] (n : ℕ) :
    coeff n (∏ i : σ, (1 + C (MvPolynomial.X i : MvPolynomial σ ℚ) * X)) =
      MvPolynomial.esymm σ ℚ n := by
  rw [prod_one_add, map_sum, MvPolynomial.esymm, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [prod_mul_distrib, ← map_prod, prod_const, coeff_C_mul_X_pow]
  simp only [eq_comm (a := n)]

/-- **The generating function of the elementary symmetric polynomials.** Let $\sigma$ be a finite
set of variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $e_k$ be the $k$-th elementary
symmetric polynomial and $p_n = \sum_{i \in \sigma} x_i^n$ the $n$-th power sum. Then, as formal
power series in $t$ with coefficients in $\mathbb{Q}[x_i : i \in \sigma]$,
$$\sum_{k \ge 0} e_k t^k = \exp\Big(\sum_{n \ge 1} \frac{(-1)^{n-1}}{n} p_n t^n\Big).$$

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 20 (`integers-2024-A46-prop-20`). -/
public theorem exp_signedPowerSumSeries_eq_esymmSeries (σ : Type*) [Fintype σ] :
    (PowerSeries.subst (PowerSeries.mk fun n => if n = 0 then 0 else
        ((-1 : ℚ) ^ (n - 1) / n) • MvPolynomial.psum σ ℚ n) (PowerSeries.exp ℚ) :
        PowerSeries (MvPolynomial σ ℚ)) =
      PowerSeries.mk fun k => MvPolynomial.esymm σ ℚ k := by
  have hprod := exp_signedPowerSumSeries_eq_prod σ
  simp only [ne_eq, ite_not] at hprod
  rw [hprod]
  apply PowerSeries.ext
  intro k
  rw [coeff_prod_one_add_X, coeff_mk]

/-- **Elementary symmetric polynomials in terms of power sums.** Let $\sigma$ be a finite set of
variables, and in $\mathbb{Q}[x_i : i \in \sigma]$ let $e_n$ be the $n$-th elementary symmetric
polynomial and $p_k = \sum_{i \in \sigma} x_i^k$ the $k$-th power sum. For a partition $\lambda$
of $n$ with parts $\lambda_1, \dots, \lambda_\ell$, write
$p_\lambda = p_{\lambda_1} \cdots p_{\lambda_\ell}$, $\varepsilon_\lambda = (-1)^{n - \ell}$ and
$z_\lambda = \prod_a a^{r_a} \, r_a!$, where $r_a$ is the number of parts equal to $a$ and the
product runs over the distinct parts $a$. Then for every $n \ge 0$,
$$e_n = \sum_{\lambda \vdash n} \frac{\varepsilon_\lambda}{z_\lambda} \, p_\lambda.$$

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 21 (`integers-2024-A46-cor-21`). -/
public theorem esymm_eq_sum_partitions (σ : Type*) [Fintype σ] (n : ℕ) :
    MvPolynomial.esymm σ ℚ n = ∑ l : n.Partition,
      ((-1 : ℚ) ^ (n - Multiset.card l.parts) /
        ((l.parts.toFinset.prod fun a => a ^ l.parts.count a * (l.parts.count a).factorial :
          ℕ) : ℚ)) • (l.parts.map (MvPolynomial.psum σ ℚ)).prod := by
  have h := congrArg (coeff (R := MvPolynomial σ ℚ) n)
    (exp_signedPowerSumSeries_eq_sum_partitions σ Set.univ)
  simpa only [Set.mem_univ, true_and, implies_true, filter_true, ne_eq, ite_not,
    exp_signedPowerSumSeries_eq_esymmSeries, coeff_mk] using h

end MetaMathlibExt

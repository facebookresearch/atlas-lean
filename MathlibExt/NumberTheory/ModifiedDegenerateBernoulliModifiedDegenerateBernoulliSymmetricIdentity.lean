/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulli
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.Tuple.NatAntidiagonal


/-!
# Symmetric identity for modified degenerate Bernoulli polynomials

We prove the symmetric identity with arbitrary complex weights and arguments from Qi-Peng Su
and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli Polynomials*, Journal of
Integer Sequences 27 (2024), Article 24.5.4, Theorem 1, equation (5).
-/

open Finset
namespace MetaMathlibExt
namespace modifiedDegenerateBernoulli_symmetric

private noncomputable def exponential {A : Type*} [CommRing A] [Algebra ℚ A] (a : A) :
    PowerSeries A := PowerSeries.rescale a (PowerSeries.exp A)

private noncomputable def bernoulliSeries {A : Type*} [CommRing A] [Algebra ℚ A]
    (a x : A) : PowerSeries A :=
  PowerSeries.rescale a (PowerSeries.mk fun k =>
    Polynomial.aeval x ((1 / k.factorial : ℚ) • Polynomial.bernoulli k))

private theorem series_mul {A : Type*} [CommRing A] [Algebra ℚ A] (a x : A) :
    bernoulliSeries a x * (exponential a - 1) =
      PowerSeries.C a * PowerSeries.X * exponential (a * x) := by
  simpa only [bernoulliSeries, exponential, map_mul, map_sub, map_one,
    PowerSeries.rescale_X, PowerSeries.rescale_rescale, mul_comm x a] using
    congrArg (PowerSeries.rescale a) (Polynomial.bernoulli_generating_function x)

private theorem exponential_add {A : Type*} [CommRing A] [Algebra ℚ A] (a b : A) :
    exponential (a + b) = exponential a * exponential b := by
  simp only [exponential, PowerSeries.exp_mul_exp_eq_exp_add]

private theorem exponential_sum {A : Type*} [CommRing A] [Algebra ℚ A]
    {ι : Type*} (s : Finset ι) (a : ι → A) :
    exponential (∑ i ∈ s, a i) = ∏ i ∈ s, exponential (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [exponential, PowerSeries.rescale_zero]
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi, exponential,
      ← PowerSeries.exp_mul_exp_eq_exp_add, ← exponential, ← exponential, ih]

private theorem exponential_telescope {A : Type*} [CommRing A] [Algebra ℚ A]
    (m : ℕ) (a : Fin m → A) :
    ∑ i, (exponential (a i) - 1) * ∏ j ∈ univ.filter (i < ·), exponential (a j) =
      exponential (∑ i, a i) - 1 := by
  have h := prod_add_ordered (univ : Finset (Fin m))
    (fun i => exponential (a i)) (fun i => 1 - exponential (a i))
  simp only [add_sub_cancel, prod_const_one, mul_one] at h
  rw [exponential_sum]
  have hneg : ∑ i, (1 - exponential (a i)) * ∏ j ∈ univ.filter (i < ·), exponential (a j) =
      -∑ i, (exponential (a i) - 1) * ∏ j ∈ univ.filter (i < ·), exponential (a j) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hneg] at h
  linear_combination h

private theorem series_product {A : Type*} [CommRing A] [Algebra ℚ A]
    {ι : Type*} (s : Finset ι) (a x : ι → A) :
    (∏ i ∈ s, bernoulliSeries (a i) (x i)) * (∏ i ∈ s, (exponential (a i) - 1)) =
      PowerSeries.C (∏ i ∈ s, a i) * PowerSeries.X ^ s.card *
        exponential (∑ i ∈ s, a i * x i) := by
  rw [← prod_mul_distrib]
  simp_rw [series_mul]
  rw [prod_mul_distrib, prod_mul_distrib, ← map_prod, prod_const, ← exponential_sum]

private theorem series_identity {A : Type*} [CommRing A] [Algebra ℚ A] [IsDomain A]
    (m : ℕ) (a x : Fin m → A) (a₀ : A) (ha₀ : a₀ ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hsum : a₀ + ∑ i, a i = 0) :
    PowerSeries.C a₀ * (∏ j, bernoulliSeries (a j) (x j)) +
      ∑ i, PowerSeries.C (a i) * (bernoulliSeries a₀ (1 - x i) *
        ∏ j ∈ univ.erase i,
          bernoulliSeries (a j) (x j - x i + if i < j then 1 else 0)) = 0 := by
  classical
  let D := (exponential a₀ - 1) * ∏ j, (exponential (a j) - 1)
  have hden (u : A) (hu : u ≠ 0) : exponential u - 1 ≠ 0 := by
    intro h
    apply hu
    simpa [exponential, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
      PowerSeries.coeff_one] using congrArg (PowerSeries.coeff 1) h
  have hD : D ≠ 0 := mul_ne_zero (hden a₀ ha₀) (prod_ne_zero_iff.mpr fun i _ => hden (a i) (ha i))
  have first : (PowerSeries.C a₀ * ∏ j, bernoulliSeries (a j) (x j)) * D =
      (PowerSeries.C (a₀ * ∏ j, a j) * PowerSeries.X ^ m) *
        (exponential (∑ j, a j * x j) * (exponential a₀ - 1)) := by
    dsimp only [D]
    calc
      _ = PowerSeries.C a₀ *
          ((∏ j, bernoulliSeries (a j) (x j)) * ∏ j, (exponential (a j) - 1)) *
          (exponential a₀ - 1) := by ring
      _ = _ := by rw [series_product, card_univ, Fintype.card_fin, map_mul]; ring
  have other (i : Fin m) :
      (PowerSeries.C (a i) * (bernoulliSeries a₀ (1 - x i) *
        ∏ j ∈ univ.erase i, bernoulliSeries (a j)
          (x j - x i + if i < j then 1 else 0))) * D =
      (PowerSeries.C (a₀ * ∏ j, a j) * PowerSeries.X ^ m) *
        (exponential (∑ j, a j * x j + a₀ + ∑ j ∈ univ.filter (i < ·), a j) *
          (exponential (a i) - 1)) := by
    dsimp only [D]
    rw [← mul_prod_erase _ _ (mem_univ i)]
    have hp := series_product (univ.erase i) a
      (fun j => x j - x i + if i < j then 1 else 0)
    have hc : (univ.erase i).card + 1 = m := by
      simpa using card_erase_add_one (s := univ) (mem_univ i)
    have he : a₀ * (1 - x i) + ∑ j ∈ univ.erase i,
        a j * (x j - x i + if i < j then 1 else 0) =
        ∑ j, a j * x j + a₀ + ∑ j ∈ univ.filter (i < ·), a j := by
      have hshift : ∑ j ∈ univ.erase i, a j * (if i < j then 1 else 0) =
          ∑ j ∈ univ.filter (i < ·), a j := by
        simp only [mul_ite, mul_one, mul_zero, ← sum_filter]
        congr 1
        ext j
        simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨ne_of_gt h, h⟩
      simp_rw [mul_add, mul_sub]
      rw [sum_add_distrib, sum_sub_distrib, hshift, ← sum_mul]
      rw [← add_sum_erase _ _ (mem_univ i)] at hsum
      rw [← add_sum_erase _ _ (mem_univ i)]
      linear_combination -x i * hsum
    calc
      _ = PowerSeries.C (a i) *
          (bernoulliSeries a₀ (1 - x i) * (exponential a₀ - 1)) *
          ((∏ j ∈ univ.erase i, bernoulliSeries (a j)
            (x j - x i + if i < j then 1 else 0)) *
              ∏ j ∈ univ.erase i, (exponential (a j) - 1)) *
          (exponential (a i) - 1) := by ring
      _ = (PowerSeries.C (a₀ * (a i * ∏ j ∈ univ.erase i, a j)) *
          PowerSeries.X ^ ((univ.erase i).card + 1)) *
          (exponential (a₀ * (1 - x i) + ∑ j ∈ univ.erase i,
            a j * (x j - x i + if i < j then 1 else 0)) *
              (exponential (a i) - 1)) := by
        rw [series_mul, hp, map_mul, map_mul, pow_add, pow_one, exponential_add]
        ring
      _ = _ := by rw [hc, mul_prod_erase _ _ (mem_univ i), he]
  apply mul_right_cancel₀ hD
  rw [zero_mul, add_mul, sum_mul, first]
  simp_rw [other]
  rw [← mul_sum, ← mul_add]
  have he : exponential a₀ * exponential (∑ j, a j) = 1 := by
    rw [← exponential_add, hsum]
    simp [exponential, PowerSeries.rescale_zero]
  have ht := exponential_telescope m a
  have hs : ∑ i, exponential (∑ j, a j * x j + a₀ + ∑ j ∈ univ.filter (i < ·), a j) *
        (exponential (a i) - 1) =
      exponential (∑ j, a j * x j) * exponential a₀ *
        (exponential (∑ j, a j) - 1) := by
    rw [← ht, mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [exponential_add, exponential_sum]
    ring
  rw [hs]
  linear_combination
    (PowerSeries.C (a₀ * ∏ j, a j) * PowerSeries.X ^ m *
      exponential (∑ j, a j * x j)) * he

private theorem coefficient_product {A : Type*} [CommRing A] (m n : ℕ)
    (f : Fin m → PowerSeries A) :
    PowerSeries.coeff n (∏ j, f j) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m n, ∏ j, PowerSeries.coeff (k j) (f j) := by
  classical
  rw [PowerSeries.coeff_prod]
  apply sum_equiv Finsupp.equivFunOnFinite
  · intro d
    simp [mem_finsuppAntidiag, Finset.Nat.mem_antidiagonalTuple]
  · intro d _
    rfl

private def index (m : ℕ) (i : Fin (m + 1)) : Fin m ↪ Fin (m + 1) :=
  ⟨fun j => Equiv.swap 0 i j.succ, (Equiv.swap 0 i).injective.comp (Fin.succ_injective m)⟩

private theorem index_ne (m : ℕ) (i : Fin (m + 1)) (j : Fin m) : index m i j ≠ i := by
  change Equiv.swap 0 i j.succ ≠ i
  intro h
  have hh := congrArg (Equiv.swap 0 i) h
  simp at hh

private theorem index_range (m : ℕ) (i : Fin (m + 1)) (v : Fin (m + 1))
    (hv : v ≠ i) : ∃ j, index m i j = v := by
  have h : Equiv.swap 0 i v ≠ 0 := by
    intro h
    apply hv
    have hh := congrArg (Equiv.swap 0 i) h
    simpa using hh
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr h
  refine ⟨j, ?_⟩
  change Equiv.swap 0 i j.succ = v
  rw [hj]
  simp

private theorem product_index {A : Type*} [CommMonoid A] (m : ℕ)
    (i : Fin (m + 1)) (f : Fin (m + 1) → A) :
    ∏ j, f (index m i j) = ∏ v ∈ univ.erase i, f v := by
  apply prod_bij (fun j _ => index m i j)
  · intro j _
    exact mem_erase.mpr ⟨index_ne m i j, mem_univ _⟩
  · intro j _ k _ h
    exact (index m i).injective h
  · intro v hv
    obtain ⟨j, hj⟩ := index_range m i v (ne_of_mem_erase hv)
    exact ⟨j, mem_univ _, hj⟩
  · intro j _
    rfl
open MvPolynomial

private noncomputable def topTerm (m n : ℕ) (i : Fin (m + 1))
    (y : Fin (m + 1) → ℂ) : MvPolynomial (Fin (m + 1)) ℂ :=
  ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
    C (∏ j, Polynomial.aeval (y (index m i j) - y i + if i < index m i j then 1 else 0)
      ((1 / (k j).factorial : ℚ) • Polynomial.bernoulli (k j))) *
        (X i * ∏ j, X (index m i j) ^ k j)

private theorem topTerm_homogeneous (m n : ℕ) (i : Fin (m + 1))
    (y : Fin (m + 1) → ℂ) : (topTerm m n i y).IsHomogeneous (n + 1) := by
  apply IsHomogeneous.sum
  intro k hk
  have hprod : (∏ j, (X (index m i j) : MvPolynomial (Fin (m + 1)) ℂ) ^ k j).IsHomogeneous
      (∑ j, k j) := by
    apply IsHomogeneous.prod
    intro j _
    simpa using (isHomogeneous_X ℂ (index m i j)).pow (k j)
  have h := (isHomogeneous_X ℂ i).mul hprod
  rw [Finset.Nat.mem_antidiagonalTuple.mp hk] at h
  apply IsHomogeneous.C_mul
  simpa only [Nat.add_comm 1 n] using h

private theorem aeval_topTerm (m n : ℕ) (i : Fin (m + 1))
    (y : Fin (m + 1) → ℂ) (a : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ) :
    aeval a (topTerm m n i y) = PowerSeries.coeff n
      (PowerSeries.C (a i) * ∏ j,
        bernoulliSeries (a (index m i j))
          (C (y (index m i j) - y i + if i < index m i j then 1 else 0))) := by
  have hC (u : ℂ) (p : Polynomial ℚ) :
      Polynomial.aeval (C u : MvPolynomial (Fin (m + 1)) ℂ) p =
        C (Polynomial.aeval u p) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℂ _) u p
  rw [PowerSeries.coeff_C_mul, coefficient_product, mul_sum]
  simp only [topTerm, map_sum, map_mul, map_prod, map_pow, aeval_C, aeval_X,
    bernoulliSeries, PowerSeries.coeff_rescale, PowerSeries.coeff_mk, hC]
  apply sum_congr rfl
  intro k _
  rw [prod_mul_distrib]
  simp only [← C_eq_algebraMap]
  ring

private theorem index_zero (m : ℕ) (j : Fin m) : index m 0 j = j.succ := by
  simp [index]

private theorem index_succ_same (m : ℕ) (i : Fin m) : index m i.succ i = 0 := by
  simp [index]

private theorem index_succ_ne (m : ℕ) (i j : Fin m) (h : j ≠ i) :
    index m i.succ j = j.succ := by
  apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j)
  exact fun hh => h (Fin.succ_injective m hh)

private theorem aeval_topTerm_zero (m n : ℕ) (x : Fin m → ℂ)
    (a : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ) :
    aeval a (topTerm m n 0 (Fin.cons (1 : ℂ) x)) = PowerSeries.coeff n
      (PowerSeries.C (a 0) * ∏ j, bernoulliSeries (a j.succ) (C (x j))) := by
  rw [aeval_topTerm]
  simp [index_zero]

private theorem aeval_topTerm_succ (m n : ℕ) (i : Fin m) (x : Fin m → ℂ)
    (a : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ) :
    aeval a (topTerm m n i.succ (Fin.cons (1 : ℂ) x)) = PowerSeries.coeff n
      (PowerSeries.C (a i.succ) * (bernoulliSeries (a 0) (C (1 - x i)) *
        ∏ j ∈ univ.erase i, bernoulliSeries (a j.succ)
          (C (x j - x i + if i < j then 1 else 0)))) := by
  rw [aeval_topTerm]
  apply congrArg (PowerSeries.coeff n)
  apply congrArg (PowerSeries.C (a i.succ) * ·)
  rw [← mul_prod_erase _ _ (mem_univ i)]
  apply congrArg₂ (· * ·)
  · simp [index_succ_same]
  · apply prod_congr rfl
    intro j hj
    simp [index_succ_ne m i j (ne_of_mem_erase hj)]

private theorem linear_dvd_of_subst_eq_zero (m : ℕ)
    (p : MvPolynomial (Fin (m + 1)) ℂ)
    (hp : aeval (Fin.cons (-∑ j : Fin m, (X j.succ : MvPolynomial (Fin (m + 1)) ℂ))
      (fun j => X j.succ)) p = 0) :
    (∑ v, X v : MvPolynomial (Fin (m + 1)) ℂ) ∣ p := by
  let L : MvPolynomial (Fin (m + 1)) ℂ := ∑ v, X v
  let I := Ideal.span {L}
  let q := Ideal.Quotient.mk I
  have hL : q L = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hq : q.comp
      (aeval (Fin.cons (-∑ j : Fin m, X j.succ) (fun j => X j.succ))).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      refine Fin.cases ?_ (fun j => ?_) v
      · change q (aeval (Fin.cons (-∑ j : Fin m, X j.succ) (fun j => X j.succ)) (X 0)) = q (X 0)
        simp only [aeval_X, Fin.cons_zero, map_neg, map_sum]
        have hsum : q (X 0) + ∑ j : Fin m, q (X j.succ) = 0 := by
          simpa only [L, Fin.sum_univ_succ, map_add, map_sum] using hL
        linear_combination -hsum
      · simp
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q p = 0
  rw [← DFunLike.congr_fun hq p]
  exact (congrArg q hp).trans (map_zero q)

private theorem sum_top_dvd (m n : ℕ) (hm : 1 ≤ m) (x : Fin m → ℂ) :
    (∑ v, X v : MvPolynomial (Fin (m + 1)) ℂ) ∣ ∑ i, topTerm m n i (Fin.cons (1 : ℂ) x) := by
  apply linear_dvd_of_subst_eq_zero
  rw [map_sum, Fin.sum_univ_succ, aeval_topTerm_zero]
  simp_rw [aeval_topTerm_succ]
  let a : Fin m → MvPolynomial (Fin (m + 1)) ℂ := fun j => X j.succ
  have hne : -∑ j, a j ≠ 0 := by
    intro h
    have hh := congrArg (MvPolynomial.eval fun v =>
      if v = (⟨0, hm⟩ : Fin m).succ then (1 : ℂ) else 0) h
    simp only [map_neg, map_sum, eval_X, map_zero, a] at hh
    simp only [Fin.succ_inj, sum_ite_eq', mem_univ, ite_true] at hh
    norm_num at hh
  have h := series_identity m a (fun j => C (x j)) (-∑ j, a j) hne
    (fun j => X_ne_zero j.succ) (by simp)
  have hh := congrArg (PowerSeries.coeff n) h
  simp only [map_add, map_sum, map_zero] at hh
  convert hh using 1; simp [a, map_add, map_sub, map_one]

private noncomputable def falling (m : ℕ) (a : Fin (m + 1) → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ fun d : Fin (m + 1) →₀ ℕ =>
    ∏ i, (descPochhammer ℂ (d i)).eval (a i)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem falling_monomial (m : ℕ) (a : Fin (m + 1) → ℂ)
    (d : Fin (m + 1) →₀ ℕ) (c : ℂ) :
    falling m a (monomial d c) = c * ∏ i, (descPochhammer ℂ (d i)).eval (a i) := by
  simp only [falling, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply, ← single_eq_monomial, AddMonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single, smul_eq_mul]

private theorem falling_step (m : ℕ) (a : Fin (m + 1) → ℂ)
    (d : Fin (m + 1) →₀ ℕ) (c : ℂ) (i : Fin (m + 1)) :
    falling m a (X i * monomial d c) = falling m a (monomial d c) * (a i - d i) := by
  rw [mul_comm, ← pow_one (X i), ← monomial_add_single, falling_monomial, falling_monomial]
  rw [← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase _ _ (mem_univ i)]
  have h : ∏ j ∈ univ.erase i,
      (descPochhammer ℂ ((d + Finsupp.single i 1 : Fin (m + 1) →₀ ℕ) j)).eval (a j) =
      ∏ j ∈ univ.erase i, (descPochhammer ℂ (d j)).eval (a j) := by
    apply prod_congr rfl
    intro j hj
    simp [Finsupp.single_eq_of_ne (ne_of_mem_erase hj)]
  rw [h, Finsupp.add_apply, Finsupp.single_eq_same, descPochhammer_succ_eval]
  ring

private theorem falling_component_mul (m n : ℕ) (a : Fin (m + 1) → ℂ)
    (ha : ∑ i, a i = n) (p : MvPolynomial (Fin (m + 1)) ℂ) :
    falling m a (homogeneousComponent (n + 1) ((∑ i, X i) * p)) = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have h : ((∑ i, X i) * monomial d c : MvPolynomial (Fin (m + 1)) ℂ).IsHomogeneous
        (d.degree + 1) := by
      have hL : (∑ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) ℂ)).IsHomogeneous 1 := by
        apply IsHomogeneous.sum
        intro i _
        exact isHomogeneous_X ℂ i
      have hd : (monomial d c : MvPolynomial (Fin (m + 1)) ℂ).IsHomogeneous d.degree :=
        isHomogeneous_monomial c rfl
      simpa only [Nat.add_comm 1 d.degree] using hL.mul hd
    rw [homogeneousComponent_of_mem h]
    by_cases hd : d.degree = n
    · rw [ite_eq_left (by omega), sum_mul, map_sum]
      simp_rw [falling_step, ← mul_sum]
      have hdeg : (∑ i, (d i : ℂ)) = n := by
        rw [Finsupp.degree_eq_sum] at hd
        exact_mod_cast hd
      rw [sum_sub_distrib, ha, hdeg, sub_self, mul_zero]
    · rw [ite_eq_right (by omega), map_zero]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, add_zero]

private theorem falling_product (m : ℕ) (a : Fin (m + 1) → ℂ) (i : Fin (m + 1))
    (k : Fin m → ℕ) (c : ℂ) :
    falling m a (C c * (X i * ∏ j, X (index m i j) ^ k j)) =
      c * a i * ∏ j, (descPochhammer ℂ (k j)).eval (a (index m i j)) := by
  classical
  let d : Fin (m + 1) →₀ ℕ := ∑ j, Finsupp.single (index m i j) (k j)
  have di : d i = 0 := by
    simp [d, Finset.sum_apply, index_ne]
  have dj (j : Fin m) : d (index m i j) = k j := by
    simp [d, Finset.sum_apply, Finsupp.single_apply, (index m i).injective.eq_iff]
  have hp : (∏ j, X (index m i j) ^ k j : MvPolynomial (Fin (m + 1)) ℂ) = monomial d 1 := by
    simp only [X_pow_eq_monomial, d, monomial_sum_one]
  rw [hp, ← mul_assoc, mul_comm (C c), mul_assoc, C_mul_monomial, mul_one,
    falling_step, falling_monomial, di, Nat.cast_zero, sub_zero]
  rw [← mul_prod_erase _ _ (mem_univ i), di]
  simp only [descPochhammer_zero, Polynomial.eval_one, one_mul]
  rw [← product_index]
  simp_rw [dj]
  ring

private theorem desc_eq_choose (a : ℂ) (k : ℕ) :
    (descPochhammer ℂ k).eval a = (k.factorial : ℂ) * Ring.choose a k := by
  rw [← descPochhammer_map (algebraMap ℤ ℂ), Polynomial.eval_map,
    ← Polynomial.aeval_def, Polynomial.aeval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

private theorem falling_topTerm (m n : ℕ) (a y : Fin (m + 1) → ℂ)
    (i : Fin (m + 1)) :
    falling m a (topTerm m n i y) = a i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
      ∏ j, Ring.choose (a (index m i j)) (k j) *
        Polynomial.aeval (y (index m i j) - y i + if i < index m i j then 1 else 0)
          (Polynomial.bernoulli (k j)) := by
  rw [topTerm, map_sum, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [falling_product]
  simp_rw [desc_eq_choose]
  simp only [map_smul, Rat.smul_def, one_div, Rat.cast_inv, Rat.cast_natCast]
  rw [mul_right_comm, ← prod_mul_distrib, mul_comm _ (a i)]
  apply congrArg (a i * ·)
  apply prod_congr rfl
  intro j _
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k j))]

private theorem ordinary_identity (m n : ℕ) (hm : 1 ≤ m)
    (a y : Fin (m + 1) → ℂ) (ha : ∑ i, a i = n) (hy : y 0 = 1) :
    ∑ i, a i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
      ∏ j, Ring.choose (a (index m i j)) (k j) *
        Polynomial.aeval (y (index m i j) - y i + if i < index m i j then 1 else 0)
          (Polynomial.bernoulli (k j)) = 0 := by
  have hy' : y = Fin.cons 1 (fun j => y j.succ) := by
    ext v
    refine Fin.cases ?_ (fun j => ?_) v <;> simp [hy]
  obtain ⟨p, hp⟩ := sum_top_dvd m n hm (fun j => y j.succ)
  have hhom : (∑ i, topTerm m n i (Fin.cons 1 (fun j => y j.succ))).IsHomogeneous (n + 1) := by
    apply IsHomogeneous.sum
    intro i _
    exact topTerm_homogeneous m n i _
  have h := falling_component_mul m n a ha p
  rw [← hp, homogeneousComponent_eq_self hhom, map_sum] at h
  simp_rw [← hy', falling_topTerm] at h
  exact h

private theorem ordinary_symmetric (m n : ℕ) (hm : 1 ≤ m) (r x : Fin m → ℂ) :
    ((n : ℂ) - ∑ j, r j) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * Polynomial.aeval (x j) (Polynomial.bernoulli (k j)) =
      -∑ i, r i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) *
          Polynomial.aeval (1 - x i) (Polynomial.bernoulli (k i)) *
            ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
              Polynomial.aeval (x j - x i + if i < j then 1 else 0)
                (Polynomial.bernoulli (k j)) := by
  let a : Fin (m + 1) → ℂ := Fin.cons ((n : ℂ) - ∑ j, r j) r
  let y : Fin (m + 1) → ℂ := Fin.cons 1 x
  have h := ordinary_identity m n hm a y
    (by simp [a, Fin.sum_univ_succ]) (by simp [y])
  rw [Fin.sum_univ_succ] at h
  have hz : ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
      ∏ j, Ring.choose (a (index m 0 j)) (k j) *
        Polynomial.aeval (y (index m 0 j) - y 0 +
          if (0 : Fin (m + 1)) < index m 0 j then 1 else 0) (Polynomial.bernoulli (k j)) =
        ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
          ∏ j, Ring.choose (r j) (k j) * Polynomial.aeval (x j) (Polynomial.bernoulli (k j)) := by
    simp [index_zero, a, y]
  have hs (i : Fin m) : ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
      ∏ j, Ring.choose (a (index m i.succ j)) (k j) *
        Polynomial.aeval (y (index m i.succ j) - y i.succ +
          if i.succ < index m i.succ j then 1 else 0) (Polynomial.bernoulli (k j)) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) *
          Polynomial.aeval (1 - x i) (Polynomial.bernoulli (k i)) *
            ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
              Polynomial.aeval (x j - x i + if i < j then 1 else 0)
                (Polynomial.bernoulli (k j)) := by
    apply sum_congr rfl
    intro k _
    rw [← mul_prod_erase _ _ (mem_univ i)]
    apply congrArg₂ (· * ·)
    · simp [index_succ_same, a, y]
    · apply prod_congr rfl
      intro j hj
      simp [index_succ_ne m i j (ne_of_mem_erase hj), a, y]
  rw [hz] at h
  simp_rw [hs] at h
  simpa only [a, Fin.cons_zero, Fin.cons_succ] using eq_neg_of_add_eq_zero_left h

private theorem scale_nonzero (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    Complex.log (1 + lam) / lam ≠ 0 := by
  apply div_ne_zero _ hlam
  intro hz
  have h := Complex.exp_log (x := 1 + lam) (by intro h; apply hlam1; linear_combination h)
  rw [hz, Complex.exp_zero] at h
  exact hlam (by linear_combination -h)

private theorem product_zpow {ι : Type*} (s : Finset ι) (c : ℂ) (hc : c ≠ 0)
    (e : ι → ℤ) : ∏ j ∈ s, c ^ e j = c ^ (∑ j ∈ s, e j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ hc]

private theorem scale_product {ι : Type*} (s : Finset ι) (lam : ℂ)
    (hc : Complex.log (1 + lam) / lam ≠ 0) (w x : ι → ℂ) (k : ι → ℕ) :
    ∏ j ∈ s, w j * modifiedDegenerateBernoulli lam (k j) (x j) =
      (Complex.log (1 + lam) / lam) ^ (∑ j ∈ s, ((k j : ℤ) - 1)) *
        ∏ j ∈ s, w j * Polynomial.aeval (x j) (Polynomial.bernoulli (k j)) := by
  rw [← product_zpow s _ hc, ← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  rw [modifiedDegenerateBernoulli]
  ring

private theorem total_exponent (m n : ℕ) (k : Fin m → ℕ)
    (hk : k ∈ Finset.Nat.antidiagonalTuple m n) :
    (∑ j, ((k j : ℤ) - 1)) = (n : ℤ) - m := by
  rw [sum_sub_distrib, ← Nat.cast_sum, Finset.Nat.mem_antidiagonalTuple.mp hk]
  simp

private theorem scaled_identity (m n : ℕ) (hm : 1 ≤ m) (r x : Fin m → ℂ)
    (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) - ∑ j, r j) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * modifiedDegenerateBernoulli lam (k j) (x j) =
      -∑ i, r i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) * modifiedDegenerateBernoulli lam (k i) (1 - x i) *
          ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0) := by
  let c := Complex.log (1 + lam) / lam
  have hc : c ≠ 0 := scale_nonzero lam hlam hlam1
  have hfirst : ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * modifiedDegenerateBernoulli lam (k j) (x j) =
      c ^ ((n : ℤ) - m) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * Polynomial.aeval (x j) (Polynomial.bernoulli (k j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [scale_product _ lam hc, total_exponent m n k hk]
  have hother (i : Fin m) : ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) * modifiedDegenerateBernoulli lam (k i) (1 - x i) *
          ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0) =
      c ^ ((n : ℤ) - m) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) *
          Polynomial.aeval (1 - x i) (Polynomial.bernoulli (k i)) *
            ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
              Polynomial.aeval (x j - x i + if i < j then 1 else 0)
                (Polynomial.bernoulli (k j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [scale_product _ lam hc, modifiedDegenerateBernoulli]
    have he : ((k i : ℤ) - 1) + (∑ j ∈ univ.erase i, ((k j : ℤ) - 1)) = (n : ℤ) - m := by
      rw [add_sum_erase univ (fun j => ((k j : ℤ) - 1)) (mem_univ i),
        total_exponent m n k hk]
    rw [← he, zpow_add₀ hc]
    ring
  rw [hfirst]
  simp_rw [hother]
  have h := ordinary_symmetric m n hm r x
  simp_rw [mul_left_comm (r _) (c ^ ((n : ℤ) - m))]
  rw [← mul_sum]
  linear_combination c ^ ((n : ℤ) - m) * h
end modifiedDegenerateBernoulli_symmetric

@[expose] public section

/-- **Symmetric identity for modified degenerate Bernoulli polynomials.** Let $m \ge 2$ and
$n \ge 1$ be integers, let $\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$,
let $r_1, \ldots, r_m$ and $x_1, \ldots, x_m$ be complex numbers, write
$\mathfrak{B}_{k,\lambda}(x)$ for the modified degenerate Bernoulli polynomials, and put
$r_0 = n - r_1 - \cdots - r_m$. Then

$$
r_0 \sum_{k_1 + \cdots + k_m = n} \prod_{j=1}^{m} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j)
= -\sum_{i=1}^{m} r_i \sum_{k_1 + \cdots + k_m = n} \binom{r_0}{k_i}
\mathfrak{B}_{k_i,\lambda}(1 - x_i)
\prod_{j \ne i} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $\binom{w}{k} = w(w-1) \cdots
(w-k+1)/k!$ is the binomial coefficient with a complex upper argument, and $[j > i]$ is $1$ if
$j > i$ and $0$ otherwise.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Theorem 1
(`jis-2024-24.5.4-thm-1`). -/
public theorem modifiedDegenerateBernoulli_symmetric_identity (m n : ℕ) (hm : 2 ≤ m)
    (hn : 1 ≤ n) (r x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) - ∑ j, r j) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * modifiedDegenerateBernoulli lam (k j) (x j) =
      -∑ i, r i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) * modifiedDegenerateBernoulli lam (k i) (1 - x i) *
          ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact modifiedDegenerateBernoulli_symmetric.scaled_identity m (d + 1) (by omega)
    r x lam hlam hlam1

end

end MetaMathlibExt

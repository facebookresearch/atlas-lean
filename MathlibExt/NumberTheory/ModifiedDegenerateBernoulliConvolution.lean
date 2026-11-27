/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulli
public import Mathlib.Algebra.Order.Antidiag.Pi

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# A convolution lemma for modified degenerate Bernoulli polynomials

We use one formal series variable with multivariate polynomial coefficients. Rescaling by the
polynomial variables keeps track of the mixed degrees, so the coefficient extraction uses the
ordinary product rule for formal series and the multinomial theorem.
-/

open Finset

namespace MetaMathlibExt

namespace ModifiedDegenerateBernoulliConvolution

private theorem prod_sub_one {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → R) :
    (∏ j, f j) - 1 = ∑ i, (f i - 1) * ∏ j ∈ Ioi i, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    have h := ih (f ∘ Fin.succ)
    simp only [Function.comp_apply] at h
    rw [← h]
    ring

variable {m : ℕ}

local notation "P" => MvPolynomial (Fin m) ℂ
local notation "V" => (MvPolynomial.X : Fin m → P)
local notation "L" => (∑ j, V j)
local notation "C" => (MvPolynomial.C : ℂ →+* P)
local notation "T" => (PowerSeries.X : PowerSeries P)
local notation "Cₜ" => (PowerSeries.C : P →+* PowerSeries P)
local notation "E" => (fun a : P => PowerSeries.rescale a (PowerSeries.exp P))

private noncomputable def spread (a : P) (f : ℕ → ℂ) : PowerSeries P :=
  PowerSeries.rescale a (PowerSeries.map C (PowerSeries.mk f))

private noncomputable def berCoeff (lam x : ℂ) : ℕ → ℂ :=
  fun n => modifiedDegenerateBernoulli lam n x / n.factorial

private noncomputable def series (lam : ℂ) (a : P) (x : ℂ) : PowerSeries P :=
  spread a (berCoeff lam x)

private theorem coeff_spread (a : P) (f : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (spread a f) = C (f n) * a ^ n := by
  simp [spread, PowerSeries.coeff_map, mul_comm]

private theorem series_mul (lam x : ℂ) (a : P) (hc : Complex.log (1 + lam) / lam ≠ 0) :
    series lam a x * (E (C (Complex.log (1 + lam) / lam) * a) - 1) =
      Cₜ a * T * E (C (Complex.log (1 + lam) / lam * x) * a) := by
  have h := congrArg (fun f => PowerSeries.rescale a (PowerSeries.map C f))
    (modifiedDegenerateBernoulli_generating_function lam x hc)
  have hmk : (PowerSeries.mk fun n => modifiedDegenerateBernoulli lam n x / n.factorial) =
      PowerSeries.mk (berCoeff lam x) := by
    apply PowerSeries.ext
    intro n
    simp [berCoeff]
  rw [hmk] at h
  simpa only [series, spread, map_mul, map_sub, map_one, ← PowerSeries.rescale_map,
    PowerSeries.map_exp, PowerSeries.map_X, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale] using h

private theorem exp_sum (s : Finset (Fin m)) (f : Fin m → P) :
    ∏ j ∈ s, E (f j) = E (∑ j ∈ s, f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj, ih, PowerSeries.exp_mul_exp_eq_exp_add]

private theorem exp_sub_one_ne_zero (a : P) (ha : a ≠ 0) : E a - 1 ≠ 0 := by
  intro h
  apply ha
  simpa [PowerSeries.coeff_exp, PowerSeries.coeff_one] using
    congrArg (PowerSeries.coeff 1) h

-- The shifted arguments leave exactly the tail exponential in the telescoping product.
private theorem shifted_sum (c : ℂ) (x : Fin m → ℂ) (i : Fin m) :
    C (c * x i) * L + ∑ j ∈ univ.erase i, C (c * (x j - x i + if i < j then 1 else 0)) * V j =
      (∑ j, C (c * x j) * V j) + ∑ j ∈ Ioi i, C c * V j := by
  have hI : (univ.erase i).filter (fun j => i < j) = Ioi i := by
    ext j
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Ioi]
    exact ⟨And.right, fun hj => ⟨hj.ne', hj⟩⟩
  rw [mul_sum, ← add_sum_erase _ (fun j => C (c * x i) * V j) (mem_univ i),
    ← add_sum_erase _ (fun j => C (c * x j) * V j) (mem_univ i), add_assoc, add_assoc,
    ← sum_add_distrib, ← hI, sum_filter, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  split_ifs <;> simp only [mul_add, mul_sub, mul_one, add_zero, map_add, map_sub] <;> ring

private theorem series_convolution (hm : 2 ≤ m) (lam : ℂ) (x : Fin m → ℂ)
    (hc : Complex.log (1 + lam) / lam ≠ 0) :
    Cₜ L * T * (∏ j, series lam (V j) (x j)) =
      ∑ i, Cₜ (V i) * T * series lam L (x i) *
        ∏ j ∈ univ.erase i, series lam (V j) (x j - x i + if i < j then 1 else 0) := by
  let c := Complex.log (1 + lam) / lam
  let d : Fin m → PowerSeries P := fun j => E (C c * V j) - 1
  let D : PowerSeries P := E (C c * L) - 1
  let a : Fin m → PowerSeries P := fun j => Cₜ (V j) * T
  let K : PowerSeries P := Cₜ L * T * (∏ j, a j) * E (∑ j, C (c * x j) * V j)
  have hL : L ≠ 0 := by
    intro hz
    have h := congrArg (MvPolynomial.eval fun _ : Fin m => (1 : ℂ)) hz
    simp at h
    omega
  have hC : C c ≠ 0 := fun h => hc (MvPolynomial.C_injective _ _ (h.trans (map_zero C).symm))
  have hD : D ≠ 0 := exp_sub_one_ne_zero _ (mul_ne_zero hC hL)
  have hd (j : Fin m) : d j ≠ 0 :=
    exp_sub_one_ne_zero _ (mul_ne_zero hC (MvPolynomial.X_ne_zero j))
  have hgf (u : P) (z : ℂ) : series lam u z * (E (C c * u) - 1) =
      Cₜ u * T * E (C (c * z) * u) := series_mul lam z u hc
  have hleft : (Cₜ L * T * (∏ j, series lam (V j) (x j))) * (D * ∏ j, d j) = K * D := by
    calc
      _ = Cₜ L * T * (∏ j, series lam (V j) (x j) * d j) * D := by
        rw [prod_mul_distrib]
        ac_rfl
      _ = _ := by
        simp only [K, d, hgf, a, prod_mul_distrib, exp_sum]
        ring
  have hright (i : Fin m) :
      (Cₜ (V i) * T * series lam L (x i) *
        ∏ j ∈ univ.erase i, series lam (V j) (x j - x i + if i < j then 1 else 0)) *
        (D * ∏ j, d j) = K * ((E (C c * V i) - 1) * ∏ j ∈ Ioi i, E (C c * V j)) := by
    let y : Fin m → ℂ := fun j => x j - x i + if i < j then 1 else 0
    calc
      _ = a i * (series lam L (x i) * D) *
          (∏ j ∈ univ.erase i, series lam (V j) (y j) * d j) * d i := by
        rw [prod_mul_distrib, ← mul_prod_erase _ d (mem_univ i)]
        dsimp only [a, y]
        ac_rfl
      _ = Cₜ L * T * (∏ j, a j) *
          (E (C (c * x i) * L) * E (∑ j ∈ univ.erase i, C (c * y j) * V j)) * d i := by
        rw [show series lam L (x i) * D = _ from hgf L (x i)]
        have h (j : Fin m) : series lam (V j) (y j) * d j = a j * E (C (c * y j) * V j) :=
          hgf (V j) (y j)
        simp_rw [h, prod_mul_distrib, exp_sum]
        rw [← mul_prod_erase _ a (mem_univ i)]
        ac_rfl
      _ = _ := by
        dsimp only [y]
        rw [PowerSeries.exp_mul_exp_eq_exp_add, shifted_sum,
          ← PowerSeries.exp_mul_exp_eq_exp_add, exp_sum]
        dsimp only [K, d]
        ac_rfl
  apply mul_right_cancel₀ (mul_ne_zero hD (prod_ne_zero_iff.mpr fun j _ => hd j))
  rw [hleft, sum_mul]
  simp_rw [hright, ← mul_sum, ← prod_sub_one, exp_sum, ← mul_sum]
  rfl

private theorem coeff_prod_tuple (f : Fin m → PowerSeries P) (n : ℕ) :
    PowerSeries.coeff n (∏ j, f j) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m n, ∏ j, PowerSeries.coeff (k j) (f j) := by
  rw [PowerSeries.coeff_prod]
  refine sum_bij (fun k _ => (k : Fin m → ℕ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro k hk
    exact Finset.Nat.mem_antidiagonalTuple.mpr (mem_finsuppAntidiag.mp hk).1
  · intro k _ l _ h
    exact Finsupp.ext fun j => congrFun h j
  · intro k hk
    refine ⟨Finsupp.equivFunOnFinite.symm k, mem_finsuppAntidiag.mpr ⟨?_, subset_univ _⟩, rfl⟩
    exact Finset.Nat.mem_antidiagonalTuple.mp hk

local notation "δ" => (Finsupp.equivFunOnFinite.symm : (Fin m → ℕ) ≃ (Fin m →₀ ℕ))

private theorem prod_monomials (t : Finset (Fin m)) (k : Fin m → ℕ) (b : Fin m → ℂ) :
    ∏ j ∈ t, C (b j) * V j ^ k j =
      MvPolynomial.monomial (δ (fun j => if j ∈ t then k j else 0)) (∏ j ∈ t, b j) := by
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one,
    ← MvPolynomial.monomial_sum_prod]
  have h : (∑ j ∈ t, Finsupp.single j (k j)) = δ (fun j => if j ∈ t then k j else 0) := by
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
  rw [h]

private noncomputable def normalizedCoeff (s : Fin m → ℕ) : P →ₗ[ℂ] ℂ :=
  (∏ j, ((s j).factorial : ℂ)) • MvPolynomial.lcoeff ℂ (δ s)

private theorem normalizedCoeff_apply (s : Fin m → ℕ) (p : P) :
    normalizedCoeff s p = (∏ j, ((s j).factorial : ℂ)) * p.coeff (δ s) := rfl

-- A product of series in distinct variables has only one contribution to each mixed coefficient.
private theorem coeff_separated (s : Fin m → ℕ) (n : ℕ) (f : Fin m → ℕ → ℂ) :
    normalizedCoeff s (PowerSeries.coeff n (∏ j, spread (V j) (f j))) =
      if (∑ j, s j) = n then ∏ j, ((s j).factorial : ℂ) * f j (s j) else 0 := by
  classical
  rw [coeff_prod_tuple, map_sum]
  simp only [coeff_spread, prod_monomials, mem_univ, ite_true, normalizedCoeff_apply,
    MvPolynomial.coeff_monomial, Equiv.apply_eq_iff_eq]
  by_cases hs : (∑ j, s j) = n
  · have hm := Finset.Nat.mem_antidiagonalTuple.mpr hs
    rw [ite_eq_left hs, sum_eq_single_of_mem s hm]
    · simp [prod_mul_distrib]
    · intro k _ hk
      simp [hk]
  · rw [ite_eq_right hs]
    refine sum_eq_zero fun k hk => ?_
    have hks : k ≠ s := fun h => hs (h ▸ Finset.Nat.mem_antidiagonalTuple.mp hk)
    simp [hks]

private theorem exp_as_spread (a : P) : E a = spread a (fun k => (k.factorial : ℂ)⁻¹) := by
  ext k
  simp [PowerSeries.coeff_exp, coeff_spread, mul_comm]

-- The exponential of a sum is the product of the coordinate exponentials. Its
-- normalized mixed coefficient is one in the requested total degree, and zero otherwise.
private theorem coeff_exp_sum (s : Fin m → ℕ) (n : ℕ) :
    normalizedCoeff s (PowerSeries.coeff n (E L)) = if (∑ j, s j) = n then 1 else 0 := by
  rw [← exp_sum univ V]
  simp_rw [exp_as_spread]
  rw [coeff_separated]
  split_ifs <;> simp [Nat.factorial_ne_zero]

-- A monomial takes up `d j` of the available degree `s j` in each variable.
-- The change in the factorial normalization gives the corresponding binomial weights.
private theorem normalize_mul_monomial (s d : Fin m → ℕ) (b : ℂ) (p : P) :
    normalizedCoeff s (MvPolynomial.monomial (δ d) b * p) =
      b * (∏ j, ((s j).choose (d j) : ℂ) * (d j).factorial) * normalizedCoeff (s - d) p := by
  rw [normalizedCoeff_apply, MvPolynomial.coeff_monomial_mul', normalizedCoeff_apply]
  by_cases h : d ≤ s
  · have h' : δ d ≤ δ s := h
    have hd : δ s - δ d = δ (s - d) := by ext j; rfl
    rw [ite_eq_left h', hd]
    have he : (∏ j, ((s j).choose (d j) : ℂ) * (d j).factorial) *
        (∏ j, (((s - d) j).factorial : ℂ)) = ∏ j, ((s j).factorial : ℂ) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (h j)
    rw [← he]
    ring
  · have hn : ¬ δ d ≤ δ s := h
    obtain ⟨j, hj⟩ : ∃ j, s j < d j := by simpa [Pi.le_def, not_forall, not_le] using h
    have hz : (∏ j, ((s j).choose (d j) : ℂ) * (d j).factorial) = 0 :=
      prod_eq_zero (mem_univ j) (by simp [Nat.choose_eq_zero_of_lt hj])
    simp [hn, hz]

private theorem prod_replace {R : Type*} [CommMonoid R] (i : Fin m) (a : R) (f : Fin m → R) :
    ∏ j, (if j = i then a else f j) = a * ∏ j ∈ univ.erase i, f j := by
  rw [← mul_prod_erase _ (fun j => if j = i then a else f j) (mem_univ i),
    ite_eq_left (show i = i from rfl)]
  congr 1
  exact prod_congr rfl fun j hj => ite_eq_right (ne_of_mem_erase hj)

private theorem spread_shift (a : P) (f : ℕ → ℂ) :
    Cₜ a * T * spread a f = spread a (fun n => if n = 0 then 0 else f (n - 1)) := by
  apply PowerSeries.ext
  intro n
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [coeff_spread]
  | succ n =>
    simp only [PowerSeries.coeff_succ_X_mul, coeff_spread, Nat.succ_ne_zero, ite_false,
      Nat.succ_sub_one, pow_succ]
    ac_rfl

private theorem factorial_shift (n : ℕ) (b : ℂ) :
    (n.factorial : ℂ) * (if n = 0 then 0 else b / (n - 1).factorial) = n * b := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul]
    field_simp [Nat.factorial_ne_zero]

private theorem coeff_left_term (lam : ℂ) (s : Fin m → ℕ) (x : Fin m → ℂ) (i : Fin m) :
    normalizedCoeff s (PowerSeries.coeff (∑ j, s j)
      (Cₜ (V i) * T * ∏ j, series lam (V j) (x j))) =
      (s i : ℂ) * modifiedDegenerateBernoulli lam (s i - 1) (x i) *
        ∏ j ∈ univ.erase i, modifiedDegenerateBernoulli lam (s j) (x j) := by
  let f (j : Fin m) (n : ℕ) := if j = i then
    (if n = 0 then 0 else berCoeff lam (x j) (n - 1)) else berCoeff lam (x j) n
  have hp : Cₜ (V i) * T * (∏ j, series lam (V j) (x j)) = ∏ j, spread (V j) (f j) := by
    rw [← mul_prod_erase _ (fun j => series lam (V j) (x j)) (mem_univ i), ← mul_assoc,
      series, spread_shift, ← mul_prod_erase _ (fun j => spread (V j) (f j)) (mem_univ i)]
    have hfi : f i = fun n => if n = 0 then 0 else berCoeff lam (x i) (n - 1) := by
      funext n
      simp [f]
    rw [hfi]
    congr 1
    exact prod_congr rfl fun j hj => by simp [f, series, ne_of_mem_erase hj]
  rw [hp, coeff_separated, ite_eq_left rfl,
    ← mul_prod_erase _ (fun j => ((s j).factorial : ℂ) * f j (s j)) (mem_univ i)]
  simp only [f, ite_eq_left rfl, berCoeff, factorial_shift]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  simp [ne_of_mem_erase hj, div_eq_mul_inv, Nat.factorial_ne_zero, mul_left_comm]

private theorem coeff_shift (lam z : ℂ) (a : P) (k : ℕ) :
    PowerSeries.coeff k (T * series lam a z) =
      if k = 0 then 0 else C (modifiedDegenerateBernoulli lam (k - 1) z) *
        PowerSeries.coeff (k - 1) (E a) := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [PowerSeries.coeff_succ_X_mul, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one,
      series, coeff_spread, exp_as_spread, berCoeff, div_eq_mul_inv, map_mul, mul_assoc]

private theorem coeff_right_summand (lam : ℂ) (s k : Fin m → ℕ) (i : Fin m) (z : ℂ)
    (y : Fin m → ℂ) (hk : (∑ j, k j) = ∑ j, s j) :
    normalizedCoeff s (V i * PowerSeries.coeff (k i) (T * series lam L z) *
      ∏ j ∈ univ.erase i, PowerSeries.coeff (k j) (series lam (V j) (y j))) =
      (s i : ℂ) * ((if k i = 0 then 0 else modifiedDegenerateBernoulli lam (k i - 1) z) *
        ∏ j ∈ univ.erase i, ((s j).choose (k j) : ℂ) *
          modifiedDegenerateBernoulli lam (k j) (y j)) := by
  by_cases hz : k i = 0
  · simp [hz, coeff_shift]
  -- The distinguished coordinate receives one power from the prefactor. All other
  -- powers left over after removing this monomial come from the series in `L`.
  let d := Function.update k i 1
  let b (j : Fin m) := berCoeff lam (y j) (k j)
  let b₀ := modifiedDegenerateBernoulli lam (k i - 1) z
  let p := PowerSeries.coeff (k i - 1) (E L)
  have hd : d i = 1 := Function.update_self ..
  have hd' (j : Fin m) (hj : j ≠ i) : d j = k j := Function.update_of_ne hj ..
  have hprod : V i * ∏ j ∈ univ.erase i, C (b j) * V j ^ k j =
      MvPolynomial.monomial (δ d) (∏ j ∈ univ.erase i, b j) := by
    have hh := prod_monomials univ d (Function.update b i 1)
    simp only [mem_univ, ite_true] at hh
    rw [← mul_prod_erase _ (fun j => C (Function.update b i 1 j) * V j ^ d j) (mem_univ i),
      ← mul_prod_erase _ (Function.update b i 1) (mem_univ i)] at hh
    simp only [Function.update_self, hd, map_one, pow_one, one_mul] at hh
    have h₁ : (∏ j ∈ univ.erase i, C (Function.update b i 1 j) * V j ^ d j) =
        ∏ j ∈ univ.erase i, C (b j) * V j ^ k j := by
      exact prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (ne_of_mem_erase hj), hd' j (ne_of_mem_erase hj)]
    have h₂ : (∏ j ∈ univ.erase i, Function.update b i 1 j) = ∏ j ∈ univ.erase i, b j :=
      prod_congr rfl fun j hj => Function.update_of_ne (ne_of_mem_erase hj) ..
    rwa [h₁, h₂] at hh
  have hextract : V i * PowerSeries.coeff (k i) (T * series lam L z) *
      ∏ j ∈ univ.erase i, PowerSeries.coeff (k j) (series lam (V j) (y j)) =
        MvPolynomial.monomial (δ d) (∏ j ∈ univ.erase i, b j) * (b₀ • p) := by
    rw [coeff_shift, ite_eq_right hz, MvPolynomial.smul_eq_C_mul, ← hprod]
    simp only [series, coeff_spread]
    change V i * (C b₀ * p) * (∏ j ∈ univ.erase i, C (b j) * V j ^ k j) = _
    ac_rfl
  rw [hextract, normalize_mul_monomial, map_smul, smul_eq_mul, ite_eq_right hz]
  have hweight : (∏ j ∈ univ.erase i, b j) * (∏ j, ((s j).choose (d j) : ℂ) * (d j).factorial) =
      (s i : ℂ) * ∏ j ∈ univ.erase i,
        ((s j).choose (k j) : ℂ) * modifiedDegenerateBernoulli lam (k j) (y j) := by
    rw [← mul_prod_erase _ (fun j => ((s j).choose (d j) : ℂ) * (d j).factorial) (mem_univ i)]
    simp only [hd, Nat.choose_one_right, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [mul_left_comm, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    rw [hd' j (ne_of_mem_erase hj)]
    dsimp [b, berCoeff]
    field_simp [Nat.factorial_ne_zero]
  rw [hweight]
  by_cases hds : d ≤ s
  · have hsum : ∑ j, (s - d) j = k i - 1 := by
      have ha : (∑ j, (s - d) j) + ∑ j, d j = ∑ j, s j := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ => Nat.sub_add_cancel (hds j)
      have hb : (∑ j, d j) + k i = (∑ j, k j) + 1 := by
        have hdk : (∑ j ∈ univ.erase i, d j) = ∑ j ∈ univ.erase i, k j :=
          sum_congr rfl fun j hj => hd' j (ne_of_mem_erase hj)
        rw [← add_sum_erase _ d (mem_univ i), ← add_sum_erase _ k (mem_univ i), hd, hdk]
        ac_rfl
      omega
    rw [coeff_exp_sum, ite_eq_left hsum, mul_one]
    dsimp only [b₀]
    ring
  · obtain ⟨j, hj⟩ : ∃ j, s j < d j := by simpa [Pi.le_def, not_forall, not_le] using hds
    by_cases hji : j = i
    · subst j
      rw [hd] at hj
      have hs : s i = 0 := by omega
      simp [hs]
    · rw [hd' j hji] at hj
      rw [prod_eq_zero (mem_erase.mpr ⟨hji, mem_univ j⟩) (by simp [Nat.choose_eq_zero_of_lt hj])]
      ring

private theorem coeff_right_term (lam : ℂ) (s : Fin m → ℕ) (i : Fin m) (z : ℂ) (y : Fin m → ℂ) :
    normalizedCoeff s (PowerSeries.coeff (∑ j, s j) (Cₜ (V i) * T * series lam L z *
      ∏ j ∈ univ.erase i, series lam (V j) (y j))) =
      (s i : ℂ) * ∑ k ∈ Finset.Nat.antidiagonalTuple m (∑ j, s j),
        (if k i = 0 then 0 else modifiedDegenerateBernoulli lam (k i - 1) z) *
          ∏ j ∈ univ.erase i, ((s j).choose (k j) : ℂ) *
            modifiedDegenerateBernoulli lam (k j) (y j) := by
  let f (j : Fin m) := if j = i then T * series lam L z else series lam (V j) (y j)
  have hf : ∏ j, f j = (T * series lam L z) * ∏ j ∈ univ.erase i, series lam (V j) (y j) :=
    prod_replace i _ _
  rw [mul_assoc (Cₜ (V i)) T, mul_assoc (Cₜ (V i)), ← hf,
    PowerSeries.coeff_C_mul, coeff_prod_tuple, mul_sum, map_sum, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hp : ∏ j, PowerSeries.coeff (k j) (f j) = PowerSeries.coeff (k i) (T * series lam L z) *
      ∏ j ∈ univ.erase i, PowerSeries.coeff (k j) (series lam (V j) (y j)) := by
    rw [← mul_prod_erase _ (fun j => PowerSeries.coeff (k j) (f j)) (mem_univ i)]
    have hfi : f i = T * series lam L z := by simp [f]
    rw [hfi]
    congr 1
    exact prod_congr rfl fun j hj => by simp [f, ne_of_mem_erase hj]
  rw [hp, ← mul_assoc]
  exact coeff_right_summand lam s k i z y (Finset.Nat.mem_antidiagonalTuple.mp hk)

end ModifiedDegenerateBernoulliConvolution

open ModifiedDegenerateBernoulliConvolution in
/-- **A convolution lemma for modified degenerate Bernoulli polynomials.** Let $m \ge 2$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, let $s_1, \ldots, s_m$ be
nonnegative integers with $S = s_1 + \cdots + s_m$, and let $x_1, \ldots, x_m$ be complex numbers.
Writing $\mathfrak{B}_{n,\lambda}(x)$ for the modified degenerate Bernoulli polynomials,

$$
\sum_{i=1}^{m} s_i\, \mathfrak{B}_{s_i-1,\lambda}(x_i)
\prod_{j \ne i} \mathfrak{B}_{s_j,\lambda}(x_j) =
\sum_{i=1}^{m} s_i \sum_{k_1 + \cdots + k_m = S} \mathfrak{B}_{k_i-1,\lambda}(x_i)
\prod_{j \ne i} \binom{s_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $[j > i]$ is $1$ if $j > i$ and $0$
otherwise, and $\mathfrak{B}_{-1,\lambda}$ is read as $0$ (on the left this term has the factor
$s_i = 0$).

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Lemma 3
(`jis-2024-24.5.4-lem-3`). -/
public theorem modifiedDegenerateBernoulli_lemma_three (m : ℕ) (hm : 2 ≤ m)
    (s : Fin m → ℕ) (x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ i, (s i : ℂ) * modifiedDegenerateBernoulli lam (s i - 1) (x i) *
        ∏ j ∈ univ.erase i, modifiedDegenerateBernoulli lam (s j) (x j) =
      ∑ i, (s i : ℂ) * ∑ k ∈ Finset.Nat.antidiagonalTuple m (∑ j, s j),
        (if k i = 0 then 0 else modifiedDegenerateBernoulli lam (k i - 1) (x i)) *
          ∏ j ∈ univ.erase i, ((s j).choose (k j) : ℂ) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0) := by
  have hc : Complex.log (1 + lam) / lam ≠ 0 := by
    apply div_ne_zero _ hlam
    have h := Complex.exp_log (x := 1 + lam) (by intro h; apply hlam1; linear_combination h)
    intro hz
    rw [hz, Complex.exp_zero] at h
    exact hlam (by linear_combination -h)
  have h := series_convolution hm lam x hc
  rw [map_sum, Finset.sum_mul, Finset.sum_mul] at h
  have he := congrArg (fun f => normalizedCoeff s (PowerSeries.coeff (∑ j, s j) f)) h
  simpa only [map_sum, coeff_left_term, coeff_right_term] using he

end MetaMathlibExt

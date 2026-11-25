/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Two-dissections of reciprocal powers of the Euler product

Splitting the square of the Jacobi theta series by parity gives the two-dissection of
`1 / f₁⁴`. Squaring and cubing it gives the identities for `1 / f₁⁸` and `1 / f₁¹²`.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace one_div_f1_pow_four_eight_twelve_two_dissection

open Analysis.SpecialFunctions.JacobiTripleProduct

private lemma norm_sq_lt {q : ℂ} (h : ‖q‖ < 1) : ‖q ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) h two_ne_zero

private lemma euler_ne {q : ℂ} (h : ‖q‖ < 1) : eulerFunction q ≠ 0 := by
  rw [eulerFunction_eq_tprod h]
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n he
    have he' : q ^ (n + 1) = 1 := by linear_combination -he
    have := pow_lt_one₀ (norm_nonneg q) h (Nat.succ_ne_zero n)
    rwa [← norm_pow, he', norm_one, lt_self_iff_false] at this
  · simpa [pow_succ, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) h).mul_right ‖q‖

private lemma plus_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ ↦ 1 + q ^ (n + 1)) (eulerFunction (q ^ 2) / eulerFunction q) := by
  have hp : Multipliable (fun n : ℕ ↦ 1 + q ^ (n + 1)) := by
    apply multipliable_one_add_of_summable
    simpa [pow_succ, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) h).mul_right ‖q‖
  have hprod := hp.hasProd.mul (hasProd_eulerFunction h)
  have he := (hasProd_eulerFunction (norm_sq_lt h)).congr_fun
    (g := fun n : ℕ ↦ (1 + q ^ (n + 1)) * (1 - q ^ (n + 1))) fun n ↦ by ring
  rw [← (eq_div_iff (euler_ne h)).mpr (hprod.unique he)]
  exact hp.hasProd

private lemma odd_plus_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ ↦ 1 + q ^ (2 * n + 1))
      ((eulerFunction (q ^ 2) / eulerFunction q) /
        (eulerFunction ((q ^ 2) ^ 2) / eulerFunction (q ^ 2))) := by
  have ho : Multipliable (fun n : ℕ ↦ 1 + q ^ (2 * n + 1)) := by
    apply multipliable_one_add_of_summable
    simpa [pow_add, pow_mul, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg _) (norm_sq_lt h)).mul_right ‖q‖
  have he := (plus_prod (norm_sq_lt h)).congr_fun
    (g := fun n : ℕ ↦ 1 + q ^ ((2 * n + 1) + 1)) fun n ↦ by ring
  have hprod := HasProd.even_mul_odd (f := fun n : ℕ ↦ 1 + q ^ (n + 1)) ho.hasProd he
  rw [← (eq_div_iff (div_ne_zero (euler_ne (norm_sq_lt (norm_sq_lt h)))
    (euler_ne (norm_sq_lt h)))).mpr (hprod.unique (plus_prod h))]
  exact ho.hasProd

/-- The square theta series is the triple product at `z = 1`. -/
private lemma theta_sum {q : ℂ} (h : ‖q‖ < 1) :
    HasSum (fun n : ℤ ↦ q ^ (n * n)) (eulerFunction (q ^ 2) ^ 5 /
      (eulerFunction q ^ 2 * eulerFunction ((q ^ 2) ^ 2) ^ 2)) := by
  obtain ⟨hs, _, he⟩ := jacobi_triple_product 1 q one_ne_zero h
  simp only [one_zpow, inv_one, one_mul] at hs he
  have hm := (hasProd_eulerFunction (norm_sq_lt h)).congr_fun
    (g := fun n : ℕ ↦ 1 - q ^ (2 * n + 2)) fun n ↦ by ring
  have hp := ((hm.mul (odd_plus_prod h)).mul (odd_plus_prod h)).tprod_eq
  rw [hp] at he
  have hsum := hs.hasSum
  rw [he] at hsum
  convert hsum using 1
  · funext n
    rw [← zpow_natCast, Int.toNat_of_nonneg (mul_self_nonneg n)]
  · field_simp [euler_ne h, euler_ne (norm_sq_lt h), euler_ne (norm_sq_lt (norm_sq_lt h))]

/-- At `z = q` the third product starts at exponent zero, contributing a factor of two. -/
private lemma shifted_sum {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    HasSum (fun n : ℤ ↦ q ^ (n * n + n)) (2 * eulerFunction ((q ^ 2) ^ 2) ^ 2 /
      eulerFunction (q ^ 2)) := by
  obtain ⟨hs, _, he⟩ := jacobi_triple_product q q hq h
  have heven := plus_prod (norm_sq_lt h)
  have hm := (hasProd_eulerFunction (norm_sq_lt h)).congr_fun
    (g := fun n : ℕ ↦ 1 - q ^ (2 * n + 2)) fun n ↦ by ring
  have hp := heven.congr_fun (g := fun n : ℕ ↦ 1 + q * q ^ (2 * n + 1)) fun n ↦ by ring
  have head := tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 + (q ^ 2) ^ n) heven.multipliable
  have hl := multipliable_one_add_of_summable (f := fun n : ℕ ↦ (q ^ 2) ^ n)
    (by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (norm_sq_lt h))
  rw [heven.tprod_eq] at head
  have ht := hl.hasProd.congr_fun (g := fun n : ℕ ↦ 1 + q⁻¹ * q ^ (2 * n + 1)) fun n ↦ by
    rw [pow_succ, ← pow_mul]
    field_simp
  rw [((hm.mul hp).mul ht).tprod_eq, head] at he
  have hsum := hs.hasSum
  rw [he] at hsum
  convert hsum using 1
  · funext n
    rw [← zpow_natCast, Int.toNat_of_nonneg (mul_self_nonneg n), ← zpow_add₀ hq, add_comm]
  · simp only [pow_zero]
    field_simp [euler_ne (norm_sq_lt h)]
    ring

/-- The two cosets of the image of the change of variables `(a, b) ↦ (a + b, a - b)`. -/
private def parityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun (a, b) ↦ (a + b, a - b)) (fun (a, b) ↦ (a + b + 1, a - b))
  invFun := fun (x, y) ↦ if (x + y) % 2 = 0 then .inl ((x + y) / 2, (x - y) / 2)
    else .inr ((x + y) / 2, (x - y) / 2)
  left_inv := by
    rintro (⟨a, b⟩ | ⟨a, b⟩)
    · simp [← two_mul]
    · have h : (a + b + 1 + (a - b)) % 2 ≠ 0 := by omega
      simp [h, Prod.mk.injEq]
      omega
  right_inv := by
    rintro ⟨x, y⟩
    by_cases h : (x + y) % 2 = 0 <;> simp [h, Prod.mk.injEq] <;> omega

private lemma sum_square {u : ℤ → ℂ} {s : ℂ} (hu : HasSum u s) :
    HasSum (fun p : ℤ × ℤ ↦ u p.1 * u p.2) (s ^ 2) := by
  rw [pow_two]
  exact hu.mul hu (summable_mul_of_summable_norm hu.summable.norm hu.summable.norm)

private lemma analytic_dissection {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    eulerFunction (q ^ 2) ^ 14 * eulerFunction (q ^ 8) ^ 4 =
      eulerFunction q ^ 4 * eulerFunction (q ^ 4) ^ 14 +
      4 * q * eulerFunction q ^ 4 * eulerFunction (q ^ 2) ^ 4 *
        eulerFunction (q ^ 4) ^ 2 * eulerFunction (q ^ 8) ^ 8 := by
  have hs := sum_square (theta_sum h)
  have he := sum_square (theta_sum (norm_sq_lt h))
  have ho := (sum_square (shifted_sum (pow_ne_zero 2 hq) (norm_sq_lt h))).mul_left q
  -- Pairs with equal parities give the ordinary square at q². The other coset gives
  -- q times the square of the shifted series at q².
  let term (p : ℤ × ℤ) := q ^ (p.1 * p.1) * q ^ (p.2 * p.2)
  have hd := HasSum.sum (f := term ∘ parityEquiv)
    (he.congr_fun fun (a, b) ↦ by
      change q ^ ((a + b) * (a + b)) * q ^ ((a - b) * (a - b)) =
        (q ^ 2) ^ (a * a) * (q ^ 2) ^ (b * b)
      rw [← zpow_add₀ hq, ← zpow_add₀ (pow_ne_zero 2 hq)]
      rw [← zpow_natCast q 2, ← zpow_mul]
      congr 1
      ring)
    (ho.congr_fun fun (a, b) ↦ by
      change q ^ ((a + b + 1) * (a + b + 1)) * q ^ ((a - b) * (a - b)) =
        q * ((q ^ 2) ^ (a * a + a) * (q ^ 2) ^ (b * b + b))
      rw [← zpow_add₀ hq, ← zpow_add₀ (pow_ne_zero 2 hq), ← zpow_natCast q 2, ← zpow_mul,
        ← zpow_one_add₀ hq]
      congr 1
      ring)
  have hid := hs.unique (parityEquiv.hasSum_iff.mp hd)
  have h2 := euler_ne (norm_sq_lt h)
  have h4 := euler_ne (norm_sq_lt (norm_sq_lt h))
  have h8 := euler_ne (norm_sq_lt (norm_sq_lt (norm_sq_lt h)))
  simp only [← pow_mul] at hid h4 h8
  norm_num1 at hid h4 h8
  field_simp [euler_ne h, h2, h4, h8] at hid
  linear_combination hid

open UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam 1

/-- A complex function represented by an integer power series on the punctured unit disk. -/
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

private lemma Represents.add {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) :
    Represents (F + G) (fun q ↦ f q + g q) := by
  intro τ
  simpa [add_mul] using (hf τ).add (hg τ)

private lemma represents_const (c : ℤ) : Represents (C c) (fun _ ↦ (c : ℂ)) := by
  intro τ
  refine (hasSum_ite_eq (0 : ℕ) (c : ℂ)).congr_fun fun n ↦ ?_
  rw [coeff_C]
  split_ifs with h <;> simp_all

private lemma represents_X : Represents X id := by
  intro τ
  simpa +contextual [coeff_X, apply_ite, ite_mul] using hasSum_ite_eq (1 : ℕ) (𝕢 τ)

private lemma Represents.pow {F : ℤ⟦X⟧} {f : ℂ → ℂ} (hf : Represents F f) (n : ℕ) :
    Represents (F ^ n) (fun q ↦ f q ^ n) := by
  induction n with
  | zero => simpa using represents_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private lemma represents_euler (k : ℕ) (hk : k ≠ 0) :
    Represents (qEulerProduct k) (fun q ↦ eulerFunction (q ^ k)) := by
  have cont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have prod := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) cont
  have eqn : qEulerProduct k = expand k hk (pentagonalSeries ℤ) := by
    simpa [qEulerProduct, Function.comp_def, pow_mul] using prod.tprod_eq
  rw [eqn]
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hk1 : ‖𝕢 τ ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) lt1 hk
  have inj : Function.Injective (k * ·) := mul_right_injective₀ hk
  apply (inj.hasSum_iff ?_).mp
  · refine (hasSum_eulerFunction_pentagonalSeries hk1).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, coeff_expand_mul, pow_mul]
    congr 1
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  · intro n hn
    have hd : ¬ k ∣ n := by simpa [dvd_def, eq_comm] using hn
    simp [coeff_expand_of_not_dvd _ _ _ hd]

private lemma Represents.eq_of_eval {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g)
    (heq : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → f q = g q) : F = G := by
  have hzero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
    simp [cuspFunction, Pi.zero_comp, Periodic.cuspFunction_zero]
  have han : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := hzero ▸ analyticAt_const
  let c (m : ℕ) : ℂ := (F.coeff m : ℂ) - G.coeff m
  have hh := hasFPowerSeriesOnBall_cuspFunction (c := c) one_pos han (fun τ ↦ by
    have he := heq _ (Periodic.qParam_ne_zero _) (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    simpa [c, smul_eq_mul, sub_mul, he] using (hf τ).sub (hg τ))
  rw [hzero] at hh
  have hz := hh.hasFPowerSeriesAt.eq_zero_of_eventually (Filter.EventuallyEq.refl _ _)
  apply PowerSeries.ext
  intro n
  have hc := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp
    (congrFun hz n)
  simpa [c, sub_eq_zero] using hc

private lemma fourth_power :
    qEulerProduct 2 ^ 14 * qEulerProduct 8 ^ 4 =
      qEulerProduct 1 ^ 4 * qEulerProduct 4 ^ 14 +
      4 * X * qEulerProduct 1 ^ 4 * qEulerProduct 2 ^ 4 * qEulerProduct 4 ^ 2 *
        qEulerProduct 8 ^ 8 := by
  have h1 := represents_euler 1 one_ne_zero
  simp only [pow_one] at h1
  have h2 := represents_euler 2 two_ne_zero
  have h4 := represents_euler 4 (by decide)
  have h8 := represents_euler 8 (by decide)
  have hc : Represents 4 (fun _ ↦ 4) := by simpa using represents_const 4
  have hmain := (h1.pow 4).mul (h4.pow 14)
  have hlinear := ((hc.mul represents_X).mul (h1.pow 4)).mul (h2.pow 4)
  have hcorr := (hlinear.mul (h4.pow 2)).mul (h8.pow 8)
  exact ((h2.pow 14).mul (h8.pow 4)).eq_of_eval (hmain.add hcorr) (fun _ ↦ analytic_dissection)

end one_div_f1_pow_four_eight_twelve_two_dissection

local notation "𝔣" => qEulerProduct

/-- **The 2-dissections of $1/f_1^4$, $1/f_1^8$ and $1/f_1^{12}$.** Write
$f_k = (q^k; q^k)_\infty$ for the Euler products. In the ring of integer power series in $q$,
the following three identities hold:
$$
f_2^{14} f_8^4 = f_1^4 f_4^{14} + 4q f_1^4 f_2^4 f_4^2 f_8^8,
$$
$$
f_2^{28} f_8^8 = f_1^8 f_4^{28} + 8q f_1^8 f_2^4 f_4^{16} f_8^8 + 16q^2 f_1^8 f_2^8 f_4^4 f_8^{16},
$$
$$
f_2^{42} f_8^{12} = f_1^{12} f_4^{42} + 12q f_1^{12} f_2^4 f_4^{30} f_8^8 +
48q^2 f_1^{12} f_2^8 f_4^{18} f_8^{16} + 64q^3 f_1^{12} f_2^{12} f_4^6 f_8^{24}.
$$
Since each $f_k$ with $k \ge 1$ has constant term $1$ and is therefore invertible, dividing by
$f_1^4 f_2^{14} f_8^4$, $f_1^8 f_2^{28} f_8^8$ and $f_1^{12} f_2^{42} f_8^{12}$ respectively turns
these into the 2-dissections
$1/f_1^4 = f_4^{14}/(f_2^{14} f_8^4) + 4q f_4^2 f_8^4/f_2^{10}$,
$1/f_1^8 = f_4^{28}/(f_2^{28} f_8^8) + 8q f_4^{16}/f_2^{24} + 16q^2 f_4^4 f_8^8/f_2^{20}$ and
$1/f_1^{12} = f_4^{42}/(f_2^{42} f_8^{12}) + 12q f_4^{30}/(f_2^{38} f_8^4) +
48q^2 f_4^{18} f_8^4/f_2^{34} + 64q^3 f_4^6 f_8^{12}/f_2^{30}$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 10 (`jis-2025-25.6.1-lem-10`). -/
public theorem one_div_f1_pow_four_eight_twelve_two_dissection :
    𝔣 2 ^ 14 * 𝔣 8 ^ 4 = 𝔣 1 ^ 4 * 𝔣 4 ^ 14 + 4 * X * 𝔣 1 ^ 4 * 𝔣 2 ^ 4 * 𝔣 4 ^ 2 * 𝔣 8 ^ 8 ∧
      𝔣 2 ^ 28 * 𝔣 8 ^ 8 =
        𝔣 1 ^ 8 * 𝔣 4 ^ 28 + 8 * X * 𝔣 1 ^ 8 * 𝔣 2 ^ 4 * 𝔣 4 ^ 16 * 𝔣 8 ^ 8 +
          16 * X ^ 2 * 𝔣 1 ^ 8 * 𝔣 2 ^ 8 * 𝔣 4 ^ 4 * 𝔣 8 ^ 16 ∧
      𝔣 2 ^ 42 * 𝔣 8 ^ 12 =
        𝔣 1 ^ 12 * 𝔣 4 ^ 42 + 12 * X * 𝔣 1 ^ 12 * 𝔣 2 ^ 4 * 𝔣 4 ^ 30 * 𝔣 8 ^ 8 +
          48 * X ^ 2 * 𝔣 1 ^ 12 * 𝔣 2 ^ 8 * 𝔣 4 ^ 18 * 𝔣 8 ^ 16 +
          64 * X ^ 3 * 𝔣 1 ^ 12 * 𝔣 2 ^ 12 * 𝔣 4 ^ 6 * 𝔣 8 ^ 24 := by
  have h := one_div_f1_pow_four_eight_twelve_two_dissection.fourth_power
  refine ⟨h, ?_, ?_⟩
  · linear_combination (norm := ring) congrArg (· ^ 2) h
  · linear_combination (norm := ring) congrArg (· ^ 3) h

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Pentagonal recurrence for partitions into distinct odd parts

Let $\operatorname{pdo}(m)$ be the number of partitions of $m$ into distinct odd parts. The main
result, `MetaMathlibExt.oddDistincts_pentagonal_recurrence`, is the recurrence
$\sum_k (-1)^k \operatorname{pdo}(n - k(3k+1)) = (-1)^{\lceil m/2 \rceil}$ if $n = m(3m+1)/2$
for an integer $m$, and $0$ otherwise. This is Corollary 3.4 of the arXiv version
(arXiv:2403.05866v1) of the source cited in its docstring.

In terms of generating functions it says
$(q^2; q^2)_\infty (-q; q^2)_\infty = \sum_{m \in \mathbb{Z}} (-1)^{\lceil m/2 \rceil}
q^{m(3m+1)/2}$, the quintuple product identity at $z = i$. The proof works as follows.

* The Jacobi triple product gives $\varphi(q) = \sum_m q^{m^2}$ and
  $\psi(-q) = \sum_a (-1)^a q^{a(2a-1)}$ as quotients of Euler functions $f(q^k)$.
* The product $\psi(-q) \varphi(q)$ equals $f(q^2) \sum_k (-1)^{\lceil k/2 \rceil}
  q^{k(3k+1)/2}$. This uses an injection of $\mathbb{Z}^2$ into the index set and a
  sign-reversing involution on the indices it misses, together with the pentagonal number
  theorem.
* The resulting identity between functions on the unit disk is transferred to integer power
  series, combined with the product formula for the generating function of distinct odd parts,
  and read off coefficientwise.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace oddDistincts_pentagonal_recurrence

/-! ### Products of Euler functions -/

private lemma norm_pow_lt {q : ℂ} (h : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) h hk

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

private lemma summable_norm_pow_lin {q : ℂ} (h : ‖q‖ < 1) (a b : ℕ) (ha : a ≠ 0) :
    Summable (fun n : ℕ => ‖q ^ (a * n + b)‖) := by
  have hg := summable_geometric_of_lt_one (norm_nonneg _) (norm_pow_lt h ha)
  refine (hg.mul_right (‖q‖ ^ b)).congr fun n => ?_
  rw [norm_pow, norm_pow, ← pow_mul, ← pow_add]

private lemma multipliable_one_add_pow_lin {q : ℂ} (h : ‖q‖ < 1) (c : ℂ) (hc : ‖c‖ ≤ 1)
    (a b : ℕ) (ha : a ≠ 0) :
    Multipliable (fun n : ℕ => 1 + c * q ^ (a * n + b)) := by
  apply multipliable_one_add_of_summable
  refine (summable_norm_pow_lin h a b ha).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

/-- `∏ (1 - q^{2n+1}) = f(q) / f(q²)`. -/
private lemma odd_minus_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 - q ^ (2 * n + 1)) (eulerFunction q / eulerFunction (q ^ 2)) := by
  have hm : Multipliable (fun n : ℕ => 1 - q ^ (2 * n + 1)) := by
    simpa [sub_eq_add_neg] using multipliable_one_add_pow_lin h (-1) (by simp) 2 1 two_ne_zero
  have hodd : HasProd (fun k : ℕ => (fun n : ℕ => 1 - q ^ (n + 1)) (2 * k + 1))
      (eulerFunction (q ^ 2)) := by
    refine (hasProd_eulerFunction (norm_pow_lt h two_ne_zero)).congr_fun fun k => ?_
    simp only [← pow_mul]
    ring_nf
  have hall := HasProd.even_mul_odd (f := fun n : ℕ => 1 - q ^ (n + 1)) hm.hasProd hodd
  have huniq := hall.unique (hasProd_eulerFunction h)
  have hval : eulerFunction q / eulerFunction (q ^ 2) = ∏' n : ℕ, (1 - q ^ (2 * n + 1)) := by
    rw [← huniq, mul_div_assoc, div_self (euler_ne (norm_pow_lt h two_ne_zero)), mul_one]
  rw [hval]
  exact hm.hasProd

/-- `∏ (1 + q^{2n+1}) = f(q²)² / (f(q) f(q⁴))`. -/
private lemma odd_plus_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ => 1 + q ^ (2 * n + 1))
      (eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4))) := by
  have hm : Multipliable (fun n : ℕ => 1 + q ^ (2 * n + 1)) := by
    simpa using multipliable_one_add_pow_lin h 1 (by simp) 2 1 two_ne_zero
  have hprod := hm.hasProd.mul (odd_minus_prod h)
  have he := (odd_minus_prod (norm_pow_lt h two_ne_zero)).congr_fun
    (g := fun n : ℕ => (1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 1))) fun n => by ring
  have huniq := hprod.unique he
  rw [← pow_mul] at huniq
  have h1 := euler_ne h
  have h2 := euler_ne (norm_pow_lt h two_ne_zero)
  have h4 := euler_ne (norm_pow_lt h (by norm_num : (4 : ℕ) ≠ 0))
  have hval : ∏' n : ℕ, (1 + q ^ (2 * n + 1)) =
      eulerFunction (q ^ 2) ^ 2 / (eulerFunction q * eulerFunction (q ^ 4)) := by
    field_simp
    field_simp at huniq
    linear_combination huniq
  rw [← hval]
  exact hm.hasProd

/-! ### Two theta functions as products -/

/-- Exponent of the bilateral series `ψ(-q) = ∑ (-1)^a q^{a(2a-1)}`. -/
private def wPsi (a : ℤ) : ℕ := (a * (2 * a - 1)).toNat

/-- Exponent of the theta series `φ(q) = ∑ q^{m²}`. -/
private def wPhi (m : ℤ) : ℕ := (m * m).toNat

private lemma natCast_wPsi (a : ℤ) : (wPsi a : ℤ) = a * (2 * a - 1) := by
  apply Int.toNat_of_nonneg
  rcases le_or_gt 0 a with ha | ha
  · rcases eq_or_lt_of_le ha with ha | ha
    · subst ha; simp
    · exact mul_nonneg ha.le (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos ha.le (by omega)

private lemma natCast_wPhi (m : ℤ) : (wPhi m : ℤ) = m * m :=
  Int.toNat_of_nonneg (mul_self_nonneg m)

open Analysis.SpecialFunctions.JacobiTripleProduct in
/-- `φ(q) f(q)² f(q⁴)² = f(q²)⁵`, from the Jacobi triple product at `z = 1`. -/
private lemma phi_eq {q : ℂ} (h : ‖q‖ < 1) :
    (∑' m : ℤ, q ^ wPhi m) * (eulerFunction q ^ 2 * eulerFunction (q ^ 4) ^ 2) =
      eulerFunction (q ^ 2) ^ 5 := by
  obtain ⟨-, -, hj⟩ := jacobi_triple_product 1 q one_ne_zero h
  simp only [one_zpow, one_mul, inv_one] at hj
  have hA : HasProd (fun n : ℕ => 1 - q ^ (2 * n + 2)) (eulerFunction (q ^ 2)) :=
    (hasProd_eulerFunction (norm_pow_lt h two_ne_zero)).congr_fun fun n => by
      rw [← pow_mul]; ring_nf
  have hB := odd_plus_prod h
  have hP := (hA.mul hB).mul hB
  rw [show (∑' m : ℤ, q ^ wPhi m) = ∑' m : ℤ, q ^ (m * m).toNat from rfl, hj, hP.tprod_eq]
  have h1 := euler_ne h
  have h4 := euler_ne (norm_pow_lt h (by norm_num : (4 : ℕ) ≠ 0))
  field_simp

open Analysis.SpecialFunctions.JacobiTripleProduct in
/-- `ψ(-q) f(q²) = f(q) f(q⁴)`, from the Jacobi triple product with nome `q²` at `z = -1/q`. -/
private lemma psi_eq {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    (∑' a : ℤ, (a.negOnePow : ℂ) * q ^ wPsi a) * eulerFunction (q ^ 2) =
      eulerFunction q * eulerFunction (q ^ 4) := by
  obtain ⟨-, -, hj⟩ := jacobi_triple_product (-q⁻¹) (q ^ 2) (by simp [hq])
    (norm_pow_lt h two_ne_zero)
  have hterm : ∀ n : ℤ, (-q⁻¹) ^ n * (q ^ 2) ^ (n * n).toNat =
      (n.negOnePow : ℂ) * q ^ wPsi n := by
    intro n
    rw [← pow_mul, ← zpow_natCast q (wPsi n), natCast_wPsi, Int.cast_negOnePow]
    have h2 : ((2 * (n * n).toNat : ℕ) : ℤ) = 2 * (n * n) := by
      push_cast; rw [Int.toNat_of_nonneg (mul_self_nonneg n)]
    rw [← zpow_natCast, h2, neg_eq_neg_one_mul, mul_zpow, inv_zpow', mul_assoc,
      ← zpow_add₀ hq]
    ring_nf
  have hfac : ∀ n : ℕ, (1 - (q ^ 2) ^ (2 * n + 2)) * (1 + (-q⁻¹) * (q ^ 2) ^ (2 * n + 1)) *
      (1 + (-q⁻¹)⁻¹ * (q ^ 2) ^ (2 * n + 1)) =
      (1 - q ^ (4 * n + 4)) * (1 + (-1) * q ^ (4 * n + 1)) * (1 + (-1) * q ^ (4 * n + 3)) := by
    intro n
    have e1 : (q ^ 2) ^ (2 * n + 2) = q ^ (4 * n + 4) := by rw [← pow_mul]; ring_nf
    have e2 : (-q⁻¹) * (q ^ 2) ^ (2 * n + 1) = (-1) * q ^ (4 * n + 1) := by
      rw [← pow_mul, show 2 * (2 * n + 1) = (4 * n + 1) + 1 by ring, pow_succ]
      field_simp
    have e3 : (-q⁻¹)⁻¹ * (q ^ 2) ^ (2 * n + 1) = (-1) * q ^ (4 * n + 3) := by
      rw [inv_neg, inv_inv, ← pow_mul, show 4 * n + 3 = 2 * (2 * n + 1) + 1 by ring, pow_succ]
      ring
    rw [e1, e2, e3]
  simp only [hterm, hfac] at hj
  have hA : HasProd (fun n : ℕ => 1 - q ^ (4 * n + 4)) (eulerFunction (q ^ 4)) :=
    (hasProd_eulerFunction (norm_pow_lt h (by norm_num : (4 : ℕ) ≠ 0))).congr_fun fun n => by
      rw [← pow_mul]; ring_nf
  have hm1 := multipliable_one_add_pow_lin h (-1) (by simp) 4 1 (by norm_num)
  have hm3 := multipliable_one_add_pow_lin h (-1) (by simp) 4 3 (by norm_num)
  have hsplit := HasProd.even_mul_odd (f := fun k : ℕ => 1 + (-1) * q ^ (2 * k + 1))
    (hm1.hasProd.congr_fun fun n => by ring_nf) (hm3.hasProd.congr_fun fun n => by ring_nf)
  have hodd := (odd_minus_prod h).congr_fun (g := fun k : ℕ => 1 + (-1) * q ^ (2 * k + 1))
    fun k => by ring
  have huniq := hsplit.unique hodd
  have hP := (hA.mul hm1.hasProd).mul hm3.hasProd
  rw [hj, hP.tprod_eq, mul_assoc (eulerFunction (q ^ 4)), huniq]
  have h2 := euler_ne (norm_pow_lt h two_ne_zero)
  field_simp

/-! ### The rearrangement of `ψ(-q) φ(q)` -/

/-- The injection of `ℤ × ℤ` into the index set of `ψ(-q) φ(q)`: its image is the set of
pairs `(a, m)` with `m - a` not congruent to `2` modulo `3`. -/
private def embedPair (x : ℤ × ℤ) : ℤ × ℤ :=
  if x.2 % 2 = 0 then (x.1 - x.2 / 2, x.1 + x.2) else (-x.1 + (x.2 + 1) / 2, -x.1 - x.2)

/-- The sign-reversing involution on the pairs `(a, m)` with `m - a ≡ 2 [ZMOD 3]`. -/
private def flipPair (y : ℤ × ℤ) : ℤ × ℤ :=
  (-y.1 - 2 * ((y.2 - y.1 - 2) / 3) - 1, -y.1 + (y.2 - y.1 - 2) / 3 + 1)

private lemma embedPair_injective : Function.Injective embedPair := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [embedPair] at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h ⊢ <;> omega

private lemma mem_range_embedPair (y : ℤ × ℤ) : y ∈ Set.range embedPair ↔ (y.2 - y.1) % 3 ≠ 2 := by
  constructor
  · rintro ⟨⟨j, k⟩, rfl⟩
    simp only [embedPair]
    split_ifs <;> omega
  · intro hy
    rcases (by omega : (y.2 - y.1) % 3 = 0 ∨ (y.2 - y.1) % 3 = 1) with h0 | h1
    · refine ⟨(y.1 + (y.2 - y.1) / 3, 2 * ((y.2 - y.1) / 3)), ?_⟩
      simp only [embedPair]
      split_ifs <;> ext <;> simp <;> omega
    · refine ⟨(-((y.2 - y.1) / 3) - y.1, -2 * ((y.2 - y.1) / 3) - 1), ?_⟩
      simp only [embedPair]
      split_ifs <;> ext <;> simp <;> omega

private lemma flipPair_mem (y : ℤ × ℤ) : ((flipPair y).2 - (flipPair y).1) % 3 = 2 := by
  simp only [flipPair]
  omega

private lemma flipPair_flipPair {y : ℤ × ℤ} (hy : (y.2 - y.1) % 3 = 2) :
    flipPair (flipPair y) = y := by
  simp only [flipPair]
  ext <;> simp <;> omega

private lemma weight_flipPair {y : ℤ × ℤ} (hy : (y.2 - y.1) % 3 = 2) :
    wPsi (flipPair y).1 + wPhi (flipPair y).2 = wPsi y.1 + wPhi y.2 := by
  obtain ⟨a, m⟩ := y
  obtain ⟨u, hu⟩ : ∃ u, m = a + 3 * u + 2 := ⟨(m - a - 2) / 3, by simp at hy; omega⟩
  have hd : (m - a - 2) / 3 = u := by omega
  apply Nat.cast_injective (R := ℤ)
  push_cast
  simp only [flipPair, natCast_wPsi, natCast_wPhi]
  rw [hd, hu]
  ring

private lemma sign_flipPair (y : ℤ × ℤ) : ((flipPair y).1).negOnePow = -(y.1.negOnePow) := by
  simp only [flipPair]
  rw [Int.negOnePow_sub, Int.negOnePow_sub, Int.negOnePow_neg, Int.negOnePow_two_mul,
    Int.negOnePow_one]
  simp

private lemma weight_embedPair (x : ℤ × ℤ) :
    wPsi (embedPair x).1 + wPhi (embedPair x).2 = 2 * pentagonal x.1 + pentagonal (-x.2) := by
  obtain ⟨j, k⟩ := x
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [two_mul_natCast_pentagonal, natCast_pentagonal]
  simp only [embedPair]
  split_ifs with hk
  · obtain ⟨u, rfl⟩ : ∃ u, k = 2 * u := ⟨k / 2, by omega⟩
    have h1 : 2 * u / 2 = u := by omega
    have h2 : -(2 * u) * (3 * -(2 * u) - 1) / 2 = u * (6 * u + 1) := by
      rw [show -(2 * u) * (3 * -(2 * u) - 1) = 2 * (u * (6 * u + 1)) by ring]
      omega
    simp only [h1, h2, natCast_wPsi, natCast_wPhi]
    ring
  · obtain ⟨v, rfl⟩ : ∃ v, k = 2 * v + 1 := ⟨k / 2, by omega⟩
    have h1 : (2 * v + 1 + 1) / 2 = v + 1 := by omega
    have h2 : -(2 * v + 1) * (3 * -(2 * v + 1) - 1) / 2 = (2 * v + 1) * (3 * v + 2) := by
      rw [show -(2 * v + 1) * (3 * -(2 * v + 1) - 1) = 2 * ((2 * v + 1) * (3 * v + 2)) by ring]
      omega
    simp only [h1, h2, natCast_wPsi, natCast_wPhi]
    ring

private lemma sign_embedPair (x : ℤ × ℤ) :
    ((embedPair x).1).negOnePow = x.1.negOnePow * ((x.2 + 1) / 2).negOnePow := by
  obtain ⟨j, k⟩ := x
  simp only [embedPair]
  split_ifs with hk
  · have h1 : k / 2 = (k + 1) / 2 := by omega
    rw [h1, Int.negOnePow_sub]
  · rw [Int.negOnePow_add, Int.negOnePow_neg]

/-- A bilateral series `∑ c a q^{w a}` with `|c a| ≤ 1` and `|a| ≤ w a` converges absolutely. -/
private lemma summable_norm_int {q : ℂ} (h : ‖q‖ < 1) (c : ℤ → ℂ) (hc : ∀ a, ‖c a‖ ≤ 1)
    (w : ℤ → ℕ) (hw : ∀ a, a.natAbs ≤ w a) : Summable (fun a : ℤ => ‖c a * q ^ w a‖) := by
  have hgeo : Summable (fun a : ℤ => ‖q‖ ^ a.natAbs) := by
    apply Summable.of_nat_of_neg
    · simpa using summable_geometric_of_lt_one (norm_nonneg q) h
    · simpa using summable_geometric_of_lt_one (norm_nonneg q) h
  refine hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) fun a => ?_
  rw [norm_mul, norm_pow]
  calc ‖c a‖ * ‖q‖ ^ w a ≤ 1 * ‖q‖ ^ a.natAbs :=
        mul_le_mul (hc a) (pow_le_pow_of_le_one (norm_nonneg q) h.le (hw a)) (by positivity)
          zero_le_one
    _ = ‖q‖ ^ a.natAbs := one_mul _

private lemma natAbs_le_wPsi (a : ℤ) : a.natAbs ≤ wPsi a := by
  zify
  rw [natCast_wPsi]
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha]; nlinarith
  · subst ha; simp
  · rw [abs_of_pos ha]; nlinarith

private lemma natAbs_le_wPhi (m : ℤ) : m.natAbs ≤ wPhi m := by
  zify
  rw [natCast_wPhi]
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [abs_of_neg hm]; nlinarith
  · subst hm; simp
  · rw [abs_of_pos hm]; nlinarith

private lemma natAbs_le_two_mul_pentagonal (j : ℤ) : j.natAbs ≤ 2 * pentagonal j := by
  zify
  rw [two_mul_natCast_pentagonal]
  rcases lt_trichotomy j 0 with hj | hj | hj
  · rw [abs_of_neg hj]; nlinarith
  · subst hj; simp
  · rw [abs_of_pos hj]; nlinarith

private lemma natAbs_le_pentagonal_neg (k : ℤ) : k.natAbs ≤ pentagonal (-k) := by
  have h2 := two_mul_natCast_pentagonal_neg k
  zify
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [abs_of_neg hk]; nlinarith
  · subst hk; simp
  · rw [abs_of_pos hk]; nlinarith

/-- `ψ(-q) φ(q) = f(q²) ∑ (-1)^{⌈k/2⌉} q^{k(3k+1)/2}`. -/
private lemma bilinear {q : ℂ} (h : ‖q‖ < 1) :
    (∑' a : ℤ, (a.negOnePow : ℂ) * q ^ wPsi a) * (∑' m : ℤ, q ^ wPhi m) =
      eulerFunction (q ^ 2) * ∑' k : ℤ, (((k + 1) / 2).negOnePow : ℂ) * q ^ pentagonal (-k) := by
  have hs1 : Summable (fun a : ℤ => ‖(a.negOnePow : ℂ) * q ^ wPsi a‖) :=
    summable_norm_int h _ (fun a => by simp) wPsi natAbs_le_wPsi
  have hs2 : Summable (fun m : ℤ => ‖q ^ wPhi m‖) := by
    simpa using summable_norm_int h (fun _ => 1) (fun _ => by simp) wPhi natAbs_le_wPhi
  set g : ℤ × ℤ → ℂ := fun y => ((y.1.negOnePow : ℂ) * q ^ wPsi y.1) * q ^ wPhi y.2 with hg_def
  have hg : Summable g :=
    summable_mul_of_summable_norm (f := fun a : ℤ => (a.negOnePow : ℂ) * q ^ wPsi a)
      (g := fun m : ℤ => q ^ wPhi m) hs1 hs2
  rw [tsum_mul_tsum_of_summable_norm (f := fun a : ℤ => (a.negOnePow : ℂ) * q ^ wPsi a)
      (g := fun m : ℤ => q ^ wPhi m) hs1 hs2]
  change ∑' y, g y = _
  rw [← hg.tsum_subtype_add_tsum_subtype_compl (Set.range embedPair),
    tsum_range g embedPair_injective]
  have hmem : ∀ y : ℤ × ℤ, y ∈ (Set.range embedPair)ᶜ ↔ (y.2 - y.1) % 3 = 2 := by
    intro y
    rw [Set.mem_compl_iff, mem_range_embedPair]
    omega
  -- The terms outside the range of `embedPair` cancel in pairs.
  have hC : ∑' y : ↥(Set.range embedPair)ᶜ, g y = 0 := by
    let τ : ↥(Set.range embedPair)ᶜ ≃ ↥(Set.range embedPair)ᶜ :=
      { toFun := fun y => ⟨flipPair y, (hmem _).2 (flipPair_mem _)⟩
        invFun := fun y => ⟨flipPair y, (hmem _).2 (flipPair_mem _)⟩
        left_inv := fun y => Subtype.ext (flipPair_flipPair ((hmem _).1 y.2))
        right_inv := fun y => Subtype.ext (flipPair_flipPair ((hmem _).1 y.2)) }
    have h1 := Equiv.tsum_eq τ (fun y => g y)
    have h2 : ∀ y : ↥(Set.range embedPair)ᶜ, g (τ y) = -g y := by
      intro y
      simp only [τ, Equiv.coe_fn_mk, hg_def]
      rw [mul_assoc, ← pow_add, weight_flipPair ((hmem _).1 y.2), sign_flipPair, mul_assoc,
        ← pow_add]
      simp
    simp_rw [h2, tsum_neg] at h1
    linear_combination (-1 / 2 : ℂ) * h1
  rw [hC, add_zero]
  -- The terms in the range of `embedPair` give the product of two series.
  have hΦ : ∀ x : ℤ × ℤ, g (embedPair x) = ((x.1.negOnePow : ℂ) * (q ^ 2) ^ pentagonal x.1) *
      ((((x.2 + 1) / 2).negOnePow : ℂ) * q ^ pentagonal (-x.2)) := by
    intro x
    simp only [hg_def]
    rw [mul_assoc, ← pow_add, weight_embedPair, sign_embedPair, ← pow_mul, pow_add]
    push_cast
    ring
  have he : Summable (fun j : ℤ => ‖(j.negOnePow : ℂ) * (q ^ 2) ^ pentagonal j‖) :=
    (summable_norm_int h (fun j : ℤ => (j.negOnePow : ℂ)) (fun a => by simp)
      (fun j => 2 * pentagonal j) natAbs_le_two_mul_pentagonal).congr fun j => by rw [pow_mul]
  have hr : Summable (fun k : ℤ => ‖(((k + 1) / 2).negOnePow : ℂ) * q ^ pentagonal (-k)‖) :=
    summable_norm_int h (fun k : ℤ => (((k + 1) / 2).negOnePow : ℂ)) (fun a => by simp)
      (fun k => pentagonal (-k)) natAbs_le_pentagonal_neg
  rw [tsum_congr hΦ, ← tsum_mul_tsum_of_summable_norm
      (f := fun j : ℤ => (j.negOnePow : ℂ) * (q ^ 2) ^ pentagonal j)
      (g := fun k : ℤ => (((k + 1) / 2).negOnePow : ℂ) * q ^ pentagonal (-k)) he hr,
    (hasSum_eulerFunction_pentagonal (norm_pow_lt h two_ne_zero)).tsum_eq]

/-- The quintuple product identity at `z = i` on the punctured unit disk:
`R(q) f(q) f(q⁴) = f(q²)³` with `R(q) = ∑ (-1)^{⌈k/2⌉} q^{k(3k+1)/2}`. -/
private lemma analytic_identity {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    (∑' k : ℤ, (((k + 1) / 2).negOnePow : ℂ) * q ^ pentagonal (-k)) *
        (eulerFunction q * eulerFunction (q ^ 4)) = eulerFunction (q ^ 2) ^ 3 := by
  have hψ := psi_eq hq h
  have hφ := phi_eq h
  have hb := bilinear h
  set Φ := ∑' m : ℤ, q ^ wPhi m
  have h1 := euler_ne h
  have h2 := euler_ne (norm_pow_lt h two_ne_zero)
  have h4 := euler_ne (norm_pow_lt h (by norm_num : (4 : ℕ) ≠ 0))
  have hne : eulerFunction (q ^ 2) ^ 2 * (eulerFunction q * eulerFunction (q ^ 4)) ≠ 0 := by
    positivity
  refine mul_left_cancel₀ hne ?_
  linear_combination
    (-(eulerFunction (q ^ 2)) * eulerFunction q ^ 2 * eulerFunction (q ^ 4) ^ 2) * hb +
      (Φ * eulerFunction q ^ 2 * eulerFunction (q ^ 4) ^ 2) * hψ +
      (eulerFunction q * eulerFunction (q ^ 4)) * hφ

/-! ### From functions on the disk to integer power series -/

section Transfer

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

private lemma represents_const (c : ℤ) : Represents (C c) (fun _ ↦ (c : ℂ)) := by
  intro τ
  refine (hasSum_ite_eq (0 : ℕ) (c : ℂ)).congr_fun fun n ↦ ?_
  rw [coeff_C]
  split_ifs with h <;> simp_all

private lemma Represents.pow {F : ℤ⟦X⟧} {f : ℂ → ℂ} (hf : Represents F f) (n : ℕ) :
    Represents (F ^ n) (fun q ↦ f q ^ n) := by
  induction n with
  | zero => simpa using represents_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private lemma qEulerProduct_eq_expand (k : ℕ) (hk : k ≠ 0) :
    qEulerProduct k = expand k hk (pentagonalSeries ℤ) := by
  have cont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have prod := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) cont
  simpa [qEulerProduct, Function.comp_def, pow_mul] using prod.tprod_eq

private lemma represents_euler (k : ℕ) (hk : k ≠ 0) :
    Represents (qEulerProduct k) (fun q ↦ eulerFunction (q ^ k)) := by
  rw [qEulerProduct_eq_expand k hk]
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

/-- The coefficient of `q^n` in `∑ (-1)^{⌈m/2⌉} q^{m(3m+1)/2}`, written as in the statement. -/
private def rcoeff (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
    if m * (3 * m + 1) / 2 = n then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0

private lemma ediv_eq_iff_pentagonal (m : ℤ) (n : ℕ) :
    m * (3 * m + 1) / 2 = n ↔ pentagonal (-m) = n := by
  rw [← Nat.cast_inj (R := ℤ), natCast_pentagonal]
  constructor <;> intro h <;> rw [← h] <;> ring_nf

private lemma rcoeff_pentagonal (k : ℤ) :
    rcoeff (pentagonal (-k)) = (((k + 1) / 2).negOnePow : ℤ) := by
  have hk : k ∈ Finset.Icc (-(pentagonal (-k) : ℤ)) (pentagonal (-k)) := by
    have := natAbs_le_pentagonal_neg k
    rw [Finset.mem_Icc]
    omega
  unfold rcoeff
  rw [Finset.sum_eq_single_of_mem k hk fun m _ hmk => ite_eq_right (by
      rw [ediv_eq_iff_pentagonal, pentagonal_inj, neg_inj]
      exact hmk),
    ite_eq_left ((ediv_eq_iff_pentagonal k _).mpr rfl)]
  have h := Int.coe_negOnePow ℤ ((k + 1) / 2)
  rw [Int.cast_id] at h
  exact h.symm

private lemma rcoeff_eq_zero {n : ℕ} (hn : n ∉ Set.range fun k : ℤ => pentagonal (-k)) :
    rcoeff n = 0 := by
  refine Finset.sum_eq_zero fun m _ => ite_eq_right ?_
  rw [ediv_eq_iff_pentagonal]
  exact fun h => hn ⟨m, h⟩

/-- The integer power series `R = ∑ (-1)^{⌈m/2⌉} q^{m(3m+1)/2}`. -/
private noncomputable def Rser : ℤ⟦X⟧ := PowerSeries.mk rcoeff

private lemma represents_R : Represents Rser
    (fun q => ∑' k : ℤ, (((k + 1) / 2).negOnePow : ℂ) * q ^ pentagonal (-k)) := by
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hs : Summable (fun k : ℤ => (((k + 1) / 2).negOnePow : ℂ) * 𝕢 τ ^ pentagonal (-k)) :=
    (summable_norm_int lt1 (fun k : ℤ => (((k + 1) / 2).negOnePow : ℂ)) (fun a => by simp)
      (fun k => pentagonal (-k)) natAbs_le_pentagonal_neg).of_norm
  have inj : Function.Injective (fun k : ℤ => pentagonal (-k)) :=
    fun a b h => neg_injective (pentagonal_injective h)
  apply (inj.hasSum_iff ?_).mp
  · refine hs.hasSum.congr_fun fun k => ?_
    simp only [Function.comp_apply, Rser, coeff_mk, rcoeff_pentagonal]
  · intro n hn
    simp [Rser, rcoeff_eq_zero hn]

/-- The quintuple product identity at `z = i` in `ℤ⟦X⟧`: `R f₁ f₄ = f₂³`. -/
private lemma formal_R : Rser * (qEulerProduct 1 * qEulerProduct 4) = qEulerProduct 2 ^ 3 := by
  have h1 := represents_euler 1 one_ne_zero
  have h2 := represents_euler 2 two_ne_zero
  have h4 := represents_euler 4 (by norm_num)
  exact (represents_R.mul (h1.mul h4)).eq_of_eval (h2.pow 3) fun q hq h => by
    simpa using analytic_identity hq h

end Transfer

/-! ### The generating function of partitions into distinct odd parts -/

/-- The generating function `D = ∑ pdo(n) q^n` of partitions into distinct odd parts. -/
private noncomputable def Dser : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((Nat.Partition.oddDistincts n).card : ℤ)

private lemma genFun_term (i : ℕ) :
    (1 : ℤ⟦X⟧) + ∑' j : ℕ, (if ¬ Even (i + 1) ∧ j + 1 < 2 then (1 : ℤ) else 0) •
      X ^ ((i + 1) * (j + 1)) = if ¬ Even (i + 1) then 1 + X ^ (i + 1) else 1 := by
  rw [tsum_eq_single 0 fun j hj => by
    have : ¬ (j + 1 < 2) := by omega
    simp [this]]
  by_cases hi : Even (i + 1) <;> simp [hi]

private lemma coeff_Dser_eq (n : ℕ) : Dser.coeff n = (Nat.Partition.genFun
    (fun i c => if ¬ Even i ∧ c < 2 then (1 : ℤ) else 0)).coeff n := by
  simp only [Dser, coeff_mk, Nat.Partition.coeff_genFun, Finsupp.prod]
  simp_rw [Finset.prod_boole]
  rw [Finset.sum_boole]
  congr 2
  ext p
  simp only [Nat.Partition.oddDistincts, Nat.Partition.odds, Nat.Partition.distincts,
    Nat.Partition.restricted, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Multiset.nodup_iff_count_le_one, Multiset.toFinsupp_support, Multiset.toFinsupp_apply,
    Multiset.mem_toFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine fun i hi => ⟨h1 i hi, ?_⟩
    have := h2 i
    omega
  · intro h
    refine ⟨fun i hi => (h i hi).1, fun a => ?_⟩
    by_cases ha : a ∈ p.parts
    · have := (h a ha).2
      omega
    · simp [Multiset.count_eq_zero.mpr ha]

private lemma hasProd_Dser_all :
    HasProd (fun i : ℕ => if ¬ Even (i + 1) then (1 : ℤ⟦X⟧) + X ^ (i + 1) else 1) Dser := by
  have h := Nat.Partition.hasProd_genFun (fun i c => if ¬ Even i ∧ c < 2 then (1 : ℤ) else 0)
  rw [show Nat.Partition.genFun (fun i c => if ¬ Even i ∧ c < 2 then (1 : ℤ) else 0) = Dser from
    (PowerSeries.ext coeff_Dser_eq).symm] at h
  exact h.congr_fun fun i => (genFun_term i).symm

private lemma tendsto_order_X_pow_lin (a b : ℕ) (ha : a ≠ 0) :
    Filter.Tendsto (fun k : ℕ => ((X : ℤ⟦X⟧) ^ (a * k + b)).order) Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n =>
    Filter.eventually_atTop.mpr ⟨n + 1, fun k hk => ?_⟩
  rw [order_X_pow]
  norm_cast
  nlinarith [Nat.one_le_iff_ne_zero.mpr ha]

private lemma multipliable_one_add_X_pow_lin (a b : ℕ) (ha : a ≠ 0) :
    Multipliable (fun k : ℕ => (1 : ℤ⟦X⟧) + X ^ (a * k + b)) :=
  WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℤ
    (tendsto_order_X_pow_lin a b ha)

private lemma multipliable_one_sub_X_pow_lin (a b : ℕ) (ha : a ≠ 0) :
    Multipliable (fun k : ℕ => (1 : ℤ⟦X⟧) - X ^ (a * k + b)) := by
  simp_rw [sub_eq_add_neg]
  refine WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℤ ?_
  simpa only [order_neg] using tendsto_order_X_pow_lin a b ha

/-- `D = ∏ (1 + q^{2k+1})`. -/
private lemma hasProd_Dser : HasProd (fun k : ℕ => (1 : ℤ⟦X⟧) + X ^ (2 * k + 1)) Dser := by
  have hm := multipliable_one_add_X_pow_lin 2 1 two_ne_zero
  have hsplit := HasProd.even_mul_odd
    (f := fun i : ℕ => if ¬ Even (i + 1) then (1 : ℤ⟦X⟧) + X ^ (i + 1) else 1)
    (hm.hasProd.congr_fun fun k => by
      have : ¬ Even (2 * k + 1) := by simp [parity_simps]
      simp [this])
    (hasProd_one.congr_fun fun k => by
      have : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
      simp [this])
  rw [mul_one] at hsplit
  rw [← hsplit.unique hasProd_Dser_all]
  exact hm.hasProd

private lemma hasProd_qEulerProduct (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun m : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (m + 1))) (qEulerProduct k) := by
  have hm : Multipliable (fun m : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (m + 1))) := by
    refine (multipliable_one_sub_X_pow_lin k k hk).congr fun m => ?_
    ring_nf
  exact hm.hasProd

/-- `D f₁ f₄ = f₂²`, from `(1 + q^{2k+1}) (1 - q^{2k+1}) = 1 - q^{4k+2}`. -/
private lemma formal_D : Dser * (qEulerProduct 1 * qEulerProduct 4) = qEulerProduct 2 ^ 2 := by
  have hO := (multipliable_one_sub_X_pow_lin 2 1 two_ne_zero).hasProd
  have hO₂ := (multipliable_one_sub_X_pow_lin 4 2 (by norm_num)).hasProd
  set O := ∏' k : ℕ, ((1 : ℤ⟦X⟧) - X ^ (2 * k + 1))
  set O₂ := ∏' k : ℕ, ((1 : ℤ⟦X⟧) - X ^ (4 * k + 2))
  have h1 : O * qEulerProduct 2 = qEulerProduct 1 := by
    have hs := HasProd.even_mul_odd (f := fun m : ℕ => (1 : ℤ⟦X⟧) - X ^ (1 * (m + 1)))
      (hO.congr_fun fun k => by ring_nf)
      ((hasProd_qEulerProduct 2 two_ne_zero).congr_fun fun k => by ring_nf)
    exact hs.unique (hasProd_qEulerProduct 1 one_ne_zero)
  have h2 : O₂ * qEulerProduct 4 = qEulerProduct 2 := by
    have hs := HasProd.even_mul_odd (f := fun m : ℕ => (1 : ℤ⟦X⟧) - X ^ (2 * (m + 1)))
      (hO₂.congr_fun fun k => by ring_nf)
      ((hasProd_qEulerProduct 4 (by norm_num)).congr_fun fun k => by ring_nf)
    exact hs.unique (hasProd_qEulerProduct 2 two_ne_zero)
  have h3 : Dser * O = O₂ := (hasProd_Dser.mul hO).unique (hO₂.congr_fun fun k => by ring)
  calc Dser * (qEulerProduct 1 * qEulerProduct 4)
      = (Dser * O) * qEulerProduct 2 * qEulerProduct 4 := by rw [← h1]; ring
    _ = qEulerProduct 2 * (O₂ * qEulerProduct 4) := by rw [h3]; ring
    _ = qEulerProduct 2 ^ 2 := by rw [h2]; ring

/-! ### Reading off coefficients -/

/-- `R = f₂ D`: the generating-function form of the recurrence. -/
private lemma Rser_eq : Rser = qEulerProduct 2 * Dser := by
  have hne : qEulerProduct 1 * qEulerProduct 4 ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [map_mul, constantCoeff_qEulerProduct le_rfl,
      constantCoeff_qEulerProduct (by norm_num), map_zero] at this
    exact absurd this (by norm_num)
  refine mul_right_cancel₀ hne ?_
  rw [formal_R, mul_assoc, formal_D]
  ring

private lemma toNat_eq_two_mul_pentagonal (k : ℤ) :
    (k * (3 * k + 1)).toNat = 2 * pentagonal (-k) := by
  have h := two_mul_natCast_pentagonal_neg k
  have hnn : 0 ≤ k * (3 * k + 1) := by rw [← h]; positivity
  zify
  rw [Int.toNat_of_nonneg hnn, h]

private lemma coeff_qEulerProduct_two (k : ℤ) :
    (qEulerProduct 2).coeff (k * (3 * k + 1)).toNat = (-1 : ℤ) ^ k.natAbs := by
  rw [toNat_eq_two_mul_pentagonal, qEulerProduct_eq_expand 2 two_ne_zero, coeff_expand_mul,
    coeff_pentagonalSeries_pentagonal, Int.negOnePow_neg, Int.coe_negOnePow]

private lemma coeff_qEulerProduct_two_eq_zero {n i : ℕ} (hi : i ≤ n)
    (hS : i ∉ ((Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ))).image
      fun k : ℤ => (k * (3 * k + 1)).toNat) :
    (qEulerProduct 2).coeff i = 0 := by
  rw [qEulerProduct_eq_expand 2 two_ne_zero, coeff_expand]
  split_ifs with hd
  · by_contra hne
    have hr : i / 2 ∈ Set.range pentagonal := by
      by_contra hr
      exact hne (coeff_pentagonalSeries_eq_zero ℤ hr)
    obtain ⟨j, hj⟩ := hr
    apply hS
    rw [Finset.mem_image]
    refine ⟨-j, ?_, ?_⟩
    · have h1 := natAbs_le_pentagonal_neg (-j)
      have h2 := two_mul_natCast_pentagonal_neg (-j)
      rw [neg_neg] at h1 h2
      have hi' : (i : ℤ) = 2 * pentagonal j := by omega
      rw [Finset.mem_filter, Finset.mem_Icc, ← h2]
      have h1' : ((-j).natAbs : ℤ) ≤ pentagonal j := by exact_mod_cast h1
      rw [Int.natCast_natAbs, abs_le] at h1'
      omega
    · rw [toNat_eq_two_mul_pentagonal, neg_neg, hj]
      omega
  · rfl

end oddDistincts_pentagonal_recurrence

open oddDistincts_pentagonal_recurrence in
/-- **Pentagonal recurrence for partitions into distinct odd parts.** Let $\operatorname{pdo}(m)$
be the number of partitions of $m$ into distinct odd parts. For every $n \ge 0$, the sum
$\sum_k (-1)^k \operatorname{pdo}(n - k(3k+1))$ over the integers $k$ with $k(3k+1) \le n$
equals $(-1)^{\lceil m/2 \rceil}$ if $n = m(3m+1)/2$ for some integer $m$, and $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 4 (`integers-2026-A60-cor-4`). -/
public theorem oddDistincts_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * ((Nat.Partition.oddDistincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          if m * (3 * m + 1) / 2 = n then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0 := by
  change _ = rcoeff n
  have hR : rcoeff n = (qEulerProduct 2 * Dser).coeff n := by
    rw [← Rser_eq, Rser, coeff_mk]
  rw [hR, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  set S := (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)) with hS
  have hsub : S.image (fun k : ℤ => (k * (3 * k + 1)).toNat) ⊆ Finset.range (n + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [hS, Finset.mem_filter] at hk
    rw [Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun k : ℤ => (k * (3 * k + 1)).toNat) S := by
    intro a _ b _ hab
    simp only [toNat_eq_two_mul_pentagonal] at hab
    exact neg_injective (pentagonal_injective (by omega))
  rw [← Finset.sum_subset hsub fun i hi hiS => by
      rw [coeff_qEulerProduct_two_eq_zero (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hiS,
        zero_mul],
    Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_qEulerProduct_two, Dser, coeff_mk]

end MetaMathlibExt

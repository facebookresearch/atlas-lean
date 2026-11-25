/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Insert
public import MathlibExt.NumberTheory.TwoPrimeDCarmichael
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Absolute Lucas pseudoprimes of the form $3qr$

We classify the six products of this form and show that each determines its three Jacobi signs.
-/

namespace MetaMathlibExt.threeQR_isDCarmichael_iff

/-- Dividing at the larger prime leaves a quotient of one or two. Eliminating the larger
prime then makes the smaller prime minus its sign divide a nonzero integer of size at most 20. -/
private lemma bounds {q r a b c : ℤ} (hq : 3 < q) (hgap : q + 2 ≤ r)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1)
    (hdq : q - b ∣ 3 * r - a * c) (hdr : r - c ∣ 3 * q - a * b) :
    q ≤ 21 ∧ r ≤ 65 := by
  obtain ⟨k, hk⟩ := hdr
  have hab : a * b = 1 ∨ a * b = -1 := by
    rcases ha with rfl | rfl <;> simp [hb]; omega
  have hpos : 0 < r - c := by omega
  have hkpos : 0 < k := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos hpos.le hn
    omega
  have hksmall : k < 3 := by
    by_contra! hn
    have hc₁ : c ≤ 1 := by omega
    have hab₁ : -1 ≤ a * b := by omega
    nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hn)]
  have hk12 : k = 1 ∨ k = 2 := by omega
  obtain ⟨j, hj⟩ := hdq
  have hd : q - b ∣ (3 - a) * (3 * b + k * c) := by
    refine ⟨k * j - 9, ?_⟩
    linear_combination k * hj + 3 * hk
  have hconst : (3 - a) * (3 * b + k * c) ≠ 0 ∧
      ((3 - a) * (3 * b + k * c)).natAbs ≤ 20 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> rcases hk12 with rfl | rfl <;> decide
  have hle := (Int.natAbs_le_of_dvd_ne_zero hd hconst.1).trans hconst.2
  rcases hk12 with rfl | rfl <;> omega

private def signature : ℕ → ℤ × ℤ × ℤ
  | 105 => (-1, 1, -1)
  | 195 => (1, 1, -1)
  | 255 | 2703 => (-1, 1, 1)
  | 399 => (-1, -1, -1)
  | _ => (1, 1, 1)

private def sign (s : Bool) : ℤ := if s then 1 else -1

private lemma encode_sign {e : ℤ} (he : e = 1 ∨ e = -1) : ∃ s, e = sign s := by
  rcases he with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

/-- Check both divisibilities for the bounded primes and all eight possible sign triples. -/
private lemma bounded_cases :
    ∀ q : Fin 22, 3 < q.val → q.val.Prime →
    ∀ r : Fin 66, q.val < r.val → r.val.Prime →
    ∀ i j k : Bool, let a := sign i; let b := sign j; let c := sign k
    (q.val : ℤ) - b ∣ 3 * r.val - a * c → (r.val : ℤ) - c ∣ 3 * q.val - a * b →
    let n := 3 * q.val * r.val
    n ∈ ({105, 195, 255, 399, 561, 2703} : Finset ℕ) ∧ (a, b, c) = signature n := by
  decide

private lemma classify {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (h3q : 3 < q) (hqr : q < r)
    {D : ℤ} (h : IsDCarmichael D (3 * q * r)) :
    3 * q * r ∈ ({105, 195, 255, 399, 561, 2703} : Finset ℕ) ∧
      (jacobiSym D 3, jacobiSym D q, jacobiSym D r) = signature (3 * q * r) := by
  have oq := hq.odd_of_ne_two (by omega)
  have or' := hr.odd_of_ne_two (by omega)
  have h₃q := (Nat.coprime_primes Nat.prime_three hq).mpr h3q.ne
  have h₃r := (Nat.coprime_primes Nat.prime_three hr).mpr (by omega)
  have hcqr := (Nat.coprime_primes hq hr).mpr hqr.ne
  have hdq := cofactor_dvd hq (h₃q.mul_left hcqr.symm)
    (by simpa [mul_right_comm] using h : IsDCarmichael D (3 * r * q))
  have hdr := cofactor_dvd hr (h₃r.mul_left hcqr) h
  rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_right' D (by decide) hr.ne_zero] at hdq
  rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_right' D (by decide) hq.ne_zero] at hdr
  have hc := h.2.2.2.2.1
  simp only [Nat.cast_mul, IsCoprime.mul_right_iff] at hc
  have signs {p : ℕ} (hp : IsCoprime D p) :=
    jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hp)
  have gap : (q : ℤ) + 2 ≤ r := by obtain ⟨u, hu⟩ := oq; obtain ⟨v, hv⟩ := or'; omega
  have hbound := bounds (by exact_mod_cast h3q) gap (signs hc.1.1) (signs hc.1.2) (signs hc.2)
    hdq hdr
  obtain ⟨i, hi⟩ := encode_sign (signs hc.1.1)
  obtain ⟨j, hj⟩ := encode_sign (signs hc.1.2)
  obtain ⟨k, hk⟩ := encode_sign (signs hc.2)
  rw [hi, hj, hk] at hdq hdr ⊢
  exact bounded_cases ⟨q, by omega⟩ h3q hq ⟨r, by omega⟩ hqr hr i j k hdq hdr

/-- Local vanishing at each of the three distinct primes gives vanishing modulo their product. -/
private lemma of_orders {D : ℤ} (q r : ℕ)
    (h : q.Prime ∧ r.Prime ∧ 3 < q ∧ q < r ∧
      (D % 4 = 0 ∨ D % 4 = 1) ∧ D.gcd (3 * q * r) = 1)
    (hd : let n := ((↑(3 * q * r) : ℤ) - jacobiSym D (3 * q * r)).toNat
      (3 - jacobiSym D 3).toNat ∣ n ∧ ((q : ℤ) - jacobiSym D q).toNat ∣ n ∧
        ((r : ℤ) - jacobiSym D r).toNat ∣ n) :
    IsDCarmichael D (3 * q * r) := by
  obtain ⟨hq, hr, h3q, hqr, hD, hc⟩ := h
  have cop := Int.isCoprime_iff_gcd_eq_one.mpr hc
  have oq := hq.odd_of_ne_two (by omega)
  have or' := hr.odd_of_ne_two (by omega)
  have h₃q := (Nat.coprime_primes Nat.prime_three hq).mpr h3q.ne
  have h₃r := (Nat.coprime_primes Nat.prime_three hr).mpr (by omega)
  have hcqr := (Nat.coprime_primes hq hr).mpr hqr.ne
  refine ⟨hD, ((by decide : Odd 3).mul oq).mul or', by nlinarith, ?_, cop, ?_⟩
  · simp [Nat.prime_mul_iff, hr.ne_one, hq.ne_one]
  · intro s _ hdisc hQ
    simp only [Nat.cast_mul, IsCoprime.mul_right_iff] at cop hQ
    apply (h₃r.mul_left hcqr).isCoprime.mul_dvd
    · rw [Nat.cast_mul]
      apply h₃q.isCoprime.mul_dvd
      · exact dvd_lucas_of_local_order_dvd Nat.prime_three (by decide) cop.1.1 s hdisc hQ.1.1 hd.1
      · exact dvd_lucas_of_local_order_dvd hq (by omega) cop.1.2 s hdisc hQ.1.2 hd.2.1
    · exact dvd_lucas_of_local_order_dvd hr (by omega) cop.2 s hdisc hQ.2 hd.2.2

private lemma exists_of_mem {n : ℕ} (hn : n ∈ ({105, 195, 255, 399, 561, 2703} : Finset ℕ)) :
    ∃ D : ℤ, IsDCarmichael D n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨41, of_orders 5 7 (by decide) (by norm_num)⟩
  · exact ⟨76, of_orders 5 13 (by decide) (by norm_num)⟩
  · exact ⟨89, of_orders 5 17 (by decide) (by norm_num)⟩
  · exact ⟨41, of_orders 7 19 (by decide) (by norm_num)⟩
  · exact ⟨1, of_orders 11 17 (by decide) (by norm_num)⟩
  · exact ⟨77, of_orders 17 53 (by decide) (by norm_num)⟩

end MetaMathlibExt.threeQR_isDCarmichael_iff

namespace MetaMathlibExt

open threeQR_isDCarmichael_iff

/-- **The $D$-Carmichael numbers of the form $3qr$.** Let $q < r$ be primes with $3 < q$. Then
$3qr$ is a $D$-Carmichael number for some integer $D$ if and only if $3qr$ is one of $105$,
$195$, $255$, $399$, $561$ and $2703$. Moreover, for all integers $D$ and $D'$ such that $3qr$
is both $D$-Carmichael and $D'$-Carmichael, the Jacobi symbols agree at $3$, $q$ and $r$:
$(D \mid 3) = (D' \mid 3)$, $(D \mid q) = (D' \mid q)$ and $(D \mid r) = (D' \mid r)$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 7 (`integers-2026-A102-thm-7`). -/
public theorem threeQR_isDCarmichael_iff {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (h3q : 3 < q) (hqr : q < r) :
    ((∃ D : ℤ, IsDCarmichael D (3 * q * r)) ↔
      3 * q * r ∈ ({105, 195, 255, 399, 561, 2703} : Finset ℕ)) ∧
    ∀ D D' : ℤ, IsDCarmichael D (3 * q * r) → IsDCarmichael D' (3 * q * r) →
      jacobiSym D 3 = jacobiSym D' 3 ∧ jacobiSym D q = jacobiSym D' q ∧
        jacobiSym D r = jacobiSym D' r := by
  refine ⟨⟨fun ⟨_, h⟩ => (classify hq hr h3q hqr h).1, exists_of_mem⟩, ?_⟩
  intro D D' h h'
  have he := (classify hq hr h3q hqr h).2.trans (classify hq hr h3q hqr h').2.symm
  simpa only [Prod.mk.injEq] using he

end MetaMathlibExt

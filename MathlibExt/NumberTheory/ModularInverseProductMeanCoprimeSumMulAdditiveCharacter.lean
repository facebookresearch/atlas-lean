/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import MathlibExt.NumberTheory.ModularInverseProductMean
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Weighted additive character sum over reduced residues

This module proves `coprime_sum_mul_additive_character`: Möbius inversion over the divisors
rewrites the coprime-weighted character sum, and each divisor term is evaluated by splitting
according as the complementary divisor divides the frequency.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 4.
-/

namespace MetaMathlibExt

open Complex Finset

private theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      if n = 1 then 1 else 0 := by
  change (∑ d ∈ n.divisors, (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) d) = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

private theorem sum_moebius_coprime (b n : ℕ) :
    ∑ d ∈ (Nat.gcd b n).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
      if Nat.Coprime b n then 1 else 0 := by
  have h := sum_moebius_divisors (Nat.gcd b n)
  have hgcd : Nat.gcd b n = 1 ↔ Nat.Coprime b n := by
    rw [Nat.coprime_iff_gcd_eq_one]
  simp_rw [hgcd] at h
  exact h

private theorem divisors_gcd_eq_filter (b n : ℕ) (hn : n ≠ 0) :
    (Nat.gcd b n).divisors = n.divisors.filter (· ∣ b) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · intro h
    obtain ⟨hdvd, hgcd0⟩ := h
    rw [Nat.dvd_gcd_iff] at hdvd
    exact ⟨⟨hdvd.2, hn⟩, hdvd.1⟩
  · intro h
    obtain ⟨⟨hdvd_n, _⟩, hdvd_b⟩ := h
    have hgcd0 : Nat.gcd b n ≠ 0 := Nat.gcd_ne_zero_right hn
    exact ⟨(Nat.dvd_gcd_iff.mpr ⟨hdvd_b, hdvd_n⟩), hgcd0⟩

private theorem coprime_sum_eq_moebius (n : ℕ) (hn : n ≠ 0) (f : ℕ → ℂ) :
    ∑ b ∈ Icc 1 n with Nat.Coprime b n, f b =
      ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b), f b := by
  have h_ind : ∀ b ∈ Icc 1 n,
      (if Nat.Coprime b n then f b else 0) =
        f b * ∑ d ∈ (Nat.gcd b n).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    intro b _
    rw [sum_moebius_coprime]
    by_cases hcp : Nat.Coprime b n <;> simp [hcp]
  have hLHS : ∑ b ∈ Icc 1 n with Nat.Coprime b n, f b =
      ∑ b ∈ Icc 1 n, f b * ∑ d ∈ (Nat.gcd b n).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun b hb => h_ind b hb)
  rw [hLHS]
  have h_push : ∀ b ∈ Icc 1 n,
      f b * ∑ d ∈ (Nat.gcd b n).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
        ∑ d ∈ (Nat.gcd b n).divisors, f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    intro b _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun b hb => h_push b hb)]
  have h_filter : ∀ b ∈ Icc 1 n,
      (∑ d ∈ (Nat.gcd b n).divisors, f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
        ∑ d ∈ n.divisors.filter (· ∣ b), f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    intro b _
    rw [divisors_gcd_eq_filter b n hn]
  rw [Finset.sum_congr rfl (fun b hb => h_filter b hb)]
  have h_swap : (∑ b ∈ Icc 1 n, ∑ d ∈ n.divisors.filter (· ∣ b),
        f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      ∑ d ∈ n.divisors, ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
        f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    have h1 : ∀ b ∈ Icc 1 n,
        (∑ d ∈ n.divisors.filter (· ∣ b), f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
          ∑ d ∈ n.divisors,
            if d ∣ b then f b * ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
      intro b _
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun b hb => h1 b hb)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_filter]
  rw [h_swap]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_mul]
  ring

private theorem exp_eq_one_of_dvd (m t k : ℕ) (hm : m ≠ 0) (hdvd : m ∣ k * t) :
    exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ)) = 1 := by
  obtain ⟨l, hl⟩ := hdvd
  have hl_cast : (k : ℂ) * (t : ℂ) = (m : ℂ) * (l : ℂ) := by
    have h2 : ((k * t : ℕ) : ℂ) = ((m * l : ℕ) : ℂ) := by rw [hl]
    simpa only [Nat.cast_mul] using h2
  rw [hl_cast]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have harg : 2 * (Real.pi : ℂ) * I * (-((m : ℂ) * (l : ℂ))) / (m : ℂ) =
      ((-(l : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have hcast : ((-(l : ℤ) : ℤ) : ℂ) = (-(l : ℂ)) := by push_cast; ring
    rw [hcast]
    field_simp
  rw [harg]
  exact Complex.exp_int_mul_two_pi_mul_I (-(l : ℤ))

private theorem exp_congr (n d m t k : ℕ) (hd : d ≠ 0) (hm : m ≠ 0)
    (hdiv : n = d * m) :
    exp (2 * Real.pi * I * (-((k : ℂ) * ((d * t : ℕ) : ℂ))) / (n : ℕ)) =
      exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ)) := by
  congr 1
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn_cast : (n : ℂ) = (d : ℂ) * (m : ℂ) := by rw [hdiv]; push_cast; ring
  rw [hn_cast]
  push_cast
  field_simp

private theorem image_mul_eq_filter (n d m : ℕ) (hd : d ≠ 0) (hdiv : n = d * m) :
    Finset.image (fun t => d * t) (Finset.Icc 1 m) =
      (Finset.Icc 1 n).filter (fun b => d ∣ b) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht1, htm⟩, rfl⟩
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    constructor
    · constructor
      · calc 1 ≤ d * 1 := Nat.le_mul_of_pos_left 1 hdpos
          _ ≤ d * t := Nat.mul_le_mul_left d ht1
      · calc d * t ≤ d * m := Nat.mul_le_mul_left d htm
          _ = n := hdiv.symm
    · exact Dvd.intro t rfl
  · intro h
    obtain ⟨⟨hb1, hbn⟩, hdvd⟩ := h
    obtain ⟨q, hq⟩ := hdvd
    have hq_mem : 1 ≤ q ∧ q ≤ m := by
      have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hq_pos : 1 ≤ q := by
        by_contra hneg
        have hq0 : q = 0 := by omega
        rw [hq0, mul_zero] at hq
        omega
      have hq_le : q ≤ m := by
        have h1 : d * q ≤ d * m := by rw [← hq, ← hdiv]; exact hbn
        exact Nat.le_of_mul_le_mul_left h1 hdpos
      exact ⟨hq_pos, hq_le⟩
    exact ⟨q, hq_mem, hq.symm⟩

private theorem injOn_mul_left (d : ℕ) (hd : d ≠ 0) (s : Finset ℕ) :
    Set.InjOn (fun t => d * t) (↑s : Set ℕ) := by
  intro x _ y _ hxy
  simp only at hxy
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hd) hxy

private theorem inner_b_eq (n k d : ℕ) (hdvd : d ∣ n) (hd0 : d ≠ 0) (hn0 : n ≠ 0) :
    ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
      (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ)) =
      (d : ℂ) * (∑ t ∈ Icc 1 (n / d - 1),
        (t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (n / d : ℕ))) +
        (n : ℂ) := by
  set m := n / d with hm_def
  have hdiv' : d * m = n := Nat.mul_div_cancel' hdvd
  have hdiv : n = d * m := hdiv'.symm
  have hm0 : m ≠ 0 := fun hm => hn0 (by rw [hdiv, hm, mul_zero])
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have himage := image_mul_eq_filter n d m hd0 hdiv
  have hinj := injOn_mul_left d hd0 (Icc 1 m)
  have h_reindex : ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
      (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ)) =
      ∑ t ∈ Icc 1 m, ((d * t : ℕ) : ℂ) *
        exp (2 * Real.pi * I * (-((k : ℂ) * ((d * t : ℕ) : ℂ))) / (n : ℕ)) := by
    rw [← himage, Finset.sum_image hinj]
  rw [h_reindex]
  have h_term : ∀ t ∈ Icc 1 m,
      ((d * t : ℕ) : ℂ) * exp (2 * Real.pi * I * (-((k : ℂ) * ((d * t : ℕ) : ℂ))) / (n : ℕ)) =
        (d : ℂ) * ((t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ))) := by
    intro t _
    rw [exp_congr n d m t k hd0 hm0 hdiv]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun t ht => h_term t ht)]
  rw [← Finset.mul_sum]
  have h_split : ∑ t ∈ Icc 1 m, (t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ)) =
      (∑ t ∈ Icc 1 (m - 1), (t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ))) +
        (m : ℂ) := by
    have hm_eq' : (m - 1) + 1 = m := Nat.sub_add_cancel hm1
    have htop := Finset.sum_Icc_succ_top (show 1 ≤ (m - 1) + 1 by omega)
      (fun t => (t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ)))
    rw [hm_eq'] at htop
    rw [htop]
    have hexp : exp (2 * Real.pi * I * (-(k * m : ℂ)) / (m : ℕ)) = 1 :=
      exp_eq_one_of_dvd m m k hm0 (Dvd.intro k (by ring))
    rw [hexp, mul_one]
  rw [h_split]
  have hdm : (d : ℂ) * (m : ℂ) = (n : ℂ) := by rw [hdiv]; push_cast; ring
  rw [mul_add, hdm]

private theorem sum_Icc_one (N : ℕ) :
    ∑ t ∈ Icc 1 N, (t : ℂ) = (N : ℂ) * ((N : ℂ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hle : 1 ≤ N + 1 := Nat.le_add_left 1 N
    rw [Finset.sum_Icc_succ_top hle]
    rw [ih]
    push_cast
    ring

private theorem sum_Icc_pred (m : ℕ) (hm : 1 ≤ m) :
    ∑ t ∈ Icc 1 (m - 1), (t : ℂ) = (m : ℂ) * ((m : ℂ) - 1) / 2 := by
  have h := sum_Icc_one (m - 1)
  rw [h]
  have hcast : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  rw [hcast]
  ring

private theorem per_div_ndiv {n k d : ℕ} (hdvd : d ∣ n) (hd0 : d ≠ 0) (hn0 : n ≠ 0)
    (hk : ¬ (n / d) ∣ k) :
    (ArithmeticFunction.moebius d : ℂ) *
        (∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
          (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ))) =
      -(n : ℂ) * ((ArithmeticFunction.moebius d : ℂ) /
        (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ)))) +
        (n : ℂ) * (ArithmeticFunction.moebius d : ℂ) := by
  have hSd := inner_b_eq n k d hdvd hd0 hn0
  have hm2' : 2 ≤ n / d := by
    by_contra hlt
    have hlt' : n / d < 2 := lt_of_not_ge hlt
    have h1 : n / d = 1 → False := by
      intro hm1
      rw [hm1] at hk
      exact absurd ⟨k, (one_mul k).symm⟩ hk
    clear hk
    match hm : n / d with
    | 0 =>
      have hcc := Nat.mul_div_cancel' hdvd
      rw [hm, mul_zero] at hcc
      exact hn0 hcc.symm
    | 1 => exact h1 hm
    | m + 2 =>
      rw [hm] at hlt'
      omega
  set m := n / d with hm_def
  have hdiv' : d * m = n := Nat.mul_div_cancel' hdvd
  have hdiv : n = d * m := hdiv'.symm
  rw [hSd]
  have hT := sum_mul_additive_character (q := m) (k := k) hm2' hk
  rw [hT]
  have hdm : (n : ℂ) = (d : ℂ) * (m : ℂ) := by rw [hdiv]; push_cast; ring
  rw [hdm]
  ring

private theorem per_div_dvd {n k d : ℕ} (hdvd : d ∣ n) (hd0 : d ≠ 0) (hn0 : n ≠ 0)
    (hk : (n / d) ∣ k) :
    (ArithmeticFunction.moebius d : ℂ) *
        (∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
          (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ))) =
      (n : ℂ) / 2 * ((ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1)) +
        (n : ℂ) * (ArithmeticFunction.moebius d : ℂ) := by
  have hSd := inner_b_eq n k d hdvd hd0 hn0
  set m := n / d with hm_def
  have hdiv' : d * m = n := Nat.mul_div_cancel' hdvd
  have hdiv : n = d * m := hdiv'.symm
  have hm0 : m ≠ 0 := fun hm => hn0 (by rw [hdiv, hm, mul_zero])
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  rw [hSd]
  have hT : (∑ t ∈ Icc 1 (m - 1),
      (t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ))) =
      (m : ℂ) * ((m : ℂ) - 1) / 2 := by
    have h1 : ∀ t ∈ Icc 1 (m - 1),
        (t : ℂ) * exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ)) = (t : ℂ) := by
      intro t _
      have hexp : exp (2 * Real.pi * I * (-(k * t : ℂ)) / (m : ℕ)) = 1 :=
        exp_eq_one_of_dvd m t k hm0 (dvd_mul_of_dvd_left hk t)
      rw [hexp, mul_one]
    rw [Finset.sum_congr rfl h1]
    exact sum_Icc_pred m hm1
  rw [hT]
  have hdm : (n : ℂ) = (d : ℂ) * (m : ℂ) := by rw [hdiv]; push_cast; ring
  rw [hdm]
  ring

private theorem sum_dvd_restrict {n k : ℕ} (hn : 2 ≤ n) :
    (∑ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
      (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1)) =
    (∑ d ∈ n.divisors.filter (fun d => d < n ∧ (n / d) ∣ k),
      (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1)) := by
  have hsub : n.divisors.filter (fun d => d < n ∧ (n / d) ∣ k) ⊆
      n.divisors.filter (fun d => (n / d) ∣ k) := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.2⟩
  have h0 : ∀ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
      d ∉ n.divisors.filter (fun d => d < n ∧ (n / d) ∣ k) →
      (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1) = 0 := by
    intro d hd_t hd_s
    rw [Finset.mem_filter] at hd_t
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd_t.1
    have hdn : d = n := by
      have hle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hge : n ≤ d := by
        by_contra hlt
        have hlt' : d < n := by omega
        exact hd_s (Finset.mem_filter.mpr ⟨hd_t.1, hlt', hd_t.2⟩)
      omega
    rw [hdn, Nat.div_self (by omega : 0 < n), Nat.cast_one, sub_self, mul_zero]
  exact (Finset.sum_subset hsub h0).symm

/-- **Weighted additive character sum over reduced residues.** For a positive integer $r$ and an
integer $x$ write $e_r(x) = \exp(2\pi i x / r)$, and let $\mu$ be the Möbius function. For all
natural numbers $n \ge 2$ and $k \ge 1$,

$$\sum_{1 \le b \le n,\ \gcd(b, n) = 1} b \, e_n(-kb)
= -n \sum_{d \mid n,\ (n/d) \nmid k} \frac{\mu(d)}{1 - e_{n/d}(-k)} +
\frac{n}{2} \sum_{d \mid n,\ d < n,\ (n/d) \mid k} \mu(d) \left(\frac{n}{d} - 1\right).$$

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 4. -/
public theorem coprime_sum_mul_additive_character {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∑ b ∈ Icc 1 n with Nat.Coprime b n, (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / n) =
      -n * ∑ d ∈ n.divisors with ¬ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) /
            (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ))) +
        n / 2 * ∑ d ∈ n.divisors with d < n ∧ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1) := by
  have hnk : n ≠ 0 ∧ k ≠ 0 := by omega
  have hn0 := hnk.1
  have hn1 : n ≠ 1 := by omega
  have hmob := coprime_sum_eq_moebius n hn0
    (fun b => (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / n))
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => (n / d) ∣ k)
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
        (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ)))
  calc (∑ b ∈ Icc 1 n with Nat.Coprime b n, (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / n))
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
          (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ)) := hmob
    _ = (∑ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
            (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ))) +
        (∑ d ∈ n.divisors.filter (fun d => ¬ (n / d) ∣ k),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
            (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ))) := hsplit.symm
    _ = -n * ∑ d ∈ n.divisors with ¬ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) /
            (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ))) +
        n / 2 * ∑ d ∈ n.divisors with d < n ∧ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1) := by
      have hA : (∑ d ∈ n.divisors.filter (fun d => ¬ (n / d) ∣ k),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
              (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ))) =
          -(n : ℂ) * (∑ d ∈ n.divisors.filter (fun d => ¬ (n / d) ∣ k),
            (ArithmeticFunction.moebius d : ℂ) /
              (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ)))) +
            (n : ℂ) * (∑ d ∈ n.divisors.filter (fun d => ¬ (n / d) ∣ k),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_filter] at hd
        have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hd.1)
        exact per_div_ndiv (Nat.dvd_of_mem_divisors hd.1) hd0 hn0 hd.2
      have hB : (∑ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            ∑ b ∈ (Icc 1 n).filter (fun b => d ∣ b),
              (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / (n : ℕ))) =
          (n : ℂ) / 2 * (∑ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
            (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1)) +
            (n : ℂ) * (∑ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_filter] at hd
        have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hd.1)
        exact per_div_dvd (Nat.dvd_of_mem_divisors hd.1) hd0 hn0 hd.2
      have hBf := sum_dvd_restrict (n := n) (k := k) hn
      have htot : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) = 0 := by
        rw [sum_moebius_divisors, ite_eq_right hn1]
      have hsplitμ := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => (n / d) ∣ k)
        (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ))
      have hzero : (n : ℂ) * (∑ d ∈ n.divisors.filter (fun d => (n / d) ∣ k),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) +
          (n : ℂ) * (∑ d ∈ n.divisors.filter (fun d => ¬ (n / d) ∣ k),
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)) = 0 := by
        rw [← mul_add, hsplitμ, htot, mul_zero]
      rw [hA, hB, hBf]
      have hcomb : ∀ X Y Z W : ℂ, (X + Y) + (Z + W) = (Z + X) + (Y + W) := by
        intro X Y Z W
        ring
      rw [hcomb, hzero, add_zero]

end MetaMathlibExt
